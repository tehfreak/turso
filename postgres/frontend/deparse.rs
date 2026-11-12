//! PostgreSQL's text of a row-level security condition, as `pg_get_expr`
//! prints it for `pg_policy.polqual` and `pg_policies.qual`.
//!
//! The catalog stores what the engine compiled the condition into, so this
//! turns the engine's forms back into PostgreSQL's: `GLOB 'a*'` is printed
//! as `~~ 'a%'::text`, `CAST (1 AS boolean)` as `true`. PostgreSQL prints the
//! condition after resolving types, with every operator in parentheses and
//! casts where types meet, such as `'x'::text` and `(v)::text` for a
//! `varchar` column, so the printer follows the types of the table's
//! columns. A form it does not know how to print as PostgreSQL does gives
//! None.

use turso_core::schema::BTreeTable;
use turso_parser::ast;
use turso_pg_parser::quote_identifier;
use turso_pg_parser::translator::role_keyword;

/// PostgreSQL's text of `condition`, a condition on the columns of `table`,
/// or None when it has a form this module does not print.
pub(crate) fn condition_text(condition: &ast::Expr, table: &BTreeTable) -> Option<String> {
    let printed = Printer { table }.expr(condition)?;
    Some(printed.typed_text(None))
}

/// The types that decide how PostgreSQL prints an expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PgType {
    Boolean,
    Integer,
    Bigint,
    Numeric,
    Text,
    Varchar,
    /// The type of `current_user` and the other role keywords.
    Name,
    /// A quoted literal that has no type until it meets another operand.
    UnknownLiteral,
    Other,
}

impl PgType {
    fn of_column(declared: &str) -> Self {
        let base = declared.split('(').next().unwrap_or("").trim();
        match base.to_ascii_uppercase().as_str() {
            "BOOLEAN" | "BOOL" => Self::Boolean,
            "INTEGER" | "INT" | "INT4" => Self::Integer,
            "BIGINT" | "INT8" => Self::Bigint,
            "NUMERIC" | "DECIMAL" => Self::Numeric,
            "TEXT" => Self::Text,
            "VARCHAR" | "CHARACTER VARYING" => Self::Varchar,
            _ => Self::Other,
        }
    }

    fn is_integer(self) -> bool {
        matches!(self, Self::Integer | Self::Bigint)
    }
}

/// An expression as PostgreSQL prints it, and its type.
struct Printed {
    text: String,
    ty: PgType,
}

impl Printed {
    fn new(text: impl Into<String>, ty: PgType) -> Self {
        Self {
            text: text.into(),
            ty,
        }
    }

    /// The text where the expression meets an operand of type `other`: a
    /// quoted literal takes that type, `text` when there is none, and a
    /// `varchar` column is compared as `text`.
    fn typed_text(&self, other: Option<PgType>) -> String {
        match self.ty {
            PgType::UnknownLiteral => {
                let label = match other {
                    Some(PgType::Name) => "name",
                    _ => "text",
                };
                format!("{}::{label}", self.text)
            }
            PgType::Varchar if other.is_some() => format!("({})::text", self.text),
            _ => self.text.clone(),
        }
    }

    /// Whether PostgreSQL prints the expression this way when it meets an
    /// operand of type `other`: a quoted literal printed as `text` or `name`
    /// must meet a string or a role keyword.
    fn meets(&self, other: PgType) -> bool {
        match (self.ty, other) {
            (PgType::UnknownLiteral, PgType::UnknownLiteral) => false,
            (PgType::UnknownLiteral, other) => {
                matches!(other, PgType::Text | PgType::Varchar | PgType::Name)
            }
            _ => true,
        }
    }
}

struct Printer<'a> {
    table: &'a BTreeTable,
}

impl Printer<'_> {
    fn expr(&self, expr: &ast::Expr) -> Option<Printed> {
        match expr {
            ast::Expr::Parenthesized(inner) => match inner.as_slice() {
                [inner] => self.expr(inner),
                _ => None,
            },
            ast::Expr::Id(name) | ast::Expr::Qualified(_, name) => self.column(name),
            ast::Expr::Literal(literal) => literal_text(literal),
            ast::Expr::Cast {
                expr,
                type_name: Some(type_name),
            } if type_name.name.eq_ignore_ascii_case("boolean") => match expr.as_ref() {
                ast::Expr::Literal(ast::Literal::Numeric(value)) if value == "1" => {
                    Some(Printed::new("true", PgType::Boolean))
                }
                ast::Expr::Literal(ast::Literal::Numeric(value)) if value == "0" => {
                    Some(Printed::new("false", PgType::Boolean))
                }
                _ => None,
            },
            ast::Expr::Unary(ast::UnaryOperator::Not, operand) => {
                let operand = self.expr(operand)?;
                Some(Printed::new(
                    format!("(NOT {})", operand.typed_text(None)),
                    PgType::Boolean,
                ))
            }
            ast::Expr::Unary(ast::UnaryOperator::Negative, operand) => match operand.as_ref() {
                ast::Expr::Literal(ast::Literal::Numeric(value)) => negative_number_text(value),
                _ => {
                    let operand = self.expr(operand)?;
                    if !operand.ty.is_integer() && operand.ty != PgType::Numeric {
                        return None;
                    }
                    Some(Printed::new(format!("(- {})", operand.text), operand.ty))
                }
            },
            ast::Expr::Binary(_, ast::Operator::And | ast::Operator::Or, _) => self.bool_expr(expr),
            ast::Expr::Binary(lhs, operator, rhs) => self.operator(lhs, *operator, rhs),
            ast::Expr::IsNull(operand) => self.null_test(operand, "IS NULL"),
            ast::Expr::NotNull(operand) => self.null_test(operand, "IS NOT NULL"),
            ast::Expr::InList { lhs, not, rhs } => self.in_list(lhs, *not, rhs),
            ast::Expr::Between {
                lhs,
                not,
                start,
                end,
            } => self.between(lhs, *not, start, end),
            ast::Expr::Like {
                lhs,
                not,
                op: ast::LikeOperator::Glob,
                rhs,
                escape: None,
            } => self.like(lhs, *not, rhs),
            ast::Expr::FunctionCall {
                name,
                distinctness: None,
                args,
                order_by,
                within_group,
                filter_over,
            } if order_by.is_empty()
                && within_group.is_empty()
                && filter_over.filter_clause.is_none()
                && filter_over.over_clause.is_none() =>
            {
                self.function_call(name.as_str(), args)
            }
            ast::Expr::Subquery(select) => self.scalar_subquery(select),
            _ => None,
        }
    }

    fn column(&self, name: &ast::Name) -> Option<Printed> {
        let (_, column) = self.table.get_column(name.as_str())?;
        Some(Printed::new(
            quote_identifier(name.as_str()),
            PgType::of_column(&column.ty_str),
        ))
    }

    /// AND and OR, with the conditions of a chain of the same operator in
    /// one list, as PostgreSQL's parser builds them: `a AND b AND c` is one
    /// AND of three conditions, while `a AND (b AND c)` keeps the inner one.
    fn bool_expr(&self, expr: &ast::Expr) -> Option<Printed> {
        let ast::Expr::Binary(_, operator, _) = expr else {
            unreachable!("the caller passes an AND or an OR");
        };
        let keyword = if *operator == ast::Operator::And {
            " AND "
        } else {
            " OR "
        };
        let mut operands = Vec::new();
        let mut left = expr;
        while let ast::Expr::Binary(lhs, op, rhs) = unparenthesized(left) {
            if op != operator {
                break;
            }
            operands.push(rhs.as_ref());
            left = lhs;
        }
        operands.push(left);
        operands.reverse();
        let texts = operands
            .into_iter()
            .map(|operand| Some(self.expr(operand)?.typed_text(None)))
            .collect::<Option<Vec<_>>>()?;
        Some(Printed::new(
            format!("({})", texts.join(keyword)),
            PgType::Boolean,
        ))
    }

    fn operator(
        &self,
        lhs: &ast::Expr,
        operator: ast::Operator,
        rhs: &ast::Expr,
    ) -> Option<Printed> {
        let (symbol, is_comparison) = match operator {
            ast::Operator::Equals => ("=", true),
            ast::Operator::NotEquals => ("<>", true),
            ast::Operator::Less => ("<", true),
            ast::Operator::LessEquals => ("<=", true),
            ast::Operator::Greater => (">", true),
            ast::Operator::GreaterEquals => (">=", true),
            ast::Operator::Add => ("+", false),
            ast::Operator::Subtract => ("-", false),
            ast::Operator::Multiply => ("*", false),
            ast::Operator::Divide => ("/", false),
            ast::Operator::Modulus => ("%", false),
            _ => return None,
        };
        let lhs = self.expr(lhs)?;
        let rhs = self.expr(rhs)?;
        if !lhs.meets(rhs.ty) || !rhs.meets(lhs.ty) {
            return None;
        }
        let ty = if is_comparison {
            PgType::Boolean
        } else {
            match (lhs.ty, rhs.ty) {
                (PgType::Integer, PgType::Integer) => PgType::Integer,
                (left, right) if left.is_integer() && right.is_integer() => PgType::Bigint,
                (PgType::Numeric, other) | (other, PgType::Numeric)
                    if other.is_integer() || other == PgType::Numeric =>
                {
                    PgType::Numeric
                }
                _ => return None,
            }
        };
        let text = format!(
            "({} {symbol} {})",
            lhs.typed_text(Some(rhs.ty)),
            rhs.typed_text(Some(lhs.ty))
        );
        Some(Printed::new(text, ty))
    }

    fn null_test(&self, operand: &ast::Expr, test: &str) -> Option<Printed> {
        let operand = self.expr(operand)?;
        Some(Printed::new(
            format!("({} {test})", operand.typed_text(None)),
            PgType::Boolean,
        ))
    }

    /// `x IN (a, b)` is `x = ANY (ARRAY[a, b])` in PostgreSQL, and `x IN
    /// (a)` is `x = a`; NOT IN is `<> ALL`.
    fn in_list(&self, lhs: &ast::Expr, not: bool, list: &[Box<ast::Expr>]) -> Option<Printed> {
        let lhs = self.expr(lhs)?;
        let elements = list
            .iter()
            .map(|element| self.expr(element))
            .collect::<Option<Vec<_>>>()?;
        if elements
            .iter()
            .any(|element| !element.meets(lhs.ty) || !lhs.meets(element.ty))
        {
            return None;
        }
        let (symbol, quantifier) = if not { ("<>", "ALL") } else { ("=", "ANY") };
        let text = match elements.as_slice() {
            [] => return None,
            [element] => format!(
                "({} {symbol} {})",
                lhs.typed_text(Some(element.ty)),
                element.typed_text(Some(lhs.ty))
            ),
            [first, ..] => {
                let texts: Vec<String> = elements
                    .iter()
                    .map(|element| element.typed_text(Some(lhs.ty)))
                    .collect();
                format!(
                    "({} {symbol} {quantifier} (ARRAY[{}]))",
                    lhs.typed_text(Some(first.ty)),
                    texts.join(", ")
                )
            }
        };
        Some(Printed::new(text, PgType::Boolean))
    }

    /// `x BETWEEN a AND b` is `x >= a AND x <= b` in PostgreSQL, and NOT
    /// BETWEEN is `x < a OR x > b`.
    fn between(
        &self,
        lhs: &ast::Expr,
        not: bool,
        start: &ast::Expr,
        end: &ast::Expr,
    ) -> Option<Printed> {
        let (low, high, keyword) = if not {
            (ast::Operator::Less, ast::Operator::Greater, "OR")
        } else {
            (
                ast::Operator::GreaterEquals,
                ast::Operator::LessEquals,
                "AND",
            )
        };
        let low = self.operator(lhs, low, start)?;
        let high = self.operator(lhs, high, end)?;
        Some(Printed::new(
            format!("({} {keyword} {})", low.text, high.text),
            PgType::Boolean,
        ))
    }

    /// The engine runs PostgreSQL's case-sensitive LIKE with a literal
    /// pattern as GLOB, with `%` and `_` turned into `*` and `?`.
    fn like(&self, lhs: &ast::Expr, not: bool, pattern: &ast::Expr) -> Option<Printed> {
        let ast::Expr::Literal(ast::Literal::String(pattern)) = pattern else {
            return None;
        };
        let glob = unquote(pattern)?;
        if glob.contains(['%', '_', '[', ']', '\\']) {
            return None;
        }
        let like_pattern = glob.replace('*', "%").replace('?', "_");
        let lhs = self.expr(lhs)?;
        if !matches!(lhs.ty, PgType::Text | PgType::Varchar) {
            return None;
        }
        let pattern = Printed::new(quote_literal(&like_pattern), PgType::UnknownLiteral);
        let symbol = if not { "!~~" } else { "~~" };
        Some(Printed::new(
            format!(
                "({} {symbol} {})",
                lhs.typed_text(Some(PgType::Text)),
                pattern.typed_text(Some(PgType::Text))
            ),
            PgType::Boolean,
        ))
    }

    fn function_call(&self, name: &str, args: &[Box<ast::Expr>]) -> Option<Printed> {
        if args.is_empty() {
            if let Some(keyword) = role_keyword(name) {
                return Some(Printed::new(keyword, PgType::Name));
            }
        }
        let args = args
            .iter()
            .map(|arg| self.expr(arg))
            .collect::<Option<Vec<_>>>()?;
        // A quoted literal argument takes its type from the function, which
        // is not known here.
        if args.iter().any(|arg| arg.ty == PgType::UnknownLiteral) {
            return None;
        }
        let texts: Vec<String> = args.iter().map(|arg| arg.text.clone()).collect();
        if name.eq_ignore_ascii_case("coalesce") {
            let first = args.first()?;
            if args.iter().any(|arg| arg.ty != first.ty) {
                return None;
            }
            return Some(Printed::new(
                format!("COALESCE({})", texts.join(", ")),
                first.ty,
            ));
        }
        let ty = match name.to_ascii_lowercase().as_str() {
            "lower" | "upper" => PgType::Text,
            _ => PgType::Other,
        };
        let name = name
            .split('.')
            .map(quote_identifier)
            .collect::<Vec<_>>()
            .join(".");
        Some(Printed::new(format!("{name}({})", texts.join(", ")), ty))
    }

    /// A subquery without FROM that computes one value, such as `(SELECT
    /// current_user)`, which PostgreSQL prints as `( SELECT CURRENT_USER AS
    /// "current_user")`.
    fn scalar_subquery(&self, select: &ast::Select) -> Option<Printed> {
        if select.with.is_some()
            || !select.order_by.is_empty()
            || select.limit.is_some()
            || !select.body.compounds.is_empty()
        {
            return None;
        }
        let ast::OneSelect::Select {
            distinctness: None,
            columns,
            from: None,
            where_clause: None,
            group_by: None,
            window_clause,
        } = &select.body.select
        else {
            return None;
        };
        let ([ast::ResultColumn::Expr(expr, alias)], true) =
            (columns.as_slice(), window_clause.is_empty())
        else {
            return None;
        };
        let value = self.expr(expr)?;
        let text = match alias {
            Some(ast::As::As(name) | ast::As::Elided(name)) => format!(
                "( SELECT {} AS {})",
                value.typed_text(None),
                quote_identifier(name.as_str())
            ),
            _ => format!("( SELECT {})", value.typed_text(None)),
        };
        Some(Printed::new(text, value.ty))
    }
}

fn unparenthesized(expr: &ast::Expr) -> &ast::Expr {
    match expr {
        ast::Expr::Parenthesized(inner) if inner.len() == 1 => unparenthesized(&inner[0]),
        _ => expr,
    }
}

fn literal_text(literal: &ast::Literal) -> Option<Printed> {
    match literal {
        ast::Literal::Numeric(value) => number_text(value),
        ast::Literal::String(quoted) => Some(Printed::new(
            quote_literal(&unquote(quoted)?),
            PgType::UnknownLiteral,
        )),
        ast::Literal::True => Some(Printed::new("true", PgType::Boolean)),
        ast::Literal::False => Some(Printed::new("false", PgType::Boolean)),
        _ => None,
    }
}

/// A number as PostgreSQL prints a constant: an `integer` as it is, a
/// `bigint` quoted with its type, and a decimal number as it is.
fn number_text(value: &str) -> Option<Printed> {
    if let Ok(number) = value.parse::<i64>() {
        return Some(if i32::try_from(number).is_ok() {
            Printed::new(number.to_string(), PgType::Integer)
        } else {
            Printed::new(format!("'{number}'::bigint"), PgType::Bigint)
        });
    }
    let is_decimal = value.chars().all(|c| c.is_ascii_digit() || c == '.')
        && value.chars().filter(|c| *c == '.').count() == 1
        && value.chars().next().is_some_and(|c| c.is_ascii_digit());
    is_decimal.then(|| Printed::new(value, PgType::Numeric))
}

/// A negative number, which PostgreSQL prints quoted with its type, such as
/// `'-1'::integer`.
fn negative_number_text(value: &str) -> Option<Printed> {
    let positive = number_text(value)?;
    let (type_name, ty) = match positive.ty {
        PgType::Integer => ("integer", PgType::Integer),
        PgType::Bigint => ("bigint", PgType::Bigint),
        PgType::Numeric => ("numeric", PgType::Numeric),
        _ => return None,
    };
    let digits = positive.text.trim_start_matches('\'');
    let digits = digits.split('\'').next().unwrap_or(digits);
    Some(Printed::new(format!("'-{digits}'::{type_name}"), ty))
}

/// The text of an engine string literal, which keeps its quotes.
fn unquote(quoted: &str) -> Option<String> {
    let inner = quoted.strip_prefix('\'')?.strip_suffix('\'')?;
    Some(inner.replace("''", "'"))
}

/// `text` as PostgreSQL's `quote_literal` writes it: in single quotes, with
/// quotes doubled, and as an escape string when it has a backslash.
fn quote_literal(text: &str) -> String {
    let quoted = text.replace('\'', "''");
    if text.contains('\\') {
        format!("E'{}'", quoted.replace('\\', "\\\\"))
    } else {
        format!("'{quoted}'")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::policies::parse_condition;

    fn table() -> BTreeTable {
        BTreeTable::from_sql(
            "CREATE TABLE t (id INT, owner TEXT, published BOOLEAN, n BIGINT, \
             v VARCHAR(10), \"Weird Col\" INT, price NUMERIC)",
            2,
        )
        .unwrap()
    }

    fn text(stored: &str) -> Option<String> {
        condition_text(&parse_condition(stored).unwrap(), &table())
    }

    /// The pairs are what the engine stores for a condition and what
    /// PostgreSQL 18's pg_get_expr prints for it.
    #[test]
    fn conditions_print_as_postgres_prints_them() {
        for (stored, expected) in [
            ("\"owner\" = current_user ()", "(owner = CURRENT_USER)"),
            (
                "\"owner\" = (SELECT current_user () current_user)",
                "(owner = ( SELECT CURRENT_USER AS \"current_user\"))",
            ),
            ("CAST (1 AS boolean)", "true"),
            ("CAST (0 AS boolean)", "false"),
            (
                "(\"id\" > 0) AND (\"id\" < 10) AND \"published\"",
                "((id > 0) AND (id < 10) AND published)",
            ),
            (
                "(NOT \"published\") OR (\"id\" IN (1, 2))",
                "((NOT published) OR (id = ANY (ARRAY[1, 2])))",
            ),
            (
                "(\"owner\" = 'a''b') AND (\"v\" = 'x') AND (\"n\" > 5) AND (\"id\" = - 1)",
                "((owner = 'a''b'::text) AND ((v)::text = 'x'::text) AND (n > 5) AND (id = '-1'::integer))",
            ),
            (
                "(\"Weird Col\" ISNULL) OR (\"id\" NOTNULL)",
                "((\"Weird Col\" IS NULL) OR (id IS NOT NULL))",
            ),
            (
                "((\"id\" + (1 * 2)) > 3) AND (lower (\"owner\") != 'x') AND (\"owner\" GLOB 'a*')",
                "(((id + (1 * 2)) > 3) AND (lower(owner) <> 'x'::text) AND (owner ~~ 'a%'::text))",
            ),
            (
                "(session_user () = \"owner\") AND (\"id\" BETWEEN 1 AND 3) AND (\"price\" > 1.5)",
                "((SESSION_USER = owner) AND ((id >= 1) AND (id <= 3)) AND (price > 1.5))",
            ),
            (
                "((\"id\" > 0) AND (\"id\" < 5)) OR ((\"id\" > 10) AND ((\"id\" < 20) OR (\"id\" = 30)))",
                "(((id > 0) AND (id < 5)) OR ((id > 10) AND ((id < 20) OR (id = 30))))",
            ),
            (
                "(COALESCE (\"id\", 0) = 0) AND (\"owner\" IN ('a', 'b')) AND (\"id\" NOT IN (1))",
                "((COALESCE(id, 0) = 0) AND (owner = ANY (ARRAY['a'::text, 'b'::text])) AND (id <> 1))",
            ),
            ("current_user () = 'x'", "(CURRENT_USER = 'x'::name)"),
            ("\"id\" = 2147483648", "(id = '2147483648'::bigint)"),
            (
                "\"id\" > 0 AND (\"id\" > 1 AND \"id\" > 2)",
                "((id > 0) AND ((id > 1) AND (id > 2)))",
            ),
        ] {
            assert_eq!(text(stored).as_deref(), Some(expected), "{stored}");
        }
    }

    #[test]
    fn conditions_postgres_prints_differently_give_none() {
        for stored in [
            "\"id\" = '1'",
            "\"owner\" GLOB 'a[bc]'",
            "\"missing\" = 1",
            "CAST (\"owner\" AS INTEGER) = 1",
            "abs ('1') = 1",
        ] {
            assert_eq!(text(stored), None, "{stored}");
        }
    }
}
