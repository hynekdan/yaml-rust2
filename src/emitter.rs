//! YAML serialization helpers.

use crate::char_traits;
use crate::yaml::{Hash, Yaml};
use std::convert::From;
use std::error::Error;
use std::fmt::{self, Display};

/// An error when emitting YAML.
#[derive(Copy, Clone, Debug)]
pub enum EmitError {
    /// A formatting error.
    FmtError(fmt::Error),
}

impl Error for EmitError {
    fn cause(&self) -> Option<&dyn Error> {
        None
    }
}

impl Display for EmitError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            EmitError::FmtError(ref err) => Display::fmt(err, formatter),
        }
    }
}

impl From<fmt::Error> for EmitError {
    fn from(f: fmt::Error) -> Self {
        EmitError::FmtError(f)
    }
}

/// The YAML serializer.
///
/// ```
/// # use yaml_rust2::{YamlLoader, YamlEmitter};
/// let input_string = "a: b\nc: d";
/// let yaml = YamlLoader::load_from_str(input_string).unwrap();
///
/// let mut output = String::new();
/// YamlEmitter::new(&mut output).dump(&yaml[0]).unwrap();
///
/// assert_eq!(output, r#"---
/// a: b
/// c: d
/// "#);
/// ```
#[allow(clippy::module_name_repetitions)]
pub struct YamlEmitter<'a> {
    writer: &'a mut dyn fmt::Write,
    best_indent: usize,
    compact: bool,
    level: isize,
    multiline_strings: bool,
}

/// A convenience alias for emitter functions that may fail without returning a value.
pub type EmitResult = Result<(), EmitError>;

// from serialize::json
fn escape_str(wr: &mut dyn fmt::Write, v: &str) -> Result<(), fmt::Error> {
    // If the string starts and ends with a single quote, wrap it in double quotes
    // this is better readable and more compact
    if v.starts_with('\'') && v.ends_with('\'') {
        wr.write_str("\"")?;
        for c in v.chars() {
            if c == '"' {
                wr.write_str("\\\"")?;
            } else if c == '\\' {
                wr.write_str("\\\\")?;
            } else {
                wr.write_char(c)?;
            }
        }
        wr.write_str("\"")?;
        return Ok(());
    }

    // Otherwise, use single-quoted style and double any single quotes inside
    wr.write_str("'")?;
    for c in v.chars() {
        if c == '\'' {
            wr.write_str("''")?;
        } else {
            wr.write_char(c)?;
        }
    }
    wr.write_str("'")?;
    Ok(())
}

impl<'a> YamlEmitter<'a> {
    /// Create a new emitter serializing into `writer`.
    pub fn new(writer: &'a mut dyn fmt::Write) -> YamlEmitter<'a> {
        YamlEmitter {
            writer,
            best_indent: 2,
            compact: true,
            level: -1,
            multiline_strings: false,
        }
    }

    /// Set 'compact inline notation' on or off, as described for block
    /// [sequences](http://www.yaml.org/spec/1.2/spec.html#id2797382)
    /// and
    /// [mappings](http://www.yaml.org/spec/1.2/spec.html#id2798057).
    ///
    /// In this form, blocks cannot have any properties (such as anchors
    /// or tags), which should be OK, because this emitter doesn't
    /// (currently) emit those anyways.
    pub fn compact(&mut self, compact: bool) {
        self.compact = compact;
    }

    /// Determine if this emitter is using 'compact inline notation'.
    #[must_use]
    pub fn is_compact(&self) -> bool {
        self.compact
    }

    /// Render strings containing multiple lines in [literal style].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use yaml_rust2::{Yaml, YamlEmitter, YamlLoader};
    ///
    /// let input = r#"{foo: "bar!\nbar!", baz: 42}"#;
    /// let parsed = YamlLoader::load_from_str(input).unwrap();
    /// eprintln!("{:?}", parsed);
    ///
    /// let mut output = String::new();
    /// let mut emitter = YamlEmitter::new(&mut output);
    /// emitter.multiline_strings(true);
    /// emitter.dump(&parsed[0]).unwrap();
    /// assert_eq!(output.as_str(), "\
    /// ---
    /// foo: |-
    ///   bar!
    ///   bar!
    /// baz: 42
    /// ");
    /// ```
    ///
    /// [literal style]: https://yaml.org/spec/1.2/spec.html#id2795688
    pub fn multiline_strings(&mut self, multiline_strings: bool) {
        self.multiline_strings = multiline_strings;
    }

    /// Determine if this emitter will emit multiline strings when appropriate.
    #[must_use]
    pub fn is_multiline_strings(&self) -> bool {
        self.multiline_strings
    }

    /// Dump Yaml to an output stream.
    /// # Errors
    /// Returns `EmitError` when an error occurs.
    pub fn dump(&mut self, doc: &Yaml) -> EmitResult {
        // write DocumentStart
        writeln!(self.writer, "---")?;
        self.level = -1;
        let emit_result = self.emit_node(doc);
        write!(self.writer, "\n")?; //finish a document with an empty line
        emit_result
    }

    fn write_indent(&mut self) -> EmitResult {
        if self.level <= 0 {
            return Ok(());
        }
        for _ in 0..self.level {
            for _ in 0..self.best_indent {
                write!(self.writer, " ")?;
            }
        }
        Ok(())
    }

    fn emit_node(&mut self, node: &Yaml) -> EmitResult {
        match *node {
            Yaml::Array(ref v) => self.emit_array(v),
            Yaml::Hash(ref h) => self.emit_hash(h),
            Yaml::String(ref v) => {
                if self.multiline_strings
                    && v.contains('\n')
                    && char_traits::is_valid_literal_block_scalar(v)
                {
                    self.emit_literal_block(v)?;
                } else if need_quotes(v) {
                    escape_str(self.writer, v)?;
                } else {
                    write!(self.writer, "{v}")?;
                }
                Ok(())
            }
            Yaml::Boolean(v) => {
                if v {
                    self.writer.write_str("true")?;
                } else {
                    self.writer.write_str("false")?;
                }
                Ok(())
            }
            Yaml::Integer(v) => {
                write!(self.writer, "{v}")?;
                Ok(())
            }
            Yaml::Real(ref v) => {
                write!(self.writer, "{v}")?;
                Ok(())
            }
            Yaml::Null | Yaml::BadValue => {
                write!(self.writer, "~")?;
                Ok(())
            }
            // XXX(chenyh) Alias
            Yaml::Alias(_) => Ok(()),
        }
    }

    fn emit_literal_block(&mut self, v: &str) -> EmitResult {
        let ends_with_newline = v.ends_with('\n');
        if ends_with_newline {
            self.writer.write_str("|")?;
        } else {
            self.writer.write_str("|-")?;
        }

        self.level += 1;
        // lines() will omit the last line if it is empty.
        for line in v.lines() {
            writeln!(self.writer)?;
            self.write_indent()?;
            // It's literal text, so don't escape special chars.
            self.writer.write_str(line)?;
        }
        self.level -= 1;
        Ok(())
    }

    fn emit_array(&mut self, v: &[Yaml]) -> EmitResult {
        if v.is_empty() {
            write!(self.writer, "[]")?;
        } else {
            self.level += 1;
            for (cnt, x) in v.iter().enumerate() {
                if cnt > 0 {
                    writeln!(self.writer)?;
                    self.write_indent()?;
                }
                write!(self.writer, "-")?;
                self.emit_val(true, x)?;
            }
            self.level -= 1;
        }
        Ok(())
    }

    fn emit_hash(&mut self, h: &Hash) -> EmitResult {
        if h.is_empty() {
            self.writer.write_str("{}")?;
        } else {
            self.level += 1;
            for (cnt, (k, v)) in h.iter().enumerate() {
                let complex_key = matches!(*k, Yaml::Hash(_) | Yaml::Array(_));
                if cnt > 0 {
                    writeln!(self.writer)?;
                    self.write_indent()?;
                }
                if complex_key {
                    write!(self.writer, "?")?;
                    self.emit_val(true, k)?;
                    writeln!(self.writer)?;
                    self.write_indent()?;
                    write!(self.writer, ":")?;
                    self.emit_val(true, v)?;
                } else {
                    self.emit_node(k)?;
                    write!(self.writer, ":")?;
                    self.emit_val(false, v)?;
                }
            }
            self.level -= 1;
        }
        Ok(())
    }

    /// Emit a yaml as a hash or array value: i.e., which should appear
    /// following a ":" or "-", either after a space, or on a new line.
    /// If `inline` is true, then the preceding characters are distinct
    /// and short enough to respect the compact flag.
    fn emit_val(&mut self, inline: bool, val: &Yaml) -> EmitResult {
        match *val {
            Yaml::Array(ref v) => {
                if (inline && self.compact) || v.is_empty() {
                    write!(self.writer, " ")?;
                } else {
                    writeln!(self.writer)?;
                    self.level += 1;
                    self.write_indent()?;
                    self.level -= 1;
                }
                self.emit_array(v)
            }
            Yaml::Hash(ref h) => {
                if (inline && self.compact) || h.is_empty() {
                    write!(self.writer, " ")?;
                } else {
                    writeln!(self.writer)?;
                    self.level += 1;
                    self.write_indent()?;
                    self.level -= 1;
                }
                self.emit_hash(h)
            }
            _ => {
                write!(self.writer, " ")?;
                self.emit_node(val)
            }
        }
    }
}

/// Check if the string requires quoting.
/// Strings starting with any of the following characters must be quoted.
/// :, &, *, ?, |, -, <, >, =, !, %, @
/// Strings containing any of the following characters must be quoted.
/// {, }, \[, t \], ,, #, `
///
/// If the string contains any of the following control characters, it must be escaped with double quotes:
/// \0, \x01, \x02, \x03, \x04, \x05, \x06, \a, \b, \t, \n, \v, \f, \r, \x0e, \x0f, \x10, \x11, \x12, \x13, \x14, \x15, \x16, \x17, \x18, \x19, \x1a, \e, \x1c, \x1d, \x1e, \x1f, \N, \_, \L, \P
///
/// Finally, there are other cases when the strings must be quoted, no matter if you're using single or double quotes:
/// * When the string is true or false (otherwise, it would be treated as a boolean value);
/// * When the string is null or ~ (otherwise, it would be considered as a null value);
/// * When the string looks like a number, such as integers (e.g. 2, 14, etc.), floats (e.g. 2.6, 14.9) and exponential numbers (e.g. 12e7, etc.) (otherwise, it would be treated as a numeric value);
/// * When the string looks like a date (e.g. 2014-12-31) (otherwise it would be automatically converted into a Unix timestamp).
#[allow(clippy::doc_markdown)]
fn need_quotes(string: &str) -> bool {
    fn need_quotes_spaces(string: &str) -> bool {
        string.starts_with(' ') || string.ends_with(' ')
    }

    string.is_empty()
        || need_quotes_spaces(string)
        || string.starts_with(|character: char| {
            matches!(
                character,
                '&' | '*' | '?' | '|' | '-' | '<' | '>' | '=' | '!' | '%' | '@'
            )
        })
        || string.contains(|character: char| {
            matches!(character, ':'
            | '{'
            | '}'
            | '['
            | ']'
            | ','
            | '#'
            | '`'
            | '\\'
            | '\0'..='\x08'
            | '\x0b'
            | '\x0c'
            | '\x0e'..='\x1f'
            | '\x7f'
            | '\t'
            | '\n'
            | '\r')
        })
        || [
            // Canonical forms of the boolean values in the Core schema.
            "true", "false", "True", "False", "TRUE", "FALSE",
            // Canonical forms of the null value in the Core schema.
            "null", "Null", "NULL", "~",
            // These can be quoted when emitting so that YAML 1.1 parsers do not parse them as
            // booleans. This doesn't cause any issue with YAML 1.2 parsers.
            "y", "Y", "n", "N", "yes", "Yes", "YES", "no", "No", "NO", "True", "TRUE", "False",
            "FALSE", "on", "On", "ON", "off", "Off", "OFF",
        ]
        .contains(&string)
        || string.starts_with('.')
        || string.starts_with("0x")
        || string.parse::<i64>().is_ok()
        || string.parse::<f64>().is_ok()
        || (string.starts_with('\'') && string.ends_with('\'')) // special case for single quotes
}

#[cfg(test)]
mod test {
    use super::YamlEmitter;
    use crate::YamlLoader;

    #[test]
    fn test_multiline_string() {
        let input = r#"{foo: "bar!\nbar!", baz: 42}"#;
        let parsed = YamlLoader::load_from_str(input).unwrap();
        let mut output = String::new();
        let mut emitter = YamlEmitter::new(&mut output);
        emitter.multiline_strings(true);
        emitter.dump(&parsed[0]).unwrap();
    }
    #[test]
    fn test_single_quote_in_string() {
        let input = r#"{description: Just for reference and test that it'll be removed in merged interface.}"#;
        let parsed = YamlLoader::load_from_str(input).unwrap();
        let mut output = String::new();
        let mut emitter = YamlEmitter::new(&mut output);
        emitter.dump(&parsed[0]).unwrap();
        assert_eq!(
            output,
            r#"---
description: Just for reference and test that it'll be removed in merged interface.
"#
        );
    }
}
