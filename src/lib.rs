use std::borrow::Cow;
use std::fmt;
use std::ops::{Deref, DerefMut};

pub use unicase::UniCase;

pub use crate::raw::{Challenge, ChallengeFields, Quote};

#[derive(Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct CowStr(pub Cow<'static, str>);

impl Deref for CowStr {
    type Target = Cow<'static, str>;

    fn deref(&self) -> &Cow<'static, str> {
        &self.0
    }
}

impl fmt::Debug for CowStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl fmt::Display for CowStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl DerefMut for CowStr {
    fn deref_mut(&mut self) -> &mut Cow<'static, str> {
        &mut self.0
    }
}

impl AsRef<str> for CowStr {
    fn as_ref(&self) -> &str {
        self
    }
}

mod raw {
    use super::*;
    use std::borrow::Cow;
    use std::collections::HashMap;
    use std::mem;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum Quote {
        Always,
        IfNeed,
    }

    /// A representation of the challenge fields
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct ChallengeFields(HashMap<UniCase<CowStr>, (String, Quote)>);

    impl Default for ChallengeFields {
        fn default() -> Self {
            Self::new()
        }
    }

    impl ChallengeFields {
        pub fn new() -> Self {
            ChallengeFields(HashMap::new())
        }
        // fn values(&self) -> Values<K, V>
        // fn values_mut(&mut self) -> ValuesMut<K, V>
        // fn iter(&self) -> Iter<K, V>
        // fn iter_mut(&mut self) -> IterMut<K, V>
        // fn entry(&mut self, key: K) -> Entry<K, V>
        pub fn len(&self) -> usize {
            self.0.len()
        }
        pub fn is_empty(&self) -> bool {
            self.0.is_empty()
        }
        // fn drain(&mut self) -> Drain<K, V>
        pub fn clear(&mut self) {
            self.0.clear()
        }
        pub fn get(&self, k: &str) -> Option<&String> {
            self.0
                .get(&UniCase::new(CowStr(Cow::Borrowed(unsafe {
                    mem::transmute::<&str, &'static str>(k)
                }))))
                .map(|(s, _)| s)
        }
        pub fn contains_key(&self, k: &str) -> bool {
            self.0
                .contains_key(&UniCase::new(CowStr(Cow::Borrowed(unsafe {
                    mem::transmute::<&str, &'static str>(k)
                }))))
        }
        pub fn get_mut(&mut self, k: &str) -> Option<&mut String> {
            self.0
                .get_mut(&UniCase::new(CowStr(Cow::Borrowed(unsafe {
                    mem::transmute::<&str, &'static str>(k)
                }))))
                .map(|&mut (ref mut s, _)| s)
        }
        pub fn insert(&mut self, k: String, v: String) -> Option<String> {
            self.0
                .insert(UniCase::new(CowStr(Cow::Owned(k))), (v, Quote::IfNeed))
                .map(|(s, _)| s)
        }
        pub fn insert_quoting(&mut self, k: String, v: String) -> Option<String> {
            self.0
                .insert(UniCase::new(CowStr(Cow::Owned(k))), (v, Quote::Always))
                .map(|(s, _)| s)
        }
        pub fn insert_static(&mut self, k: &'static str, v: String) -> Option<String> {
            self.0
                .insert(UniCase::new(CowStr(Cow::Borrowed(k))), (v, Quote::IfNeed))
                .map(|(s, _)| s)
        }
        pub fn insert_static_quoting(&mut self, k: &'static str, v: String) -> Option<String> {
            self.0
                .insert(UniCase::new(CowStr(Cow::Borrowed(k))), (v, Quote::Always))
                .map(|(s, _)| s)
        }
        pub fn remove(&mut self, k: &str) -> Option<String> {
            self.0
                .remove(&UniCase::new(CowStr(Cow::Borrowed(unsafe {
                    mem::transmute::<&str, &'static str>(k)
                }))))
                .map(|(s, _)| s)
        }
    }
    // index

    /// A representation of raw challenges. A Challenge is either a token or
    /// fields.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum Challenge {
        Token68(String),
        Fields(ChallengeFields),
    }

    fn need_quote(s: &str, q: &Quote) -> bool {
        if q == &Quote::Always {
            true
        } else {
            s.bytes().any(|c| !parser::is_token_char(c))
        }
    }

    impl fmt::Display for Challenge {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            use self::Challenge::*;
            match *self {
                Token68(ref token) => write!(f, "{token}")?,
                Fields(ref fields) => {
                    for (k, (v, quote)) in fields.0.iter() {
                        if need_quote(v, quote) {
                            write!(f, "{k}={v:?}, ")?
                        } else {
                            write!(f, "{k}={v}, ")?
                        }
                    }
                }
            }
            Ok(())
        }
    }
}

type ParserResult<T> = Result<T, &'static str>;

mod parser {
    use crate::ParserResult;

    use super::raw::{Challenge, ChallengeFields};
    use std::cell::Cell;
    use std::str::from_utf8_unchecked;

    pub struct Stream<'a>(Cell<usize>, &'a [u8]);

    pub fn is_ws(c: u8) -> bool {
        // See https://tools.ietf.org/html/rfc7230#section-3.2.3
        b"\t ".contains(&c)
    }

    pub fn is_token_char(c: u8) -> bool {
        // See https://tools.ietf.org/html/rfc7230#section-3.2.6
        br#"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890!#$%&'*+-.^_`|~"#
            .contains(&c)
    }

    pub fn is_obs_text(c: u8) -> bool {
        // See https://tools.ietf.org/html/rfc7230#section-3.2.6
        // u8 is always under 0xFF
        0x80 <= c
    }

    pub fn is_vchar(c: u8) -> bool {
        // consult the ASCII definition
        (0x21..=0x7E).contains(&c)
    }

    pub fn is_qdtext(c: u8) -> bool {
        // See https://tools.ietf.org/html/rfc7230#section-3.2.6
        b"\t \x21".contains(&c) || (0x23..=0x5B).contains(&c) || (0x5D <= 0x7E) || is_obs_text(c)
    }

    pub fn is_quoting(c: u8) -> bool {
        b"\t ".contains(&c) || is_vchar(c) || is_obs_text(c)
    }

    impl<'a> Stream<'a> {
        pub fn new(data: &'a [u8]) -> Self {
            Stream(Cell::from(0), data)
        }

        pub fn inc(&self, i: usize) {
            let pos = self.pos();
            self.0.set(pos + i);
        }

        pub fn pos(&self) -> usize {
            self.0.get()
        }

        pub fn is_end(&self) -> bool {
            self.1.len() <= self.pos()
        }

        pub fn cur(&self) -> u8 {
            self.1[self.pos()]
        }

        pub fn skip_a(&self, c: u8) -> ParserResult<()> {
            if self.cur() == c {
                self.inc(1);
                Ok(())
            } else {
                Err("Invalid Header")
            }
        }
        pub fn skip_a_next(&self, c: u8) -> ParserResult<()> {
            self.skip_ws()?;
            if self.is_end() {
                return Err("Invalid Header");
            }
            self.skip_a(c)
        }

        pub fn take_while<F>(&self, f: F) -> ParserResult<&[u8]>
        where
            F: Fn(u8) -> bool,
        {
            let start = self.pos();
            while !self.is_end() && f(self.cur()) {
                self.inc(1);
            }
            Ok(&self.1[start..self.pos()])
        }

        pub fn take_while1<F>(&self, f: F) -> ParserResult<&[u8]>
        where
            F: Fn(u8) -> bool,
        {
            self.take_while(f).and_then(|b| {
                if b.is_empty() {
                    Err("Invalid Header")
                } else {
                    Ok(b)
                }
            })
        }

        pub fn r#try<F, T>(&self, f: F) -> ParserResult<T>
        where
            F: FnOnce() -> ParserResult<T>,
        {
            let init = self.pos();
            match f() {
                ok @ Ok(_) => ok,
                err @ Err(_) => {
                    self.0.set(init);
                    err
                }
            }
        }

        pub fn skip_ws(&self) -> ParserResult<()> {
            self.take_while(is_ws).map(|_| ())
        }

        pub fn skip_next_comma(&self) -> ParserResult<()> {
            self.skip_a_next(b',')
        }

        pub fn skip_field_sep(&self) -> ParserResult<()> {
            self.skip_ws()?;
            if self.is_end() {
                return Ok(());
            }
            self.skip_next_comma()?;
            while self.skip_next_comma().is_ok() {}
            self.skip_ws()?;
            Ok(())
        }

        pub fn token(&self) -> ParserResult<&str> {
            self.take_while1(is_token_char)
                .map(|s| unsafe { from_utf8_unchecked(s) })
        }

        pub fn next_token(&self) -> ParserResult<&str> {
            self.skip_ws()?;
            self.token()
        }

        pub fn quoted_string(&self) -> ParserResult<String> {
            // See https://tools.ietf.org/html/rfc7230#section-3.2.6
            if self.is_end() {
                return Err("Invalid Header");
            }

            if self.cur() != b'"' {
                return Err("Invalid Header");
            }
            self.inc(1);
            let mut s = Vec::new();
            while !self.is_end() && self.cur() != b'"' {
                if self.cur() == b'\\' {
                    self.inc(1);
                    if is_quoting(self.cur()) {
                        s.push(self.cur());
                        self.inc(1);
                    } else {
                        return Err("Invalid Header");
                    }
                } else if is_qdtext(self.cur()) {
                    s.push(self.cur());
                    self.inc(1);
                } else {
                    return Err("Invalid Header");
                }
            }
            if self.is_end() {
                return Err("Invalid Header");
            } else {
                debug_assert!(self.cur() == b'"');
                self.inc(1);
            }
            String::from_utf8(s).map_err(|_| "Invalid Header")
        }

        pub fn token68(&self) -> ParserResult<&str> {
            let start = self.pos();
            // See https://tools.ietf.org/html/rfc7235#section-2.1
            self.take_while1(|c| {
                b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890-._~+/".contains(&c)
            })?;
            self.take_while(|c| c == b'=')?;
            Ok(unsafe { from_utf8_unchecked(&self.1[start..self.pos()]) })
        }

        pub fn kv_token(&self) -> ParserResult<(&str, &str)> {
            let k = self.token()?;
            self.skip_a_next(b'=')?;
            self.skip_ws()?;
            let v = self.token()?;
            Ok((k, v))
        }

        pub fn kv_quoted(&self) -> ParserResult<(&str, String)> {
            let k = self.token()?;
            self.skip_a_next(b'=')?;
            self.skip_ws()?;
            let v = self.quoted_string()?;
            Ok((k, v))
        }

        pub fn field(&self) -> ParserResult<(String, String)> {
            self.r#try(|| self.kv_token().map(|(k, v)| (k.to_string(), v.to_string())))
                .or_else(|_| self.kv_quoted().map(|(k, v)| (k.to_string(), v)))
        }

        pub fn raw_token68(&self) -> ParserResult<Challenge> {
            let ret = self
                .token68()
                .map(ToString::to_string)
                .map(Challenge::Token68)?;
            self.skip_field_sep()?;
            Ok(ret)
        }

        pub fn raw_fields(&self) -> ParserResult<Challenge> {
            let mut map = ChallengeFields::new();
            loop {
                match self.r#try(|| self.field()) {
                    Err(_) => return Ok(Challenge::Fields(map)),
                    Ok((k, v)) => {
                        if self.skip_field_sep().is_ok() {
                            if map.insert(k, v).is_some() {
                                // field key must not be duplicated
                                return Err("Invalid Header");
                            }
                            if self.is_end() {
                                return Ok(Challenge::Fields(map));
                            }
                        } else {
                            return Err("Invalid Header");
                        }
                    }
                }
            }
        }

        pub fn challenge(&self) -> ParserResult<(String, Challenge)> {
            let scheme = self.next_token()?;
            self.take_while1(is_ws)?;
            let challenge = self
                .r#try(|| self.raw_token68())
                .or_else(|_| self.raw_fields())?;
            Ok((scheme.to_string(), challenge))
        }
    }

    #[test]
    fn test_parese_quoted_field() {
        let b = b"realm=\"secret zone\"";
        let stream = Stream::new(b);
        let (k, v) = stream.field().unwrap();
        assert_eq!(k, "realm");
        assert_eq!(v, "secret zone");
        assert!(stream.is_end());
    }

    #[test]
    fn test_parese_quoted_field_nonvchars() {
        let b = b"realm=\"secret zone\t\xe3\x8a\x99\"";
        let stream = Stream::new(b);
        let (k, v) = stream.field().unwrap();
        assert_eq!(k, "realm");
        assert_eq!(v, "secret zone\t㊙");
        assert!(stream.is_end());
    }

    #[test]
    fn test_parese_token_field() {
        let b = b"algorithm=MD5";
        let stream = Stream::new(b);
        let (k, v) = stream.field().unwrap();
        assert_eq!(k, "algorithm");
        assert_eq!(v, "MD5");
        assert!(stream.is_end());
    }

    #[test]
    fn test_parese_raw_quoted_fields() {
        let b = b"realm=\"secret zone\"";
        let stream = Stream::new(b);
        match stream.raw_fields().unwrap() {
            Challenge::Token68(_) => panic!(),
            Challenge::Fields(fields) => {
                assert_eq!(fields.len(), 1);
                assert_eq!(fields.get("realm").unwrap(), "secret zone");
            }
        }
        assert!(stream.is_end());
    }

    #[test]
    fn test_parese_raw_token_fields() {
        let b = b"algorithm=MD5";
        let stream = Stream::new(b);
        match stream.raw_fields().unwrap() {
            Challenge::Token68(_) => panic!(),
            Challenge::Fields(fields) => {
                assert_eq!(fields.len(), 1);
                assert_eq!(fields.get("algorithm").unwrap(), "MD5");
            }
        }
        assert!(stream.is_end());
    }
    #[test]
    fn test_parese_token68() {
        let b = b"auea1./+=";
        let stream = Stream::new(b);
        let token = stream.token68().unwrap();
        assert_eq!(token, "auea1./+=");
        assert!(stream.is_end());
    }

    #[test]
    fn test_parese_raw_token68() {
        let b = b"auea1./+=";
        let stream = Stream::new(b);
        match stream.raw_token68().unwrap() {
            Challenge::Token68(token) => assert_eq!(token, "auea1./+="),
            Challenge::Fields(_) => panic!(),
        }
        assert!(stream.is_end());
    }

    #[test]
    fn test_parese_challenge1() {
        let b = b"Token abceaqj13-.+=";
        let stream = Stream::new(b);
        match stream.challenge().unwrap() {
            (scheme, Challenge::Token68(token)) => {
                assert_eq!(scheme, "Token");
                assert_eq!(token, "abceaqj13-.+=");
            }
            (_, Challenge::Fields(_)) => panic!(),
        }
        assert!(stream.is_end());
    }

    #[test]
    fn test_parese_challenge2() {
        let b = b"Basic realm=\"secret zone\"";
        let stream = Stream::new(b);
        match stream.challenge().unwrap() {
            (_, Challenge::Token68(_)) => panic!(),
            (scheme, Challenge::Fields(fields)) => {
                assert_eq!(scheme, "Basic");
                assert_eq!(fields.len(), 1);
                assert_eq!(fields.get("realm").unwrap(), "secret zone");
            }
        }
        assert!(stream.is_end());
    }

    #[test]
    fn test_parese_challenge3() {
        let b = b"Bearer token=aeub8_";
        let stream = Stream::new(b);
        match stream.challenge().unwrap() {
            (_, Challenge::Token68(_)) => panic!(),
            (scheme, Challenge::Fields(fields)) => {
                assert_eq!(scheme, "Bearer");
                assert_eq!(fields.len(), 1);
                assert_eq!(fields.get("token").unwrap(), "aeub8_");
            }
        }
        assert!(stream.is_end());
    }

    #[test]
    fn test_parese_challenge4() {
        let b = b"Bearer token=aeub8_, user=\"fooo\"";
        let stream = Stream::new(b);
        match stream.challenge().unwrap() {
            (_, Challenge::Token68(_)) => panic!(),
            (scheme, Challenge::Fields(fields)) => {
                assert_eq!(scheme, "Bearer");
                assert_eq!(fields.len(), 2);
                assert_eq!(fields.get("token").unwrap(), "aeub8_");
                assert_eq!(fields.get("user").unwrap(), "fooo");
            }
        }
        assert!(stream.is_end());
    }

    #[test]
    fn test_parese_challenge5() {
        let b = b"Bearer user=\"fooo\",,, token=aeub8_,,";
        let stream = Stream::new(b);
        match stream.challenge().unwrap() {
            (_, Challenge::Token68(_)) => panic!(),
            (scheme, Challenge::Fields(fields)) => {
                assert_eq!(scheme, "Bearer");
                assert_eq!(fields.len(), 2);
                assert_eq!(fields.get("token").unwrap(), "aeub8_");
                assert_eq!(fields.get("user").unwrap(), "fooo");
            }
        }
        assert!(stream.is_end());
    }

    #[test]
    #[should_panic]
    fn test_parse_null() {
        let b = b"";
        let stream = Stream::new(b);
        println!("{:?}", stream.challenge().unwrap());
    }
}

/// Parses a WWW-Authenticate HTTP header value into a single authentication scheme and its corresponding challenge.
///
/// # Arguments
///
/// * www_authenticate_header - A string slice representing the value of a WWW-Authenticate header, for example: "Basic realm=\"secret zone\"".
///
/// # Returns
///
/// Returns a Result which on success contains:
/// - A tuple where the first element is the authentication scheme as a case-insensitive owned string (`UniCase<CowStr>`),
/// - The second element is the parsed Challenge associated with that scheme.
///
/// On failure, returns a static string error describing the parsing issue.
///
/// # Example
/// ```rust
/// let header = r#"Basic realm="secret zone""#;
/// let result = parse_header(header).unwrap();
/// assert_eq!(result.0, UniCase::new("basic"));
/// ```
///
/// # Error Handling
///
/// Returns Err if:
/// - The input cannot be parsed as a valid WWW-Authenticate header challenge,
/// - Or if the stream ends unexpectedly during parsing.
///
/// # Notes
///
/// - This function handles exactly one challenge with its scheme.
/// - Parsing behavior strictly complies with RFC 7235 specifications for WWW-Authenticate headers.
/// - The returned scheme is wrapped in UniCase to enable case-insensitive comparison.
pub fn parse_header(
    www_authenticate_header: &str,
) -> Result<(UniCase<CowStr>, Challenge), &'static str> {
    let stream = parser::Stream::new(www_authenticate_header.as_bytes());
    match stream.challenge() {
        Ok(v) => Ok((UniCase::new(CowStr(Cow::Owned(v.0))), v.1)),
        Err(e) => {
            if stream.is_end() {
                Err("Error in stream")
            } else {
                Err(e)
            }
        }
    }
}
