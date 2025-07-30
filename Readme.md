# WWW-Authenticate Header Parser in Rust

This crate provides a Rust implementation for parsing the `WWW-Authenticate` HTTP header. The parser supports extracting authentication schemes and their associated challenges as defined by [RFC 7235](https://tools.ietf.org/html/rfc7235).

---

## Features

- Parses a single `WWW-Authenticate` header string into an authentication scheme and its challenge.
- Supports token68 and fields formats in challenges.
- Case-insensitive scheme handling using `UniCase`.
- Correctly handles quoted strings and token characters according to the HTTP specification.

---

## Credits

This crate is a modified version of [KeenS/www-authenticate](https://github.com/KeenS/www-authenticate).
