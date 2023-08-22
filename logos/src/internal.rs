use crate::{Filter, FilterResult, Lexer, Logos, Skip, Source};

/// Trait used by the functions contained in the `Lexicon`.
///
/// # WARNING!
///
/// **This trait, and its methods, are not meant to be used outside of the
/// code produced by `#[derive(Logos)]` macro.**
pub trait LexerInternal<'source> {
    type Token: Logos<'source>;

    /// Read a chunk at current position.
    fn read<const N: usize>(
        &self,
    ) -> Option<<<Self::Token as Logos<'source>>::Source as Source>::Chunk<'source, N>>;

    fn read_byte(&self) -> Option<u8>;

    /// Read a chunk at current position, offset by `n`.
    fn read_at<const N: usize>(
        &self,
        n: usize,
    ) -> Option<<<Self::Token as Logos<'source>>::Source as Source>::Chunk<'source, N>>;

    fn read_byte_at(&self, n: usize) -> Option<u8>;

    /// Unchecked read a chunk at current position, offset by `n`.
    unsafe fn read_unchecked<const N: usize>(
        &self,
        n: usize,
    ) -> <<Self::Token as Logos<'source>>::Source as Source>::Chunk<'source, N>;

    unsafe fn read_byte_unchecked(&self, n: usize) -> u8;

    /// Test a chunk at current position with a closure.
    fn test<const N: usize, F: FnOnce(&[u8; N]) -> bool>(&self, test: F) -> bool;

    fn test_byte<F: FnOnce(u8) -> bool>(&self, test: F) -> bool;

    /// Test a chunk at current position offset by `n` with a closure.
    fn test_at<const N: usize, F: FnOnce(&[u8; N]) -> bool>(&self, n: usize, test: F) -> bool;

    /// Bump the position by `size`.
    fn bump_unchecked(&mut self, size: usize);

    /// Reset `token_start` to `token_end`.
    fn trivia(&mut self);

    /// Set the current token to appropriate `#[error]` variant.
    /// Guarantee that `token_end` is at char boundary for `&str`.
    fn error(&mut self);

    fn end(&mut self);

    fn set(
        &mut self,
        token: Result<
            Self::Token,
            <<Self as LexerInternal<'source>>::Token as Logos<'source>>::Error,
        >,
    );
}

pub trait CallbackResult<'s, P, T: Logos<'s>> {
    fn construct<Constructor>(self, c: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(P) -> T;
}

impl<'s, P, T: Logos<'s>> CallbackResult<'s, P, T> for P {
    #[inline]
    fn construct<Constructor>(self, c: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(P) -> T,
    {
        lex.set(Ok(c(self)))
    }
}

impl<'s, T: Logos<'s>> CallbackResult<'s, (), T> for bool {
    #[inline]
    fn construct<Constructor>(self, c: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(()) -> T,
    {
        match self {
            true => lex.set(Ok(c(()))),
            false => lex.set(Err(T::Error::default())),
        }
    }
}

impl<'s, P, T: Logos<'s>> CallbackResult<'s, P, T> for Option<P> {
    #[inline]
    fn construct<Constructor>(self, c: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(P) -> T,
    {
        match self {
            Some(product) => lex.set(Ok(c(product))),
            None => lex.set(Err(T::Error::default())),
        }
    }
}

impl<'s, P, E, T: Logos<'s>> CallbackResult<'s, P, T> for Result<P, E>
where
    E: Into<T::Error>,
{
    #[inline]
    fn construct<Constructor>(self, c: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(P) -> T,
    {
        match self {
            Ok(product) => lex.set(Ok(c(product))),
            Err(err) => lex.set(Err(err.into())),
        }
    }
}

impl<'s, T: Logos<'s>> CallbackResult<'s, (), T> for Skip {
    #[inline]
    fn construct<Constructor>(self, _: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(()) -> T,
    {
        lex.trivia();
        T::lex(lex);
    }
}

impl<'s, P, T: Logos<'s>> CallbackResult<'s, P, T> for Filter<P> {
    #[inline]
    fn construct<Constructor>(self, c: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(P) -> T,
    {
        match self {
            Filter::Emit(product) => lex.set(Ok(c(product))),
            Filter::Skip => {
                lex.trivia();
                T::lex(lex);
            }
        }
    }
}

impl<'s, P, E, T: Logos<'s>> CallbackResult<'s, P, T> for FilterResult<P, E>
where
    E: Into<T::Error>,
{
    fn construct<Constructor>(self, c: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(P) -> T,
    {
        match self {
            FilterResult::Emit(product) => lex.set(Ok(c(product))),
            FilterResult::Skip => {
                lex.trivia();
                T::lex(lex);
            }
            FilterResult::Error(err) => lex.set(Err(err.into())),
        }
    }
}

impl<'s, T: Logos<'s>> CallbackResult<'s, (), T> for T {
    #[inline]
    fn construct<Constructor>(self, _: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(()) -> T,
    {
        lex.set(Ok(self))
    }
}

impl<'s, T: Logos<'s>> CallbackResult<'s, (), T> for Result<T, T::Error> {
    #[inline]
    fn construct<Constructor>(self, _: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(()) -> T,
    {
        match self {
            Ok(product) => lex.set(Ok(product)),
            Err(err) => lex.set(Err(err)),
        }
    }
}

impl<'s, T: Logos<'s>> CallbackResult<'s, (), T> for Filter<T> {
    #[inline]
    fn construct<Constructor>(self, _: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(()) -> T,
    {
        match self {
            Filter::Emit(product) => lex.set(Ok(product)),
            Filter::Skip => {
                lex.trivia();
                T::lex(lex);
            }
        }
    }
}

impl<'s, T: Logos<'s>> CallbackResult<'s, (), T> for FilterResult<T, T::Error> {
    fn construct<Constructor>(self, _: Constructor, lex: &mut Lexer<'s, T>)
    where
        Constructor: Fn(()) -> T,
    {
        match self {
            FilterResult::Emit(product) => lex.set(Ok(product)),
            FilterResult::Skip => {
                lex.trivia();
                T::lex(lex);
            }
            FilterResult::Error(err) => lex.set(Err(err)),
        }
    }
}
