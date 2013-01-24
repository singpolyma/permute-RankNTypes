{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Text.ParserCombinators.Perm
-- Copyright   :  (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007, (c) Troels Henriksen 2011
-- License     :  BSD-style (see the file LICENSE)
-- 
-- Maintainer  :  athas@sigkill.dk
-- Stability   :  stable
-- Portability :  non-portable (uses RankNTypes)
-- 
-- This module implements permutation parsers, and is a generalisation
-- of 'Text.Parsec.Perm' that will work with any parser combinator
-- library.  The algorithm is described in:
-- 
-- /Parsing Permutation Phrases,/
-- by Arthur Baars, Andres Loh and Doaitse Swierstra.
-- 
-----------------------------------------------------------------------------
module Text.ParserCombinators.Perm
    ( PermParser -- abstract
    , permute
    , (<||>), (<$$>)
    , (<|?>), (<$?>)
    ) where

import Control.Applicative

infixl 1 <||>, <|?>
infixl 2 <$$>, <$?>

{---------------------------------------------------------------
  test using Parsec -- parse a permutation of
  * an optional string of 'a's
  * a required 'b'
  * an optional 'c'
---------------------------------------------------------------}
{-
test input
  = parse (do{ x <- ptest; eof; return x }) "" input

ptest :: Parser (String,Char,Char)
ptest
  = permute $
    (,,) <$?> ("",many1 (char 'a'))
         <||> char 'b'
         <|?> ('_',char 'c')
-}

{---------------------------------------------------------------
  Building a permutation parser
---------------------------------------------------------------}

-- | The expression @perm \<||> p@ adds parser @p@ to the permutation
-- parser @perm@. The parser @p@ is not allowed to accept empty input -
-- use the optional combinator ('<|?>') instead. Returns a
-- new permutation parser that includes @p@. 

(<||>) :: PermParser p (a -> b) -> p a -> PermParser p b
perm <||> p = add perm p

-- | The expression @f \<$$> p@ creates a fresh permutation parser
-- consisting of parser @p@. The the final result of the permutation
-- parser is the function @f@ applied to the return value of @p@. The
-- parser @p@ is not allowed to accept empty input - use the optional
-- combinator ('<$?>') instead.
--
-- If the function @f@ takes more than one parameter, the type variable
-- @b@ is instantiated to a functional type which combines nicely with
-- the adds parser @p@ to the ('<||>') combinator. This
-- results in stylized code where a permutation parser starts with a
-- combining function @f@ followed by the parsers. The function @f@
-- gets its parameters in the order in which the parsers are specified,
-- but actual input can be in any order.

(<$$>) :: (a -> b) -> p a -> PermParser p b
f <$$> p = newperm f <||> p

-- | The expression @perm \<||> (x,p)@ adds parser @p@ to the
-- permutation parser @perm@. The parser @p@ is optional - if it can
-- not be applied, the default value @x@ will be used instead. Returns
-- a new permutation parser that includes the optional parser @p@. 

(<|?>) :: PermParser p (a -> b) -> (a, p a) -> PermParser p b
perm <|?> (x,p) = addopt perm x p

-- | The expression @f \<$?> (x,p)@ creates a fresh permutation parser
-- consisting of parser @p@. The the final result of the permutation
-- parser is the function @f@ applied to the return value of @p@. The
-- parser @p@ is optional - if it can not be applied, the default value
-- @x@ will be used instead. 

(<$?>) :: (a -> b) -> (a, p a) -> PermParser p b
f <$?> (x,p) = newperm f <|?> (x,p)

{---------------------------------------------------------------
  The permutation tree
---------------------------------------------------------------}

-- | The type @PermParser p a@ denotes a permutation parser that,
-- when converted by the 'permute' function, parses 
-- @s@ streams with user state @st@ and returns a value of
-- type @a@ on success.
--
-- Normally, a permutation parser is first build with special operators
-- like ('<||>') and than transformed into a normal parser
-- using 'permute'.

data PermParser p a = Perm (Maybe a) [StreamBranch p a]

data StreamBranch p a = Branch (forall r. (forall b. (PermParser p (b -> a), p b) -> r) -> r)

mkBranch :: PermParser p (b -> a) -> p b -> StreamBranch p a
mkBranch perm p = Branch (\k ->
		k (perm, p)
	)

choice :: Alternative a => [a b] -> a b
choice = foldl (<|>) empty

-- | The parser @permute perm@ parses a permutation of parser described
-- by @perm@. For example, suppose we want to parse a permutation of:
-- an optional string of @a@'s, the character @b@ and an optional @c@.
-- This can be described by:
--
-- >  test  = permute (tuple <$?> ("",many1 (char 'a'))
-- >                         <||> char 'b' 
-- >                         <|?> ('_',char 'c'))
-- >        where
-- >          tuple a b c  = (a,b,c)

-- transform a permutation tree into a normal parser
permute :: (Alternative p, Monad p) => PermParser p a -> p a
permute (Perm def xs) = choice (map branch xs ++ empty)
  where empty = case def of Nothing -> []
                            Just x  -> [return x]

        branch (Branch br) = br $ \(perm, p) -> do x <- p
                                                   f <- permute perm
                                                   return (f x)

-- build permutation trees
newperm :: (a -> b) -> PermParser p (a -> b)
newperm f = Perm (Just f) []

add :: PermParser p (a -> b) -> p a -> PermParser p b
add perm@(Perm _mf fs) p = Perm Nothing (first:map insert fs)
  where first                    = mkBranch perm p
        insert (Branch br) = br (\(perm',p') -> mkBranch (add (mapPerms flip perm') p) p')

addopt :: PermParser p (a -> b) -> a -> p a -> PermParser p b
addopt perm@(Perm mf fs) x p = Perm (fmap ($ x) mf) (first:map insert fs)
  where first                    = mkBranch perm p
        insert (Branch br) = br (\(perm', p') -> mkBranch (addopt (mapPerms flip perm') x p) p')

mapPerms :: (a -> b) -> PermParser p a -> PermParser p b
mapPerms f (Perm x xs) = Perm (fmap f x) (map mapBranch xs)
  where mapBranch (Branch br) = br (\(perm, p) -> mkBranch (mapPerms (f.) perm) p)
