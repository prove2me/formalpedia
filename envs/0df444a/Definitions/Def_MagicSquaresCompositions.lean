-- Prove2me | Definitions.Def_MagicSquaresCompositions
-- name    : MagicSquaresCompositions
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-16T17:58:47.671258+00:00
-- url     : https://prove2.me/theorems/73ed6522-7b76-4bfc-b852-f197b90ec3b2
-- title:
--   Compositions of an integer into a fixed number of parts
-- statement:
--   Compositions of an integer into a fixed number of parts.
--
--   A **composition of $n$ into $k$ parts** is a $k$-tuple
--   $x=(x_{1},\dots,x_{k})$ of nonnegative integers with
--   $x_{1}+\cdots+x_{k}=n$. The classical stars-and-bars count is
--
--   $$\#\{x\in\mathbb{N}^{k} : x_{1}+\cdots+x_{k}=n\} = \binom{n+k-1}{n}.$$
--
--   Since $\mathbb{N}^{k}$ is infinite, the count is taken inside a box: for a
--   bound $N$, `comps N k n` is the set of functions $\mathrm{Fin}(k)\to
--   \mathrm{Fin}(N+1)$ whose values sum to $n$. When $n\le N$ the bound is
--   inactive, because every coordinate of such a tuple is at most $n$ and hence at
--   most $N$; so the box does not change the count. Keeping $N$ fixed while $k$ and
--   $n$ vary is also what makes the natural induction work: splitting off the first
--   coordinate leaves a tail that still lives in the same box, which avoids any
--   reindexing.
--
--   This is the form of stars and bars needed to evaluate MacMahon's
--   parametrization of $3\times3$ semi-magic squares, where the parametrizing data
--   are compositions of $t$ (or $t-1$, $t-2$) into five parts.
-- source:
--   Classical stars-and-bars; see R. P. Stanley, Enumerative Combinatorics, Vol. I, 2nd ed., Cambridge University Press, 2012, Section 1.1.

import Mathlib

set_option autoImplicit false

open scoped BigOperators

/-!
# Compositions of an integer into a fixed number of parts

A **composition of `n` into `k` parts** is a $k$-tuple of nonnegative integers
summing to $n$. The classical *stars and bars* count is

$$\#\\{x\in\mathbb{N}^{k} : x_{1}+\cdots+x_{k}=n\\}=\binom{n+k-1}{n}.$$

Because $\mathbb{N}^{k}$ is infinite, the count is taken inside a box: for a
bound `N` we consider `comps N k n`, the set of functions `Fin k → Fin (N+1)`
whose values sum to `n`. When `n ≤ N` this is lossless — every coordinate of
such a tuple is at most `n`, hence at most `N` — so the box does not change the
count. Holding `N` fixed while `k` and `n` vary is also what makes the
induction work: splitting off the first coordinate produces a tail that still
lives in the same box.

The evaluation `(comps N k n).card = (n + k - 1).choose n` is submitted
separately as a theorem; it is the form of stars and bars needed to count
MacMahon's parametrization of $3\times3$ semi-magic squares.
-/

namespace MagicSquares

/-- The compositions of `n` into `k` parts, with every part bounded by `N`.
For `n ≤ N` the bound is inactive. -/
def comps (N k n : ℕ) : Finset (Fin k → Fin (N + 1)) :=
  by
    classical
    exact Finset.univ.filter fun q => (∑ i : Fin k, (q i : ℕ)) = n

/-- The number of compositions of `n` into `k` parts. -/
def compsCount (N k n : ℕ) : ℕ := (comps N k n).card

end MagicSquares


