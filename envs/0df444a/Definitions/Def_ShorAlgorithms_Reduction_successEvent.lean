-- Prove2me | Definitions.Def_ShorAlgorithms_Reduction_successEvent
-- name    : ShorAlgorithms_Reduction_successEvent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T08:19:35.307823+00:00
-- url     : https://prove2.me/theorems/fdacef42-0dc3-4067-b011-693851f2825e
-- title:
--   The reduction's success event: r even and 1 < gcd(x^{r/2} − 1, n) < n
-- statement:
--   Let $n \ge 1$ be an integer and let $x$ be a unit of $\mathbb{Z}/n\mathbb{Z}$, with multiplicative order $r$, the least positive integer such that $x^r \equiv 1 \pmod n$. The classical reduction from factoring to order finding computes
--
--   $$
--   g(x) = \gcd\bigl(x^{r/2} - 1,\ n\bigr),
--   $$
--
--   where $x^{r/2}$ is represented by its least nonnegative residue modulo $n$ and $r/2$ is the integer part of $r/2$.
--
--   The procedure **yields a nontrivial factor of $n$** at $x$ when
--
--   1. $r$ is even, so that $r/2$ is an integer, and
--   2. $1 < g(x) < n$.
--
--   This is the event whose probability the mission's goal theorem bounds from below. Because $\gcd(z - 1, n)$ depends only on $z \bmod n$, the choice of the least nonnegative representative does not affect the factor produced.
--
--   **Formalization Note** Two declarations: `factorCandidate n u` is $g(x)$, computed as `Nat.gcd ((u ^ (orderOf u / 2)).val - 1) n` with `.val` the least nonnegative residue in $[0, n)$; `successEvent n u` is `Even (orderOf u) ∧ 1 < factorCandidate n u ∧ factorCandidate n u < n`. For a unit and $n > 1$ the residue is at least $1$, so the natural-number subtraction does not truncate; `orderOf u / 2` is natural-number division, exact because evenness of the order is part of the event.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1498, §5, "To find a factor of an odd number n, given a method for computing the order r of x, choose a random x (mod n), find its order r, and compute gcd(x^{r/2} − 1, n)" and "This procedure fails only if r is odd … or if x^{r/2} ≡ −1 (mod n)"

import Mathlib

namespace ShorAlgorithms.Reduction

/-- Shor (1997), §5, p. 1498: the number `gcd(x^{r/2} - 1, n)` computed by the classical
reduction, where `x = u` is a unit mod `n`, `r = orderOf u` is its multiplicative order, and
`x^{r/2}` is represented by its least nonnegative residue `.val ∈ [0, n)`.
For a unit and `n > 1` that residue is `≥ 1`, so the natural-number subtraction `val - 1`
never truncates. `r / 2` is natural-number division; it is exact exactly when `r` is even,
which `successEvent` requires. -/
noncomputable def factorCandidate (n : ℕ) (u : (ZMod n)ˣ) : ℕ :=
  Nat.gcd (((u : ZMod n) ^ (orderOf u / 2)).val - 1) n

/-- Shor (1997), §5, p. 1498: the procedure "choose a random `x (mod n)`, find its order `r`,
and compute `gcd(x^{r/2} - 1, n)`" *yields a nontrivial factor of `n`*: the order `r` is even
(so `r/2` is an integer) and the gcd lies strictly between `1` and `n`. -/
def successEvent (n : ℕ) (u : (ZMod n)ˣ) : Prop :=
  Even (orderOf u) ∧ 1 < factorCandidate n u ∧ factorCandidate n u < n

end ShorAlgorithms.Reduction


