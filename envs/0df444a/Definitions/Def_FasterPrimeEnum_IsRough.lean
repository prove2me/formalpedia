-- Prove2me | Definitions.Def_FasterPrimeEnum_IsRough
-- name    : FasterPrimeEnum_IsRough
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:37:48.913292+00:00
-- url     : https://prove2.me/theorems/e7f8095f-c167-4d9b-9250-48bcc95b5194
-- title:
--   $y$-rough and square-$y$-rough integers; $\Phi(x,y)$; the rough bit array
-- statement:
--   Let $y$ be a real number and $n$ a positive integer.
--
--   1. $n$ is **$y$-rough** if it has no prime divisor $p\le y$.
--   2. $n$ is **square-$y$-rough** if $n=m^2n'$ with $m\ge1$ an integer and $n'$ $y$-rough; equivalently, every prime $p\le y$ divides $n$ to an even power.
--
--   Zero is neither $y$-rough nor square-$y$-rough. For real $x$ and $y$, $\Phi(x,y)$ is the number of $y$-rough integers $n\in[1,x]$. For integers $N,Y$, the **rough bit array** is $(u_1,\dots,u_{N-1})$ with $u_n=1$ exactly when $n$ is $Y$-rough.
--
--   Rough integers are what the deterministic algorithm sieves for (Theorem 10.1), and square-rough integers are how it certifies that an interval contains no unexpected square-primes.
--
--   **Formalization Note** The paper takes $y>1$; the predicates are defined for every real $y$, and for $y<2$ they say only $n>0$, which is the reading Lemma 9.11 needs at $Y=1$.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Definition 8.1, p.68; Remark 8.5, p.69; p.96 (Φ); Theorem 10.1, p.95 (bit array)

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **`y`-rough integers** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held
version, sha256 7fc13f17…), Definition 8.1, p.68: "Let y > 1 be a real number and let n be a
positive integer. We say that n is y-rough if it has no prime divisors p ⩽ y."

**Formalization Note.** Zero is not rough (Remark 8.5, p.69: "Zero is not considered to be
square-z-rough (or z-rough)"), so positivity is part of the predicate. The predicate is defined for
every real `y`; for `y < 2` it says only `0 < n` (Lemma 9.11 uses `Y = 1`). -/
def IsRough (y : ℝ) (n : ℕ) : Prop := 0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → y < p

/-- **Square-`y`-rough integers** — Definition 8.1, p.68: "We say that n is square-y-rough if it
is of the form n = m²n′ where m ⩾ 1 is an integer and n′ is y-rough." Zero is not square-rough
(Remark 8.5), since a rough `n′` is positive. -/
def IsSquareRough (y : ℝ) (n : ℕ) : Prop := ∃ m n' : ℕ, 1 ≤ m ∧ IsRough y n' ∧ n = m ^ 2 * n'

open Classical in
/-- **`Φ(x, y)`** — p.96: "For x ⩾ y ⩾ 2 let Φ(x, y) denote the number of y-rough integers
n ∈ [1, x]." The integers `n` with `1 ≤ n ≤ ⌊x⌋`. -/
noncomputable def roughCount (x y : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter fun n => IsRough y n).card

open Classical in
/-- **The output of Theorem 10.1** — p.95: "a bit array (u_1, …, u_{N−1}) such that u_n = 1 if
and only if n is Y-rough." The list `[u_1, …, u_{N-1}]` in index order (`true` = 1). -/
noncomputable def roughArray (N Y : ℕ) : List Bool :=
  (List.range (N - 1)).map fun i => decide (IsRough (Y : ℝ) (i + 1))

end FasterPrimeEnum


