-- Prove2me | Definitions.Def_NonsmoothQN_Secant_Expansion
-- name    : NonsmoothQN_Secant_Expansion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:08.700893+00:00
-- url     : https://prove2.me/theorems/2ae789f1-74a0-4a69-99e9-150482d8139a
-- title:
--   Theorem 5.2, p. 153 — alternating binary expansions $x=\sum_{j=0}^{m}(-1)^j2^{-a_j}$
-- statement:
--   Let $x>0$. An **alternating binary expansion** of $x$ is a length $m\in\{0,1,2,\dots\}\cup\{\infty\}$ together with integers $a_0<a_1<a_2<\cdots$ ($m+1$ of them if $m<\infty$) such that
--   $$x=\sum_{j=0}^{m}(-1)^j\,2^{-a_j}.$$
--   The expansion is **canonical** if either $m=0$, or $m=\infty$, or $m$ is finite with $m\ge1$ and $a_m\ge a_{m-1}+2$. The **tail** from index $k$ is $\sum_{j=k}^{m}(-1)^j2^{-a_j}$ (zero if $k>m$).
--
--   Canonicity excludes the trivial lengthening $2^{-a}=2^{-(a-1)}-2^{-a}$ of a finite expansion (for instance $1=2^{0}=2^{1}-2^{0}$), which is what makes the expansion unique.
--
--   **Formalization Note** The length is an element of `ℕ∞` and the exponents form a sequence `a : ℕ → ℤ` of which only the terms with index $j\le m$ matter; the series is a `HasSum` over $\mathbb N$ whose terms beyond $m$ are $0$, and powers of two with integer (possibly negative) exponents are `zpow`. The canonical condition is not in the paper; it is the correction needed for the uniqueness claim of Theorem 5.2 (see the milestone on that sentence).
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, pp. 152–153, Theorem 5.2 (first sentence) and (5.3)

import Mathlib

namespace NonsmoothQN.Secant

/-- The `j`-th term of a (finite or infinite) alternating series of powers of two with length
`m ∈ {0, 1, 2, …, ∞}` and exponents `a`: `(-1)^j 2^{-a_j}` for `j ≤ m`, and `0` beyond `m`. -/
noncomputable def altTerm (m : ℕ∞) (a : ℕ → ℤ) (j : ℕ) : ℝ :=
  if (j : ℕ∞) ≤ m then (-1 : ℝ) ^ j * (2 : ℝ) ^ (-(a j)) else 0

/-- `(m, a)` is an alternating binary expansion of `x` (Theorem 5.2, p. 153):
`a_0 < a_1 < ⋯` (the `m + 1` exponents with index `≤ m`) and `x = ∑_{j=0}^{m} (-1)^j 2^{-a_j}`. -/
def IsAltBinExpansion (x : ℝ) (m : ℕ∞) (a : ℕ → ℤ) : Prop :=
  StrictMonoOn a {j : ℕ | (j : ℕ∞) ≤ m} ∧ HasSum (altTerm m a) x

/-- The expansion is *canonical*: if it is finite with `m ≥ 1` terms after the first, the last
gap is at least two, `a_m ≥ a_{m-1} + 2`. This excludes the lengthening
`2^{-a} = 2^{-(a-1)} - 2^{-a}` of a finite expansion. -/
def IsCanonicalExpansion (m : ℕ∞) (a : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, m = (n : ℕ∞) → 1 ≤ n → a (n - 1) + 2 ≤ a n

/-- The tail `∑_{j=k}^{m} (-1)^j 2^{-a_j}`. -/
noncomputable def tailSum (m : ℕ∞) (a : ℕ → ℤ) (k : ℕ) : ℝ :=
  ∑' j : ℕ, if k ≤ j then altTerm m a j else 0

end NonsmoothQN.Secant


