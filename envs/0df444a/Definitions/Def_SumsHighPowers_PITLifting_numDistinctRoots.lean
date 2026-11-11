-- Prove2me | Definitions.Def_SumsHighPowers_PITLifting_numDistinctRoots
-- name    : SumsHighPowers_PITLifting_numDistinctRoots
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:09:48.970588+00:00
-- url     : https://prove2.me/theorems/3207bea3-02d4-43fb-bea7-7ed3c5b136f9
-- title:
--   $\nu(h)$, the number of distinct roots over the algebraic closure (p. 18)
-- statement:
--   Let $F$ be a field with algebraic closure $\overline F$. For a polynomial $h\in F[x]$, $\nu(h)$ is the number of distinct roots of $h$ in $\overline F$:
--   $$\nu(h)=\#\{\beta\in\overline F:\ h(\beta)=0\}\qquad (h\neq 0).$$
--   For example $\nu\big((x-1)^3(x^2+1)\big)=3$ over $\mathbb Q$. $\nu$ is used in the ABC theorem (Theorem 2.7).
--
--   **Formalization Note.** `numDistinctRoots h` maps $h$ to `AlgebraicClosure F` and counts the distinct elements of its multiset of roots (`roots.toFinset.card`). For $h=0$ the multiset is empty, so the value is $0$; the mission applies $\nu$ only to nonzero polynomials. Over an imperfect field this differs from the degree of the radical of $h$ (for $x^p-t$ over $\mathbb F_p(t)$, $\nu=1$), and $\nu$ is the paper's quantity.
-- source:
--   Kaplan, Shpilka, Tal, PIT and Reconstruction for Sums of High Powers, STOC 2027 submission (manuscript, sha256 63d31ceb…9b604b19), p. 18, §2.3 (definition of ν(h) before Theorem 2.7)

import Mathlib

namespace SumsHighPowers.PITLifting

open Classical in
/-- **`ν(h)`, the number of distinct roots** (Kaplan–Shpilka–Tal, §2.3, p. 18): for `h ∈ F[x]`,
`ν(h)` is the number of distinct roots of `h` over the algebraic closure `F̄`.

**Formalization Note.** `h` is mapped to `AlgebraicClosure F`, and `ν(h)` is the number of distinct
elements of its multiset of roots. For `h = 0` Mathlib's `roots` is empty, so `ν(0) = 0`; the
theorems of this mission apply `ν` only to nonzero polynomials. -/
noncomputable def numDistinctRoots {F : Type*} [Field F] (h : Polynomial F) : ℕ :=
  (h.map (algebraMap F (AlgebraicClosure F))).roots.toFinset.card

end SumsHighPowers.PITLifting


