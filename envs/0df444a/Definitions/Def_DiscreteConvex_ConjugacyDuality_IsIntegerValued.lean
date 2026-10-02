-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_IsIntegerValued
-- name    : DiscreteConvex_ConjugacyDuality_IsIntegerValued
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:09:28.82989+00:00
-- url     : https://prove2.me/theorems/74c92dea-9b12-4214-9ff1-fbc3cb76b650
-- title:
--   Integer-valuedness of an R-cup-infinity function
-- statement:
--   $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ is **integer valued** if every finite value it takes is an integer — the classes $M[\mathbb Z\to\mathbb Z]$, $L[\mathbb Z\to\mathbb Z]$ of Theorem 8.12 are exactly the M-/L-convex functions additionally satisfying this.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212

import Mathlib

/-!
Integer-valuedness of an `R ∪ {+∞}`-valued lattice function, used for the classes `M[Z→Z]` and
`L[Z→Z]` (Murota, *Discrete Convex Analysis*, SIAM 2003, p.212), in
`DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- `f : Zⱽ → R ∪ {+∞}` is **integer valued** if every finite value it takes is (the cast of)
an integer. -/
def IsIntegerValued {V : Type*} (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℤ, f x = ⊤ ∨ ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.ConjugacyDuality


