-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_TRF
-- name    : DiscreteConvex_ConjugacyDualityB_TRF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:05.259988+00:00
-- url     : https://prove2.me/theorems/a61a77a2-f650-4c91-ac6d-07fa4c27f747
-- title:
--   TRF
-- statement:
--   Axiom (TRF[Z]): $\exists r$, $g(p+\mathbf 1)=g(p)+r$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z])

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[Z]): `∃r, g(p+1) = g(p)+r`. -/
def TRF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)

end DiscreteConvex.ConjugacyDualityB


