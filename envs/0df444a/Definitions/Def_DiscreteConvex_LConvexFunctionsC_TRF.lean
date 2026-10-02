-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRF
-- name    : DiscreteConvex_LConvexFunctionsC_TRF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:31:40.036985+00:00
-- url     : https://prove2.me/theorems/dbb1be5e-1ec2-40ab-9b44-620b44b8da02
-- title:
--   TRF
-- statement:
--   Axiom (TRF[Z]): $\exists r$, $g(p+\mathbf 1)=g(p)+r$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z])

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[Z]): `∃r, g(p+1) = g(p)+r`. -/
def TRF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsC


