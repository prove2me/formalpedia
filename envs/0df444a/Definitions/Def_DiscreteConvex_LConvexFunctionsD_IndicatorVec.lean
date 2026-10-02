-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_IndicatorVec
-- name    : DiscreteConvex_LConvexFunctionsD_IndicatorVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:58:44.468467+00:00
-- url     : https://prove2.me/theorems/2d703845-da3d-477f-a5b0-b7a6277adc68
-- title:
--   IndicatorVec
-- statement:
--   The characteristic vector $\chi_Y \in \mathbb Z^V$ of $Y \subseteq V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.185.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.185

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The characteristic vector `χ_Y ∈ Zⱽ` of `Y ⊆ V`. -/
def IndicatorVec (Y : Finset V) : V → ℤ := fun v => if v ∈ Y then 1 else 0

end DiscreteConvex.LConvexFunctionsD


