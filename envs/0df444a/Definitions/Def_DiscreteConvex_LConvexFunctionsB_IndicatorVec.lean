-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_IndicatorVec
-- name    : DiscreteConvex_LConvexFunctionsB_IndicatorVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:20:22.183986+00:00
-- url     : https://prove2.me/theorems/010bcd4e-f469-44d4-8bd7-5748c82d9317
-- title:
--   IndicatorVec
-- statement:
--   The indicator vector $\chi_Y \in \mathbb Z^V$ of $Y \subseteq V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.185.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.185

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The indicator vector `χ_Y ∈ Zⱽ` of `Y ⊆ V`. -/
def IndicatorVec (Y : Finset V) : V → ℤ := fun v => if v ∈ Y then 1 else 0

end DiscreteConvex.LConvexFunctionsB


