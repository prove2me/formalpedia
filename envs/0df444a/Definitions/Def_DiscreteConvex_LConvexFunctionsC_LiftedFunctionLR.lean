-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LiftedFunctionLR
-- name    : DiscreteConvex_LConvexFunctionsC_LiftedFunctionLR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:10.514976+00:00
-- url     : https://prove2.me/theorems/060e4f10-ea65-49c2-80bd-518356f4aad0
-- title:
--   LiftedFunctionLR
-- statement:
--   The lift of a real-domain function to one extra real coordinate.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, real-variable analogue of Eq. (7.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, real-variable analogue of Eq. (7.2)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift of a real-domain function to one extra real coordinate. -/
def LiftedFunctionLR (g : (V → ℝ) → WithTop ℝ) : (Option V → ℝ) → WithTop ℝ :=
  fun x => g (fun v => x (some v) - x none)

end DiscreteConvex.LConvexFunctionsC


