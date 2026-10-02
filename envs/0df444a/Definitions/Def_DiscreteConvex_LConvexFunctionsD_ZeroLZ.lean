-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZ
-- name    : DiscreteConvex_LConvexFunctionsD_ZeroLZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:05:10.315761+00:00
-- url     : https://prove2.me/theorems/6d8bf6ef-1c79-4e22-8e4c-efdae2bb5656
-- title:
--   ZeroLZ
-- statement:
--   The class $0L[\mathbb Z\to\mathbb R]$: L-convex functions on integer points whose convex extension is positively homogeneous.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ConvexClosureVal
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosHomogeneous

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0L[Z→R]`: L-convex functions on integer points whose convex extension is
positively homogeneous. -/
def ZeroLZ (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF g ∧ TRF g ∧ PosHomogeneous (fun p => ConvexClosureVal g p)

end DiscreteConvex.LConvexFunctionsD


