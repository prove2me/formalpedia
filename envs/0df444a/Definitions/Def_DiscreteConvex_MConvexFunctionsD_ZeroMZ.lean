-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMZ
-- name    : DiscreteConvex_MConvexFunctionsD_ZeroMZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:55:30.830987+00:00
-- url     : https://prove2.me/theorems/d5f32bb1-08af-41ba-a08a-cbaa99fb62be
-- title:
--   ZeroMZ
-- statement:
--   The class $0M[\mathbb Z\to\mathbb R]$: M-convex functions whose convex extension is positively homogeneous.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ConvexClosureVal
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosHomogeneous

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0M[Z→R]`: M-convex functions whose convex extension is positively homogeneous. -/
def ZeroMZ (f : (V → ℤ) → WithTop ℝ) : Prop := MExchangeAxiom f ∧ PosHomogeneous (ConvexClosureVal f)

end DiscreteConvex.MConvexFunctionsD


