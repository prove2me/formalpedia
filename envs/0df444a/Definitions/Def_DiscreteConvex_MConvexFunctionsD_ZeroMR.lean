-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR
-- name    : DiscreteConvex_MConvexFunctionsD_ZeroMR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:42.828168+00:00
-- url     : https://prove2.me/theorems/bf4f60a0-aec7-4fc7-993b-f2c3dd6236ba
-- title:
--   ZeroMR
-- statement:
--   The class $0M[\mathbb R\to\mathbb R]$: polyhedral M-convex, positively homogeneous functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosHomogeneous

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0M[R→R]`: polyhedral M-convex, positively homogeneous functions. -/
def ZeroMR (g : (V → ℝ) → WithTop ℝ) : Prop := MExchangeAxiomR g ∧ PosHomogeneous g

end DiscreteConvex.MConvexFunctionsD


