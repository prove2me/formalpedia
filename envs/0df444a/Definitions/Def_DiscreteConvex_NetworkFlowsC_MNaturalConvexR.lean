-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_MNaturalConvexR
-- name    : DiscreteConvex_NetworkFlowsC_MNaturalConvexR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:03:01.895556+00:00
-- url     : https://prove2.me/theorems/bf301060-9a10-43c5-be8e-770e0583ae1e
-- title:
--   MNaturalConvexR
-- statement:
--   $f$ is M$^\natural$-convex (real domain): its lift is M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, redeclared, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, redeclared, real version

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LiftedFunctionR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def MNaturalConvexR (f : (V → ℝ) → WithTop ℝ) : Prop := MExchangeAxiomR (LiftedFunctionR f)

end DiscreteConvex.NetworkFlowsC


