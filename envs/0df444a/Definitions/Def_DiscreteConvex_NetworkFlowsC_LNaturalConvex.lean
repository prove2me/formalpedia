-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_LNaturalConvex
-- name    : DiscreteConvex_NetworkFlowsC_LNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:08.449281+00:00
-- url     : https://prove2.me/theorems/61c45d2b-3a7e-4386-9ca9-bbceff5d9410
-- title:
--   LNaturalConvex
-- statement:
--   $g$ is L$^\natural$-convex: its lift is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SBF
import Definitions.Def_DiscreteConvex_NetworkFlowsC_TRF
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LiftedFunctionL

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def LNaturalConvex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF (LiftedFunctionL g) ∧ TRF (LiftedFunctionL g)

end DiscreteConvex.NetworkFlowsC


