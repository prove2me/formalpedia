-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP0
-- name    : DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:25:12.27982+00:00
-- url     : https://prove2.me/theorems/0cf9949c-a161-4472-aa8e-d0d463e20c95
-- title:
--   FeasibleFlowMCFP0
-- statement:
--   Feasibility for MCFP0, via its MCFP3 encoding.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.246, Eqs. (9.3)-(9.4), via the MCFP3 encoding.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.246, Eqs. (9.3)-(9.4), via the MCFP3 encoding

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArcCostMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryCostMCFP0

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Feasibility for MCFP0, via its MCFP3 encoding. -/
def FeasibleFlowMCFP0 (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ) : Prop :=
  FeasibleFlowMCFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi

end DiscreteConvex.NetworkFlowsB


