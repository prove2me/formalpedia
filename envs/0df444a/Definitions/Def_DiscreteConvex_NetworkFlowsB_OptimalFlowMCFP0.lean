-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP0
-- name    : DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:27:27.418509+00:00
-- url     : https://prove2.me/theorems/7a1d9ec3-7c87-4640-8896-3a109628d853
-- title:
--   OptimalFlowMCFP0
-- statement:
--   $\xi$ is an optimal flow for MCFP0, via its MCFP3 encoding.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.246, via the MCFP3 encoding.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.246, via the MCFP3 encoding

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArcCostMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryCostMCFP0

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `ξ` is an optimal flow for MCFP0, via its MCFP3 encoding. -/
def OptimalFlowMCFP0 (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ) : Prop :=
  OptimalFlowMCFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi

end DiscreteConvex.NetworkFlowsB


