-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetMCFP0
-- name    : DiscreteConvex_NetworkFlowsB_OptimalPotentialSetMCFP0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:36:21.344998+00:00
-- url     : https://prove2.me/theorems/9bb8439b-3f18-48f8-9642-c305dcf43f44
-- title:
--   OptimalPotentialSetMCFP0
-- statement:
--   The set of optimal potentials for MCFP0.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.252, the set $\\Pi^*$ of Theorem 9.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.252, the set $\\Pi^*$ of Theorem 9.6

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetMSFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArcCostMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryCostMCFP0

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The set of optimal potentials for MCFP0. -/
def OptimalPotentialSetMCFP0 (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (x : V → ℝ) : Set (V → ℝ) :=
  OptimalPotentialSetMSFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x)

-- ===== Auxiliary networks and negative cycles (shared machinery) =====

end DiscreteConvex.NetworkFlowsB


