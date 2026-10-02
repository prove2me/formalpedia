-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotential
-- name    : DiscreteConvex_NetworkFlowsB_IsOptimalPotential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:25:33.983522+00:00
-- url     : https://prove2.me/theorems/485722fd-f8dd-4913-b370-3c5301850304
-- title:
--   IsOptimalPotential
-- statement:
--   $p$ is an optimal potential for the flow $\xi$: conditions (i) and (ii) of (POT).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.250, condition (POT).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.250, condition (POT)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMinArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMinR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedArcCost
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedBoundaryCost

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `p` is an optimal potential for the flow `ξ`: conditions (i) and (ii) of (POT). -/
def IsOptimalPotential (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) (p : V → ℝ) : Prop :=
  (∀ a : A, xi a ∈ ArgMinArc (ReducedArcCost tail head fa p a)) ∧
    Boundary tail head xi ∈ ArgMinR (ReducedBoundaryCost f p)

end DiscreteConvex.NetworkFlowsB


