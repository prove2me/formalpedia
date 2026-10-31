-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_reducedCost
-- name    : CombOpt_MinCostFlow_Digraph_reducedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:02.956887+00:00
-- url     : https://prove2.me/theorems/7d9546b6-9858-4b11-bc90-3534eebaa25f
-- title:
--   Reduced cost $\bar c$
-- statement:
--   For a digraph $G$, costs $c\in\mathbb R^E$ and a node vector $y\in\mathbb R^V$, the **reduced cost** of the arc $e=vw$ (tail $v$, head $w$) is
--
--   $$\bar c_{vw}=c_{vw}+y_v-y_w.$$
--
--   Reduced costs express the dual feasibility and complementary slackness conditions of the minimum-cost flow problem.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §4.1, p. 92 (PDF p. 100)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph

namespace CombOpt.MinCostFlow

/-- **Reduced cost c̄.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §4.1, p. 92 (PDF p. 100): "For a vector (y_v : v ∈ V), it is convenient to denote
c_vw + y_v − y_w by c̄_vw, and call it the *reduced cost* of vw."

`G.reducedCost c y e = c e + y (tail e) − y (head e)`. -/
def Digraph.reducedCost {V E : Type*} (G : Digraph V E) (c : E → ℝ) (y : V → ℝ) (e : E) : ℝ :=
  c e + y (G.tail e) - y (G.head e)

end CombOpt.MinCostFlow


