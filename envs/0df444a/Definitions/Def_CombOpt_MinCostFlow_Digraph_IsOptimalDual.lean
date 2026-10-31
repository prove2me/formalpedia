-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_IsOptimalDual
-- name    : CombOpt_MinCostFlow_Digraph_IsOptimalDual
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:21.066998+00:00
-- url     : https://prove2.me/theorems/734a0a3b-cbf2-45cf-ac05-90a7668a4779
-- title:
--   Optimal solution of the dual linear program (4.3)
-- statement:
--   A pair $(y,z)$ is an **optimal solution** of the dual program (4.3) when it is dual feasible and its objective is at least that of every dual feasible pair. Following the book, a node vector $y$ alone is called an optimal dual solution when it extends to an optimal pair $(y,z)$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §4.1, (4.3), p. 92 (PDF p. 100)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_IsDualFeasible
import Definitions.Def_CombOpt_MinCostFlow_Digraph_dualObjective

namespace CombOpt.MinCostFlow

/-- **Optimal solution of the dual linear program (4.3).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §4.1, p. 92 (PDF p. 100). `G.IsOptimalDual b u c y z` holds when `(y, z)` is feasible for
(4.3) and its objective is at least that of every feasible `(y', z')`. Following p. 92, "we may
refer to y alone as a feasible or optimal dual solution, if it extends in this way to a feasible or
optimal solution of (4.3)": `y` alone is optimal when `∃ z, G.IsOptimalDual b u c y z`. -/
def Digraph.IsOptimalDual {V E : Type*} [Fintype V] [Fintype E] (G : Digraph V E)
    (b : V → ℝ) (u : E → EReal) (c : E → ℝ) (y : V → ℝ) (z : {e : E // u e ≠ ⊤} → ℝ) : Prop :=
  G.IsDualFeasible u c y z ∧
    ∀ (y' : V → ℝ) (z' : {e : E // u e ≠ ⊤} → ℝ), G.IsDualFeasible u c y' z' →
      G.dualObjective b u y' z' ≤ G.dualObjective b u y z

end CombOpt.MinCostFlow


