-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_dualObjective
-- name    : CombOpt_MinCostFlow_Digraph_dualObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:08.816955+00:00
-- url     : https://prove2.me/theorems/c2f029cc-a797-43ed-8652-d9c3662ae47e
-- title:
--   Objective of the dual linear program (4.3)
-- statement:
--   For a pair $(y,z)$ of dual variables, the objective of the dual program (4.3) is
--
--   $$\sum(b_v y_v : v\in V)-\sum(u_e z_e : e\in E,\ u_e\neq\infty).$$
--
--   **Formalization Note** On an arc of finite capacity, $u_e$ is read as a real number.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §4.1, (4.3), p. 92 (PDF p. 100)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph

namespace CombOpt.MinCostFlow

/-- **Objective of the dual linear program (4.3).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §4.1, p. 92 (PDF p. 100): "Σ(b_v y_v : v ∈ V) − Σ(u_vw z_vw : vw ∈ E)", the second sum
over the arcs that carry a dual variable, i.e. those with `u_vw ≠ ∞`.

**Formalization Note.** On a finite-capacity arc `u e` is a real number, read through
`EReal.toReal`; the theorems assume `0 ≤ u`, so `u e ≠ ⊥` and `toReal` is exact there. -/
noncomputable def Digraph.dualObjective {V E : Type*} [Fintype V] [Fintype E] (_G : Digraph V E)
    (b : V → ℝ) (u : E → EReal) (y : V → ℝ) (z : {e : E // u e ≠ ⊤} → ℝ) : ℝ := by
  classical
  exact (∑ v, b v * y v) - ∑ e : {e : E // u e ≠ ⊤}, (u e.1).toReal * z e

end CombOpt.MinCostFlow


