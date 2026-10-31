-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_IsOptimalFlow
-- name    : CombOpt_MinCostFlow_Digraph_IsOptimalFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:51.217999+00:00
-- url     : https://prove2.me/theorems/58cf699a-f823-48e3-bd8d-0d35450242bb
-- title:
--   Optimal solution of the minimum-cost flow problem (4.1)
-- statement:
--   Given a digraph $G$, demands $b$, capacities $u$ and costs $c\in\mathbb R^E$, the **minimum-cost flow problem** (4.1) is
--
--   $$\text{minimize } \sum(c_e x_e : e\in E)\quad\text{subject to } f_x(v)=b_v\ (v\in V),\ 0\le x_e\le u_e\ (e\in E).$$
--
--   A vector $x$ is an **optimal solution** when it is feasible and $\sum c_e x_e\le\sum c_e x'_e$ for every feasible $x'$. "(4.1) has an optimal solution" means such an $x$ exists, so the minimum is attained.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §4.1, (4.1), p. 91 (PDF p. 99)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_IsFeasibleFlow

namespace CombOpt.MinCostFlow

/-- **Optimal solution of the minimum-cost flow problem (4.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §4.1, p. 91 (PDF p. 99): (4.1) is "Minimize Σ(c_e x_e : e ∈ E)" over the feasible flows.

`G.IsOptimalFlow b u c x` holds when `x` is feasible and `Σ c_e x_e ≤ Σ c_e x'_e` for every
feasible `x'`; "(4.1) has an optimal solution" is `∃ x, G.IsOptimalFlow b u c x`.

**Formalization Note.** Optimality means the minimum is attained at `x`; no infimum is taken. -/
def Digraph.IsOptimalFlow {V E : Type*} [Fintype E] [DecidableEq V] (G : Digraph V E)
    (b : V → ℝ) (u : E → EReal) (c : E → ℝ) (x : E → ℝ) : Prop :=
  G.IsFeasibleFlow b u x ∧
    ∀ x' : E → ℝ, G.IsFeasibleFlow b u x' → ∑ e, c e * x e ≤ ∑ e, c e * x' e

end CombOpt.MinCostFlow


