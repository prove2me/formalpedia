-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_subtourBound
-- name    : CombOpt_HeldKarp_Graph_subtourBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:26.390003+00:00
-- url     : https://prove2.me/theorems/97364c28-e2a7-46d9-8bfd-3588ce477eec
-- title:
--   The subtour bound
-- statement:
--   The **subtour bound** of $G$ with edge costs $c$ is the optimal value of the linear program (7.1):
--   $$\min\Big\{\sum_{e\in E}c_ex_e : x \text{ feasible for (7.1)}\Big\}.$$
--
--   **Formalization Note** Computed as an infimum in `EReal`; the feasible set is a polytope, so the minimum is attained when (7.1) is feasible, and the value is $+\infty$ when it is infeasible.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, p. 259 (PDF p. 267)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_SubtourFeasible

namespace CombOpt.HeldKarp

/-- **The subtour bound: the optimal value of (7.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, p. 259
(PDF p. 267): "the optimal value of (7.1) is a lower bound on the cost of any tour. We call this the
subtour bound for the TSP."

`G.subtourBound c` is the infimum of `Σ_e c_e x_e` over all `x` feasible for (7.1).

**Formalization Note.** The value lies in `EReal`. The feasible set is a polytope, so when it is
nonempty the infimum is attained (the optimal value); when (7.1) is infeasible the value is `⊤`. -/
noncomputable def Graph.subtourBound {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E)
    (c : E → ℝ) : EReal :=
  ⨅ (x : E → ℝ) (_ : G.SubtourFeasible x), ((∑ e, c e * x e : ℝ) : EReal)

end CombOpt.HeldKarp


