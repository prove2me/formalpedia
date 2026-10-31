-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_Graph_system63
-- name    : CombOpt_MatchingPolytope_Graph_system63
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:40.180914+00:00
-- url     : https://prove2.me/theorems/4dd52d42-d919-436b-94c9-109619cf2eed
-- title:
--   The solution set of the perfect matching system (6.3)
-- statement:
--   For a graph $G=(V,E)$, the system (6.3) in the variables $x\in\mathbb R^E$ is
--   $$\begin{aligned} x(\delta(v))&=1, && \text{for all } v\in V,\\ x(\delta(S))&\ge1, && \text{for all } S\subseteq V,\ |S|\ge3 \text{ and odd},\\ x_e&\ge0, && \text{for all } e\in E.\end{aligned}$$
--   This definition is the set of its solutions.
--
--   By Theorem 6.3 this set equals the convex hull of the characteristic vectors of perfect matchings when $G$ has no loops.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.1, p. 201 (PDF p. 209), system (6.3)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_cut

namespace CombOpt.MatchingPolytope

/-- **The solution set of the system (6.3).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.1, p. 201 (PDF p. 209):
```
x(δ(v)) = 1,   for all v ∈ V                     (6.3)
x(δ(S)) ≥ 1,   for all S ⊆ V, |S| ≥ 3 and odd
x_e ≥ 0,       for all e ∈ E.
```
Here `x(A) = Σ_{e ∈ A} x_e` (p. 39) and `δ(v) = δ({v})`. -/
noncomputable def Graph.system63 {V E : Type*} [Fintype E] (G : Graph V E) : Set (E → ℝ) :=
  {x | (∀ v : V, ∑ e ∈ G.cut {v}, x e = 1) ∧
      (∀ S : Finset V, 3 ≤ S.card → Odd S.card → 1 ≤ ∑ e ∈ G.cut S, x e) ∧
      (∀ e : E, 0 ≤ x e)}

end CombOpt.MatchingPolytope


