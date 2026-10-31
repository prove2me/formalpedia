-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_Graph_system67
-- name    : CombOpt_MatchingPolytope_Graph_system67
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:51.936147+00:00
-- url     : https://prove2.me/theorems/49cb7c7d-7c4a-4338-903a-1b20aca79484
-- title:
--   The solution set of the matching system (6.7)
-- statement:
--   For a graph $G=(V,E)$, the system (6.7) in the variables $x\in\mathbb R^E$ is
--   $$\begin{aligned} x(\delta(v))&\le1, && \text{for all } v\in V,\\ x(\gamma(S))&\le\frac{|S|-1}{2}, && \text{for all } S\subseteq V,\ |S|\ge3 \text{ and odd},\\ x_e&\ge0, && \text{for all } e\in E,\end{aligned}$$
--   where $x(A)=\sum_{e\in A}x_e$. This definition is the set of its solutions.
--
--   By Theorem 6.20 this set equals the matching polytope $M(G)$ when $G$ has no loops.
--
--   **Formalization Note** $(|S|-1)/2$ is computed in $\mathbb R$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.3, p. 214 (PDF p. 222), system (6.7)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_cut
import Definitions.Def_CombOpt_MatchingPolytope_Graph_gamma

namespace CombOpt.MatchingPolytope

/-- **The solution set of the system (6.7).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.3, p. 214 (PDF p. 222):
```
x(δ(v)) ≤ 1,              for all v ∈ V                      (6.7)
x(γ(S)) ≤ (|S| − 1)/2,    for all S ⊆ V, |S| ≥ 3 and odd.
x_e ≥ 0,                  for all e ∈ E.
```
Here `x(A) = Σ_{e ∈ A} x_e` (p. 39) and `δ(v) = δ({v})`.

**Formalization Note.** `(|S| − 1)/2` is computed in `ℝ` (no truncation); `|S|` ranges over odd
cardinalities `≥ 3` exactly as printed. -/
noncomputable def Graph.system67 {V E : Type*} [Fintype E] (G : Graph V E) : Set (E → ℝ) :=
  {x | (∀ v : V, ∑ e ∈ G.cut {v}, x e ≤ 1) ∧
      (∀ S : Finset V, 3 ≤ S.card → Odd S.card →
        ∑ e ∈ G.gamma S, x e ≤ ((S.card : ℝ) - 1) / 2) ∧
      (∀ e : E, 0 ≤ x e)}

end CombOpt.MatchingPolytope


