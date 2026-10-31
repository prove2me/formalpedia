-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_SubtourFeasible
-- name    : CombOpt_HeldKarp_Graph_SubtourFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:31.847269+00:00
-- url     : https://prove2.me/theorems/53f636b5-96b3-49f3-b4f2-5ac2650631b6
-- title:
--   Feasibility for the subtour linear program (7.1)
-- statement:
--   A vector $x\in\mathbb R^E$ is **feasible for (7.1)** if
--   $$x(\delta(v))=2\ \ (v\in V),\qquad x(\delta(S))\ge 2\ \ (\emptyset\ne S\ne V),\qquad 0\le x_e\le 1\ \ (e\in E).$$
--   These are the degree equations, the **subtour constraints**, and the bounds of the Dantzig–Fulkerson–Johnson relaxation of the TSP.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, (7.1), p. 259 (PDF p. 267)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_cut

namespace CombOpt.HeldKarp

/-- **x is feasible for the subtour linear program (7.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, (7.1),
p. 259 (PDF p. 267): "Minimize Σ(c_e x_e : e ∈ E) subject to x(δ(v)) = 2, for all v ∈ V;
x(δ(S)) ≥ 2, for all ∅ ≠ S ≠ V; 0 ≤ x_e ≤ 1, for all e ∈ E."

`G.SubtourFeasible x` is the conjunction of the three constraint families, with
`x(A) = Σ_{e ∈ A} x_e`.

**Formalization Note.** `S` ranges over subsets of `V` (`Finset V`) with `S ≠ ∅` and `S ≠ V`. -/
def Graph.SubtourFeasible {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E) (x : E → ℝ) :
    Prop :=
  (∀ v : V, ∑ e ∈ G.cut {v}, x e = 2) ∧
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 2 ≤ ∑ e ∈ G.cut S, x e) ∧
  (∀ e : E, 0 ≤ x e ∧ x e ≤ 1)

end CombOpt.HeldKarp


