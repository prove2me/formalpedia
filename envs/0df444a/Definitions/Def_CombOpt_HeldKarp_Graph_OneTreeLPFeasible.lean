-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_OneTreeLPFeasible
-- name    : CombOpt_HeldKarp_Graph_OneTreeLPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:42.550045+00:00
-- url     : https://prove2.me/theorems/ed4b454e-50fa-48f2-8869-a94be8c1f444
-- title:
--   Feasibility for the 1-tree linear program (7.7)
-- statement:
--   Fix a node $v_1$. A vector $x\in\mathbb R^E$ is **feasible for (7.7)** if it satisfies (7.4) (for nonempty $S$), (7.5), (7.6) and $x(\delta(v_1))=2$:
--   $$x(\gamma(S))\le|S|-1\ (\emptyset\ne S\subseteq V,\ v_1\notin S),\quad x(\gamma(V\setminus\{v_1\}))=|V|-2,\quad 0\le x\le 1,\quad x(\delta(v_1))=2.$$
--
--   **Formalization Note** As for (7.2), $S=\emptyset$ is excluded from (7.4).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, (7.7), p. 260 (PDF p. 268)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_cut
import Definitions.Def_CombOpt_HeldKarp_Graph_gamma

namespace CombOpt.HeldKarp

/-- **x is feasible for the 1-tree linear program (7.7).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, (7.7),
p. 260 (PDF p. 268): "min {c^T x : x satisfies (7.4), (7.5), (7.6), and x(δ(v_1)) = 2}", where
(p. 259) (7.4) is x(γ(S)) ≤ |S| − 1 for all S ⊆ V, v_1 ∉ S; (7.5) is x(γ(V \ {v_1})) = |V| − 2;
(7.6) is 0 ≤ x_e ≤ 1 for all e ∈ E.

`G.OneTreeLPFeasible v₁ x` is the conjunction of (7.4) for **nonempty** `S`, (7.5), (7.6) and
`x(δ(v₁)) = 2`.

**Formalization Note.** As in `Graph.InsideFeasible`, (7.4) is imposed for nonempty `S` only: at
`S = ∅` the printed constraint reads `0 ≤ −1` and would make (7.7) infeasible always (a correction,
recorded on the theorem that uses it). `|S| − 1` and `|V| − 2` are computed in `ℝ`. -/
def Graph.OneTreeLPFeasible {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : Graph V E)
    (v₁ : V) (x : E → ℝ) : Prop :=
  (∀ S : Finset V, S.Nonempty → v₁ ∉ S → ∑ e ∈ G.gamma S, x e ≤ (S.card : ℝ) - 1) ∧
  (∑ e ∈ G.gamma (Finset.univ.erase v₁), x e = (Fintype.card V : ℝ) - 2) ∧
  (∀ e : E, 0 ≤ x e ∧ x e ≤ 1) ∧
  (∑ e ∈ G.cut {v₁}, x e = 2)

end CombOpt.HeldKarp


