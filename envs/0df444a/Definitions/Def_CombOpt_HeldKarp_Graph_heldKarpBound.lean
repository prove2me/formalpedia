-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_heldKarpBound
-- name    : CombOpt_HeldKarp_Graph_heldKarpBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:36.46808+00:00
-- url     : https://prove2.me/theorems/e66bbe9f-5963-490b-ad79-cd44a04c9d80
-- title:
--   The Held–Karp bound for node numbers $y$
-- statement:
--   Given edge costs $c$, a node $v_1$ and node numbers $y\in\mathbb R^V$, let $C$ be the 1-tree bound of $G$ with respect to $v_1$ and the altered costs $\bar c_e=c_e-y_u-y_v$. The **Held–Karp bound** is
--   $$2\sum_{v\in V}y_v + C .$$
--   The **optimal Held–Karp bound** is its supremum over all $y\in\mathbb R^V$.
--
--   **Formalization Note** Valued in `EReal`; it is $+\infty$ exactly when $G$ has no 1-tree.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, box "Held-Karp Bound", p. 255 (PDF p. 263); p. 256

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_oneTreeBound
import Definitions.Def_CombOpt_HeldKarp_Graph_reducedCost

namespace CombOpt.HeldKarp

/-- **The Held–Karp bound for node numbers y.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, box
"Held-Karp Bound", p. 255 (PDF p. 263): "let C be the 1-tree bound for G with respect to the edge
costs (c̄_e : e ∈ E). Then 2Σ(y_v : v ∈ V) + C is a lower bound for the TSP on G".

`G.heldKarpBound c v₁ y = 2 Σ_{v ∈ V} y_v + C`, with `C` the 1-tree bound (`Graph.oneTreeBound`)
for the altered costs `c̄ = G.reducedCost c y` and the same node `v₁`.

**Formalization Note.** The value lies in `EReal`; it is `⊤` exactly when the 1-tree bound is `⊤`
(no 1-tree exists). The optimal Held–Karp bound of p. 256 is its supremum over all `y : V → ℝ`. -/
noncomputable def Graph.heldKarpBound {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E)
    (c : E → ℝ) (v₁ : V) (y : V → ℝ) : EReal :=
  ((2 * ∑ v, y v : ℝ) : EReal) + G.oneTreeBound (G.reducedCost c y) v₁

end CombOpt.HeldKarp


