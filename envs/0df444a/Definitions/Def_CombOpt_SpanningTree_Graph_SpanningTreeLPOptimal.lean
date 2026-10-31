-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_SpanningTreeLPOptimal
-- name    : CombOpt_SpanningTree_Graph_SpanningTreeLPOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:46.084389+00:00
-- url     : https://prove2.me/theorems/bdc3a4af-4bd0-42e7-ab64-db1753ef631b
-- title:
--   Optimal solution of the spanning-tree LP (2.1)
-- statement:
--   Given costs $c\in\mathbb R^E$, the linear program (2.1) is
--   $$\text{minimize } c^{T}x \text{ subject to (2.2)–(2.4)}.$$
--   A vector $x$ is an **optimal solution** of (2.1) if it is feasible and $c^{T}x\le c^{T}y$ for every feasible $y$.
--
--   **Formalization Note** Optimality is stated directly; no optimal value (infimum) is defined.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 16 (PDF p. 25), (2.1)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_SpanningTreeLPFeasible

namespace CombOpt.SpanningTree

/-- **An optimal solution of the spanning-tree linear program (2.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 16 (PDF p. 25): "Minimize c^T x (2.1) subject to (2.2)–(2.4)".

`G.SpanningTreeLPOptimal c x` says that `x` is feasible for (2.2)–(2.4) and
`∑_e c e · x e ≤ ∑_e c e · y e` for every feasible `y`.

**Formalization Note.** Optimality is stated directly (feasible and no feasible point does
better); no optimal value is defined, so nothing depends on the value of an infimum over a
possibly empty set. -/
def Graph.SpanningTreeLPOptimal {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E)
    (c : E → ℝ) (x : E → ℝ) : Prop :=
  G.SpanningTreeLPFeasible x ∧
    ∀ y : E → ℝ, G.SpanningTreeLPFeasible y → ∑ e, c e * x e ≤ ∑ e, c e * y e

end CombOpt.SpanningTree


