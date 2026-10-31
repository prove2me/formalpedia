-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_IsFeasibleFlow
-- name    : CombOpt_MinCostFlow_Digraph_IsFeasibleFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:51.372992+00:00
-- url     : https://prove2.me/theorems/472473f0-5d33-4a4e-ace3-79156202d66a
-- title:
--   Feasible solution of the minimum-cost flow problem (4.1)
-- statement:
--   Let $G=(V,E)$ be a digraph with **demands** $b\in\mathbb R^V$ and **capacities** $u\in(\mathbb R\cup\{\infty\})^E$. A vector $x\in\mathbb R^E$ is a **feasible solution** of the minimum-cost flow problem (4.1) when
--
--   1. $f_x(v)=b_v$ for every node $v\in V$, and
--   2. $0\le x_e\le u_e$ for every arc $e\in E$.
--
--   An infinite capacity $u_e=\infty$ imposes no upper bound on $x_e$.
--
--   **Formalization Note** Capacities are `EReal`, with $u_e=\infty$ encoded as `⊤`. The standing assumptions $u\ge 0$ and $b(V)=0$ of §4.1 are hypotheses of the theorems that use this predicate.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §4.1, (4.1), p. 91 (PDF p. 99)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_netInflow

namespace CombOpt.MinCostFlow

/-- **Feasible solution of the minimum-cost flow problem (4.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §4.1, p. 91 (PDF p. 99): the constraints of (4.1) are
`f_x(v) = b_v` for all v ∈ V and `0 ≤ x_e ≤ u_e` for all e ∈ E, where the demands `b ∈ ℝ^V`
and the capacities `u ∈ (ℝ ∪ {∞})^E`.

`G.IsFeasibleFlow b u x` holds when the net flow into every node `v` is `b v` and every arc
satisfies `0 ≤ x e ≤ u e`.

**Formalization Note.** Capacities are `EReal`; `u e = ⊤` is the book's `u_e = ∞` (no upper
bound). The book's standing assumptions `u ≥ 0` and `b(V) = 0` (p. 91) are hypotheses of the
theorems, not part of this predicate. -/
def Digraph.IsFeasibleFlow {V E : Type*} [Fintype E] [DecidableEq V] (G : Digraph V E)
    (b : V → ℝ) (u : E → EReal) (x : E → ℝ) : Prop :=
  (∀ v, G.netInflow x v = b v) ∧ ∀ e, 0 ≤ x e ∧ (x e : EReal) ≤ u e

end CombOpt.MinCostFlow


