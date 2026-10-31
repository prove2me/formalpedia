-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_IsDualFeasible
-- name    : CombOpt_MinCostFlow_Digraph_IsDualFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:01.035893+00:00
-- url     : https://prove2.me/theorems/c5a428ba-9550-495f-9a33-cce5456ecbb0
-- title:
--   Feasible solution of the dual linear program (4.3)
-- statement:
--   The dual of the minimum-cost flow problem (4.1) is
--
--   $$\text{maximize } \sum(b_v y_v : v\in V)-\sum(u_{vw}z_{vw} : vw\in E)$$
--
--   subject to $-y_v+y_w-z_{vw}\le c_{vw}$ and $z_{vw}\ge 0$ for all arcs $vw$, where there is no variable $z_{vw}$ when $u_{vw}=\infty$ (the corresponding primal constraint is absent). A pair $(y,z)$ is **dual feasible** when every arc of finite capacity has $z_e\ge0$ and $-y_v+y_w-z_e\le c_e$, and every arc of infinite capacity has $-y_v+y_w\le c_e$.
--
--   **Formalization Note** The vector $z$ is indexed by the arcs of finite capacity only.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §4.1, (4.3), p. 92 (PDF p. 100)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph

namespace CombOpt.MinCostFlow

/-- **Feasible solution of the dual linear program (4.3).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §4.1, p. 92 (PDF p. 100): the dual of (4.1) is
"Maximize Σ(b_v y_v : v ∈ V) − Σ(u_vw z_vw : vw ∈ E) subject to −y_v + y_w − z_vw ≤ c_vw for all
vw ∈ E, z_vw ≥ 0 for all vw ∈ E", where "if u_vw = ∞, then there is no dual variable z_vw".

`G.IsDualFeasible u c y z` holds when every finite-capacity arc `e = vw` has `z_e ≥ 0` and
`−y_v + y_w − z_e ≤ c_e`, and every infinite-capacity arc has `−y_v + y_w ≤ c_e`.

**Formalization Note.** The variables `z` are indexed by the finite-capacity arcs
`{e // u e ≠ ⊤}`, so that, as in the book, there is no `z_e` when `u_e = ∞`. -/
def Digraph.IsDualFeasible {V E : Type*} (G : Digraph V E) (u : E → EReal) (c : E → ℝ)
    (y : V → ℝ) (z : {e : E // u e ≠ ⊤} → ℝ) : Prop :=
  (∀ e : {e : E // u e ≠ ⊤}, 0 ≤ z e ∧ -y (G.tail e.1) + y (G.head e.1) - z e ≤ c e.1) ∧
    ∀ e, u e = ⊤ → -y (G.tail e) + y (G.head e) ≤ c e

end CombOpt.MinCostFlow


