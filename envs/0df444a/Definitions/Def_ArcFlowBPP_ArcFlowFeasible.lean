-- Prove2me | Definitions.Def_ArcFlowBPP_ArcFlowFeasible
-- name    : ArcFlowBPP_ArcFlowFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:06:58.192522+00:00
-- url     : https://prove2.me/theorems/c64221fe-63df-495a-a2fc-4a7cb553ec73
-- title:
--   Feasible solution of the general arc-flow model (17)–(22)
-- statement:
--   Let $m$ be the number of items, $b \in \mathbb N^m$ the demands and $J \subseteq \{1,\dots,m\}$ the set of items whose demands must be met exactly. A pair $(f, z)$ is **feasible** for the general arc-flow model
--
--   $$
--   \begin{aligned}
--   \text{minimize}\quad & z && (17)\\
--   \text{subject to}\quad & \textstyle\sum_{(u,v,i):v=k} f_{uvi} - \sum_{(v,r,i):v=k} f_{vri} = -z,\ z,\ 0 \text{ for } k = s,\ t,\ \text{other} && (18)\\
--   & \textstyle\sum_{(u,v,j):j=i} f_{uvj} \ge b_i, \quad i \notin J, && (19)\\
--   & \textstyle\sum_{(u,v,j):j=i} f_{uvj} = b_i, \quad i \in J, && (20)\\
--   & f_{uvi} \le b_i \quad \text{for every arc with } i \ne 0, && (21)\\
--   & f_{uvi} \ge 0 && (22)
--   \end{aligned}
--   $$
--
--   if it satisfies (18)–(22). The coefficient ring is $\mathbb N$ for the integer program ((22) "integer") and $\mathbb R$ for its linear relaxation.
--
--   **Formalization Note** Items are `Fin m` and loss arcs (label $0$) have label `none`; (21) puts no bound on loss arcs, as on the page.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, model (17)–(22), p.7

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph
import Definitions.Def_ArcFlowBPP_FlowConservation
import Definitions.Def_ArcFlowBPP_labelFlow

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, model (17)–(22), p.7: `(f, z)` is a feasible solution of the general arc-flow model
with demands `b` and exact-demand set `J` ("a subset of items whose demands are required to be
satisfied exactly", p.7):
1. (18) flow conservation with value `z` (`ArcFlowBPP.FlowConservation`);
2. (19) `∑_{label = i} f ≥ bᵢ` for `i ∉ J`;
3. (20) `∑_{label = i} f = bᵢ` for `i ∈ J`;
4. (21) `f_{uvi} ≤ bᵢ` for every arc with item label `i ≠ 0` (no bound on loss arcs);
5. (22) `f ≥ 0`.
The objective (17) is `z`.

**Formalization Note.** Over `R = ℕ` this is the integer program ((22) "integer"); over `R = ℝ`
it is its linear relaxation. Items are `Fin m`, a loss arc has label `none`. -/
def ArcFlowFeasible {m : ℕ} {V A : Type*} [Fintype A] [DecidableEq V] (R : Type*) [Semiring R]
    [PartialOrder R] (G : LabelledGraph m V A) (b : Fin m → ℕ) (J : Finset (Fin m)) (f : A → R)
    (z : R) : Prop :=
  FlowConservation G f z ∧
    (∀ i, i ∉ J → (b i : R) ≤ labelFlow G f i) ∧
    (∀ i, i ∈ J → labelFlow G f i = (b i : R)) ∧
    (∀ a i, G.label a = some i → f a ≤ (b i : R)) ∧
    (∀ a, 0 ≤ f a)

end ArcFlowBPP


