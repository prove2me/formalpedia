-- Prove2me | Definitions.Def_TwoChoicesSuffice_KOut_Leaders
-- name    : TwoChoicesSuffice_KOut_Leaders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:22.659205+00:00
-- url     : https://prove2.me/theorems/1bfbe062-a8af-4a7e-9231-5263da31f1ea
-- title:
--   Leaders, owners, depths, $x^j_G(H)$, $L_G(H)$ and the augmented graph $H^{2+}$
-- statement:
--   Fix a vertex weight $w$ and a total order on $V$. Order vertices by increasing $w$, breaking ties by the fixed order. The **leader** $\alpha_C$ of a component $C$ of a spanning subgraph $H$ is its largest vertex in this order; a component is **higher** (lower) than another if its leader is. With $w=\deg_G$ the leader of $C$ has the largest original degree in $C$, so $\Phi_G(H)=\sum_C\deg_G(\alpha_C)$.
--
--   A crossing edge $uv\in X_G(H)$ is **owned** by its endpoint in the higher component. The **depth** of a vertex is its distance in $H$ to the leader of its component. For $j\ge0$, $x^j_G(H)$ is the number of crossing edges whose owner is at depth $j$ (degree order). The quantity
--   $$
--   L_G(H)=\sum_{C\in\mathrm{CC}(H)}\bigl|\{x\in N_G(\alpha_C):\ x\text{ lies in a component of }H\text{ lower than }C\}\bigr|
--   $$
--   counts the leaders' neighbours in lower components; it equals $x^0_G(H)$.
--
--   The **augmented two-out graph** $H^{2+}_G(\sigma)$ is built from an outcome with at least three choices per vertex: start with $H^2_G(\sigma)$, and for the leader $\alpha_C$ of each $H^2$-component add the edge to its third choice $s_3(\alpha_C)$ exactly when that neighbour lies in a higher $H^2$-component. All decisions are taken in $H^2_G(\sigma)$, not sequentially. Thus $H^2_G(\sigma)\subseteq H^{2+}_G(\sigma)\subseteq H^3_G(\sigma)$.
--
--   These objects drive the potential bound of §5 and the refined switching of §6.
--
--   **Formalization Note** The order is the lexicographic key `(w v, v)` with the `LinearOrder` of `V` as tie-break. `leader w H v` is the maximum of the key over the component of `v`; `depth` uses `SimpleGraph.dist` to that leader, which is always reachable. `ownedCount w G H j P` counts crossing edges $uv$ with owner $u$ at depth $j$ satisfying a side condition `P u v`. `augment w G H t` adds, for every leader $v$, the edge $v\,t(v)$ when $t(v)$ is a $G$-neighbour in a higher component; `augTwoOut G σ` is $H^{2+}_G(\sigma)$ with $t=s_3$ (position index 2).
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), §5 and §5.1.1 (leaders, augmented 2-out graph, depth, x^j_G, L_G), printed p. 9, PDF p. 10; PDF pp. 10–11

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling

open scoped Classical

namespace TwoChoicesSuffice.KOut

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The total order used to pick leaders: vertices are sorted by increasing weight `w`,
ties broken by the fixed total order of `V` (the `LinearOrder` instance, which plays the
role of the paper's arbitrary tie-breaking order, resp. of `π` in §7). The key
`(w v, v)` in lexicographic order is injective, so this order is total and strict. -/
def rankKey (w : V → ℕ) (v : V) : ℕ ×ₗ V := toLex (w v, v)

/-- The leader `α_C` of the component of `v` in `H`: the largest vertex of that component
in the order `rankKey w`. Source: §5, PDF p. 10 (printed p. 9); §7.2, PDF p. 16. -/
noncomputable def leader (w : V → ℕ) (H : SimpleGraph V) (v : V) : V :=
  (ofLex ((Finset.univ.filter fun u => H.Reachable v u).sup'
    ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ v, SimpleGraph.Reachable.refl v⟩⟩
    (rankKey w))).2

/-- `v`'s component of `H` is lower than `u`'s component (their leaders compare so). -/
def CompLower (w : V → ℕ) (H : SimpleGraph V) (v u : V) : Prop :=
  rankKey w (leader w H v) < rankKey w (leader w H u)

/-- Depth of `v` in `H`: its `H`-distance to the leader of its own component. -/
noncomputable def depth (w : V → ℕ) (H : SimpleGraph V) (v : V) : ℕ :=
  H.dist v (leader w H v)

/-- The number of crossing edges `e = uv ∈ X_G(H)` whose owner `u` (the endpoint in the
higher component) is at depth `j` and such that `P u v` holds (owner first). -/
noncomputable def ownedCount (w : V → ℕ) (G H : SimpleGraph V) (j : ℕ) (P : V → V → Prop) :
    ℕ :=
  ((crossingEdges G H).filter fun e =>
    ∃ u v : V, e = s(u, v) ∧ CompLower w H v u ∧ depth w H u = j ∧ P u v).card

/-- `x^j_G(H)`: crossing edges whose owner is at depth `j`, for the leader order by
increasing original degree `deg_G`, ties broken by the order of `V`.
Source: §5.1.1, PDF p. 11 (printed p. 10). -/
noncomputable def depthCrossing (G H : SimpleGraph V) (j : ℕ) : ℕ :=
  ownedCount (fun v => G.degree v) G H j (fun _ _ => True)

/-- `L_G(H) = ∑_{C ∈ CC(H)} d_C^↓`: for every leader `α_C` of `H` (degree order), the
number of its `G`-neighbours in lower components of `H`, summed over components.
Source: §5.1, PDF p. 11 (printed p. 10). -/
noncomputable def leaderLowerNeighbors (G H : SimpleGraph V) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v => leader (fun x => G.degree x) H v = v),
    (Finset.univ.filter fun x => G.Adj v x ∧ CompLower (fun y => G.degree y) H x v).card

/-- Leader augmentation: to `H` add, for every leader `v` of `H` (order `rankKey w`), the
edge from `v` to `t v` exactly when `t v` is a `G`-neighbour of `v` lying in a higher
component of `H`. All decisions are made in `H` itself (not sequentially). -/
noncomputable def augment (w : V → ℕ) (G H : SimpleGraph V) (t : V → V) : SimpleGraph V :=
  H ⊔ SimpleGraph.fromEdgeSet {e | ∃ v, leader w H v = v ∧ G.Adj v (t v) ∧
    CompLower w H v (t v) ∧ e = s(v, t v)}

/-- The third choice `σ v 2` of an outcome with at least three positions (dummy `v` when
`k < 3`, which never yields an edge). -/
def thirdChoice {k : ℕ} (σ : V → Fin k → V) (v : V) : V :=
  if h : 2 < k then σ v ⟨2, h⟩ else v

/-- The augmented two-out graph `H^{2+}_G(σ)`: start from `H^2_G(σ)` and add each
`H^2`-leader's third choice exactly when it reaches a higher `H^2`-component (leaders by
increasing original degree). For `σ` with `k ≥ 3` positions,
`H^2(σ) ≤ H^{2+}(σ) ≤ H^3(σ)`. Source: §5, PDF p. 10 (printed p. 9). -/
noncomputable def augTwoOut (G : SimpleGraph V) {k : ℕ} (σ : V → Fin k → V) :
    SimpleGraph V :=
  augment (fun v => G.degree v) G (prefixGraph G σ 2) (thirdChoice σ)

end TwoChoicesSuffice.KOut


