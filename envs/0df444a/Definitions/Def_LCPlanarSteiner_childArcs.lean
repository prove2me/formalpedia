-- Prove2me | Definitions.Def_LCPlanarSteiner_childArcs
-- name    : LCPlanarSteiner_childArcs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:57.417866+00:00
-- url     : https://prove2.me/theorems/54a50102-e816-4a24-88c6-0e00a1182761
-- title:
--   The child region containing a vertex and its owned arcs
-- statement:
--   Let $(C, B, E_R)$ be a region with surviving set $K_R$ (horizon $H$, estimate $\Gamma$) and let $S$ be the separator vertices, $B' = B \cup S$. The **child component** of a vertex $t \in K_R \setminus S$ is its weak component in the graph on $K_R \setminus S$ whose edges are the owned arcs with both ends there. The child owns
--   $$
--   E_i = \{ uv \in E_R : v \in C_i,\ u \in B' \cup C_i \}.
--   $$
--
--   This is the region in which the recursion continues for the terminals of $C_i$.
--
--   **Formalization Note** The component is taken as the reflexive–transitive closure of adjacency, so it always contains $t$.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §3.1, p.5

import Mathlib
import Definitions.Def_LCPlanarSteiner_InK

namespace LCPlanarSteiner

/-- **The child region containing a vertex, and its owned arcs `E_i`.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §3.1, p.5: "The separator host is the contracted graph restricted to {b_R} ∪ K_R … Write
S = (⋃_j V(P_j)) \ B and B′ = B ∪ S. For each weak component C_i of the separator host after
deleting its root and S, retain those containing terminals. Its child owns
E_i = {uv ∈ E_R : v ∈ C_i, u ∈ B′ ∪ C_i}."

`childComp G C B ER H Γ S t` is the weak component of `t` in the graph on `K_R \ S` whose edges
are the owned arcs with both ends in `K_R \ S` (either direction). `childArcs … t` is the set of
owned arcs whose head is in that component and whose tail is in `B ∪ S` or in the component.

**Formalization Note.** The component is the reflexive–transitive closure of the adjacency, so it
always contains `t`; it is the paper's `C_i` when `t ∈ K_R \ S`. Membership is a `Set`, no
decidability is needed. -/
def childComp (G : Net) (C B ER : Finset ℕ) (H Γ : ℚ) (S : Finset ℕ) (t : ℕ) : Set ℕ :=
  {u | Relation.ReflTransGen
    (fun a c => InK G C B ER H Γ a ∧ a ∉ S ∧ InK G C B ER H Γ c ∧ c ∉ S ∧
      ∃ e ∈ ER, (G.tl e = a ∧ G.hd e = c) ∨ (G.tl e = c ∧ G.hd e = a)) t u}

/-- The owned arcs `E_i` of the child region containing `t`. -/
def childArcs (G : Net) (C B ER : Finset ℕ) (H Γ : ℚ) (S : Finset ℕ) (t : ℕ) : Set ℕ :=
  {e | e ∈ ER ∧ G.hd e ∈ childComp G C B ER H Γ S t ∧
    (G.tl e ∈ B ∨ G.tl e ∈ S ∨ G.tl e ∈ childComp G C B ER H Γ S t)}

end LCPlanarSteiner


