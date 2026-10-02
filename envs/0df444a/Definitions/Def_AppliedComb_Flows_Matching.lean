-- Prove2me | Definitions.Def_AppliedComb_Flows_Matching
-- name    : AppliedComb_Flows_Matching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:38:44.741014+00:00
-- url     : https://prove2.me/theorems/823155a1-67d8-421e-a155-d76a02a54229
-- title:
--   Bipartitions, matchings, saturated vertices and neighbor sets (Section 14.2)
-- statement:
--   Let $G = (V, E)$ be a finite simple graph. A **bipartition** $V = V_1 \cup V_2$ of $G$ is a partition of the vertex set into two disjoint parts such that every edge of $G$ has one endpoint in $V_1$ and the other in $V_2$; $G$ is bipartite when it has one.
--
--   A set $M \subseteq E$ is a **matching** if no two edges of $M$ share an endpoint. If $v$ is an endpoint of an edge of $M$, then $M$ **saturates** $v$. For a set $A$ of vertices, the set of **neighbors** of the vertices in $A$ is
--   $$N(A) = \{y \in V : y \text{ is adjacent to some } x \in A\}.$$
--
--   These are the notions of Hall's Theorem (Theorem 14.7).
--
--   **Formalization Note.** The graph is a Mathlib `SimpleGraph V` on a type with `[Fintype V] [DecidableEq V]`; the bipartition is given as two `Finset V`s. Edges are elements of `Sym2 V`, and a matching is a `Set (Sym2 V)` contained in `G.edgeSet`. The neighbor set is the `Finset` of all vertices adjacent to a vertex of `A`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 280 and 283, Section 14.2 (bipartite graph, matching, saturation, neighbors)

import Mathlib

namespace AppliedComb.Flows

variable {V : Type*}

/-- `V = V₁ ∪ V₂` is a **bipartition** of the graph `G` (Keller & Trotter, *Applied
Combinatorics*, 2017 Edition, p. 280, Section 14.2): `V₁` and `V₂` are disjoint, together they
are the whole vertex set, and every edge of `G` has one endpoint in `V₁` and the other in `V₂`
(so `V₁` and `V₂` are independent sets). -/
def IsBipartition [Fintype V] [DecidableEq V] (G : SimpleGraph V) (V₁ V₂ : Finset V) : Prop :=
  Disjoint V₁ V₂ ∧ V₁ ∪ V₂ = Finset.univ ∧
  ∀ x y, G.Adj x y → (x ∈ V₁ ∧ y ∈ V₂) ∨ (x ∈ V₂ ∧ y ∈ V₁)

/-- A set `M` of edges is a **matching** in `G` (p. 280): `M ⊆ E` and no two (distinct) edges of
`M` share an endpoint. -/
def IsMatching (G : SimpleGraph V) (M : Set (Sym2 V)) : Prop :=
  M ⊆ G.edgeSet ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : V, v ∈ e → v ∉ f

/-- `M` **saturates** the vertex `v` (p. 280): `v` is an endpoint of an edge of `M`. -/
def Saturates (M : Set (Sym2 V)) (v : V) : Prop :=
  ∃ e ∈ M, v ∈ e

open Classical in
/-- The set `N ⊆ V` of neighbors of the vertices in `A` (p. 283): all vertices adjacent in `G` to
at least one vertex of `A`. -/
noncomputable def neighborsOf [Fintype V] (G : SimpleGraph V) (A : Finset V) : Finset V :=
  Finset.univ.filter (fun y => ∃ x ∈ A, G.Adj x y)

end AppliedComb.Flows


