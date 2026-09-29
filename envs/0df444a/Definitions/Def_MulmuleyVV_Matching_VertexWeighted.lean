-- Prove2me | Definitions.Def_MulmuleyVV_Matching_VertexWeighted
-- name    : MulmuleyVV_Matching_VertexWeighted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:34:23.21308+00:00
-- url     : https://prove2.me/theorems/8d05fa96-555c-40ab-88a0-7f6924f02f2f
-- title:
--   Matchings, maximum matchings, matching sets and the lexicographically largest matching set
-- statement:
--   Let $G = (V, E)$ be a finite simple graph.
--
--   1. A **matching** is a set of edges of $G$, no two of which share a vertex; a **maximum matching** is a matching of largest cardinality.
--   2. A set $V' \subseteq V$ is a **matching set** if $V'$ is the set of vertices covered by some maximum matching of $G$.
--   3. Sort the vertices of $G$ by a linear order (in §5c: by decreasing weight). Two matching sets are compared **lexicographically**: $L$ is larger than $H$ if the first vertex, in the sorted order, at which they differ belongs to $L$. The **lexicographically largest matching set** $L$ is a matching set that is larger than every other matching set.
--
--   These are the objects of Lemma 4, which reduces the vertex-weighted matching problem to finding the lexicographically largest matching set.
--
--   **Formalization Note** Matchings are `Finset (Sym2 V)` whose members are edges of `G` (`IsMatchingEdges`, `IsMaximumMatching`); `coveredVertices M` is the set of vertices in some edge of `M`. The sorted order is the `LinearOrder` on `V`; `IsLexLargestMatchingSet G L` says that for every matching set $H \neq L$ some $v \in L \setminus H$ has $u \in L \iff u \in H$ for every $u < v$.
-- source:
--   Mulmuley, Vazirani, Vazirani, Matching is as easy as matrix inversion, Combinatorica 7 (1987), p. 110, §5c (definition of a matching set and of the lexicographic comparison, before Lemma 4)

import Mathlib

namespace MulmuleyVV.Matching

/-- `M`, a finite set of unordered pairs, is a matching of `G`: every pair in `M` is an edge of
`G`, and no vertex lies in two distinct pairs of `M` (MVV 1987, §5c, p. 110). -/
def IsMatchingEdges {V : Type*} (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ v : V, ∀ e ∈ M, ∀ e' ∈ M, v ∈ e → v ∈ e' → e = e'

/-- `M` is a maximum matching of `G`: a matching of largest cardinality. -/
def IsMaximumMatching {V : Type*} (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  IsMatchingEdges G M ∧ ∀ M' : Finset (Sym2 V), IsMatchingEdges G M' → M'.card ≤ M.card

/-- The set of vertices covered by the edges of `M`. -/
noncomputable def coveredVertices {V : Type*} [Fintype V] (M : Finset (Sym2 V)) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ e ∈ M, v ∈ e)

/-- `X ⊆ V` is a matching set of `G`: the set of vertices covered by some maximum matching
(MVV 1987, §5c, p. 110). -/
def IsMatchingSet {V : Type*} [Fintype V] (G : SimpleGraph V) (X : Finset V) : Prop :=
  ∃ M : Finset (Sym2 V), IsMaximumMatching G M ∧ coveredVertices M = X

/-- `L` is the lexicographically largest matching set of `G` for the order on `V` (the vertices
sorted by decreasing weight, earliest = heaviest): `L` is a matching set, and for every other
matching set `H`, the first vertex (in the order of `V`) at which `L` and `H` differ lies in `L`
(MVV 1987, §5c, p. 110). -/
def IsLexLargestMatchingSet {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (L : Finset V) : Prop :=
  IsMatchingSet G L ∧ ∀ H : Finset V, IsMatchingSet G H → H ≠ L →
    ∃ v ∈ L, v ∉ H ∧ ∀ u : V, u < v → (u ∈ L ↔ u ∈ H)

end MulmuleyVV.Matching


