-- Prove2me | Definitions.Def_MatousekLP_Integrality_BipartiteGraph
-- name    : MatousekLP_Integrality_BipartiteGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T10:16:31.787725+00:00
-- url     : https://prove2.me/theorems/7de7c5c8-c971-4fe6-96fd-d968db38105f
-- title:
--   Bipartite graphs, bipartitions, matchings and neighbourhoods
-- statement:
--   Let $G = (V, E)$ be a simple graph on a finite vertex set $V$.
--
--   1. A pair of vertex sets $X, Y \subseteq V$ is a **bipartition** of $G$ if $X \cap Y = \emptyset$, $X \cup Y = V$ (written $V = X \,\dot\cup\, Y$), and every edge of $G$ connects a vertex of $X$ to a vertex of $Y$. The graph $G$ is **bipartite** if it has at least one bipartition.
--   2. A **matching** in $G$ is a set $M \subseteq E$ of edges with the property that each vertex is incident to at most one edge of $M$:
--   $$
--   \bigl|\{e \in M : v \in e\}\bigr| \le 1 \qquad \text{for every } v \in V .
--   $$
--   3. For sets $Y, T \subseteq V$, the **neighbourhood of $T$ in $Y$** is
--   $$
--   N(T) = \{ w \in Y : \{v, w\} \in E \text{ for some } v \in T \}.
--   $$
--
--   These are the graph notions of Sections 3.2 and 8.2 of Matoušek–Gärtner: the bipartite graph of the job-assignment problem, the matchings whose maximum size König's theorem computes, and the neighbourhood used in Hall's condition. Vertex covers (a set $C \subseteq V$ meeting every edge) are taken from Mathlib's `SimpleGraph.IsVertexCover`, which is literally the book's definition.
--
--   **Formalization Note** Edges are unordered pairs (`Sym2 V`); a matching is a `Finset (Sym2 V)` all of whose elements are edges of $G$, so its size is `M.card`. The neighbourhood is a `Finset` filtered from $Y$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 33 (§3.2, bipartite graph V = X ∪̇ Y), p. 143 (§8.2, matching), p. 144 (Theorem 8.2.1, neighbourhood N(T))

import Mathlib

namespace MatousekLP.Integrality

/-- `X, Y` is a bipartition of the simple graph `G` on the finite vertex type `V`:
`X` and `Y` are disjoint, together they contain every vertex, and every edge of `G`
joins a vertex of `X` to a vertex of `Y` (Matoušek–Gärtner, p. 33 and p. 143:
`V = X ∪̇ Y`, "each edge connects a vertex of X to a vertex of Y"). -/
def IsBipartition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X Y : Finset V) : Prop :=
  Disjoint X Y ∧ X ∪ Y = Finset.univ ∧
    ∀ u v : V, G.Adj u v → (u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)

/-- `G` is bipartite: it admits some bipartition `V = X ∪̇ Y`. -/
def IsBipartite {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ X Y : Finset V, IsBipartition G X Y

/-- A matching of `G` (p. 143): a set `M` of edges of `G` such that each vertex is
incident to at most one edge of `M`. Edges are unordered pairs `Sym2 V`. -/
def IsMatching {V : Type*} [DecidableEq V] (G : SimpleGraph V) (M : Finset (Sym2 V)) :
    Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ v : V, (M.filter (fun e => v ∈ e)).card ≤ 1

/-- The neighbourhood `N(T) = {w ∈ Y : {v, w} ∈ E for some v ∈ T}` of a set `T` of
vertices, taken inside the class `Y` (Theorem 8.2.1, p. 144). -/
def neighborhood {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (Y T : Finset V) :
    Finset V :=
  Y.filter (fun w => ∃ v ∈ T, G.Adj v w)

end MatousekLP.Integrality


