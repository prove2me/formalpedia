-- Prove2me | Definitions.Def_PathsTreesFlowers_Invariance_Basic
-- name    : PathsTreesFlowers_Invariance_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:07.146808+00:00
-- url     : https://prove2.me/theorems/bf0d1369-3f68-42b0-b577-5ca45aa8e5e8
-- title:
--   3.0–4.3, pp. 452–455 — exposed vertices, maximum matchings, subgraphs and induced subgraphs, alternating trees, planted trees
-- statement:
--   Throughout, $G$ is a finite graph in the sense of Edmonds (1965, p. 449): a finite set $V$ of vertices and a finite set $E$ of edges, each edge meeting exactly two distinct vertices; parallel edges are allowed. A *matching* is a set $M \subseteq E$ of edges no two of which meet a common vertex. This file fixes the graph-level notions of Sections 3 and 4.
--
--   1. **Exposed vertex** (3.4). A vertex $v$ is *exposed* for a set of edges $M$ if no edge of $M$ meets $v$.
--   2. **Maximum matching** (3.0). A matching $M$ of $G$ is *maximum* if $|M'| \le |M|$ for every matching $M'$ of $G$; "maximum" always refers to cardinality.
--   3. **Subgraphs** (3.0). A subgraph $H$ of $G$ consists of a vertex set and a set of edges of $G$ whose end-points lie in that vertex set. A matching of $H$ is a matching of $G$ all of whose edges are edges of $H$; it is a *maximum matching of $H$* if it has the largest cardinality among those.
--   4. **Induced subgraphs** (4.9). For $U \subseteq V$, $U^+ = G - (G - U)$ is the subgraph with vertex set $U$ and all edges of $G$ having both end-points in $U$. The graph $G - v$ of 6.6 is the induced subgraph on $V \setminus \{v\}$.
--   5. **Connected subgraphs**. A subgraph is connected if it has a vertex and any two of its vertices are joined by a sequence of its edges.
--   6. **Alternating tree** (4.0 (3), 4.1). An *alternating tree* $J$ in $G$ is a connected subgraph with one more vertex than edges (a tree), together with a split of its vertices into *inner* and *outer* vertices such that every edge of $J$ joins an inner vertex to an outer vertex and every inner vertex meets exactly two edges of $J$.
--   7. **Planted tree** (4.3). A *planted tree* $J = J(M)$ of $G$ for $M$, with *root* $r$, is an alternating tree $J$ such that $M \cap J$ is a maximum matching of $J$, $r$ is a vertex of $J$ exposed for $M \cap J$, and $r$ is also exposed for $M$.
--
--   These are the objects in terms of which the outer and inner vertices of a graph are defined in Section 6.
--
--   **Formalization Note** The graph is the published `EdmondsMatching65.Polyhedron.Graph` (a multigraph without loops); matchings are its `IsMatching`. A subgraph is a vertex set with an edge set, not a new graph type, so a matching of a subgraph is a matching of $G$ contained in the subgraph's edges. The inner/outer split of an alternating tree is part of the data, as in the paper. The root of a planted tree is a parameter; that it is unique and outer follows from 4.2 and is not built into the definition.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), pp. 452–455, 3.0, 3.2, 3.4, 4.0 (definition (3)), 4.1, 4.3; p. 456, 4.9 (U⁺)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic

namespace PathsTreesFlowers.Invariance

open EdmondsMatching65.Polyhedron (IsMatching)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A subgraph of `G` (3.0): a set of vertices and a set of edges of `G` whose end-points lie in
that vertex set. -/
structure Sub (G : EdmondsMatching65.Polyhedron.Graph V E) where
  /-- the vertices of the subgraph -/
  verts : Finset V
  /-- the edges of the subgraph -/
  edges : Finset E
  /-- every end-point of an edge of the subgraph is a vertex of the subgraph -/
  ends_mem : ∀ e ∈ edges, ∀ v ∈ G.ends e, v ∈ verts

/-- `M` is a maximum matching *of the subgraph* `H`: a matching of `G` using only edges of `H`, of
largest cardinality among all such matchings. -/
def IsMaxMatchingIn (G : EdmondsMatching65.Polyhedron.Graph V E) (H : Sub G) (M : Finset E) :
    Prop :=
  M ⊆ H.edges ∧ IsMatching G M ∧
    ∀ M' : Finset E, M' ⊆ H.edges → IsMatching G M' → M'.card ≤ M.card

/-- The subgraph `U⁺ = G − (G − U)` induced on a vertex set `U` (4.9, p. 456): the vertices `U`
and all edges of `G` with both end-points in `U`. "`G − H`" (3.2) is `induced G (univ \ H.verts)`. -/
def induced (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) : Sub G where
  verts := U
  edges := Finset.univ.filter (fun e => G.ends e ∈ U.sym2)
  ends_mem := by
    intro e he v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact Finset.mem_sym2_iff.1 he v hv

/-- Two vertices are adjacent in the subgraph `H`: some edge of `H` joins them. -/
def Sub.Adj {G : EdmondsMatching65.Polyhedron.Graph V E} (H : Sub G) (a b : V) : Prop :=
  ∃ e ∈ H.edges, G.ends e = s(a, b)

/-- A subgraph is *connected*: it has a vertex, and any two of its vertices are joined by a
sequence of edges of the subgraph. -/
def Sub.Connected {G : EdmondsMatching65.Polyhedron.Graph V E} (H : Sub G) : Prop :=
  H.verts.Nonempty ∧ ∀ x ∈ H.verts, ∀ y ∈ H.verts, Relation.ReflTransGen H.Adj x y

/-- An *alternating tree* `J` in `G` (4.0 (3), 4.1, p. 454): a tree — a connected subgraph with
one more vertex than edges — whose vertices are split into *inner* and *outer* vertices so that
each edge of `J` joins an inner vertex to an outer vertex and each inner vertex meets exactly two
edges of `J`. -/
structure AltTree (G : EdmondsMatching65.Polyhedron.Graph V E) extends Sub G where
  /-- the inner vertices -/
  inner : Finset V
  /-- the outer vertices -/
  outer : Finset V
  /-- the vertices of the tree are its inner and its outer vertices -/
  verts_eq : verts = inner ∪ outer
  /-- no vertex is both inner and outer -/
  disjoint_inner_outer : Disjoint inner outer
  /-- each edge joins an inner vertex to an outer vertex -/
  edge_inner_outer : ∀ e ∈ edges, ∃ u ∈ inner, ∃ w ∈ outer, G.ends e = s(u, w)
  /-- each inner vertex meets exactly two edges of the tree -/
  inner_degree : ∀ u ∈ inner, (edges.filter (fun e => u ∈ G.ends e)).card = 2
  /-- a tree is connected … -/
  connected : toSub.Connected
  /-- … with one more vertex than edges (4.0, definition (3)) -/
  card_verts : verts.card = edges.card + 1

/-- A *planted tree* `J = J(M)` of `G` for `M` with root `r` (4.3, pp. 454–455): an alternating
tree such that `M ∩ J` is a maximum matching of `J`, and the vertex `r` of `J` which is exposed
for `M ∩ J` is also exposed for `M`. -/
structure IsPlantedTree (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E)
    (J : AltTree G) (r : V) : Prop where
  /-- `M ∩ J` is a maximum matching of `J` -/
  max_in : IsMaxMatchingIn G J.toSub (M ∩ J.edges)
  /-- the root is a vertex of `J` -/
  root_mem : r ∈ J.verts
  /-- the root is exposed for `M ∩ J` -/
  root_exposed_in : PathsTreesFlowers.Duality.IsExposed G (M ∩ J.edges) r
  /-- the root is also exposed for `M` -/
  root_exposed : PathsTreesFlowers.Duality.IsExposed G M r

end PathsTreesFlowers.Invariance


