-- Prove2me | Definitions.Def_PathsTreesFlowers_Duality_Basic
-- name    : PathsTreesFlowers_Duality_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:56:40.208996+00:00
-- url     : https://prove2.me/theorems/9493d7fa-5481-406b-b0ec-7688765e387d
-- title:
--   §3.0–§4.6, pp. 452–456 — exposed vertices, maximum matchings, subgraphs, alternating paths and circuits, stems, blossoms, flowers, alternating / planted / Hungarian trees
-- statement:
--   The graph-level notions of Edmonds' §3 and §4, for a finite graph $G$ with vertex set $V$ and edge set $E$ in which every edge meets exactly two distinct vertices (parallel edges allowed), and a matching $M \subseteq E$ (no two edges of $M$ meet the same vertex).
--
--   1. **Exposed vertex** (3.4). A vertex $v$ is *exposed* for $M$ if it meets no edge of $M$.
--   2. **Maximum matching** (3.0). "Maximum" refers to cardinality: $M$ is a maximum matching if $|M'| \le |M|$ for every matching $M'$ of $G$.
--   3. **Subgraphs** (3.0, 3.2). A subgraph $H$ is a set of vertices together with a set of edges whose end-points lie in it. A matching *of* $H$ is a matching of $G$ all of whose edges are edges of $H$; a maximum matching of $H$ is one of largest cardinality among these. The *induced* subgraph $U^+$ on a vertex set $U$ has all edges of $G$ with both end-points in $U$. $G - H$ is the induced subgraph on the vertices not in $H$. A subgraph is *connected* if it is non-empty and any two of its vertices are linked by a chain of its edges.
--   4. **Paths and circuits** (3.3). A (simple) path is a sequence of pairwise distinct vertices $v_0, \dots, v_m$ and edges $e_0, \dots, e_{m-1}$ with $e_i$ joining $v_i$ and $v_{i+1}$; $m = 0$ is the single vertex, joining itself to itself. A circuit is a cyclic sequence of $m \ge 2$ pairwise distinct vertices and $m$ pairwise distinct edges, $e_i$ joining $v_i$ and $v_{(i+1) \bmod m}$; it is *odd* when $m$ is odd.
--   5. **Alternating path** (3.4). A path whose consecutive edges alternate between $M$ and $\bar M$, the edges of $G$ not in $M$.
--   6. **Stem** (4.3). Either an exposed vertex, or an alternating path with an exposed vertex (the *root*) at one end and an edge of $M$ at the other end, whose end-point there is the *tip*.
--   7. **Blossom and flower** (4.5). A blossom with base $b$ is an odd circuit $B$ such that $M \cap B$ is a maximum matching of $B$ and $b$ is a vertex of $B$ exposed for $M \cap B$. A flower is a blossom together with a stem whose tip is $b$, the two having only $b$ in common.
--   8. **Alternating tree** (4.0, 4.1). A tree — a connected graph with one more vertex than edges, 4.0 (3) — whose vertices are split into *inner* and *outer* vertices so that every edge joins an inner vertex to an outer vertex and every inner vertex meets exactly two edges of the tree.
--   9. **Planted tree** (4.3). An alternating tree $J$ with a vertex $r$ (its *root*) such that $M \cap J$ is a maximum matching of $J$, $r$ is exposed for $M \cap J$, and $r$ is also exposed for $M$.
--   10. **Hungarian tree** (4.6). An alternating tree whose outer vertices are joined by edges of $G$ only to its inner vertices.
--
--   These are the objects in terms of which Edmonds' blossom algorithm and the proof of the matching-duality theorem are phrased.
--
--   **Formalization Note** Paths and circuits are lists of vertices and edges rather than subgraphs; a path and its reversal are the same subgraph. The inner/outer split of an alternating tree is part of its data, as in the paper. The root of a planted tree is an argument; that it is unique (4.2) is a theorem, not part of the definition.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), pp. 452–456, 3.0, 3.2, 3.3, 3.4, 4.0, 4.1, 4.3, 4.5, 4.6

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace PathsTreesFlowers.Duality

open EdmondsMatching65.Polyhedron (IsMatching)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- 3.4, p. 453: for the pair `(G, M)`, a vertex `v` is *exposed* if it meets no edge of `M`. -/
def IsExposed (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) (v : V) : Prop :=
  ∀ e ∈ M, v ∉ G.ends e

instance (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) :
    DecidablePred (IsExposed G M) := fun v => by
  unfold IsExposed; infer_instance

/-- A *maximum* matching (3.0, p. 452: "maximum ... will refer to cardinality"): a matching of `G`
with at least as many edges as every matching of `G`. -/
def IsMaxMatching (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) : Prop :=
  IsMatching G M ∧ ∀ M' : Finset E, IsMatching G M' → M'.card ≤ M.card

/-- 3.0, p. 452: a *subgraph* of `G`, given by a set of vertices and a set of edges of `G` whose
end-points lie in that vertex set (with the incidences of `G`). -/
structure Sub (G : EdmondsMatching65.Polyhedron.Graph V E) where
  /-- the vertices of the subgraph -/
  verts : Finset V
  /-- the edges of the subgraph -/
  edges : Finset E
  /-- every end-point of an edge of the subgraph is a vertex of the subgraph -/
  edges_sub : ∀ e ∈ edges, G.ends e ∈ verts.sym2

/-- A *maximum matching of a part of `G` with edge set `F`*: a matching of `G` using only edges of
`F`, with at least as many edges as every matching of `G` using only edges of `F`. A matching of a
subgraph is a matching of `G` all of whose edges lie in the subgraph. -/
def IsMaxMatchingOn (G : EdmondsMatching65.Polyhedron.Graph V E) (F M : Finset E) : Prop :=
  M ⊆ F ∧ IsMatching G M ∧ ∀ M' : Finset E, M' ⊆ F → IsMatching G M' → M'.card ≤ M.card

/-- A matching of the subgraph `H` (a matching of `G` using only edges of `H`). -/
def IsMatchingIn (G : EdmondsMatching65.Polyhedron.Graph V E) (H : Sub G) (M : Finset E) : Prop :=
  M ⊆ H.edges ∧ IsMatching G M

/-- A maximum matching of the subgraph `H`. -/
def IsMaxMatchingIn (G : EdmondsMatching65.Polyhedron.Graph V E) (H : Sub G) (M : Finset E) :
    Prop :=
  IsMaxMatchingOn G H.edges M

/-- The edges of `G` with both end-points in `U`. -/
def edgesWithin (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) : Finset E :=
  Finset.univ.filter (fun e => G.ends e ∈ U.sym2)

/-- The induced subgraph on `U`: the vertices of `U` and all edges of `G` with both end-points in
`U`. For `U` the vertex set of `H` this is `H⁺ = G − (G − H)` (4.9, p. 456). -/
def induced (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) : Sub G where
  verts := U
  edges := edgesWithin G U
  edges_sub := fun _ he => (Finset.mem_filter.1 he).2

/-- 3.2, p. 452: `G − H`, the subgraph of `G` consisting of the vertices of `G` not in `H` and
the edges of `G` not meeting vertices of `H`. -/
def deleteSub (G : EdmondsMatching65.Polyhedron.Graph V E) (H : Sub G) : Sub G :=
  induced G (Finset.univ \ H.verts)

/-- The vertices of `U` that meet no edge of `M` lying inside `U`: the vertices left exposed in
the induced subgraph on `U` by the matching `M ∩ U⁺`. -/
def exposedIn (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) (M : Finset E) :
    Finset V :=
  U.filter (fun v => ∀ e ∈ M, G.ends e ∈ U.sym2 → v ∉ G.ends e)

/-- 3.0, p. 452: a subgraph is *connected* if it is non-empty and any two of its vertices are
linked by a chain of edges of the subgraph. -/
def IsConnectedSub (G : EdmondsMatching65.Polyhedron.Graph V E) (H : Sub G) : Prop :=
  H.verts.Nonempty ∧ ∀ u ∈ H.verts, ∀ w ∈ H.verts,
    Relation.ReflTransGen (fun a b => ∃ e ∈ H.edges, G.ends e = s(a, b)) u w

/-- 3.3, p. 453: a (simple) *path*, as the list of its vertices `vs = [v₀, …, vₘ]` (pairwise
distinct) and the list of its edges `es = [e₀, …, e_{m-1}]`, where `eᵢ` joins `vᵢ` and `vᵢ₊₁`.
`m = 0` is the single-vertex path. The path joins `v₀` and `vₘ`. -/
def IsPath (G : EdmondsMatching65.Polyhedron.Graph V E) (vs : List V) (es : List E) : Prop :=
  vs.Nodup ∧ vs.length = es.length + 1 ∧
    es.map G.ends = List.zipWith (fun a b => s(a, b)) vs vs.tail

/-- 3.3, p. 453: a *circuit*, as the cyclic list of its `m ≥ 2` pairwise distinct vertices
`vs = [v₀, …, v_{m-1}]` and of its `m` pairwise distinct edges `es`, where `eᵢ` joins `vᵢ` and
`v_{(i+1) mod m}`. It is *odd* when `m` is odd. -/
def IsCircuit (G : EdmondsMatching65.Polyhedron.Graph V E) (vs : List V) (es : List E) : Prop :=
  vs.Nodup ∧ es.Nodup ∧ 2 ≤ vs.length ∧ vs.length = es.length ∧
    es.map G.ends = List.zipWith (fun a b => s(a, b)) vs (vs.rotate 1)

/-- 3.4, p. 453: an *alternating path* in `(G, M)`: a path whose consecutive edges alternate
between `M` and `M̄` (the edges of `G` not in `M`). -/
def IsAlternatingPath (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) (vs : List V)
    (es : List E) : Prop :=
  IsPath G vs es ∧ es.IsChain (fun e f => (e ∈ M ↔ f ∉ M))

/-- 4.3, p. 455: a *stem* in `(G, M)`: either an exposed vertex, or an alternating path with an
exposed vertex at one end (the *root*, `vs.head`) and a matching edge at the other end (whose
end-point is the *tip*, `vs.getLast`). -/
def IsStem (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) (vs : List V)
    (es : List E) : Prop :=
  IsAlternatingPath G M vs es ∧ (∀ r ∈ vs.head?, IsExposed G M r) ∧ (∀ e ∈ es.getLast?, e ∈ M)

/-- 4.5, p. 455: a *blossom* in `(G, M)` with base `b`: an odd circuit `B = (vs, es)` of `G` for
which `M ∩ B` is a maximum matching of `B` (among matchings using edges of `B` only) and `b` is a
vertex of `B` exposed for `M ∩ B`. -/
def IsBlossom (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) (vs : List V)
    (es : List E) (b : V) : Prop :=
  IsCircuit G vs es ∧ Odd vs.length ∧ IsMaxMatchingOn G es.toFinset (M ∩ es.toFinset) ∧
    b ∈ vs ∧ ∀ e ∈ M ∩ es.toFinset, b ∉ G.ends e

/-- 4.5, p. 455: a *flower* in `(G, M)`: a blossom `(vs, es)` with base `b` and a stem
`(svs, ses)` whose tip is `b`, the two intersecting only at `b`. -/
def IsFlower (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) (vs : List V)
    (es : List E) (b : V) (svs : List V) (ses : List E) : Prop :=
  IsBlossom G M vs es b ∧ IsStem G M svs ses ∧ svs.getLast? = some b ∧ ∀ v ∈ svs, v ∈ vs → v = b

/-- 4.0–4.1, p. 454: an *alternating tree* `J` of `G`, given with its split into *inner* and
*outer* vertices. It is a tree in the sense of 4.0 (3) — a connected graph with one more vertex
than edges — each of whose edges joins an inner vertex to an outer vertex, and each inner vertex
meets exactly two edges of `J`. -/
structure AltTree (G : EdmondsMatching65.Polyhedron.Graph V E) where
  /-- the inner vertices -/
  inner : Finset V
  /-- the outer vertices -/
  outer : Finset V
  /-- the edges of the tree -/
  edges : Finset E
  disjoint : Disjoint inner outer
  /-- every edge of `J` joins an inner vertex to an outer vertex -/
  edge_ends : ∀ e ∈ edges, ∃ u ∈ inner, ∃ w ∈ outer, G.ends e = s(u, w)
  /-- every inner vertex meets exactly two edges of `J` -/
  inner_deg : ∀ u ∈ inner, (edges.filter (fun e => u ∈ G.ends e)).card = 2
  /-- `J` is connected: non-empty, and any two vertices linked by edges of `J` -/
  connected : (inner ∪ outer).Nonempty ∧ ∀ u ∈ inner ∪ outer, ∀ w ∈ inner ∪ outer,
    Relation.ReflTransGen (fun a b => ∃ e ∈ edges, G.ends e = s(a, b)) u w
  /-- one more vertex than edges -/
  card_verts : (inner ∪ outer).card = edges.card + 1

/-- The vertex set of an alternating tree. -/
def AltTree.verts {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) : Finset V :=
  J.inner ∪ J.outer

/-- An alternating tree as a subgraph of `G`. -/
def AltTree.toSub {G : EdmondsMatching65.Polyhedron.Graph V E} (J : AltTree G) : Sub G where
  verts := J.inner ∪ J.outer
  edges := J.edges
  edges_sub := fun e he => by
    obtain ⟨u, hu, w, hw, h⟩ := J.edge_ends e he
    rw [h, Finset.mk_mem_sym2_iff]
    exact ⟨Finset.mem_union_left _ hu, Finset.mem_union_right _ hw⟩

/-- 4.3, p. 454–455: `J` is a *planted tree* for the matching `M`, with *root* `r`: an alternating
tree such that `M ∩ J` is a maximum matching of `J`, and the vertex `r` of `J` which is exposed for
`M ∩ J` is also exposed for `M`. -/
def IsPlantedTree (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) (J : AltTree G)
    (r : V) : Prop :=
  IsMaxMatchingOn G J.edges (M ∩ J.edges) ∧ r ∈ J.verts ∧
    (∀ e ∈ M ∩ J.edges, r ∉ G.ends e) ∧ IsExposed G M r

/-- 4.6, p. 456: a *Hungarian tree* in `G`: an alternating tree whose outer vertices are joined by
edges of `G` only to its inner vertices. -/
def IsHungarianTree (G : EdmondsMatching65.Polyhedron.Graph V E) (J : AltTree G) : Prop :=
  ∀ (e : E) (u : V), u ∈ J.outer → u ∈ G.ends e → ∃ w ∈ J.inner, G.ends e = s(u, w)

end PathsTreesFlowers.Duality


