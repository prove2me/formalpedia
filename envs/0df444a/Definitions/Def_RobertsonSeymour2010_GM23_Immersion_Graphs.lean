-- Prove2me | Definitions.Def_RobertsonSeymour2010_GM23_Immersion_Graphs
-- name    : RobertsonSeymour2010_GM23_Immersion_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:44.622074+00:00
-- url     : https://prove2.me/theorems/2cf4cb21-0f96-4ac5-84e9-ac96d4e7f9d6
-- title:
--   Finite graphs with loops and parallel edges, paths, circuits and immersion (p. 1); hypergraphs and collapse (p. 1); transpose (p. 2)
-- statement:
--   This module fixes the objects of Section 1 of Robertson and Seymour's *Graph Minors XXIII*.
--
--   1. **Graphs.** A graph $G$ has a vertex set $V(G)$ and an edge set $E(G)$; every edge $e$ has an unordered pair of ends $\{u,v\}$, and $e$ is a **loop** at $v$ when $u=v$. Loops and parallel edges (several edges with the same ends) are allowed. $G$ is **loopless** if every edge has two distinct ends. All graphs are finite.
--
--   2. **Walks, paths, circuits.** A walk of $G$ is a vertex sequence $v_0,\dots,v_n$ together with an edge sequence $e_0,\dots,e_{n-1}$ such that $e_r$ has ends $v_r, v_{r+1}$. A **path with ends $a,b$** is a walk whose vertices are pairwise distinct and whose first and last vertices are $a$ and $b$ (in either order); a path has at least one vertex. A **circuit** is a closed walk ($v_0=v_n$) with at least one edge, pairwise distinct edges, and pairwise distinct vertices $v_1,\dots,v_n$. A single loop and a pair of parallel edges are circuits. The vertex set $V(P)$ and edge set $E(P)$ of a path or circuit $P$ are the vertices and edges it lists.
--
--   3. **Immersion.** For graphs $H, G$, an **immersion of $H$ in $G$** is a map $\alpha$ on $V(H)\cup E(H)$ such that
--      - $\alpha(v)\in V(G)$ for all $v\in V(H)$, and $\alpha(u)\ne\alpha(v)$ for distinct $u,v$;
--      - for each edge $e$ of $H$: if $e$ has distinct ends $u,v$, then $\alpha(e)$ is a path of $G$ with ends $\alpha(u),\alpha(v)$; if $e$ is a loop at $v$, then $\alpha(e)$ is a circuit of $G$ with $\alpha(v)\in V(\alpha(e))$;
--      - for distinct $e,f\in E(H)$, $E(\alpha(e))\cap E(\alpha(f))=\emptyset$.
--
--      The paths and circuits are edge-disjoint, not vertex-disjoint, and a path may pass through the image of a vertex that is not one of its ends.
--
--   4. **Hypergraphs.** A hypergraph $G$ has a finite vertex set $V(G)$, a finite edge set $E(G)$ and an incidence relation between them; $V(e)$ is the set of vertices incident with the edge $e$ (its ends). An edge may have any number of ends, including none.
--
--   5. **Collapse.** Let $K_{V}$ denote the complete graph on the vertex set $V$. For hypergraphs $H, G$, a **collapse of $G$ to $H$** is a map $\eta$ on $V(H)\cup E(H)$ such that
--      1. $\eta(v)$ is a non-null connected subgraph of $K_{V(G)}$ for each $v\in V(H)$, and $\eta(u),\eta(v)$ are vertex-disjoint for distinct $u,v$;
--      2. $\eta(e)\in E(G)$ for each $e\in E(H)$, and $\eta(e)\ne\eta(f)$ for distinct $e,f$;
--      3. if $e$ is incident in $H$ with $v$, then $\eta(e)$ is incident in $G$ with some vertex of $\eta(v)$;
--      4. for each $v\in V(H)$ and each edge of $\eta(v)$ with ends $x,y$, some edge of $G$ is incident with both $x$ and $y$.
--
--      A collapse of $G$ to $H$ maps $H$ into $G$. The edge in (iv) may itself be one of the $\eta(e)$.
--
--   6. **Transpose.** The transpose $G'$ of a graph $G$ is the hypergraph with $V(G')=E(G)$ and $E(G')=V(G)$, with the same incidence relation as $G$.
--
--   These are the objects in which the immersion theorem 1.1 and the hypergraph theorems 1.2–1.6 are stated.
--
--   **Formalization Note.** A graph is a structure `Graph V E` with `ends : E → Sym2 V`; a walk stores its vertex and edge lists. "Path with ends $a,b$" accepts either orientation of the list, since the paper's ends are unordered. An immersion is the structure `GraphImmersion H G` with components `vmap : V(H) → V(G)` and `emap : E(H) → walks of G`. A hypergraph is `Hypergraph V E` with `inc : E → V → Prop`. $K_{V(G)}$ is Mathlib's complete simple graph `⊤ : SimpleGraph V(G)`, and $\eta(v)$ is a `Subgraph` of it; Mathlib's `Subgraph.Connected` includes non-emptiness. A collapse is the structure `Collapse G H` (a collapse *of $G$ to $H$*). The transpose is defined for every graph; the theorems that use it assume looplessness, as the paper does. Finiteness is imposed by `Fintype` hypotheses in the theorems.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), Section 1, pp. 1–2

import Mathlib

namespace RobertsonSeymour2010.GM23.Immersion

/-- A graph with vertex type `V` and edge type `E` (Robertson–Seymour, Graph Minors XXIII, p. 1).
Each edge has an unordered pair of ends; `ends e = s(v, v)` means that `e` is a loop at `v`.
Loops and parallel edges are allowed. Finiteness ("all graphs in this paper are finite") is imposed
by `Fintype` binders in the theorems. -/
structure Graph (V E : Type) where
  /-- The unordered pair of ends of each edge. -/
  ends : E → Sym2 V

/-- An edge is a loop if its two ends coincide. -/
def Graph.IsLoop {V E : Type} (G : Graph V E) (e : E) : Prop := (G.ends e).IsDiag

/-- A graph is loopless if every edge has two distinct ends (p. 2). -/
def Graph.Loopless {V E : Type} (G : Graph V E) : Prop := ∀ e, ¬ G.IsLoop e

/-- A walk in `G`: a vertex list `vs = [v₀, …, vₙ]` and an edge list `es = [e₀, …, eₙ₋₁]`
such that each `eᵣ` has ends `vᵣ, vᵣ₊₁`. The subgraph it traces has vertex set the entries of `vs`
and edge set the entries of `es`. -/
structure Graph.Walk {V E : Type} (G : Graph V E) where
  /-- The vertices, in order. -/
  vs : List V
  /-- The edges, in order. -/
  es : List E
  /-- There is one more vertex than edges. -/
  length_eq : vs.length = es.length + 1
  /-- The `r`-th edge has ends the `r`-th and the `(r+1)`-th vertex. -/
  adj : ∀ r : ℕ, ∀ e : E, es[r]? = some e →
    ∃ a b : V, vs[r]? = some a ∧ vs[r + 1]? = some b ∧ G.ends e = s(a, b)

/-- A walk is a path with ends `a, b` (p. 1: "Paths have at least one vertex, and no repeated
vertices"): its vertices are pairwise distinct and its first and last vertices are `a` and `b`, in
either order (the ends of a path are unordered). -/
def Graph.Walk.IsPathWithEnds {V E : Type} {G : Graph V E} (W : G.Walk) (a b : V) : Prop :=
  W.vs.Nodup ∧
    ((W.vs.head? = some a ∧ W.vs.getLast? = some b) ∨
      (W.vs.head? = some b ∧ W.vs.getLast? = some a))

/-- A walk is a circuit (p. 1: "Circuits have at least one edge and no repeated vertices"): it has
at least one edge, it is closed, its edges are pairwise distinct and its vertices other than the
repeated first/last one are pairwise distinct. A single loop and two parallel edges are circuits;
traversing one edge forth and back is not. -/
def Graph.Walk.IsCircuit {V E : Type} {G : Graph V E} (W : G.Walk) : Prop :=
  W.es ≠ [] ∧ W.es.Nodup ∧ W.vs.head? = W.vs.getLast? ∧ W.vs.tail.Nodup

/-- An immersion of `H` in `G` (p. 1): an injective map `vmap` on vertices and, for every edge `e`
of `H`, a walk `emap e` of `G` such that
* if `e` has distinct ends `u, v`, then `emap e` is a path of `G` with ends `vmap u, vmap v`;
* if `e` is a loop at `v`, then `emap e` is a circuit of `G` through `vmap v`;
* for distinct edges `e ≠ f` of `H`, the walks `emap e` and `emap f` have no common edge.
Vertices may be shared between different `emap e` (this is not strong immersion). -/
structure GraphImmersion {VH EH VG EG : Type} (H : Graph VH EH) (G : Graph VG EG) where
  /-- Image of each vertex of `H`. -/
  vmap : VH → VG
  /-- Image of each edge of `H`: a walk of `G`. -/
  emap : EH → G.Walk
  /-- Distinct vertices have distinct images. -/
  vmap_injective : Function.Injective vmap
  /-- A non-loop edge with ends `u, v` goes to a path of `G` with ends `vmap u, vmap v`. -/
  isPath : ∀ (e : EH) (u v : VH), H.ends e = s(u, v) → u ≠ v →
    (emap e).IsPathWithEnds (vmap u) (vmap v)
  /-- A loop at `v` goes to a circuit of `G` containing `vmap v`. -/
  isCircuit : ∀ (e : EH) (v : VH), H.ends e = s(v, v) →
    (emap e).IsCircuit ∧ vmap v ∈ (emap e).vs
  /-- Images of distinct edges are edge-disjoint. -/
  edge_disjoint : ∀ e f : EH, e ≠ f → ∀ x ∈ (emap e).es, x ∉ (emap f).es

/-- A hypergraph (p. 1): vertices `V`, edges `E` and an incidence relation between them.
`inc e v` means that edge `e` is incident with vertex `v`. An edge may have any number of ends,
including none. Finiteness is imposed by `Fintype` binders in the theorems. -/
structure Hypergraph (V E : Type) where
  /-- Incidence: `inc e v` iff `v` is an end of `e`. -/
  inc : E → V → Prop

/-- The set `V(e)` of ends of an edge `e`. -/
def Hypergraph.endSet {V E : Type} (G : Hypergraph V E) (e : E) : Set V := {v | G.inc e v}

/-- A collapse of `G` to `H` (p. 1) — note that it maps `H` into `G`. `vmap v` is a subgraph of the
complete graph `K_{V(G)}` (here `(⊤ : SimpleGraph VG).Subgraph`) and `emap` maps edges of `H` to
edges of `G`, such that
(i) each `vmap v` is non-null and connected, and `vmap u`, `vmap v` are vertex-disjoint for `u ≠ v`;
(ii) `emap` is injective;
(iii) if `e` is incident in `H` with `v`, then `emap e` is incident in `G` with a vertex of `vmap v`;
(iv) for each `v` and each edge of `vmap v` with ends `x, y`, some edge of `G` is incident with both
`x` and `y` (that edge may lie in the image of `emap`). -/
structure Collapse {VG EG VH EH : Type} (G : Hypergraph VG EG) (H : Hypergraph VH EH) where
  /-- (i) Image of each vertex of `H`: a subgraph of `K_{V(G)}`. -/
  vmap : VH → (⊤ : SimpleGraph VG).Subgraph
  /-- (ii) Image of each edge of `H`: an edge of `G`. -/
  emap : EH → EG
  /-- (i) Each `vmap v` is non-null and connected (Mathlib's `Subgraph.Connected` includes
  nonemptiness). -/
  connected : ∀ v : VH, (vmap v).Connected
  /-- (i) Images of distinct vertices are disjoint. -/
  disjoint : ∀ u v : VH, u ≠ v → Disjoint (vmap u).verts (vmap v).verts
  /-- (ii) Distinct edges have distinct images. -/
  emap_injective : Function.Injective emap
  /-- (iii) Incidences are preserved up to the branch set. -/
  inc : ∀ (e : EH) (v : VH), H.inc e v → ∃ x ∈ (vmap v).verts, G.inc (emap e) x
  /-- (iv) Every edge `xy` of `vmap v` is covered by an edge of `G` incident with `x` and `y`. -/
  covered : ∀ (v : VH) (x y : VG), (vmap v).Adj x y → ∃ e : EG, G.inc e x ∧ G.inc e y

/-- The transpose of a graph `G` (p. 2): the hypergraph with vertex set `E(G)`, edge set `V(G)`,
and the same incidence relation as `G` (the edge `v` of the transpose is incident with the vertex `e`
iff `v` is an end of `e` in `G`). The paper defines it for loopless graphs; the definition makes sense
for all graphs, and the theorems carry the looplessness hypotheses. -/
def Graph.transpose {V E : Type} (G : Graph V E) : Hypergraph E V where
  inc v e := v ∈ G.ends e

end RobertsonSeymour2010.GM23.Immersion


