-- Prove2me | Definitions.Def_BipDijoin_BipGraph
-- name    : BipDijoin_BipGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:39.353654+00:00
-- url     : https://prove2.me/theorems/0f3b069a-f1c8-4b88-8681-cd482383ee5a
-- title:
--   Bipartite multigraphs with edge identities, induced subgraphs, deletion and contraction
-- statement:
--   A **bipartite multigraph** $G=(L\uplus R,E)$ is recorded as a finite vertex set $V\subseteq\mathbb N$, a finite set $E\subseteq\mathbb N$ of edge identities, a side map assigning each vertex to $L$ or to $R$, and for every edge $e$ its left end $\ell(e)$ and right end $r(e)$. Read as a digraph, $e$ is the arc $\ell(e)\to r(e)$, so every arc points from $L$ to $R$; parallel edges are distinct identities with the same ends. The graph is **well formed** when every edge joins a left vertex of $V$ to a right vertex of $V$.
--
--   The module also defines, for a well-formed $G$:
--
--   1. $L(G)$ and $R(G)$, the left and right vertices;
--   2. **simplicity** (no two edges with the same ends) and **no isolated vertex** (every vertex is an end of an edge);
--   3. **weak connectivity** (any two vertices are joined in the underlying undirected multigraph, $V\ne\emptyset$) and **2-edge-connectivity** (weakly connected, and still so after deleting any one edge; a one-vertex graph qualifies);
--   4. the **induced subgraph** $G[U]$, the **deletion** $G-U$, and the **contraction** $G/U$ of a vertex set $U$ to a new vertex $x$ placed on a chosen side: edges with both ends in $U$ (loops) are discarded, every other edge keeps its identity and has its ends in $U$ redirected to $x$, and parallel edges are kept.
--
--   These are the graphs of every statement of the mission (§2.1: "Contractions discard loops and retain parallel edges").
--
--   **Formalization Note** Because contraction keeps edge identities, an edge of a quotient is literally an edge of the original graph, and the paper's lifting maps (App. A) are identities on edges.
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), §2.1, p.2 (PDF p.4)

import Mathlib

set_option autoImplicit false

namespace BipDijoin

/-!
# Bipartite multigraphs with edge identities

C. Nalam, T. Saranurak, *Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and
Local Graph Algorithms*, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), §2.1, p.2
(PDF p.4): "Let D = (L ⊎ R, A) be a weakly connected bipartite digraph in which every arc is
directed from L to R … Contractions discard loops and retain parallel edges. We use m and n to
denote the numbers of edges (including parallel edges) and vertices in the graph."

**Formalization Note.**
* A bipartite multigraph is a finite vertex set `V ⊆ ℕ`, a finite set `E ⊆ ℕ` of edge
  identities, a side map `isLeft` (true = left side `L`, false = right side `R`) and two endpoint
  maps: every edge `e` joins its left end `tl e` to its right end `hd e`. As a digraph, `e` is the
  arc `tl e → hd e` (all arcs point from `L` to `R`). Parallel edges are distinct identities with
  the same ends.
* Well-formedness `WF` (ends in `V`, on the right sides) is a separate predicate, so that
  contraction is a plain function. Every statement of the mission assumes `WF` of its input.
* Contracting `U` to a fresh vertex `x` keeps the identities of the surviving edges, drops the
  edges with both ends in `U` (loops) and keeps parallel edges; `x` is placed on side `s`
  (a source end's representative on the left, a sink end's on the right, p.3).
-/

/-- A bipartite multigraph `G = (L ⊎ R, E)` with edge identities: vertices `V`, edge identities
`E`, sides `isLeft`, and the left end `tl e` and right end `hd e` of each edge (§2.1, p.2). -/
structure BipGraph where
  /-- The vertex set. -/
  V : Finset ℕ
  /-- The edge identities. -/
  E : Finset ℕ
  /-- The side of a vertex: `true` for `L`, `false` for `R`. -/
  isLeft : ℕ → Bool
  /-- The left end (tail of the arc) of an edge. -/
  tl : ℕ → ℕ
  /-- The right end (head of the arc) of an edge. -/
  hd : ℕ → ℕ

namespace BipGraph

variable (G : BipGraph)

/-- Well-formedness: every edge joins a left vertex of `V` to a right vertex of `V`. -/
def WF : Prop :=
  ∀ e ∈ G.E, G.tl e ∈ G.V ∧ G.hd e ∈ G.V ∧ G.isLeft (G.tl e) = true ∧ G.isLeft (G.hd e) = false

/-- The left side `L = V ∩ L`. -/
def left : Finset ℕ := G.V.filter (fun v => G.isLeft v = true)

/-- The right side `R = V ∩ R`. -/
def right : Finset ℕ := G.V.filter (fun v => G.isLeft v = false)

/-- `G` is simple: no two distinct edges have the same two ends (§5.2, p.18). -/
def Simple : Prop :=
  ∀ e ∈ G.E, ∀ f ∈ G.E, G.tl e = G.tl f → G.hd e = G.hd f → e = f

/-- `G` has no isolated vertex: every vertex is an end of some edge. -/
def NoIsolated : Prop := ∀ v ∈ G.V, ∃ e ∈ G.E, G.tl e = v ∨ G.hd e = v

/-- Adjacency in the underlying undirected multigraph. -/
def adj (u v : ℕ) : Prop :=
  ∃ e ∈ G.E, (G.tl e = u ∧ G.hd e = v) ∨ (G.tl e = v ∧ G.hd e = u)

/-- Weak connectivity: `V` is nonempty and any two vertices are joined by a path of the underlying
undirected multigraph. -/
def WeaklyConnected : Prop :=
  G.V.Nonempty ∧ ∀ u ∈ G.V, ∀ v ∈ G.V, Relation.ReflTransGen G.adj u v

/-- `G − e`: delete one edge, keep every vertex. -/
def deleteEdge (e : ℕ) : BipGraph := { G with E := G.E.erase e }

/-- 2-edge-connectivity: weakly connected, and still weakly connected after deleting any one edge.
A one-vertex graph is 2-edge-connected (as in the proof of Theorem 4.2, p.14). -/
def TwoEdgeConnected : Prop :=
  G.WeaklyConnected ∧ ∀ e ∈ G.E, (G.deleteEdge e).WeaklyConnected

/-- The induced subgraph `G[U]`: vertices `U`, edges with both ends in `U`. -/
def induced (U : Finset ℕ) : BipGraph :=
  { G with V := U, E := G.E.filter (fun e => G.tl e ∈ U ∧ G.hd e ∈ U) }

/-- `G − U`: delete the vertices of `U` and every edge with an end in `U` (Lemma 6.7, p.31). -/
def deleteVerts (U : Finset ℕ) : BipGraph :=
  { G with V := G.V \ U, E := G.E.filter (fun e => G.tl e ∉ U ∧ G.hd e ∉ U) }

/-- The contraction `G/U` to the vertex `x`, placed on side `s`: the vertices of `U` are replaced
by `x`, edges with both ends in `U` are discarded (loops), every other edge keeps its identity and
has its ends in `U` redirected to `x`; parallel edges are kept (§2.1, p.2). -/
def contract (U : Finset ℕ) (x : ℕ) (s : Bool) : BipGraph where
  V := (G.V \ U) ∪ {x}
  E := G.E.filter (fun e => ¬ (G.tl e ∈ U ∧ G.hd e ∈ U))
  isLeft := Function.update G.isLeft x s
  tl := fun e => if G.tl e ∈ U then x else G.tl e
  hd := fun e => if G.hd e ∈ U then x else G.hd e

end BipGraph

end BipDijoin


