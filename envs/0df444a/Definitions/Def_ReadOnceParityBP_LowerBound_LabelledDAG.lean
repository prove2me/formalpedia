-- Prove2me | Definitions.Def_ReadOnceParityBP_LowerBound_LabelledDAG
-- name    : ReadOnceParityBP_LowerBound_LabelledDAG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:24:05.161078+00:00
-- url     : https://prove2.me/theorems/36c1053d-d546-42a0-9462-1d1c78172ae5
-- title:
--   Finite labelled acyclic multigraphs and edge paths
-- statement:
--   A labelled graph G has finite numbered vertex and edge sets V and E, independently specified terminals s and t, endpoint maps, and a label on every edge. Its general multigraph is the published CombOpt.ShortestPath.Digraph, which has only tail and head maps. Walks are lists of edges with matching endpoints; parallel edges remain distinct. Acyclicity means every closed walk is empty.
--
--   $$\operatorname{Paths}(G)=\{p:p\text{ is an edge walk from }s\text{ to }t\},\qquad |G|=|E|.$$
--
--   This is the common graph substrate for both program models. It imposes no layering or degree constraint, allows dead vertices and edges, and includes the empty walk when s=t. Finiteness of the path set is a separate theorem, not a stored certificate.
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Definitions 1.1 and 2.1, pp.2–3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- A walk in a finite directed multigraph whose edges are `Fin m`, with endpoint maps
`src`, `tgt` into the vertex set `Fin k`: `IsWalk src tgt p u v` says that the list of edges
`p` is a directed walk from `u` to `v` (each edge leaves the vertex the previous one entered).
The empty list is the walk from a vertex to itself. Parallel edges are distinct list entries,
so they give distinct walks. -/
def IsWalk {m k : ℕ} (src tgt : Fin m → Fin k) : List (Fin m) → Fin k → Fin k → Prop
  | [], u, v => u = v
  | e :: p, u, v => src e = u ∧ IsWalk src tgt p (tgt e) v

/-- Volk, Definitions 1.1 and 2.1 (pp. 2–3): the common graph substrate of read-once parity
branching programs and algebraic branching programs. A finite directed acyclic multigraph,
with vertices `Fin numV` and edges `Fin numE` (so parallel edges and arbitrary in- and
out-degrees are allowed, and no layering is imposed), a source `s`, a target `t`, and an
edge label from the type `L`. Acyclicity: the only closed walk is the empty one. -/
structure LabelledDAG (L : Type) where
  numV : ℕ
  numE : ℕ
  graph : CombOpt.ShortestPath.Digraph (Fin numV) (Fin numE)
  label : Fin numE → L
  s : Fin numV
  t : Fin numV
  acyclic : ∀ (v : Fin numV) (p : List (Fin numE)), IsWalk graph.tail graph.head p v v → p = []

namespace LabelledDAG

variable {L : Type}

/-- Tail of an edge, from the published general multigraph substrate. -/
def src (G : LabelledDAG L) : Fin G.numE → Fin G.numV := G.graph.tail

/-- Head of an edge, from the published general multigraph substrate. -/
def tgt (G : LabelledDAG L) : Fin G.numE → Fin G.numV := G.graph.head

/-- The `s → t` paths of the program: the edge lists that are directed walks from `s` to `t`
(in an acyclic graph every walk is a path). -/
def stPaths (G : LabelledDAG L) : Set (List (Fin G.numE)) :=
  {p | IsWalk G.src G.tgt p G.s G.t}

/-- The size of a branching program is its number of edges (Definitions 1.1, 2.1). -/
def size (G : LabelledDAG L) : ℕ := G.numE

end LabelledDAG

end ReadOnceParityBP.LowerBound


