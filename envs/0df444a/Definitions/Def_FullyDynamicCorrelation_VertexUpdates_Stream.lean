-- Prove2me | Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Stream
-- name    : FullyDynamicCorrelation_VertexUpdates_Stream
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:50:21.819102+00:00
-- url     : https://prove2.me/theorems/757a72df-b73e-46b1-a0a4-ea085846d136
-- title:
--   Definition 2: the worst-case dynamic vertex insertion–deletion stream
-- statement:
--   Definition 2 (p. 13). An update is `ins v P` (insert vertex $v$ with positive edges to the vertices of $P$ already present) or `del v` (delete $v$ and all its edges); `SGraph.apply` performs it, starting from `SGraph.empty`. `graphAt us t` is the graph after the first $t$ updates of the stream `us`, which is fixed in advance. With the known bound $n$, vertex names are the slots $0,\dots,n-1$: a valid insertion (`Update.Valid`) names a slot $v<n$ not currently in use and positive neighbours among the present vertices, a valid deletion names a present vertex. So at most $n$ vertices are present at any time, a freed slot may be reused by a later (new) vertex, and the number of updates is not bounded by $n$. `ValidStream n us`: every update is valid when it arrives.
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Definition 2 (p. 13), Table 1 (p. 19)

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Graph

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-!
# Definition 2: the worst-case dynamic vertex insertion–deletion model

Braverman et al. (2026), supplied manuscript sha256 07ee1c8f…aab2, Definition 2 (p. 13) and
Table 1 (p. 19).

The graph starts empty. An insertion `ins v P` adds a vertex named `v` with positive edges to
the vertices of `P` that are already present; a deletion `del v` removes `v` and all its edges.
Edges between surviving vertices never change otherwise. With the known bound `n`, vertices are
named by slots `0, …, n − 1`, so at most `n` vertices are present at any time; a slot freed by a
deletion may be reused by a later insertion, which is a new vertex (the number of updates is not
bounded by `n`).
-/

/-- A vertex update. -/
inductive Update where
  /-- insert vertex `v` together with its positive neighbours `P` -/
  | ins (v : ℕ) (P : Finset ℕ)
  /-- delete vertex `v` and all its incident edges -/
  | del (v : ℕ)

namespace SGraph

/-- The empty graph `G⁺ = (∅, ∅)`. -/
def empty : SGraph := ⟨∅, ⊥⟩

/-- The graph after one update (the adjacency lists are updated before the algorithm acts). -/
noncomputable def apply (H : SGraph) : Update → SGraph
  | .ins v P =>
      ⟨insert v H.V,
        H.E ⊔ SimpleGraph.fromEdgeSet ((fun u => s(v, u)) '' ((P ∩ H.V : Finset ℕ) : Set ℕ))⟩
  | .del v => ⟨H.V.erase v, H.E.deleteEdges (H.E.incidenceSet v)⟩

end SGraph

/-- A valid update for the current graph `H` and the vertex bound `n`: an insertion names a
free slot `v < n` and positive neighbours among the present vertices; a deletion names a
present vertex. -/
def Update.Valid (n : ℕ) (H : SGraph) : Update → Prop
  | .ins v P => v < n ∧ v ∉ H.V ∧ P ⊆ H.V
  | .del v => v ∈ H.V

/-- `G^{(t)}`: the graph after the first `t` updates of the stream. -/
noncomputable def graphAt (us : List Update) (t : ℕ) : SGraph :=
  (us.take t).foldl SGraph.apply SGraph.empty

/-- Every update of the stream (fixed in advance) is valid when it arrives. -/
def ValidStream (n : ℕ) (us : List Update) : Prop :=
  ∀ t (ht : t < us.length), (us[t]'ht).Valid n (graphAt us t)

end FullyDynamicCorrelation.VertexUpdates


