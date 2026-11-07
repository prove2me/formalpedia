-- Prove2me | Definitions.Def_DoublingMST_completeGraph
-- name    : DoublingMST_completeGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:39.465636+00:00
-- url     : https://prove2.me/theorems/04182270-5cdd-48e3-a7c6-8d045dcb5566
-- title:
--   Complete graph on the points
-- statement:
--   The complete graph on $X$, as an instance of the published multigraph structure: nodes are the points and every unordered pair $\{x,y\}$ is an edge with ends $x,y$.
--
--   Spanning trees and minimum spanning trees of $X$ are those of this graph, with the published definitions of a spanning tree (a connected forest) and of an MST.
--
--   **Formalization Note** The pairs $\{x,x\}$ are loops; a loop is a circuit, so no spanning tree contains one. Spanning trees of this graph are exactly the spanning trees of $K_n$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §1, p.1 (PDF p.3): the MST of the complete weighted graph on X

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph

namespace DoublingMST

/-- **The complete graph on the points.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §1, p.1 (PDF p.3): a spanning tree "on X"; the MST of X is that of the complete weighted
graph on X (p.1: "construct the complete weighted graph on X and compute its MST").

The published multigraph `CombOpt.SpanningTree.Graph` with node type `Fin n`, edge type
`Sym2 (Fin n)` and `ends = id`: every unordered pair is an edge.

**Formalization Note.** The diagonal pairs `s(x, x)` are loops of this multigraph. A loop is a
circuit, so no spanning tree (`CombOpt.SpanningTree.Graph.IsSpanningTree`, a connected forest)
contains one: spanning trees of this graph are exactly the spanning trees of `K_n`, as sets of
unordered pairs of distinct points. -/
def completeGraph (n : ℕ) : CombOpt.SpanningTree.Graph (Fin n) (Sym2 (Fin n)) :=
  ⟨id⟩

end DoublingMST


