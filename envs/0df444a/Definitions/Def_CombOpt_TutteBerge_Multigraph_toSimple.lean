-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_toSimple
-- name    : CombOpt_TutteBerge_Multigraph_toSimple
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:05.214668+00:00
-- url     : https://prove2.me/theorems/a3cbb55e-63c5-48c3-b97a-7f36a86bc040
-- title:
--   The simple graph underlying a graph
-- statement:
--   The simple graph underlying $G$ has the same nodes; two distinct nodes are adjacent exactly when some edge of $G$ has them as its ends. Loops are dropped and parallel edges merged.
--
--   **Formalization Note** The book has no name for this object. It is used only to obtain connected components from Mathlib: connectivity of $G$ depends only on which pairs of distinct nodes are joined by an edge, so $G$ and its underlying simple graph have the same components.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph

namespace CombOpt.TutteBerge

/-- **The simple graph underlying a graph.**
Two distinct nodes are adjacent iff some edge has them as its ends. Loops are dropped and parallel
edges are merged.

This definition carries no content of its own in the book. It is the bridge to Mathlib's connected
components: "connected" (p. 10, PDF p. 19: "every pair of nodes is joined by a path") depends only
on which pairs of distinct nodes are joined by an edge, so `G` and `G.toSimple` have the same
components. -/
def Multigraph.toSimple {V E : Type*} (G : Multigraph V E) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => ∃ e, G.ends e = s(u, v))

end CombOpt.TutteBerge


