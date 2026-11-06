-- Prove2me | Definitions.Def_TreeMultiflow_RatInstance_graph
-- name    : TreeMultiflow_RatInstance_graph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:49.968123+00:00
-- url     : https://prove2.me/theorems/4cf60a11-c4f9-4735-9adb-3fe8fb6cf7d2
-- title:
--   Tree of a rational instance
-- statement:
--   The simple graph on the vertices $\{0,\dots,n\}$ of a rational instance whose edges are the listed pairs $\{a,b\}$.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (Let T = (V, E) be a tree)

import Mathlib
import Definitions.Def_TreeMultiflow_RatInstance_vertex

namespace TreeMultiflow

/-- **The graph of a rational instance.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2 ("Let T = (V, E) be a tree").

`I.graph` is the simple graph on `Fin (I.n + 1)` whose edges are the pairs listed in `I.edges`
(in either orientation). -/
def RatInstance.graph (I : RatInstance) : SimpleGraph (Fin (I.n + 1)) :=
  SimpleGraph.fromRel fun i j => ∃ t ∈ I.edges, I.vertex t.1 = i ∧ I.vertex t.2.1 = j

end TreeMultiflow


