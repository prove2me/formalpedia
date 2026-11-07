-- Prove2me | Definitions.Def_CutwidthCircuitLB_IsConnected
-- name    : CutwidthCircuitLB_IsConnected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:14.788851+00:00
-- url     : https://prove2.me/theorems/e82423f7-c926-4617-be69-2f4413f61b02
-- title:
--   Connected multigraph
-- statement:
--   A multigraph is **connected** if any two vertices are joined by a path, i.e. the simple graph in which two distinct vertices are adjacent iff some edge joins them is connected.
--
--   **Formalization Note** Mathlib's notion of a connected graph includes nonemptiness, so a connected multigraph has at least one vertex.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 1.1, p.2, and Definition 2.5, p.8

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph

namespace CutwidthCircuitLB

/-- A multigraph is **connected** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §1.1, p.2, and Definition 2.5, p.8): the simple graph in
which two distinct vertices are adjacent iff some edge joins them is connected.

**Formalization Note** Mathlib's `SimpleGraph.Connected` includes nonemptiness, so a connected
multigraph has at least one vertex. -/
def IsConnected {V E : Type*} (G : CombOpt.MatchingPolytope.Graph V E) : Prop :=
  (SimpleGraph.fromRel (fun u v : V => ∃ e : E, G.ends e = s(u, v))).Connected

end CutwidthCircuitLB


