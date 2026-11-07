-- Prove2me | Definitions.Def_CutwidthCircuitLB_edgeMultiset
-- name    : CutwidthCircuitLB_edgeMultiset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:40.594363+00:00
-- url     : https://prove2.me/theorems/b0f53c89-82ee-419f-84a5-121415ba2efb
-- title:
--   Edge multiset of a multigraph
-- statement:
--   The edges of a finite multigraph, as a multiset of unordered pairs of vertices: parallel edges appear with their multiplicity.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.4, p.8

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph

namespace CutwidthCircuitLB

/-- The edges of a finite multigraph as a multiset of unordered vertex pairs, with multiplicity
(McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.4, p.8). -/
def edgeMultiset {V E : Type*} [Fintype E] (G : CombOpt.MatchingPolytope.Graph V E) : Multiset (Sym2 V) :=
  Finset.univ.val.map G.ends

end CutwidthCircuitLB


