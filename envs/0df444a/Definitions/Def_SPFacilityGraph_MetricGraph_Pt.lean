-- Prove2me | Definitions.Def_SPFacilityGraph_MetricGraph_Pt
-- name    : SPFacilityGraph_MetricGraph_Pt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:48:32.21071+00:00
-- url     : https://prove2.me/theorems/1343d038-a6e2-477c-95a6-2b0020346122
-- title:
--   Points $x \in G$ of a metric graph
-- statement:
--   The type of **points** $x \in G$ of a metric graph: the elements of its carrier $\bigcup_e [a_e, b_e] \subseteq \mathbb R^k$. Peaks, reports, outcomes and true locations are all points of this type.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.1, p.4 ("Points x, y, z ∈ G may be vertices or lie in edge interiors")

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_carrier

set_option autoImplicit false

namespace SPFacilityGraph

/-- The points `x ∈ G` of a metric graph (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.1, p.4: "Points x, y, z ∈ G may be
vertices or lie in edge interiors"), as the subtype of the carrier. -/
abbrev MetricGraph.Pt {k : ℕ} (G : MetricGraph k) : Type := ↥G.carrier

end SPFacilityGraph


