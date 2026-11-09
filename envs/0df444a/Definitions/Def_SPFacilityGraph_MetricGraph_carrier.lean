-- Prove2me | Definitions.Def_SPFacilityGraph_MetricGraph_carrier
-- name    : SPFacilityGraph_MetricGraph_carrier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:34.244405+00:00
-- url     : https://prove2.me/theorems/cbbbd5ed-8599-4c3c-bc57-b5bd76c1240f
-- title:
--   Point set of a metric graph
-- statement:
--   The **carrier** of a metric graph $G$ is the subset of $\mathbb R^k$ it occupies: the union of its edge segments,
--   $$
--   G = \bigcup_{e = (a,b) \in E(G)} [a, b] .
--   $$
--   Points of $G$ may be vertices or lie in edge interiors.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.1, p.4

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph

set_option autoImplicit false

namespace SPFacilityGraph

/-- The point set of a metric graph: the union of its edge segments, the subset `G ⊆ ℝ^k`
itself (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.1, p.4). -/
def MetricGraph.carrier {k : ℕ} (G : MetricGraph k) : Set (EuclideanSpace ℝ (Fin k)) :=
  ⋃ e ∈ G.edges, segment ℝ e.1 e.2

end SPFacilityGraph


