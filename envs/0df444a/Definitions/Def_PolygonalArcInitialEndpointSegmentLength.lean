-- Prove2me | Definitions.Def_PolygonalArcInitialEndpointSegmentLength
-- name    : PolygonalArcInitialEndpointSegmentLength
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T21:35:33.188008+00:00
-- url     : https://prove2.me/theorems/e25b1155-d5ad-46f5-88d1-a29cb39e88c7
-- title:
--   Initial endpoint segment length of a polygonal arc
-- statement:
--   The Euclidean length of the first edge of a polygonal arc, measured from its initial endpoint to its first subsequent vertex.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInitialEndpointSegmentLength.lean

import Definitions.Def_PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcInitialEndpointSegmentLength]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInitialEndpointSegmentLength.lean#L1-L10
def PolygonalArcInitialEndpointSegmentLength (γ : PolygonalArc) : ℝ :=
  let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
  dist γ.source (γ.vertices[1]'hfirst)


