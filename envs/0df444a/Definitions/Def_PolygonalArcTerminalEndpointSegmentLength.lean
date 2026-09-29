-- Prove2me | Definitions.Def_PolygonalArcTerminalEndpointSegmentLength
-- name    : PolygonalArcTerminalEndpointSegmentLength
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T21:35:49.250892+00:00
-- url     : https://prove2.me/theorems/d24d1c57-5f37-4869-a9a2-b05f9ef1067b
-- title:
--   Terminal endpoint segment length of a polygonal arc
-- statement:
--   The Euclidean length of the final edge of a polygonal arc, measured from its terminal endpoint to its preceding vertex.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcTerminalEndpointSegmentLength.lean

import Mathlib.Tactic
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcTerminalEndpointSegmentLength]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcTerminalEndpointSegmentLength.lean#L1-L11
def PolygonalArcTerminalEndpointSegmentLength (γ : PolygonalArc) : ℝ :=
  let hprev : γ.vertices.length - 2 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  dist γ.target (γ.vertices[γ.vertices.length - 2]'hprev)


