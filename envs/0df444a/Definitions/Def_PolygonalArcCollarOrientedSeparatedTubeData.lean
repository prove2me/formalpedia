-- Prove2me | Definitions.Def_PolygonalArcCollarOrientedSeparatedTubeData
-- name    : PolygonalArcCollarOrientedSeparatedTubeData
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T23:48:33.131443+00:00
-- url     : https://prove2.me/theorems/00af3e2c-c9cc-4a90-823b-11be78edeaed
-- title:
--   PolygonalArcCollarOrientedSeparatedTubeData
-- statement:
--   A separated polygonal-arc collar tube system whose normal vectors are fixed to be the positive quarter-turns of the corresponding edge directions.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarOrientedSeparatedTubeData.lean#L1-18

import Definitions.Def_PolygonalArcCollarSeparatedTubeData

-- [TABLET NODE: PolygonalArcCollarOrientedSeparatedTubeData]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarOrientedSeparatedTubeData.lean#L1-18
structure PolygonalArcCollarOrientedSeparatedTubeData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    extends
      PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins where
  normal_eq_positive_quarter_turn :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      normal j hj =
        WithLp.toLp 2 (fun k : Fin 2 =>
          if k = 0 then -((γ.vertices[j + 1] - γ.vertices[j]) 1)
          else (γ.vertices[j + 1] - γ.vertices[j]) 0)


