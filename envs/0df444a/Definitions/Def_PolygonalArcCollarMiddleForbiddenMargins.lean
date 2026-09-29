-- Prove2me | Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins
-- name    : PolygonalArcCollarMiddleForbiddenMargins
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T23:46:50.169121+00:00
-- url     : https://prove2.me/theorems/b953c2f1-16c3-41d7-b288-5f9f92586476
-- title:
--   PolygonalArcCollarMiddleForbiddenMargins
-- statement:
--   Positive separation margins for the selected middle edge segments of a polygonal-arc collar, recording their distances from nonadjacent edges, nonincident vertex disks, and other middle cores.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarMiddleForbiddenMargins.lean#L1-31

import Definitions.Def_PolygonalArcCollarMiddleSegmentData

-- [TABLET NODE: PolygonalArcCollarMiddleForbiddenMargins]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarMiddleForbiddenMargins.lean#L1-31
structure PolygonalArcCollarMiddleForbiddenMargins (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii) where
  margin : (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  margin_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < margin j hj
  middle_segment_separation :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) →
          ∀ z, z ∈ middleSegments.middle j hj →
            ∀ q, q ∈ segment ℝ γ.vertices[k] γ.vertices[k + 1] →
              margin j hj ≤ dist z q
  middle_control_disk_separation :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (i : Fin γ.vertices.length),
        i.1 ≠ j → i.1 ≠ j + 1 →
          ∀ z, z ∈ middleSegments.middle j hj →
            ∀ q, q ∈ Metric.closedBall γ.vertices[i.1] (controlRadii.radius i) →
              margin j hj ≤ dist z q
  middle_core_separation :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) →
          ∀ z, z ∈ middleSegments.middle j hj →
            ∀ q, q ∈ middleSegments.middle k hk →
              margin j hj ≤ dist z q


