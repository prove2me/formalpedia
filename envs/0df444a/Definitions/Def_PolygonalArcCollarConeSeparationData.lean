-- Prove2me | Definitions.Def_PolygonalArcCollarConeSeparationData
-- name    : PolygonalArcCollarConeSeparationData
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-28T02:00:09.295416+00:00
-- url     : https://prove2.me/theorems/e1b83508-f012-428f-bc41-68573d13a5f2
-- title:
--   Cone bounds and signed-cone separation data for polygonal arc collars
-- statement:
--   This structure records positive initial and terminal cone bounds and the four signed-cone disjointness conclusions for adjacent polygonal segments. The cone expressions use the explicit positive quarter-turn of each segment direction, matching the orientation field used by the final compatible tube structure.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L29-L109, L1190-L1461

import Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins
import Definitions.Def_PlanarRot90

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollarConeSeparationData]
-- Source phase: PolygonalArcCollarCompatibleOrientedTubeDataExists,
-- cone-bound and signed-cone separation phase.
structure PolygonalArcCollarConeSeparationData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) where
  initialConeBound :
    (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  terminalConeBound :
    (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  initialConeBound_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      0 < initialConeBound j hj
  terminalConeBound_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      0 < terminalConeBound j hj
  initial_signed_cone_disjoint_previous_segment :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      Disjoint
        {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
          ∃ s : ℝ, s ≠ 0 ∧ |s| < initialConeBound j hj * t ∧
            z =
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])}
        (segment ℝ γ.vertices[j - 1] γ.vertices[j])
  terminal_signed_cone_disjoint_next_segment :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      Disjoint
        {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
          ∃ s : ℝ, s ≠ 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
            z =
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])}
        (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2])
  successive_positive_negative_cones_disjoint :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      Disjoint
        {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
          ∃ s : ℝ, 0 < s ∧ s < terminalConeBound j hj * (1 - t) ∧
            z =
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])}
        {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
          ∃ s : ℝ, s < 0 ∧ |s| < initialConeBound (j + 1) hnext * t ∧
            z =
              AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                s • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1])}
  successive_negative_positive_cones_disjoint :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      Disjoint
        {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
          ∃ s : ℝ, s < 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
            z =
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])}
        {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
          ∃ s : ℝ, 0 < s ∧ s < initialConeBound (j + 1) hnext * t ∧
            z =
              AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                s • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1])}


