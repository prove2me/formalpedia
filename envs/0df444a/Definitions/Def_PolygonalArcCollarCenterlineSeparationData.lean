-- Prove2me | Definitions.Def_PolygonalArcCollarCenterlineSeparationData
-- name    : PolygonalArcCollarCenterlineSeparationData
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-28T01:59:27.066489+00:00
-- url     : https://prove2.me/theorems/adba01f9-ea6e-4460-8f11-32416e8f93f6
-- title:
--   Compact centerline separation data for polygonal arc collars
-- statement:
--   This structure records three positive separation functions for the initial, terminal, and successive centerline pieces of a polygonal arc collar. Each function comes with the exact quantified lower bound against the corresponding adjacent segment or centerline, using the original control-radius parameter intervals.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L332-L614

import Definitions.Def_PolygonalArcCollarParameterData

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollarCenterlineSeparationData]
-- Source phase: PolygonalArcCollarCompatibleOrientedTubeDataExists,
-- compact centerline/PositiveSeparation phase.
structure PolygonalArcCollarCenterlineSeparationData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (parameters :
      PolygonalArcCollarParameterData γ controlRadii middleSegments forbiddenMargins) where
  initialAwaySeparation :
    (j : ℕ) → j + 1 < γ.vertices.length → 0 < j → ℝ
  terminalAwaySeparation :
    (j : ℕ) → j + 1 < γ.vertices.length →
      (j + 1) + 1 < γ.vertices.length → ℝ
  successiveAwaySeparation :
    (j : ℕ) → j + 1 < γ.vertices.length →
      (j + 1) + 1 < γ.vertices.length → ℝ
  initialAwaySeparation_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      0 < initialAwaySeparation j hj hprev
  terminalAwaySeparation_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      0 < terminalAwaySeparation j hj hnext
  successiveAwaySeparation_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      0 < successiveAwaySeparation j hj hnext
  initial_centerline_previous_segment_away :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      ∀ t : ℝ,
        t ∈ Set.Icc
          (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) →
          ∀ q, q ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] →
            initialAwaySeparation j hj hprev ≤
              dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q
  terminal_centerline_next_segment_away :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      ∀ t : ℝ,
        t ∈ Set.Icc (0 : ℝ)
          (1 - controlRadii.radius ⟨j + 1, hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1]) →
          ∀ q, q ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] →
            terminalAwaySeparation j hj hnext ≤
              dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q
  successive_centerlines_away :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      ∀ t : ℝ,
        t ∈ Set.Icc (0 : ℝ)
          (1 - controlRadii.radius ⟨j + 1, hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1]) →
        ∀ u : ℝ,
          u ∈ Set.Icc
            (controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j + 1] γ.vertices[j + 2]) (1 : ℝ) →
          successiveAwaySeparation j hj hnext ≤
            dist
              (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
              (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u)


