-- Prove2me | Definitions.Def_PolygonalArcCollarParameterData
-- name    : PolygonalArcCollarParameterData
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-28T01:59:01.886925+00:00
-- url     : https://prove2.me/theorems/217c0421-397c-4af8-b482-dfbc58b049a2
-- title:
--   Parameter data for polygonal arc collars
-- statement:
--   This structure packages the parameter, slack, endpoint-normal, and elementary inequality data used to build an oriented tube around every segment of a polygonal arc. The fields retain the original control-radius and forbidden-margin dependencies and expose the exact identities and positivity relations needed by the later centerline, tube, and cone phases.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L109-L332

import Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins
import Definitions.Def_PlanarRot90

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollarParameterData]
-- Source phase: PolygonalArcCollarCompatibleOrientedTubeDataExists, parameter/normal phase.
structure PolygonalArcCollarParameterData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) where
  leftParam :
    (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  rightParam :
    (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  segmentLength :
    (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  paramSlack :
    (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  lowerParam :
    (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  upperParam :
    (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  normal :
    (j : ℕ) → j + 1 < γ.vertices.length → EuclideanSpace ℝ (Fin 2)
  leftParam_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      leftParam j hj =
        controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1]
  rightParam_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      rightParam j hj =
        1 - controlRadii.radius ⟨j + 1, hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1]
  segmentLength_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      segmentLength j hj = dist γ.vertices[j] γ.vertices[j + 1]
  paramSlack_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      paramSlack j hj =
        min (leftParam j hj / 2)
          (min ((1 - rightParam j hj) / 2)
            (forbiddenMargins.margin j hj /
              (8 * (segmentLength j hj + 1))))
  lowerParam_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      lowerParam j hj = leftParam j hj - paramSlack j hj
  upperParam_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      upperParam j hj = rightParam j hj + paramSlack j hj
  normal_eq_positive_quarter_turn :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      normal j hj = PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])
  leftParam_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < leftParam j hj
  leftParam_lt_rightParam :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      leftParam j hj < rightParam j hj
  rightParam_lt_one :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), rightParam j hj < 1
  paramSlack_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < paramSlack j hj
  paramSlack_mul_segmentLength_lt_margin_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      paramSlack j hj * segmentLength j hj <
        forbiddenMargins.margin j hj / 4
  lowerParam_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < lowerParam j hj
  lowerParam_lt_leftParam :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      lowerParam j hj < leftParam j hj
  rightParam_lt_upperParam :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      rightParam j hj < upperParam j hj
  upperParam_lt_one :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), upperParam j hj < 1
  one_sub_upperParam_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      0 < 1 - upperParam j hj
  normal_orthogonal :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      inner ℝ (γ.vertices[j + 1] - γ.vertices[j]) (normal j hj) = 0
  normal_norm_eq_segmentLength :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      ‖normal j hj‖ = segmentLength j hj
  segmentLength_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      0 < segmentLength j hj


