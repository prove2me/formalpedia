-- Prove2me | Definitions.Def_PolygonalArcCollarOrientedTubeWitness
-- name    : PolygonalArcCollarOrientedTubeWitness
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-28T01:59:50.129094+00:00
-- url     : https://prove2.me/theorems/95b5b3cc-a77b-45af-abcd-a2d9892aa7cf
-- title:
--   Oriented separated tube witness for polygonal arc collars
-- statement:
--   This structure packages an oriented separated tube together with the cone-width and centerline-away inequalities required by the compatible collar construction. Its cone bounds are supplied as parameters, so the half-width construction is independent of the separate geometric proof that such bounds yield signed-cone disjointness.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L614-L1174

import Definitions.Def_PolygonalArcCollarCenterlineSeparationData
import Definitions.Def_PolygonalArcCollarOrientedSeparatedTubeData

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollarOrientedTubeWitness]
-- Source phase: PolygonalArcCollarCompatibleOrientedTubeDataExists,
-- half-width/tube construction and disjointness phase.
structure PolygonalArcCollarOrientedTubeWitness (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (parameters :
      PolygonalArcCollarParameterData γ controlRadii middleSegments forbiddenMargins)
    (separations :
      PolygonalArcCollarCenterlineSeparationData γ controlRadii middleSegments
        forbiddenMargins parameters)
    (initialConeBound terminalConeBound :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (initialConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < initialConeBound j hj)
    (terminalConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < terminalConeBound j hj) where
  orientedTubes :
    PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
      forbiddenMargins
  initial_halfWidth_lt_cone_mul_lowerParam :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth j hj <
        initialConeBound j hj *
          orientedTubes.toPolygonalArcCollarSeparatedTubeData.lowerParam j hj
  terminal_halfWidth_lt_cone_mul_one_sub_upperParam :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth j hj <
        terminalConeBound j hj *
          (1 - orientedTubes.toPolygonalArcCollarSeparatedTubeData.upperParam j hj)
  initial_halfWidth_mul_normal_norm_lt_away_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth j hj *
          ‖orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj‖ <
        separations.initialAwaySeparation j hj hprev / 4
  terminal_halfWidth_mul_normal_norm_lt_away_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth j hj *
          ‖orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj‖ <
        separations.terminalAwaySeparation j hj hnext / 4
  successive_halfWidth_normal_sum_lt_away_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
      orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth j hj *
          ‖orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj‖ +
        orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth (j + 1) hnext *
          ‖orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal (j + 1) hnext‖ <
        separations.successiveAwaySeparation j hj hnext / 4


