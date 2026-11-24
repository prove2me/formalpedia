-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSameOrderBranchesMeet
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSameOrderBranchesMeet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:33.939082+00:00
-- url     : https://prove2.me/theorems/b86c1b3f-0cb1-4809-9dc5-22e3482c09b6
-- title:
--   PSame Order Branches Meet
-- statement:
--   Definitions and structural lemmas for PSame Order Branches Meet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrderBranchesMeet.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrderBranchesMeet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInCurveComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology
noncomputable def VarBranch.restrictInto {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I k q) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ t ∈ Metric.ball (0 : Fin k → ℂ) ε, c.toFun t ∈ zeroSet J) : VarBranch J k q where
  radius := min ε c.radius
  radius_pos := lt_min hε c.radius_pos
  toFun := c.toFun
  differentiableOn := c.differentiableOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  injOn := c.injOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  map_zero := c.map_zero
  mapsTo := fun t ht ↦ h t (Metric.ball_subset_ball (min_le_left _ _) ht)
end GroundTheory.Heights₂.Heights


