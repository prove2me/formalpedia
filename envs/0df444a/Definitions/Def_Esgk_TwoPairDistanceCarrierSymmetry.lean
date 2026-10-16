-- Prove2me | Definitions.Def_Esgk_TwoPairDistanceCarrierSymmetry
-- name    : Esgk_TwoPairDistanceCarrierSymmetry
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:51:53.159499+00:00
-- url     : https://prove2.me/theorems/5b6fb285-0f27-4435-ba13-7a852d27884e
-- title:
--   Reflection in the line through two points
-- statement:
--   This constructs horizontal reflection as a linear and affine isometry. Conjugating it by a direct isometry that normalizes two distinct points defines reflection in their joining line.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_BridgeIdentity
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationNonsingularLift
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageInfiniteCorrespondence
import Definitions.Def_Esgk_NormalizedDistancePairInfiniteProjection
import Definitions.Def_Esgk_SelfCurveDistancePairNormalization
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open EuclideanGeometry
open PachDeZeeuw.Algebraic
open IrreduciblePlanePolynomial

noncomputable def bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionLinear : Point2 ≃ₗᵢ[ℝ] Point2 :=
  (ℝ ∙ xAxisPoint 1).reflection

noncomputable def bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine :
    Point2 ≃ᵃⁱ[ℝ] Point2 :=
  bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionLinear.toAffineIsometryEquiv


noncomputable def bundle_Esgk_TwoPairDistanceCarrierSymmetry_targetReflection (b e : Point2) (hbe : b ≠ e) :
    Point2 ≃ᵃⁱ[ℝ] Point2 := by
  let r : ℝ := dist b e / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (dist_pos.mpr hbe) (by norm_num)
  have htarget : dist b e = dist (xAxisPoint (-r)) (xAxisPoint r) := by
    rw [dist_xAxisPoint_neg_eq r hr.le]
    dsimp [r]
    ring
  let g : Point2 ≃ᵃⁱ[ℝ] Point2 :=
    directAffineIsometryEquivOfSendPair b e (xAxisPoint (-r))
      (xAxisPoint r) hbe htarget
  exact g.trans (bundle_Esgk_TwoPairDistanceCarrierSymmetry_horizontalReflectionAffine.trans g.symm)


end Esgk


