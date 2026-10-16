-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneDistanceImageDegreeOne
-- name    : Esgk_IrreduciblePlaneDistanceImageDegreeOne
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:51:21.333814+00:00
-- url     : https://prove2.me/theorems/42b1a05e-b223-4ed7-88b5-13512e5b7737
-- title:
--   Distance-image field isomorphism under reflection asymmetry
-- statement:
--   If a nonzero distance parameter gives a distance-image map whose curve image is not invariant under horizontal reflection, this constructs the resulting algebra isomorphism with the plane-curve function field.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageField
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_SelfCurveFunctionFieldSymmetry
import Definitions.Def_Esgk_SelfCurveReflectionInvariance
import Definitions.Def_Esgk_SelfCurveTwoAnchorFunctionField
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


theorem distanceImageFunctionFieldHom_surjective_of_xAxisReflection_image_zeroSet_ne
    (C : IrreduciblePlanePolynomial ℝ) {r : ℝ} (hr : r ≠ 0)
    (hns :
      xAxisReflectionPoint '' PlaneCurveZeroSet C.polynomial ≠
        PlaneCurveZeroSet C.polynomial) :
    Function.Surjective (C.distanceImageFunctionFieldHom r) := by
  rw [← AlgHom.fieldRange_eq_top]
  rw [C.distanceImageFunctionFieldHom_fieldRange]
  exact C.twoAnchorDistanceField_eq_top_of_xAxisReflection_image_zeroSet_ne
    hr hns


noncomputable def distanceImageFunctionFieldAlgEquivOfNonsymmetric
    (C : IrreduciblePlanePolynomial ℝ) {r : ℝ} (hr : r ≠ 0)
    (hns :
      xAxisReflectionPoint '' PlaneCurveZeroSet C.polynomial ≠
        PlaneCurveZeroSet C.polynomial) :
    C.DistanceImageFunctionField r ≃ₐ[ℝ] C.FunctionField :=
  AlgEquiv.ofBijective (C.distanceImageFunctionFieldHom r)
    ⟨C.distanceImageFunctionFieldHom_injective r,
      C.distanceImageFunctionFieldHom_surjective_of_xAxisReflection_image_zeroSet_ne
        hr hns⟩


end IrreduciblePlanePolynomial

end Esgk


