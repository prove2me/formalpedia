-- Prove2me | Definitions.Def_Esgk_PlaneHorizontalReflection
-- name    : Esgk_PlaneHorizontalReflection
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:01:06.057771+00:00
-- url     : https://prove2.me/theorems/d9ad4fa4-aa07-49f8-97de-b84415ad1047
-- title:
--   Reflection in the horizontal axis
-- statement:
--   This constructs reflection in the horizontal axis as a linear map, a linear isometry, and an affine isometry of the Euclidean plane.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryReduction
import Definitions.Def_Esgk_RichnessLevels
import Definitions.Def_Esgk_SelfCurveDistancePairNormalization
import Definitions.Def_Esgk_SelfCurveReflectionInvariance
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 as described in the repository LICENSE.
-/


namespace Esgk

open EuclideanGeometry

noncomputable def xAxisReflectionLinear : Point2 →ₗ[ℝ] Point2 :=
  { toFun := xAxisReflectionPoint
    map_add' := by
      intro x y
      ext i
      fin_cases i <;> simp [xAxisReflectionPoint] <;> ring
    map_smul' := by
      intro a x
      ext i
      fin_cases i <;> simp [xAxisReflectionPoint] }


theorem xAxisReflectionLinear_involutive :
    Function.Involutive xAxisReflectionLinear := by
  intro x
  ext i
  fin_cases i <;> simp [xAxisReflectionLinear, xAxisReflectionPoint]

noncomputable def xAxisReflectionLinearIsometry : Point2 ≃ₗᵢ[ℝ] Point2 :=
  { LinearEquiv.ofInvolutive xAxisReflectionLinear
      xAxisReflectionLinear_involutive with
    norm_map' := by
      intro x
      change ‖xAxisReflectionLinear x‖ = ‖x‖
      have hsq : ‖xAxisReflectionLinear x‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        simp [xAxisReflectionLinear, xAxisReflectionPoint, Fin.sum_univ_two]
      nlinarith [norm_nonneg (xAxisReflectionLinear x), norm_nonneg x] }

noncomputable def xAxisReflectionAffineIsometry : Point2 ≃ᵃⁱ[ℝ] Point2 :=
  AffineIsometryEquiv.mk' xAxisReflectionPoint xAxisReflectionLinearIsometry 0 (by
    intro x
    simp [xAxisReflectionLinearIsometry, xAxisReflectionLinear,
      xAxisReflectionPoint])


end Esgk


