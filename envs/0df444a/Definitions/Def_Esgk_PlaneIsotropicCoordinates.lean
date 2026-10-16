-- Prove2me | Definitions.Def_Esgk_PlaneIsotropicCoordinates
-- name    : Esgk_PlaneIsotropicCoordinates
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:46:47.943859+00:00
-- url     : https://prove2.me/theorems/aa40844e-2f57-4bf7-b948-aa3142e6021e
-- title:
--   Complex isotropic coordinates and translations
-- statement:
--   This constructs the polynomial coordinate changes $u=X+iY$, $v=X-iY$ and their inverses. It also constructs translations by conjugate pairs of complex constants in these coordinates, with inverse substitution maps.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
import Mathlib
import Mathlib.Algebra.MvPolynomial.Monad

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

 
def planeToIsotropicCoordinates : ComplexPlanePoly →+* ComplexPlanePoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
      MvPolynomial.C (1 / (2 * Complex.I)) * (MvPolynomial.X 0 - MvPolynomial.X 1)]

 
def isotropicToPlaneCoordinates : ComplexPlanePoly →+* ComplexPlanePoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1,
      MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1]

@[simp]
theorem planeToIsotropicCoordinates_C (c : ℂ) :
    planeToIsotropicCoordinates (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [planeToIsotropicCoordinates]

@[simp]
theorem planeToIsotropicCoordinates_X_zero :
    planeToIsotropicCoordinates (MvPolynomial.X 0) =
      MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1) := by
  simp [planeToIsotropicCoordinates]

@[simp]
theorem planeToIsotropicCoordinates_X_one :
    planeToIsotropicCoordinates (MvPolynomial.X 1) =
      MvPolynomial.C (1 / (2 * Complex.I)) *
        (MvPolynomial.X 0 - MvPolynomial.X 1) := by
  simp [planeToIsotropicCoordinates]

@[simp]
theorem isotropicToPlaneCoordinates_C (c : ℂ) :
    isotropicToPlaneCoordinates (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [isotropicToPlaneCoordinates]

@[simp]
theorem isotropicToPlaneCoordinates_X_zero :
    isotropicToPlaneCoordinates (MvPolynomial.X 0) =
      MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1 := by
  simp [isotropicToPlaneCoordinates]

@[simp]
theorem isotropicToPlaneCoordinates_X_one :
    isotropicToPlaneCoordinates (MvPolynomial.X 1) =
      MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1 := by
  simp [isotropicToPlaneCoordinates]

theorem bundle_Esgk_PlaneIsotropicCoordinates_C_half_mul_two :
    (MvPolynomial.C (1 / 2 : ℂ) : ComplexPlanePoly) * 2 = 1 := by
  change MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C (2 : ℂ) = MvPolynomial.C 1
  rw [← map_mul]
  norm_num

theorem bundle_Esgk_PlaneIsotropicCoordinates_C_I_sq :
    (MvPolynomial.C Complex.I : ComplexPlanePoly) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]


theorem isotropicToPlaneCoordinates_comp_planeToIsotropicCoordinates :
    isotropicToPlaneCoordinates.comp planeToIsotropicCoordinates = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    fin_cases i
    · simp [RingHom.comp_apply]
      ring_nf
      calc
        _ = ((MvPolynomial.C (1 / 2 : ℂ) : ComplexPlanePoly) * 2) *
            MvPolynomial.X 0 := by ring
        _ = MvPolynomial.X 0 := by rw [bundle_Esgk_PlaneIsotropicCoordinates_C_half_mul_two, one_mul]
    · simp [RingHom.comp_apply]
      ring_nf
      rw [bundle_Esgk_PlaneIsotropicCoordinates_C_I_sq]
      ring_nf
      calc
        _ = ((MvPolynomial.C (1 / 2 : ℂ) : ComplexPlanePoly) * 2) *
            MvPolynomial.X 1 := by ring
        _ = MvPolynomial.X 1 := by rw [bundle_Esgk_PlaneIsotropicCoordinates_C_half_mul_two, one_mul]


theorem planeToIsotropicCoordinates_comp_isotropicToPlaneCoordinates :
    planeToIsotropicCoordinates.comp isotropicToPlaneCoordinates = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    fin_cases i
    · simp [RingHom.comp_apply]
      ring_nf
      rw [bundle_Esgk_PlaneIsotropicCoordinates_C_I_sq]
      ring_nf
      calc
        _ = ((MvPolynomial.C (1 / 2 : ℂ) : ComplexPlanePoly) * 2) *
            MvPolynomial.X 0 := by ring
        _ = MvPolynomial.X 0 := by rw [bundle_Esgk_PlaneIsotropicCoordinates_C_half_mul_two, one_mul]
    · simp [RingHom.comp_apply]
      ring_nf
      rw [bundle_Esgk_PlaneIsotropicCoordinates_C_I_sq]
      ring_nf
      calc
        _ = ((MvPolynomial.C (1 / 2 : ℂ) : ComplexPlanePoly) * 2) *
            MvPolynomial.X 1 := by ring
        _ = MvPolynomial.X 1 := by rw [bundle_Esgk_PlaneIsotropicCoordinates_C_half_mul_two, one_mul]

 
def planeIsotropicCoordinateEquiv : ComplexPlanePoly ≃+* ComplexPlanePoly where
  toFun := planeToIsotropicCoordinates
  invFun := isotropicToPlaneCoordinates
  left_inv p := RingHom.congr_fun
    isotropicToPlaneCoordinates_comp_planeToIsotropicCoordinates p
  right_inv p := RingHom.congr_fun
    planeToIsotropicCoordinates_comp_isotropicToPlaneCoordinates p
  map_mul' := map_mul planeToIsotropicCoordinates
  map_add' := map_add planeToIsotropicCoordinates


def isotropicTranslation (ξ : ℂ) : ComplexPlanePoly →+* ComplexPlanePoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.X 0 - MvPolynomial.C ξ,
      MvPolynomial.X 1 - MvPolynomial.C (star ξ)]

 
def inverseIsotropicTranslation (ξ : ℂ) : ComplexPlanePoly →+* ComplexPlanePoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.X 0 + MvPolynomial.C ξ,
      MvPolynomial.X 1 + MvPolynomial.C (star ξ)]

@[simp]
theorem isotropicTranslation_C (ξ c : ℂ) :
    isotropicTranslation ξ (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [isotropicTranslation]

@[simp]
theorem isotropicTranslation_X_zero (ξ : ℂ) :
    isotropicTranslation ξ (MvPolynomial.X 0) = MvPolynomial.X 0 - MvPolynomial.C ξ := by
  simp [isotropicTranslation]

@[simp]
theorem isotropicTranslation_X_one (ξ : ℂ) :
    isotropicTranslation ξ (MvPolynomial.X 1) =
      MvPolynomial.X 1 - MvPolynomial.C (star ξ) := by
  simp [isotropicTranslation]

@[simp]
theorem inverseIsotropicTranslation_C (ξ c : ℂ) :
    inverseIsotropicTranslation ξ (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [inverseIsotropicTranslation]

@[simp]
theorem inverseIsotropicTranslation_X_zero (ξ : ℂ) :
    inverseIsotropicTranslation ξ (MvPolynomial.X 0) = MvPolynomial.X 0 + MvPolynomial.C ξ := by
  simp [inverseIsotropicTranslation]

@[simp]
theorem inverseIsotropicTranslation_X_one (ξ : ℂ) :
    inverseIsotropicTranslation ξ (MvPolynomial.X 1) =
      MvPolynomial.X 1 + MvPolynomial.C (star ξ) := by
  simp [inverseIsotropicTranslation]

 
theorem inverseIsotropicTranslation_comp_isotropicTranslation (ξ : ℂ) :
    (inverseIsotropicTranslation ξ).comp (isotropicTranslation ξ) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    fin_cases i <;> simp [RingHom.comp_apply]

 
theorem isotropicTranslation_comp_inverseIsotropicTranslation (ξ : ℂ) :
    (isotropicTranslation ξ).comp (inverseIsotropicTranslation ξ) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    fin_cases i <;> simp [RingHom.comp_apply]

 
def isotropicTranslationEquiv (ξ : ℂ) : ComplexPlanePoly ≃+* ComplexPlanePoly where
  toFun := isotropicTranslation ξ
  invFun := inverseIsotropicTranslation ξ
  left_inv p := RingHom.congr_fun
    (inverseIsotropicTranslation_comp_isotropicTranslation ξ) p
  right_inv p := RingHom.congr_fun
    (isotropicTranslation_comp_inverseIsotropicTranslation ξ) p
  map_mul' := map_mul (isotropicTranslation ξ)
  map_add' := map_add (isotropicTranslation ξ)


end Esgk


