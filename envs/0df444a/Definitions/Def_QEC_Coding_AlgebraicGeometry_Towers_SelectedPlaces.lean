-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:05:37.174002+00:00
-- url     : https://prove2.me/theorems/c4ead802-6e1e-4d5d-9dbd-411be1794362
-- title:
--   Selected Places
-- statement:
--   Definitions and structural lemmas for Selected Places, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SelectedPlaces.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_evaluate_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_evaluate_stepDistinguishedCoordinate_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
@[reducible] def SelectedPlaceIndex : ℕ → Type
  | 0 => BasePoint
  | i + 1 => SelectedPlaceIndex i × LinearMap.ker f256ArtinSchreier
def selectedPlaceIndexBasePoint :
    ∀ i : ℕ, SelectedPlaceIndex i → BasePoint
  | 0, a => a
  | i + 1, index => selectedPlaceIndexBasePoint i index.1
noncomputable instance selectedPlaceIndexFintype :
    ∀ i : ℕ, Fintype (SelectedPlaceIndex i)
  | 0 => inferInstance
  | i + 1 =>
      letI := selectedPlaceIndexFintype i
      inferInstance
structure SelectedPlaceData (i : ℕ) where
  place : RationalPlace F256 (Field i)
  coordinate_regular :
    GlobalPlace.RegularAt place.place (distinguishedCoordinate i)
  coordinate_evaluate_ne_zero :
    place.evaluateRegular (distinguishedCoordinate i) coordinate_regular ≠ 0
noncomputable def selectedPlaceData :
    ∀ i : ℕ, SelectedPlaceIndex i → SelectedPlaceData i
  | 0, a =>
      { place := baseRationalPlace a
        coordinate_regular := baseRationalPlace_X_regular a
        coordinate_evaluate_ne_zero := by
          change (baseRationalPlace a).evaluateRegular RatFunc.X
            (baseRationalPlace_X_regular a) ≠ 0
          rw [baseRationalPlace_evaluate_X]
          exact Units.ne_zero a }
  | i + 1, index =>
      let previous := selectedPlaceData i index.1
      { place := splitUpperRationalPlace previous.place
          (distinguishedPlace i) (distinguishedCoordinate i)
          (distinguishedCoordinate_order i) previous.coordinate_regular index.2
        coordinate_regular :=
          splitAbovePlace_stepDistinguishedCoordinate_regular
            previous.place (distinguishedPlace i) (distinguishedCoordinate i)
            (distinguishedCoordinate_order i) previous.coordinate_regular
            previous.coordinate_evaluate_ne_zero index.2
        coordinate_evaluate_ne_zero :=
          splitUpperRationalPlace_evaluate_stepDistinguishedCoordinate_ne_zero
            previous.place (distinguishedPlace i) (distinguishedCoordinate i)
            (distinguishedCoordinate_order i) previous.coordinate_regular
            previous.coordinate_evaluate_ne_zero index.2 }
noncomputable def selectedRationalPlace (i : ℕ)
    (index : SelectedPlaceIndex i) : RationalPlace F256 (Field i) :=
  (selectedPlaceData i index).place
theorem selectedRationalPlace_coordinate_regular (i : ℕ)
    (index : SelectedPlaceIndex i) :
    GlobalPlace.RegularAt (selectedRationalPlace i index).place
      (distinguishedCoordinate i) :=
  (selectedPlaceData i index).coordinate_regular
noncomputable def baseCoordinate (i : ℕ) : Field i :=
  algebraMap (RatFunc F256) (Field i) RatFunc.X
@[simp]
theorem baseCoordinate_zero : baseCoordinate 0 = RatFunc.X :=
  rfl
theorem baseCoordinate_succ (i : ℕ) :
    baseCoordinate (i + 1) = stepEmbedding i (baseCoordinate i) :=
  rfl
theorem selectedRationalPlace_baseCoordinate_regular :
    ∀ (i : ℕ) (index : SelectedPlaceIndex i),
      GlobalPlace.RegularAt (selectedRationalPlace i index).place
        (baseCoordinate i)
  | 0, a => by
      exact baseRationalPlace_X_regular a
  | i + 1, index => by
      rcases index with ⟨index, c⟩
      let previous := selectedPlaceData i index
      have hregular := selectedRationalPlace_baseCoordinate_regular i index
      have hupper := splitAbovePlace_stepEmbedding_regular
        previous.place (distinguishedPlace i) (distinguishedCoordinate i)
        (distinguishedCoordinate_order i) c (baseCoordinate i) hregular
      simp only [selectedRationalPlace, selectedPlaceData,
        baseCoordinate_succ] at hupper ⊢
      exact hupper
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


