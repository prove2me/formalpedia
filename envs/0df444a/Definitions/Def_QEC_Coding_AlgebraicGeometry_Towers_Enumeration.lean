-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
-- name    : QEC_Coding_AlgebraicGeometry_Towers_Enumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:13:12.561736+00:00
-- url     : https://prove2.me/theorems/1fa28a33-bebe-437f-ae11-bae251b7cff1
-- title:
--   Enumeration
-- statement:
--   Definitions and structural lemmas for Enumeration, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Enumeration.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fintype
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedRationalPlace_place_injective
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
open Filter
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
noncomputable instance selectedFieldField (i : ℕ) :
    _root_.Field (Field (i + 2)) :=
  fieldField (i + 2)
noncomputable instance selectedFieldConstantAlgebra (i : ℕ) :
    Algebra F256 (Field (i + 2)) :=
  fieldConstantAlgebra (i + 2)
noncomputable instance selectedFieldRatFuncAlgebra (i : ℕ) :
    Algebra (RatFunc F256) (Field (i + 2)) :=
  fieldRatFuncAlgebra (i + 2)
noncomputable instance selectedFieldConstantTower (i : ℕ) :
    IsScalarTower F256 (RatFunc F256) (Field (i + 2)) :=
  fieldConstantTower (i + 2)
noncomputable instance selectedFieldFunctionField (i : ℕ) :
    _root_.FunctionField F256 (Field (i + 2)) :=
  fieldFunctionField (i + 2)
noncomputable instance fieldPolynomialAlgebra (i : ℕ) :
    Algebra (Polynomial F256) (Field i) :=
  ((algebraMap (RatFunc F256) (Field i)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
noncomputable instance fieldPolynomialRatFuncTower (i : ℕ) :
    IsScalarTower (Polynomial F256) (RatFunc F256) (Field i) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
noncomputable instance fieldRatFuncSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (Field i) := by
  induction i with
  | zero => exact inferInstance
  | succ i ih =>
      letI : Algebra.IsSeparable (RatFunc F256) (Field i) := ih
      exact Algebra.IsSeparable.trans (RatFunc F256) (Field i) (Field (i + 1))
noncomputable instance selectedFieldRatFuncSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (Field (i + 2)) :=
  fieldRatFuncSeparable (i + 2)
def selectedLength (i : ℕ) : ℕ :=
  Fintype.card (SelectedPlaceIndex (i + 2))
noncomputable def selectedPlaceIndexEquiv (i : ℕ) :
    Fin (selectedLength i) ≃ SelectedPlaceIndex (i + 2) :=
  (Fintype.equivFin (SelectedPlaceIndex (i + 2))).symm
noncomputable def selectedRationalPlaceAt (i : ℕ)
    (j : Fin (selectedLength i)) : RationalPlace F256 (Field (i + 2)) :=
  selectedRationalPlace (i + 2) (selectedPlaceIndexEquiv i j)
theorem selectedRationalPlaceAt_baseCoordinate_regular (i : ℕ)
    (j : Fin (selectedLength i)) :
    GlobalPlace.RegularAt (selectedRationalPlaceAt i j).place
      (baseCoordinate (i + 2)) :=
  selectedRationalPlace_baseCoordinate_regular
    (i + 2) (selectedPlaceIndexEquiv i j)
noncomputable def selectedPlace (i : ℕ) (j : Fin (selectedLength i)) :
    GlobalPlace F256 (Field (i + 2)) :=
  (selectedRationalPlaceAt i j).place
@[simp]
theorem selectedRationalPlaceAt_place (i : ℕ)
    (j : Fin (selectedLength i)) :
    (selectedRationalPlaceAt i j).place = selectedPlace i j :=
  rfl
theorem selectedPlace_injective (i : ℕ) :
    Function.Injective (selectedPlace i) := by
  intro a b hab
  apply (selectedPlaceIndexEquiv i).injective
  apply selectedRationalPlace_place_injective (i + 2)
  exact hab
noncomputable def selectedPlaces (i : ℕ) :
    Finset (GlobalPlace F256 (Field (i + 2))) := by
  classical
  exact Finset.univ.image (selectedPlace i)
theorem selectedPlaces_coe (i : ℕ) :
    (selectedPlaces i : Set (GlobalPlace F256 (Field (i + 2)))) =
      Set.range (selectedPlace i) := by
  classical
  ext P
  simp only [selectedPlaces, Finset.coe_image, Finset.coe_univ,
    Set.image_univ]
noncomputable def selectedPlaceEquiv (i : ℕ) :
    Fin (selectedLength i) ≃ ↥(selectedPlaces i) :=
  (Equiv.ofInjective (selectedPlace i) (selectedPlace_injective i)).trans
    (Equiv.setCongr (selectedPlaces_coe i).symm)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


