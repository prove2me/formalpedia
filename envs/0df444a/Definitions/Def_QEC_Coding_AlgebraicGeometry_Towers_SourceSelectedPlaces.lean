-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:46:13.839965+00:00
-- url     : https://prove2.me/theorems/9033073b-24aa-4b46-9cde-36021ab99155
-- title:
--   Source Selected Places
-- statement:
--   Definitions and structural lemmas for Source Selected Places, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaces.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_evaluate_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_split
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
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
@[reducible] def SourceSelectedPlaceIndex : ℕ → Type
  | 0 => GaloisBaseSplitPoint
  | i + 1 =>
      SourceSelectedPlaceIndex i × LinearMap.ker f256ArtinSchreier
def sourceSelectedPlaceIndexBasePoint :
    ∀ i : ℕ, SourceSelectedPlaceIndex i → GaloisBaseSplitPoint
  | 0, a => a
  | i + 1, index => sourceSelectedPlaceIndexBasePoint i index.1
noncomputable instance sourceSelectedPlaceIndexFintype :
    ∀ i : ℕ, Fintype (SourceSelectedPlaceIndex i)
  | 0 => inferInstance
  | i + 1 =>
      letI := sourceSelectedPlaceIndexFintype i
      inferInstance
theorem galoisBaseSplitRationalPlace_X_regular
    (a : GaloisBaseSplitPoint) :
    GlobalPlace.RegularAt (galoisBaseSplitRationalPlace a).place RatFunc.X := by
  change GlobalPlace.RegularAt (baseRationalPlace _).place RatFunc.X
  exact baseRationalPlace_X_regular _
theorem galoisBaseSplitRationalPlace_evaluate_X
    (a : GaloisBaseSplitPoint) :
    (galoisBaseSplitRationalPlace a).evaluateRegular RatFunc.X
        (galoisBaseSplitRationalPlace_X_regular a) = (a : F256) := by
  change (baseRationalPlace _).evaluateRegular RatFunc.X
      (baseRationalPlace_X_regular _) = (a : F256)
  rw [baseRationalPlace_evaluate_X]
  rfl
structure SourceSelectedPlaceData (i : ℕ) where
  place : RationalPlace F256 (SourceField i)
  coordinate_regular :
    GlobalPlace.RegularAt place.place (sourceDistinguishedCoordinate i)
  coordinate_split :
    galoisBaseWValue
      (place.evaluateRegular (sourceDistinguishedCoordinate i)
        coordinate_regular) ≠ 0
noncomputable def sourceSelectedPlaceData :
    ∀ i : ℕ, SourceSelectedPlaceIndex i → SourceSelectedPlaceData i
  | 0, a =>
      { place := galoisBaseSplitRationalPlace a
        coordinate_regular := galoisBaseSplitRationalPlace_X_regular a
        coordinate_split := by
          change galoisBaseWValue
            ((galoisBaseSplitRationalPlace a).evaluateRegular RatFunc.X
              (galoisBaseSplitRationalPlace_X_regular a)) ≠ 0
          rw [galoisBaseSplitRationalPlace_evaluate_X]
          exact a.property }
  | i + 1, index =>
      let previous := sourceSelectedPlaceData i index.1
      { place := sourceSplitUpperRationalPlace previous.place
          (sourceDistinguishedPlace i) (sourceDistinguishedCoordinate i)
          (sourceDistinguishedCoordinate_order i)
          previous.coordinate_regular previous.coordinate_split index.2
        coordinate_regular :=
          sourceSplitAbovePlace_sourceStepCoordinate_regular
            previous.place (sourceDistinguishedPlace i)
            (sourceDistinguishedCoordinate i)
            (sourceDistinguishedCoordinate_order i)
            previous.coordinate_regular previous.coordinate_split index.2
        coordinate_split :=
          sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_split
            previous.place (sourceDistinguishedPlace i)
            (sourceDistinguishedCoordinate i)
            (sourceDistinguishedCoordinate_order i)
            previous.coordinate_regular previous.coordinate_split index.2 }
noncomputable def sourceSelectedRationalPlace (i : ℕ)
    (index : SourceSelectedPlaceIndex i) : RationalPlace F256 (SourceField i) :=
  (sourceSelectedPlaceData i index).place
@[simp]
theorem sourceSelectedRationalPlace_zero (a : GaloisBaseSplitPoint) :
    sourceSelectedRationalPlace 0 a = galoisBaseSplitRationalPlace a := by
  rfl
theorem sourceSelectedRationalPlace_coordinate_regular (i : ℕ)
    (index : SourceSelectedPlaceIndex i) :
    GlobalPlace.RegularAt (sourceSelectedRationalPlace i index).place
      (sourceDistinguishedCoordinate i) :=
  (sourceSelectedPlaceData i index).coordinate_regular
noncomputable def sourceBaseCoordinate (i : ℕ) : SourceField i :=
  algebraMap (RatFunc F256) (SourceField i) RatFunc.X
@[simp]
theorem sourceBaseCoordinate_zero : sourceBaseCoordinate 0 = RatFunc.X :=
  rfl
theorem sourceBaseCoordinate_succ (i : ℕ) :
    sourceBaseCoordinate (i + 1) =
      sourceRecursionEmbedding i (sourceBaseCoordinate i) :=
  rfl
theorem sourceSelectedRationalPlace_baseCoordinate_regular :
    ∀ (i : ℕ) (index : SourceSelectedPlaceIndex i),
      GlobalPlace.RegularAt (sourceSelectedRationalPlace i index).place
        (sourceBaseCoordinate i)
  | 0, a => by
      exact galoisBaseSplitRationalPlace_X_regular a
  | i + 1, index => by
      rcases index with ⟨index, c⟩
      let previous := sourceSelectedPlaceData i index
      have hregular :=
        sourceSelectedRationalPlace_baseCoordinate_regular i index
      have hupper := sourceSplitAbovePlace_sourceStepEmbedding_regular
        previous.place (sourceDistinguishedPlace i)
        (sourceDistinguishedCoordinate i)
        (sourceDistinguishedCoordinate_order i) c
        (sourceBaseCoordinate i) hregular
      simp only [sourceSelectedRationalPlace, sourceSelectedPlaceData,
        sourceBaseCoordinate_succ] at hupper ⊢
      exact hupper
noncomputable def sourceGaloisBaseParameter (i : ℕ) : SourceField i :=
  algebraMap (RatFunc F256) (SourceField i) galoisBaseZ
theorem sourceGaloisBaseParameter_eq (i : ℕ) :
    sourceGaloisBaseParameter i =
      (sourceBaseCoordinate i ^ 16 + sourceBaseCoordinate i) ^ 15 := by
  simp [sourceGaloisBaseParameter, galoisBaseZ, galoisBaseW,
    sourceBaseCoordinate]
theorem sourceGaloisBaseParameter_regular (i : ℕ)
    (index : SourceSelectedPlaceIndex i) :
    GlobalPlace.RegularAt (sourceSelectedRationalPlace i index).place
      (sourceGaloisBaseParameter i) := by
  let Q := sourceSelectedRationalPlace i index
  have hx : sourceBaseCoordinate i ∈ Q.place.valuationRing :=
    (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
      (sourceSelectedRationalPlace_baseCoordinate_regular i index)
  rw [GlobalPlace.regularAt_iff_mem_valuationRing,
    sourceGaloisBaseParameter_eq]
  exact Q.place.valuationRing.pow_mem
    (Q.place.valuationRing.add_mem _ _
      (Q.place.valuationRing.pow_mem hx 16) hx) 15
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


