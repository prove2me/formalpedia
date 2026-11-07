-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:23:46.654472+00:00
-- url     : https://prove2.me/theorems/eba154a9-e79e-432e-bd21-c50f14cd5adb
-- title:
--   LPSOriginal Integer Model Charts
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integer Model Charts, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerBaseFractionMap_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
def lpsOriginalJReciprocalPolynomialMap :
    Polynomial ℚ →+* FractionRing (Polynomial ℚ) :=
  (Polynomial.aeval
    ((algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X)⁻¹)).toRingHom
lemma lpsOriginalJReciprocalPolynomialMap_injective :
    Function.Injective lpsOriginalJReciprocalPolynomialMap := by
  apply transcendental_iff_injective.mp
  have hx : Transcendental ℚ
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X) :=
    (transcendental_algebraMap_iff
      (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).mpr
        (Polynomial.transcendental_X ℚ)
  exact fun h => hx (IsAlgebraic.inv_iff.mp h)
def lpsOriginalJFractionInversion :
    FractionRing (Polynomial ℚ) →+* FractionRing (Polynomial ℚ) :=
  IsFractionRing.lift lpsOriginalJReciprocalPolynomialMap_injective
lemma lpsOriginalJFractionInversion_polynomial (P : Polynomial ℚ) :
    lpsOriginalJFractionInversion
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P)=
        lpsOriginalJReciprocalPolynomialMap P :=
  IsFractionRing.lift_algebraMap _ P
lemma lpsOriginalJFractionInversion_X :
    lpsOriginalJFractionInversion
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X)=
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X)⁻¹ := by
  rw [lpsOriginalJFractionInversion_polynomial]
  exact Polynomial.aeval_X _
def lpsOriginalIntegerReciprocalBaseFractionMap :
    Polynomial ℤ →+* FractionRing (Polynomial ℚ) :=
  lpsOriginalJFractionInversion.comp lpsOriginalIntegerBaseFractionMap
def lpsOriginalIntegerReciprocalBaseToGeneratedField
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial ℤ →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).comp
    lpsOriginalIntegerReciprocalBaseFractionMap
lemma lpsOriginalIntegerBaseFractionMap_X_ne_zero :
    lpsOriginalIntegerBaseFractionMap Polynomial.X≠0 :=
  (map_ne_zero_iff _ lpsOriginalIntegerBaseFractionMap_injective).mpr
    Polynomial.X_ne_zero
lemma lpsOriginalIntegerBaseFractionMap_powers_unit
    (s : Submonoid.powers (Polynomial.X : Polynomial ℤ)) :
    IsUnit (lpsOriginalIntegerBaseFractionMap s) := by
  obtain ⟨n,hn⟩ := s.property
  rw [←hn,map_pow]
  exact (IsUnit.mk0 _ lpsOriginalIntegerBaseFractionMap_X_ne_zero).pow n
def lpsOriginalIntegerLaurentBaseFractionMap :
    LaurentPolynomial ℤ →+* FractionRing (Polynomial ℚ) :=
  IsLocalization.lift (S := LaurentPolynomial ℤ)
    (lpsOriginalIntegerBaseFractionMap_powers_unit)
lemma lpsOriginalIntegerLaurentBaseFractionMap_polynomial (P : Polynomial ℤ) :
    lpsOriginalIntegerLaurentBaseFractionMap (Polynomial.toLaurent P)=
      lpsOriginalIntegerBaseFractionMap P :=
  IsLocalization.lift_eq _ P
lemma lpsOriginalIntegerLaurentBaseFractionMap_T_one :
    lpsOriginalIntegerLaurentBaseFractionMap (LaurentPolynomial.T 1)=
      lpsOriginalIntegerBaseFractionMap Polynomial.X := by
  rw [←Polynomial.toLaurent_X,lpsOriginalIntegerLaurentBaseFractionMap_polynomial]
lemma lpsOriginalIntegerLaurentBaseFractionMap_T_neg_one :
    lpsOriginalIntegerLaurentBaseFractionMap (LaurentPolynomial.T (-1))=
      (lpsOriginalIntegerBaseFractionMap Polynomial.X)⁻¹ := by
  have h : lpsOriginalIntegerBaseFractionMap Polynomial.X *
      lpsOriginalIntegerLaurentBaseFractionMap (LaurentPolynomial.T (-1))=1 := by
    rw [←lpsOriginalIntegerLaurentBaseFractionMap_T_one,←map_mul,
      ←LaurentPolynomial.T_add]
    simp
  apply (mul_left_cancel₀ lpsOriginalIntegerBaseFractionMap_X_ne_zero)
  rw [h,mul_inv_cancel₀ lpsOriginalIntegerBaseFractionMap_X_ne_zero]
lemma lpsOriginalIntegerLaurentBaseFractionMap_reciprocalPolynomial
    (P : Polynomial ℤ) :
    lpsOriginalIntegerLaurentBaseFractionMap
      (LaurentPolynomial.invert (Polynomial.toLaurent P))=
        lpsOriginalIntegerReciprocalBaseFractionMap P := by
  have h : lpsOriginalIntegerLaurentBaseFractionMap.comp
      ((LaurentPolynomial.invert (R := ℤ)).toRingHom.comp Polynomial.toLaurent)=
        lpsOriginalIntegerReciprocalBaseFractionMap := by
    apply Polynomial.ringHom_ext
    · intro z
      change lpsOriginalIntegerLaurentBaseFractionMap
        (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C z)))=_
      rw [Polynomial.toLaurent_C,LaurentPolynomial.invert_C,
        ←Polynomial.toLaurent_C,lpsOriginalIntegerLaurentBaseFractionMap_polynomial]
      change lpsOriginalIntegerBaseFractionMap (Polynomial.C z)=
        lpsOriginalJFractionInversion
          (lpsOriginalIntegerBaseFractionMap (Polynomial.C z))
      simp [lpsOriginalIntegerBaseFractionMap]
    · change lpsOriginalIntegerLaurentBaseFractionMap
        (LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X))=_
      rw [Polynomial.toLaurent_X,LaurentPolynomial.invert_T,
        lpsOriginalIntegerLaurentBaseFractionMap_T_neg_one]
      change (lpsOriginalIntegerBaseFractionMap Polynomial.X)⁻¹=
        lpsOriginalJFractionInversion (lpsOriginalIntegerBaseFractionMap Polynomial.X)
      simp only [lpsOriginalIntegerBaseFractionMap,RingHom.comp_apply,
        Polynomial.coe_mapRingHom,Polynomial.map_X]
      exact lpsOriginalJFractionInversion_X.symm
  exact RingHom.congr_fun h P
def lpsOriginalIntegerLaurentBaseToGeneratedField
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    LaurentPolynomial ℤ →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).comp
    lpsOriginalIntegerLaurentBaseFractionMap
lemma lpsOriginalIntegerLaurentBaseToGeneratedField_polynomial
    (N : ℕ) (hN : 0<N) (P : Polynomial ℤ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerLaurentBaseToGeneratedField N hN (Polynomial.toLaurent P)=
      lpsOriginalIntegerBaseToGeneratedField N hN P := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalIntegerLaurentBaseFractionMap (Polynomial.toLaurent P))=_
  rw [lpsOriginalIntegerLaurentBaseFractionMap_polynomial]
  rfl
lemma lpsOriginalIntegerLaurentBase_scalarTower
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    IsScalarTower (Polynomial ℤ) (LaurentPolynomial ℤ)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  exact .of_algebraMap_eq' (RingHom.ext
    (lpsOriginalIntegerLaurentBaseToGeneratedField_polynomial N hN)).symm
def lpsOriginalIntegerNormalChartToOverlap
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) →+*
      integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  letI := lpsOriginalIntegerLaurentBase_scalarTower N hN
  exact
    { toFun := fun x => ⟨x.val,x.property.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
def lpsOriginalIntegerReciprocalLaurentPolynomialMap :
    Polynomial ℤ →+* LaurentPolynomial ℤ :=
  (LaurentPolynomial.invert (R := ℤ)).toRingHom.comp Polynomial.toLaurent
lemma lpsOriginalIntegerReciprocalLaurentBaseToGeneratedField_polynomial
    (N : ℕ) (hN : 0<N) (P : Polynomial ℤ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    lpsOriginalIntegerLaurentBaseToGeneratedField N hN
      (lpsOriginalIntegerReciprocalLaurentPolynomialMap P)=
      lpsOriginalIntegerReciprocalBaseToGeneratedField N hN P := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalIntegerLaurentBaseFractionMap
      (LaurentPolynomial.invert (Polynomial.toLaurent P)))=_
  rw [lpsOriginalIntegerLaurentBaseFractionMap_reciprocalPolynomial]
  rfl
lemma lpsOriginalIntegerReciprocalLaurentBase_scalarTower
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    IsScalarTower (Polynomial ℤ) (LaurentPolynomial ℤ)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  exact .of_algebraMap_eq' (RingHom.ext
    (lpsOriginalIntegerReciprocalLaurentBaseToGeneratedField_polynomial N hN)).symm
def lpsOriginalIntegerReciprocalNormalChartToOverlap
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) →+*
      integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  letI := lpsOriginalIntegerReciprocalLaurentBase_scalarTower N hN
  exact
    { toFun := fun x => ⟨x.val,x.property.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
end
end QEC.Coding.TannerLiftedProduct


