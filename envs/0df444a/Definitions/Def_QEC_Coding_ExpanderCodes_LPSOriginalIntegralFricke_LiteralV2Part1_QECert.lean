-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part1_QECert
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part1_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:14:19.319878+00:00
-- url     : https://prove2.me/theorems/c4ee9488-2739-4268-9e2b-9695a7312ee0
-- title:
--   Fricke integral construction: literal segment 1
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integral Fricke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Reverse
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerAffineToNormal_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_cover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_openImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedOverlap_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_proper
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBaseFractionMap_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalNormalOverlap_localization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
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
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
def lpsOriginalRationalFrickePullback (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let f := lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
    (lpsOriginalFrickeMatrix_pos N hN)
  exact
    { toFun := fun x => ⟨f x, by
        have hm := Subfield.map_mem_map f.toRingHom
          (s := (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield) (x := x)
        rw [lpsOriginalGeneratedFunctionFieldQ_fricke_map] at hm
        exact hm.mpr x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f (x : LPSOriginalHolomorphicFractionField) (y : LPSOriginalHolomorphicFractionField))
      map_zero' := Subtype.ext (map_zero f)
      map_add' := fun x y => Subtype.ext (map_add f (x : LPSOriginalHolomorphicFractionField) (y : LPSOriginalHolomorphicFractionField)) }
lemma lpsOriginalRationalFrickePullback_coe (N : ℕ) (hN : 0 < N)
    (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalFrickePullback N hN x : lpsOriginalGeneratedFunctionFieldQ N hN) :
      LPSOriginalHolomorphicFractionField) =
    lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
      (lpsOriginalFrickeMatrix_pos N hN) x := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rfl
lemma lpsOriginalRationalFrickePullback_involutive (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Function.Involutive (lpsOriginalRationalFrickePullback N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let f := lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
    (lpsOriginalFrickeMatrix_pos N hN)
  have hg : Set.EqOn (f.toRingHom.comp f.toRingHom)
      (RingHom.id LPSOriginalHolomorphicFractionField)
      {lpsOriginalJInFractionField, lpsOriginalJNInFractionField N hN} := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with hy | hy
    · subst y
      change f (f lpsOriginalJInFractionField) = lpsOriginalJInFractionField
      simp only [f, lpsOriginalPositiveFractionPullback_fricke_j,
        lpsOriginalPositiveFractionPullback_fricke_jN]
    · have he := Set.mem_singleton_iff.mp hy
      subst y
      change f (f (lpsOriginalJNInFractionField N hN)) = lpsOriginalJNInFractionField N hN
      simp only [f, lpsOriginalPositiveFractionPullback_fricke_jN,
        lpsOriginalPositiveFractionPullback_fricke_j]
  intro x
  apply Subtype.ext
  change f (f (x : LPSOriginalHolomorphicFractionField)) = (x : LPSOriginalHolomorphicFractionField)
  apply RingHom.eqOn_field_closure hg
  rw [← lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure N hN]
  exact x.property
def lpsOriginalRationalFrickeEquiv (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN ≃+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let f := lpsOriginalRationalFrickePullback N hN
  exact
    { toFun := f
      invFun := f
      left_inv := lpsOriginalRationalFrickePullback_involutive N hN
      right_inv := lpsOriginalRationalFrickePullback_involutive N hN
      map_mul' := f.map_mul
      map_add' := f.map_add }
lemma lpsOriginalIntegerBaseToGeneratedField_X_coe (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalIntegerBaseToGeneratedField N hN Polynomial.X :
      lpsOriginalGeneratedFunctionFieldQ N hN) : LPSOriginalHolomorphicFractionField) =
        lpsOriginalJInFractionField := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change lpsOriginalJFractionEmbeddingQ (lpsOriginalIntegerBaseFractionMap Polynomial.X) = _
  rw [lpsOriginalIntegerBaseFractionMap, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.map_X, lpsOriginalJFractionEmbeddingQ_polynomial,
    lpsOriginalJHolomorphicEvalQ_localization]
  simp [lpsOriginalJInFractionField]
def lpsOriginalIntegerFrickeCoefficientMap (N : ℕ) [NeZero N] (hN : 0 < N) :
    Polynomial ℤ →+* lpsOriginalIntegerNormalZeroChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact Polynomial.eval₂RingHom (Int.castRingHom _)
    (lpsOriginalIntegerAffineToNormal N hN (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN)))
lemma lpsOriginalIntegerFrickeCoefficientMap_compatibility
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    (algebraMap (lpsOriginalIntegerNormalZeroChart N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN)).comp
      (lpsOriginalIntegerFrickeCoefficientMap N hN) =
    (lpsOriginalRationalFrickePullback N hN).comp
      (lpsOriginalIntegerBaseToGeneratedField N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalIntegerFrickeCoefficientMap]
  · apply Subtype.ext
    simp only [RingHom.comp_apply, lpsOriginalIntegerFrickeCoefficientMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change ((lpsOriginalIntegerAffineToNormal N hN
      (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN))).val.val) =
      ((lpsOriginalRationalFrickePullback N hN
        (lpsOriginalIntegerBaseToGeneratedField N hN Polynomial.X) :
          lpsOriginalGeneratedFunctionFieldQ N hN) : LPSOriginalHolomorphicFractionField)
    rw [lpsOriginalIntegerAffineToNormal_root]
    rw [lpsOriginalRationalFrickePullback_coe,
      lpsOriginalIntegerBaseToGeneratedField_X_coe,
      lpsOriginalPositiveFractionPullback_fricke_j]
lemma lpsOriginalIntegerFricke_preserves_normalZero
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (x : lpsOriginalIntegerNormalZeroChart N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    IsIntegral (Polynomial ℤ)
      (lpsOriginalRationalFrickePullback N hN (x : lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  have h := IsIntegral.map_of_comp_eq (lpsOriginalIntegerFrickeCoefficientMap N hN)
    (lpsOriginalRationalFrickePullback N hN)
    (lpsOriginalIntegerFrickeCoefficientMap_compatibility N hN) x.property
  exact isIntegral_trans (R := Polynomial ℤ) _ h
def lpsOriginalIntegerNormalZeroFrickePullback
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalZeroChart N hN →+* lpsOriginalIntegerNormalZeroChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact
    { toFun := fun x => ⟨lpsOriginalRationalFrickePullback N hN x.val,
        lpsOriginalIntegerFricke_preserves_normalZero N hN x⟩
      map_one' := Subtype.ext (map_one (lpsOriginalRationalFrickePullback N hN))
      map_mul' := fun x y => Subtype.ext (map_mul (lpsOriginalRationalFrickePullback N hN) x.val y.val)
      map_zero' := Subtype.ext (map_zero (lpsOriginalRationalFrickePullback N hN))
      map_add' := fun x y => Subtype.ext (map_add (lpsOriginalRationalFrickePullback N hN) x.val y.val) }
end
end QEC.Coding.TannerLiftedProduct


