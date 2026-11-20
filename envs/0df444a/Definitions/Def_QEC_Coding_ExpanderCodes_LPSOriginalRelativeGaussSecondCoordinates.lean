-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:32:43.417033+00:00
-- url     : https://prove2.me/theorems/5e6d1d6e-6cd7-41ec-93c3-2bf3a583dbae
-- title:
--   LPSOriginal Relative Gauss Second Coordinates
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Second Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondCoordinates.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalHeckePullback_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeToGenerated_base_coe
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
noncomputable section
lemma lpsOriginalBivariateIntegerCoefficientEval_comp_hom
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    f.comp (Polynomial.eval₂RingHom (Int.castRingHom R) x) =
      Polynomial.eval₂RingHom (Int.castRingHom S) (f x) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp
lemma lpsOriginalIntegerPolynomial_ambientRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
        lpsOriginalJInFractionField) (lpsOriginalJNInFractionField N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  have h := congrArg (lpsOriginalGeneratedFunctionFieldQ N hN).val.toRingHom
    (lpsOriginalIntegerPolynomial_generatedRoot N hN)
  rw [Polynomial.hom_eval₂, map_zero,
    lpsOriginalBivariateIntegerCoefficientEval_comp_hom] at h
  change (lpsOriginalIntegerPolynomial N hN).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
      (lpsOriginalRationalJElement N hN).val)
    (lpsOriginalRationalJNElement N hN).val = 0 at h
  simpa only [lpsOriginalRationalJElement_coe, lpsOriginalRationalJNElement_coe] using h
def lpsOriginalRelativeGaussSecondJField
    (N p : ℕ) [NeZero N] [NeZero p] (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact lpsOriginalRationalHeckePullback N p hN hp h4N
    (lpsOriginalRationalJElement N hN)
lemma lpsOriginalRelativeGaussSecondJField_coe
    (N p : ℕ) [NeZero N] [NeZero p] (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalRelativeGaussSecondJField N p h4N hN hp).val =
      lpsOriginalJNInFractionField p hp := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRelativeGaussSecondJField, lpsOriginalRationalHeckePullback_coe,
    lpsOriginalRationalJElement_coe, lpsOriginalDilationFractionPullback_j]
lemma lpsOriginalRelativeGaussSecondJField_primeRoot
    (N p : ℕ) [NeZero N] [NeZero p] (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerPolynomial p hp).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalRationalJElement (N*p) (Nat.mul_pos hN hp)))
      (lpsOriginalRelativeGaussSecondJField N p h4N hN hp) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).val.injective
  rw [map_zero, Polynomial.hom_eval₂,
    lpsOriginalBivariateIntegerCoefficientEval_comp_hom]
  change (lpsOriginalIntegerPolynomial p hp).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
      (lpsOriginalRationalJElement (N*p) (Nat.mul_pos hN hp)).val)
    (lpsOriginalRelativeGaussSecondJField N p h4N hN hp).val = 0
  rw [lpsOriginalRationalJElement_coe, lpsOriginalRelativeGaussSecondJField_coe]
  exact lpsOriginalIntegerPolynomial_ambientRoot p hp
lemma lpsOriginalRelativeGaussBase_integerDiagram
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalRationalJElement (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    apply (lpsOriginalGeneratedFunctionFieldQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).val.injective
    change (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)
        (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
          (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)))).val =
      (lpsOriginalRationalJElement (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)).val
    rw [lpsOriginalRationalJElement_coe,lpsOriginalRelativeGaussHeckeToGenerated_base_coe]
    change (lpsOriginalGaussBaseToGeneratedField N hN p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)).val = _
    rw [lpsOriginalGaussBaseToGeneratedField_base]
    exact lpsOriginalIntegerBaseToGeneratedField_X_coe N hN
lemma lpsOriginalRelativeGaussSecondJField_integral
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    IsIntegral (LPSOriginalGaussBase p)
      (lpsOriginalRelativeGaussSecondJField N p h4N hN (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
  refine ⟨(lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)),
    (lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).map _, ?_⟩
  rw [Polynomial.eval₂_map]
  change (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
    (((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)))
    (lpsOriginalRelativeGaussSecondJField N p h4N hN (Fact.out : p.Prime).pos) = 0
  rw [lpsOriginalRelativeGaussBase_integerDiagram]
  exact lpsOriginalRelativeGaussSecondJField_primeRoot N p h4N hN (Fact.out : p.Prime).pos
def lpsOriginalRelativeGaussNormalizationSecondJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  ⟨lpsOriginalRelativeGaussSecondJField N p h4N hN (Fact.out : p.Prime).pos,
    lpsOriginalRelativeGaussSecondJField_integral N p hNp h4N hN⟩
def lpsOriginalRelativeGaussNormalizationFirstJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN
    (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))
end
end QEC.Coding.TannerLiftedProduct


