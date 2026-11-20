-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T11:37:42.89798+00:00
-- url     : https://prove2.me/theorems/c03b3efb-f363-48f9-b11c-e9c83623850e
-- title:
--   LPSOriginal Relative Gauss Fricke
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Fricke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFricke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondResidueDegrees
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineToGenerated_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeToGenerated_base_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationRoot_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_root
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
def lpsOriginalRelativeGaussNormalizationFrickeCoefficientMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalGaussBase p →+* LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).comp
    (lpsOriginalGaussFrickeBaseMap N hN p hpN)
lemma lpsOriginalRelativeGaussNormalizationFrickeCoefficientMap_generatedDiagram
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    (algebraMap (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))).comp
      (lpsOriginalRelativeGaussNormalizationFrickeCoefficientMap N p hNp h4N hN hpN) =
        (lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)).comp
          (algebraMap (LPSOriginalGaussBase p)
            (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · apply Subtype.ext
    change (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
      (lpsOriginalGaussFrickeBaseMap N hN p hpN
        (algebraMap (Polynomial ℤ) A Polynomial.X))).val.val =
      (lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)
        (algebraMap A L (algebraMap (Polynomial ℤ) A Polynomial.X))).val
    rw [lpsOriginalGaussFrickeBaseMap_integer, Polynomial.eval₂_X,
      lpsOriginalRelativeGaussNormalizationSecondOrderMap_root,
      lpsOriginalRelativeGaussNormalizationRoot_coe, lpsOriginalRationalFrickePullback_coe]
    have hj : (algebraMap A L (algebraMap (Polynomial ℤ) A Polynomial.X)).val =
        lpsOriginalJInFractionField := by
      change (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN
        (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)
          (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
            (algebraMap (Polynomial ℤ) A Polynomial.X)))).val = _
      rw [lpsOriginalRelativeGaussHeckeToGenerated_base_coe,
        lpsOriginalGaussAffineToGenerated_j]
    rw [hj, lpsOriginalPositiveFractionPullback_fricke_j]
lemma lpsOriginalRelativeGaussFricke_preserves_normalization
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (x : LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    IsIntegral (LPSOriginalGaussBase p)
      (lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos) x.val) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  have h := IsIntegral.map_of_comp_eq
    (lpsOriginalRelativeGaussNormalizationFrickeCoefficientMap N p hNp h4N hN hpN)
    (lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))
    (lpsOriginalRelativeGaussNormalizationFrickeCoefficientMap_generatedDiagram N p hNp h4N hN hpN)
    x.property
  exact isIntegral_trans (R := A) _ h
def lpsOriginalRelativeGaussNormalizationFrickePullback
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+*
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  let f := lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  exact { toFun := fun x => ⟨f x.val,
            lpsOriginalRelativeGaussFricke_preserves_normalization N p hNp h4N hN hpN x⟩
          map_one' := Subtype.ext (map_one f)
          map_mul' := fun x y => Subtype.ext (map_mul f x.val y.val)
          map_zero' := Subtype.ext (map_zero f)
          map_add' := fun x y => Subtype.ext (map_add f x.val y.val) }
lemma lpsOriginalRelativeGaussNormalizationFrickePullback_involutive
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    Function.Involutive (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  intro x
  apply Subtype.ext
  exact lpsOriginalRationalFrickePullback_involutive (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos) x.val
def lpsOriginalRelativeGaussNormalizationFrickeRingEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN ≃+*
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  RingEquiv.ofBijective (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationFrickePullback_involutive N p hNp h4N hN hpN).bijective
end
end QEC.Coding.TannerLiftedProduct


