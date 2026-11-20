-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part2_QECert
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part2_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:18:29.370179+00:00
-- url     : https://prove2.me/theorems/b2659fa1-0786-45aa-938d-8c8adc61be75
-- title:
--   Fricke integral construction: literal segment 2
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integral Fricke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part1_QECert
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
lemma lpsOriginalBivariateSwap_coeff_zero_zero (P : Polynomial (Polynomial ℤ)) :
    ((Polynomial.Bivariate.swap P).coeff 0).coeff 0 = (P.coeff 0).coeff 0 := by
  have h := Polynomial.Bivariate.aevalAeval_swap (R := ℤ) (A := ℤ) (0 : ℤ) 0 P
  simpa only [Polynomial.coe_aevalAeval_eq_evalEval, Polynomial.evalEval,
    Polynomial.C_0, ← Polynomial.coeff_zero_eq_eval_zero] using h
def lpsOriginalIntegerFrickeReciprocalDenominator (P : Polynomial (Polynomial ℤ)) :
    Polynomial ℤ := (Polynomial.Bivariate.swap P.reverse).coeff 0
def lpsOriginalIntegerFrickeReciprocalPolynomial (P : Polynomial (Polynomial ℤ)) :
    Polynomial (Polynomial ℤ) := (Polynomial.Bivariate.swap P.reverse).reverse
lemma lpsOriginalIntegerFrickeReciprocalDenominator_coeff_zero
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) :
    (lpsOriginalIntegerFrickeReciprocalDenominator P).coeff 0 = 1 := by
  rw [lpsOriginalIntegerFrickeReciprocalDenominator,
    lpsOriginalBivariateSwap_coeff_zero_zero, Polynomial.coeff_zero_reverse, hP.leadingCoeff]
  simp
lemma lpsOriginalIntegerFrickeReciprocalDenominator_ne_zero
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) :
    lpsOriginalIntegerFrickeReciprocalDenominator P ≠ 0 := by
  intro h
  have hc := lpsOriginalIntegerFrickeReciprocalDenominator_coeff_zero P hP
  rw [h, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc
lemma lpsOriginalIntegerFrickeReciprocalPolynomial_leadingCoeff
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) :
    (lpsOriginalIntegerFrickeReciprocalPolynomial P).leadingCoeff =
      lpsOriginalIntegerFrickeReciprocalDenominator P := by
  rw [lpsOriginalIntegerFrickeReciprocalPolynomial, Polynomial.reverse_leadingCoeff,
    Polynomial.trailingCoeff_eq_coeff_zero
      (lpsOriginalIntegerFrickeReciprocalDenominator_ne_zero P hP)]
  rfl
lemma lpsOriginalIntegerFrickeReciprocalDenominator_coprime_X
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) :
    IsCoprime Polynomial.X (lpsOriginalIntegerFrickeReciprocalDenominator P) := by
  have hd := Polynomial.X_dvd_sub_C (p := lpsOriginalIntegerFrickeReciprocalDenominator P)
  rw [lpsOriginalIntegerFrickeReciprocalDenominator_coeff_zero P hP, Polynomial.C_1] at hd
  simpa only [sub_add_cancel] using IsCoprime.add_one_right_of_dvd hd
lemma lpsOriginalBivariateAevalAeval_eq_eval2 {S : Type*} [CommRing S]
    (x y : S) (P : Polynomial (Polynomial ℤ)) :
    Polynomial.aevalAeval x y P =
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x) y := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, Polynomial.eval₂_add, hP, hQ]
  | monomial n p =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, Polynomial.aevalAeval_C,
      Polynomial.aevalAeval_Y, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_pow, Polynomial.eval₂_X]
    congr 1
lemma lpsOriginalBivariateSwap_eval2 {S : Type*} [CommRing S]
    (x y : S) (P : Polynomial (Polynomial ℤ)) :
    (Polynomial.Bivariate.swap P).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom S) x) y =
    P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) y) x := by
  rw [← lpsOriginalBivariateAevalAeval_eq_eval2,
    Polynomial.Bivariate.aevalAeval_swap, lpsOriginalBivariateAevalAeval_eq_eval2]
lemma lpsOriginalBivariateIntegerCoefficientEval_comp {S : Type*} [CommRing S]
    (f : S →+* S) (x : S) :
    f.comp (Polynomial.eval₂RingHom (Int.castRingHom S) x) =
      Polynomial.eval₂RingHom (Int.castRingHom S) (f x) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp
lemma lpsOriginalIntegerFrickeReciprocalPolynomial_root_iff
    {S : Type*} [Field S] (P : Polynomial (Polynomial ℤ))
    (x y : S) (hx : x ≠ 0) (hy : y ≠ 0) :
    (lpsOriginalIntegerFrickeReciprocalPolynomial P).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom S) x⁻¹) y⁻¹ = 0 ↔
    P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) y) x = 0 := by
  let := invertibleOfNonzero hx
  let := invertibleOfNonzero hy
  have h₁ := Polynomial.eval₂_reverse_eq_zero_iff
    (Polynomial.eval₂RingHom (Int.castRingHom S) x⁻¹) y
    (Polynomial.Bivariate.swap P.reverse)
  have h₂ := Polynomial.eval₂_reverse_eq_zero_iff
    (Polynomial.eval₂RingHom (Int.castRingHom S) y) x P
  simp only [invOf_eq_inv] at h₁ h₂
  rw [lpsOriginalIntegerFrickeReciprocalPolynomial, h₁,
    lpsOriginalBivariateSwap_eval2, h₂]
lemma lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerBaseToGeneratedField N hN Polynomial.X =
      lpsOriginalRationalJElement N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalIntegerBaseFractionMap Polynomial.X) =
    algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X)
  congr 1
  simp [lpsOriginalIntegerBaseFractionMap]
def lpsOriginalRationalJNElement (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact lpsOriginalIntegerAffineToGenerated N hN
    (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN))
lemma lpsOriginalRationalJElement_coe (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalJElement N hN : lpsOriginalGeneratedFunctionFieldQ N hN) :
      LPSOriginalHolomorphicFractionField) = lpsOriginalJInFractionField := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [← lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ N hN]
  exact lpsOriginalIntegerBaseToGeneratedField_X_coe N hN
lemma lpsOriginalRationalJNElement_coe (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalJNElement N hN : lpsOriginalGeneratedFunctionFieldQ N hN) :
      LPSOriginalHolomorphicFractionField) = lpsOriginalJNInFractionField N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact lpsOriginalIntegerAffineToNormal_root N hN
lemma lpsOriginalIntegerBaseToGeneratedField_eq_eval (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerBaseToGeneratedField N hN =
      Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJElement N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simpa using lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ N hN
lemma lpsOriginalRationalFrickePullback_JElement
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalFrickePullback N hN (lpsOriginalRationalJElement N hN) =
      lpsOriginalRationalJNElement N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Subtype.ext
  rw [lpsOriginalRationalFrickePullback_coe, lpsOriginalRationalJElement_coe,
    lpsOriginalRationalJNElement_coe, lpsOriginalPositiveFractionPullback_fricke_j]
lemma lpsOriginalRationalFrickePullback_JNElement
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalFrickePullback N hN (lpsOriginalRationalJNElement N hN) =
      lpsOriginalRationalJElement N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Subtype.ext
  rw [lpsOriginalRationalFrickePullback_coe, lpsOriginalRationalJNElement_coe,
    lpsOriginalRationalJElement_coe, lpsOriginalPositiveFractionPullback_fricke_jN]
lemma lpsOriginalRationalJElement_ne_zero (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalJElement N hN ≠ 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [← lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ N hN]
  change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalIntegerBaseFractionMap Polynomial.X) ≠ 0
  exact (map_ne_zero_iff _ (algebraMap (FractionRing (Polynomial ℚ))
    (lpsOriginalGeneratedFunctionFieldQ N hN)).injective).mpr
      lpsOriginalIntegerBaseFractionMap_X_ne_zero
lemma lpsOriginalRationalJNElement_ne_zero (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalJNElement N hN ≠ 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [← lpsOriginalRationalFrickePullback_JElement N hN]
  exact (map_ne_zero_iff _ (lpsOriginalRationalFrickePullback N hN).injective).mpr
    (lpsOriginalRationalJElement_ne_zero N hN)
lemma lpsOriginalIntegerPolynomial_generatedRoot (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJElement N hN))
      (lpsOriginalRationalJNElement N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let f := lpsOriginalIntegerAffineToGenerated N hN
  have hc : f.comp (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN)) =
      lpsOriginalIntegerBaseToGeneratedField N hN := by
    apply RingHom.ext
    intro P
    exact lpsOriginalIntegerAffineToGenerated_base N hN P
  have h := congrArg f (AdjoinRoot.eval₂_root (lpsOriginalIntegerPolynomial N hN))
  rw [Polynomial.hom_eval₂, map_zero, hc, lpsOriginalIntegerBaseToGeneratedField_eq_eval] at h
  exact h
lemma lpsOriginalIntegerPolynomial_frickeSwappedRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJNElement N hN))
      (lpsOriginalRationalJElement N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  have h := congrArg (lpsOriginalRationalFrickePullback N hN)
    (lpsOriginalIntegerPolynomial_generatedRoot N hN)
  rw [Polynomial.hom_eval₂, map_zero, lpsOriginalBivariateIntegerCoefficientEval_comp,
    lpsOriginalRationalFrickePullback_JElement, lpsOriginalRationalFrickePullback_JNElement] at h
  exact h
lemma lpsOriginalIntegerFrickeOriginalReciprocalRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerFrickeReciprocalPolynomial (lpsOriginalIntegerPolynomial N hN)).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJElement N hN)⁻¹)
      (lpsOriginalRationalJNElement N hN)⁻¹ = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalIntegerFrickeReciprocalPolynomial_root_iff _ _ _
    (lpsOriginalRationalJElement_ne_zero N hN)
    (lpsOriginalRationalJNElement_ne_zero N hN)).mpr
      (lpsOriginalIntegerPolynomial_frickeSwappedRoot N hN)
lemma lpsOriginalIntegerReciprocalBaseToGeneratedField_injective
    (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Function.Injective (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).injective.comp
    lpsOriginalIntegerReciprocalBaseFractionMap_injective
lemma lpsOriginalIntegerReciprocalBaseToGeneratedField_eq_eval
    (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerReciprocalBaseToGeneratedField N hN =
      Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJElement N hN)⁻¹ := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalJFractionInversion (lpsOriginalIntegerBaseFractionMap Polynomial.X)) = _
    have hx : lpsOriginalIntegerBaseFractionMap Polynomial.X =
        algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X := by
      simp [lpsOriginalIntegerBaseFractionMap]
    rw [hx, lpsOriginalJFractionInversion_X, map_inv₀]
    rfl
abbrev lpsOriginalIntegerFrickeLocalizedBase (N : ℕ) [NeZero N] (hN : 0 < N) :=
  Localization.Away (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN))
def lpsOriginalIntegerFrickeLocalizedBaseMap (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerFrickeLocalizedBase N hN →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let q := lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)
  let f := lpsOriginalIntegerReciprocalBaseToGeneratedField N hN
  have hq : f q ≠ 0 :=
    (map_ne_zero_iff f (lpsOriginalIntegerReciprocalBaseToGeneratedField_injective N hN)).mpr
      (lpsOriginalIntegerFrickeReciprocalDenominator_ne_zero _
        (lpsOriginalIntegerPolynomial_monic N hN))
  exact IsLocalization.Away.lift q (IsUnit.mk0 _ hq)
lemma lpsOriginalIntegerFrickeLocalizedBaseMap_comp
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).comp
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerFrickeLocalizedBase N hN)) =
      lpsOriginalIntegerReciprocalBaseToGeneratedField N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  simp [lpsOriginalIntegerFrickeLocalizedBaseMap]
lemma lpsOriginalIntegerFrickeLocalizedDenominator_ne_zero
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    algebraMap (Polynomial ℤ) (lpsOriginalIntegerFrickeLocalizedBase N hN)
      (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)) ≠ 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let q := lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)
  let f := lpsOriginalIntegerFrickeLocalizedBaseMap N hN
  have hq : lpsOriginalIntegerReciprocalBaseToGeneratedField N hN q ≠ 0 :=
    (map_ne_zero_iff _ (lpsOriginalIntegerReciprocalBaseToGeneratedField_injective N hN)).mpr
      (lpsOriginalIntegerFrickeReciprocalDenominator_ne_zero _
        (lpsOriginalIntegerPolynomial_monic N hN))
  intro h
  have he := RingHom.congr_fun (lpsOriginalIntegerFrickeLocalizedBaseMap_comp N hN) q
  exact hq (he.symm.trans ((congrArg f h).trans (map_zero f)))
def lpsOriginalIntegerFrickeLocalizedMonicPolynomial
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Polynomial (lpsOriginalIntegerFrickeLocalizedBase N hN) := by
  let q := lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)
  exact (lpsOriginalIntegerFrickeReciprocalPolynomial (lpsOriginalIntegerPolynomial N hN)).map
    (algebraMap (Polynomial ℤ) (lpsOriginalIntegerFrickeLocalizedBase N hN)) *
    Polynomial.C (IsLocalization.Away.invSelf q : lpsOriginalIntegerFrickeLocalizedBase N hN)
lemma lpsOriginalIntegerFrickeLocalizedMonicPolynomial_monic
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerFrickeLocalizedMonicPolynomial N hN).Monic := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : Nontrivial (lpsOriginalIntegerFrickeLocalizedBase N hN) :=
    (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).domain_nontrivial
  let q := lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)
  let A := lpsOriginalIntegerFrickeLocalizedBase N hN
  let g := algebraMap (Polynomial ℤ) A
  let P := lpsOriginalIntegerFrickeReciprocalPolynomial (lpsOriginalIntegerPolynomial N hN)
  have hP : P.leadingCoeff = q :=
    lpsOriginalIntegerFrickeReciprocalPolynomial_leadingCoeff _ (lpsOriginalIntegerPolynomial_monic N hN)
  have hq : g q ≠ 0 := lpsOriginalIntegerFrickeLocalizedDenominator_ne_zero N hN
  have hl : (P.map g).leadingCoeff = g q := by
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ (by rw [hP]; exact hq), hP]
  have hi : IsUnit (IsLocalization.Away.invSelf q : A) := by
    refine ⟨⟨IsLocalization.Away.invSelf q, g q, ?_, ?_⟩, rfl⟩
    · simpa only [mul_comm] using (IsLocalization.Away.mul_invSelf q : g q * IsLocalization.Away.invSelf q = 1)
    · exact IsLocalization.Away.mul_invSelf q
  change ((P.map g) * Polynomial.C (IsLocalization.Away.invSelf q : A)).leadingCoeff = 1
  rw [Polynomial.leadingCoeff_mul_C_of_isUnit hi, hl]
  exact IsLocalization.Away.mul_invSelf q
lemma lpsOriginalIntegerFrickeLocalizedMonicPolynomial_root
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerFrickeLocalizedMonicPolynomial N hN).eval₂
      (lpsOriginalIntegerFrickeLocalizedBaseMap N hN) (lpsOriginalRationalJNElement N hN)⁻¹ = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalIntegerFrickeLocalizedMonicPolynomial, Polynomial.eval₂_mul,
    Polynomial.eval₂_map, Polynomial.eval₂_C, lpsOriginalIntegerFrickeLocalizedBaseMap_comp,
    lpsOriginalIntegerReciprocalBaseToGeneratedField_eq_eval,
    lpsOriginalIntegerFrickeOriginalReciprocalRoot, zero_mul]
lemma lpsOriginalIntegerFrickeLocalizedInverseJN_integral
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
    IsIntegral (lpsOriginalIntegerFrickeLocalizedBase N hN) (lpsOriginalRationalJNElement N hN)⁻¹ := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  refine ⟨lpsOriginalIntegerFrickeLocalizedMonicPolynomial N hN,
    lpsOriginalIntegerFrickeLocalizedMonicPolynomial_monic N hN, ?_⟩
  exact lpsOriginalIntegerFrickeLocalizedMonicPolynomial_root N hN
lemma lpsOriginalIntegerFrickeLocalizedBase_scalarTower
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
    IsScalarTower (Polynomial ℤ) (lpsOriginalIntegerFrickeLocalizedBase N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    (lpsOriginalIntegerFrickeLocalizedBaseMap_comp N hN).symm
abbrev lpsOriginalIntegerFrickeLocalizedNormalChart
    (N : ℕ) [NeZero N] (hN : 0 < N) : Type :=
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  integralClosure (lpsOriginalIntegerFrickeLocalizedBase N hN)
    (lpsOriginalGeneratedFunctionFieldQ N hN)
end
end QEC.Coding.TannerLiftedProduct


