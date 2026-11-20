-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T11:13:22.892124+00:00
-- url     : https://prove2.me/theorems/23081e06-519e-4f36-82c0-3deecdc5a553
-- title:
--   LPSOriginal Relative Gauss Second Order Map
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Second Order Map, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondInteger_isUnit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondLevelRoot
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
def lpsOriginalRelativeGaussNormalizationSecondBaseMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalGaussBase p →+* LPSOriginalRelativeGaussNormalization N p hNp h4N hN := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  exact IsLocalization.lift (M := (lpsOriginalGaussPrime p).primeCompl) (S := LPSOriginalGaussBase p)
    (g := Polynomial.eval₂RingHom (Int.castRingHom _)
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))
    (fun s => lpsOriginalRelativeGaussNormalization_secondInteger_isUnit
      N p hNp h4N hN hpN s s.property)
lemma lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (P : Polynomial ℤ) :
    lpsOriginalRelativeGaussNormalizationSecondBaseMap N p hNp h4N hN hpN
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P) =
      P.eval₂ (Int.castRingHom _)
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  dsimp only [lpsOriginalRelativeGaussNormalizationSecondBaseMap]
  exact IsLocalization.lift_eq _ P
lemma lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer_comp
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationSecondBaseMap N p hNp h4N hN hpN).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) := by
  apply RingHom.ext
  intro P
  exact lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer N p hNp h4N hN hpN P
lemma lpsOriginalRelativeGaussNormalizationSecondBaseMap_levelRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalGaussPolynomial N hN p).eval₂
      (lpsOriginalRelativeGaussNormalizationSecondBaseMap N p hNp h4N hN hpN)
      (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN) = 0 := by
  change ((lpsOriginalIntegerPolynomial N hN).map
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))).eval₂ _ _ = 0
  rw [Polynomial.eval₂_map,
    lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer_comp]
  exact lpsOriginalRelativeGaussNormalization_secondLevelRoot N p hNp h4N hN hpN
def lpsOriginalRelativeGaussNormalizationSecondOrderMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalGaussAffineOrder N hN p →+*
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  AdjoinRoot.lift (lpsOriginalRelativeGaussNormalizationSecondBaseMap N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationSecondBaseMap_levelRoot N p hNp h4N hN hpN)
end
end QEC.Coding.TannerLiftedProduct


