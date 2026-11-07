-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalVerticalUnramified
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalVerticalUnramified
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:21:44.018503+00:00
-- url     : https://prove2.me/theorems/bd943f04-994a-48f4-bed6-112efa1b7363
-- title:
--   LPSOriginal Vertical Unramified
-- statement:
--   Definitions and structural lemmas for LPSOriginal Vertical Unramified, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalVerticalUnramified.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.Locus
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
def localizedPrimeAtPrimeEquiv
    {C D : Type*} [CommRing C] [CommRing D] [Algebra C D]
    (M : Submonoid C) [IsLocalization M D]
    (q : Ideal C) [q.IsPrime] (hd : Disjoint (M : Set C) (q : Set C)) :
    let Q := q.map (algebraMap C D)
    let : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M D q inferInstance hd
    let : Algebra C (Localization.AtPrime Q) :=
      ((algebraMap D (Localization.AtPrime Q)).comp (algebraMap C D)).toAlgebra
    Localization.AtPrime q ≃ₐ[C] Localization.AtPrime Q := by
  let Q := q.map (algebraMap C D)
  let : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M D q inferInstance hd
  let instCQ : Algebra C (Localization.AtPrime Q) :=
    ((algebraMap D (Localization.AtPrime Q)).comp (algebraMap C D)).toAlgebra
  let : SMul C (Localization.AtPrime Q) := instCQ.toSMul
  let instDQ : Algebra D (Localization.AtPrime Q) := inferInstance
  let : SMul D (Localization.AtPrime Q) := instDQ.toSMul
  let : IsScalarTower C D (Localization.AtPrime Q) :=
    .of_algebraMap_eq' rfl
  have hcon : Q.comap (algebraMap C D) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M D inferInstance hd
  let : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M (Localization.AtPrime Q) Q
    simpa only [hcon] using h
  exact IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
    (Localization.AtPrime Q)
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring verticalPrimeJAlgebra
  verticalPrimeBaseFieldAlgebra verticalPrimeNormalCommRing verticalPrimeNormalRing
  verticalPrimeNormalSemiring
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
local notation "K" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "C" => integralClosure (Polynomial ℤ) K
local notation "D" => integralClosure (LPSOriginalGaussBase p) K
include hN
end
end QEC.Coding.TannerLiftedProduct


