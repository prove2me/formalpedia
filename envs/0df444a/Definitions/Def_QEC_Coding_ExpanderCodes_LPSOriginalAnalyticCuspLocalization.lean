-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T01:23:33.581628+00:00
-- url     : https://prove2.me/theorems/10e3bd02-f0f6-4202-bf92-11373290041e
-- title:
--   LPSOriginal Analytic Cusp Localization
-- statement:
--   Definitions and structural lemmas for LPSOriginal Analytic Cusp Localization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_qpow
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
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
abbrev lpsOriginalAnalyticCuspLaurentParameter : lpsOriginalCuspAnalyticSubring :=
  ⟨fun q : ℂ=>q,analyticAt_id⟩
abbrev lpsOriginalAnalyticCuspLaurentRing : Type :=
  Localization.Away lpsOriginalAnalyticCuspLaurentParameter
abbrev lpsOriginalComplexCuspLaurentRing : Type :=
  Localization.Away (PowerSeries.X : PowerSeries ℂ)
lemma lpsOriginalAnalyticCuspLaurentParameter_taylor :
    lpsOriginalCuspTaylorRingHom lpsOriginalAnalyticCuspLaurentParameter=
      PowerSeries.X := by
  change lpsOriginalTaylorSeries (fun q : ℂ=>q)=PowerSeries.X
  simpa only [pow_one] using lpsOriginalTaylorSeries_qpow 1
def lpsOriginalAnalyticCuspLocalizedTaylor :
    lpsOriginalAnalyticCuspLaurentRing →+* lpsOriginalComplexCuspLaurentRing :=
  IsLocalization.Away.lift lpsOriginalAnalyticCuspLaurentParameter
    (g:=(algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing).comp
      lpsOriginalCuspTaylorRingHom)
    (by
      change IsUnit (algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
        (lpsOriginalCuspTaylorRingHom lpsOriginalAnalyticCuspLaurentParameter))
      rw [lpsOriginalAnalyticCuspLaurentParameter_taylor]
      exact IsLocalization.Away.algebraMap_isUnit PowerSeries.X)
def lpsOriginalAnalyticCuspLocalizedNomeEval (τ : ℍ) :
    lpsOriginalAnalyticCuspLaurentRing →+* ℂ :=
  IsLocalization.Away.lift lpsOriginalAnalyticCuspLaurentParameter
    (g:=lpsOriginalCuspEvaluateRingHom (Function.Periodic.qParam 1 (τ:ℂ)))
    (by
      change IsUnit (Function.Periodic.qParam 1 (τ:ℂ))
      exact isUnit_iff_ne_zero.mpr (Function.Periodic.qParam_ne_zero _))
def lpsOriginalAnalyticClearedAffineBranch (m : ℕ) (hm : 0<m) (r : ℚ) :
    lpsOriginalCuspAnalyticSubring :=
  ⟨lpsOriginalClearedAffineCusp m m r,
    lpsOriginalClearedAffineCusp_analytic m m hm.ne' r⟩
def lpsOriginalAnalyticCuspAffineBranch (m : ℕ) (hm : 0<m) (r : ℚ) :
    lpsOriginalAnalyticCuspLaurentRing :=
  (IsLocalization.Away.invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
      lpsOriginalAnalyticCuspLaurentParameter)^m *
    algebraMap lpsOriginalCuspAnalyticSubring lpsOriginalAnalyticCuspLaurentRing
      (lpsOriginalAnalyticClearedAffineBranch m hm r)
end
end QEC.Coding.TannerLiftedProduct


