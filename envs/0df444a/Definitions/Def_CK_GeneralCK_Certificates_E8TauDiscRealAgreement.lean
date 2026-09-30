-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TauDiscRealAgreement
-- name    : CK_GeneralCK_Certificates_E8TauDiscRealAgreement
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:09:38.388785+00:00
-- url     : https://prove2.me/theorems/de1d9493-92c1-4db3-bc46-0af691d2b6e8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TauDiscRealAgreement` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TauDiscRealAgreement` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TauDiscRealAgreement` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TauDiscRealAgreement (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TauDiscRealAgreement.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginPositiveConsumer
import Definitions.Def_CK_GeneralCK_ReflectionComplexRealBridge

-- ===== source module GeneralCK.Certificates.E8TauDiscRealAgreement =====
section

namespace GeneralCK.Certificates.E8TauDiscRealAgreement

open Metric Set
open GeneralCK.E8AnalyticGerm
open GeneralCK.Reflection
open GeneralCK.Reflection.ComplexContactGerm
open GeneralCK.Reflection.ComplexGlobalAnalytic
open GeneralCK.Reflection.ComplexRealBridge
open GeneralCK.Certificates.Reflection
open E8QuantitativeBranchBridge
open E8TauInverseContraction
open E8TauDiscCertificateOfContraction
open E8OriginAnalyticCertificate
open E8OriginPositiveConsumer

private abbrev tauDisc : Set ℂ := closedBall 0 tauRadius

theorem six_fifths_le_e8Theta_logTwo_div_five
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc) :
    (6 / 5 : ℝ) ≤ e8Theta (Real.log 2 / 5) := by
  let tau : ℝ := 2 / 5
  let c : ℝ := biasContact (1 / tau)
  have htau : 0 < tau := by norm_num [tau]
  have htau7 : tau ≤ (7 / 10 : ℝ) := by norm_num [tau]
  have hc : c ∈ Ioo (0 : ℝ) 1 := biasContact_mem (one_div_pos.mpr htau)
  have hfp : fixedPointOnDisc (tau : ℂ) = (c : ℂ) := by
    rw [fixedPointOnDisc_eq (by simp [tau]; norm_num)]
    simpa only [c] using fixedPoint_eq_biasContact' htau htau7
  have hfix : c = tau * biasE c := by
    simpa only [c] using biasContact_fixed_eq htau
  have hE : 0 < biasE c := biasE_pos_wide (c := c) (by linarith [hc.1]) hc.2
  have hx : xParamReal c = Real.log 2 / 5 := by
    calc
      xParamReal c = Real.log 2 * c / (2 * biasE c) := rfl
      _ = Real.log 2 * (tau * biasE c) / (2 * biasE c) :=
        congrArg (fun z : ℝ => Real.log 2 * z / (2 * biasE c)) hfix
      _ = Real.log 2 * tau / 2 := by field_simp [hE.ne']
      _ = Real.log 2 / 5 := by dsimp [tau]; ring
  have htheta : thetaOfTau (tau : ℂ) = (e8Theta (Real.log 2 / 5) : ℂ) := by
    unfold thetaOfTau
    rw [hfp]
    have hp := param_ofReal (c := c) (by linarith [hc.1]) hc.2
    rw [hp.1, ← e8Theta_xParamReal hc.1 hc.2, hx]
  have htmem : (tau : ℂ) ∈ tauDisc := by
    simp [tauDisc, tauRadius, tau, mem_closedBall, dist_zero_right]
  have hzero : (0 : ℂ) ∈ tauDisc := by
    simp [tauDisc, tauRadius]
    norm_num
  have hR := hLip.dist_le_mul (tau : ℂ) htmem 0 hzero
  have hRnorm : ‖thetaTauRemainder (tau : ℂ)‖ ≤ (2 / 5 : ℝ) := by
    simpa [thetaTauRemainder_zero, dist_eq_norm, tau] using hR
  have hdecomp : thetaOfTau (tau : ℂ) =
      (4 : ℂ) * tau + thetaTauRemainder (tau : ℂ) := by
    unfold thetaTauRemainder
    ring
  have hlower : (6 / 5 : ℝ) ≤ ‖thetaOfTau (tau : ℂ)‖ := by
    rw [hdecomp]
    have hrev := norm_sub_norm_le ((4 : ℂ) * tau)
      (-thetaTauRemainder (tau : ℂ))
    rw [norm_neg, show (4 : ℂ) * tau - -thetaTauRemainder (tau : ℂ) =
      (4 : ℂ) * tau + thetaTauRemainder (tau : ℂ) by ring] at hrev
    have hfour : ‖(4 : ℂ) * tau‖ = (8 / 5 : ℝ) := by
      norm_num [tau, norm_mul]
    rw [hfour] at hrev
    linarith
  rw [htheta, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (e8Theta_pos (by positivity : 0 < Real.log 2 / 5))] at hlower
  exact hlower

theorem e8Theta_logTwo_div_five_gt
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc) :
    (4 / 25 : ℝ) < e8Theta (Real.log 2 / 5) :=
  (show (4 / 25 : ℝ) < 6 / 5 by norm_num).trans_le
    (six_fifths_le_e8Theta_logTwo_div_five hLip)

noncomputable def quantitativeCertificateOfLipschitz
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc) :
    QuantitativeCertificate :=
  quantitativeCertificate_of_inverse (tauDiscInverseCertificateOfLipschitz hLip)

theorem realAgreementBelowAnchor_of_lipschitz
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc) :
    ∀ y : ℝ, y ∈ e8SlopeRange → y < 6 / 5 →
      qReal (quantitativeCertificateOfLipschitz hLip) y = e8Q y := by
  intro y hyRange hyUpper
  have hyPos : 0 < y := e8SlopeRange_subset_pos hyRange
  let x := e8Q y
  have hxPos : 0 < x := e8Q_pos hyRange
  have hthetaX : e8Theta x = y := e8Theta_e8Q hyRange
  have hxUpper : x < Real.log 2 / 5 := by
    by_contra hn
    have hle : Real.log 2 / 5 ≤ x := le_of_not_gt hn
    have hanchorPos : 0 < Real.log 2 / 5 := by positivity
    have hmono := strictMonoOn_e8Theta_pos.monotoneOn hanchorPos hxPos hle
    rw [hthetaX] at hmono
    linarith [six_fifths_le_e8Theta_logTwo_div_five hLip]
  let tau : ℝ := 2 * x / Real.log 2
  have htauPos : 0 < tau := by
    dsimp [tau]
    positivity
  have htauUpper : tau < (2 / 5 : ℝ) := by
    dsimp [tau]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    apply (div_lt_iff₀ hlog).2
    nlinarith
  let c : ℝ := biasContact (1 / tau)
  have hc : c ∈ Ioo (0 : ℝ) 1 := biasContact_mem (one_div_pos.mpr htauPos)
  have hfp : fixedPointOnDisc (tau : ℂ) = (c : ℂ) := by
    rw [fixedPointOnDisc_eq (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htauPos]
      exact htauUpper.trans (by norm_num))]
    simpa only [c] using fixedPoint_eq_biasContact' htauPos
      (htauUpper.le.trans (by norm_num))
  have hfix : c = tau * biasE c := by
    simpa only [c] using biasContact_fixed_eq htauPos
  have hE : 0 < biasE c := biasE_pos_wide (c := c) (by linarith [hc.1]) hc.2
  have hxParam : xParamReal c = x := by
    calc
      xParamReal c = Real.log 2 * c / (2 * biasE c) := rfl
      _ = Real.log 2 * (tau * biasE c) / (2 * biasE c) :=
        congrArg (fun z : ℝ => Real.log 2 * z / (2 * biasE c)) hfix
      _ = Real.log 2 * tau / 2 := by field_simp [hE.ne']
      _ = x := by
        dsimp [tau]
        field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  have hthetaParam : thetaParam (c : ℂ) = (y : ℂ) := by
    have hp := param_ofReal (c := c) (by linarith [hc.1]) hc.2
    rw [hp.1, ← e8Theta_xParamReal hc.1 hc.2, hxParam, hthetaX]
  have htauMem : (tau : ℂ) ∈ tauDisc := by
    simp only [tauDisc, mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos htauPos]
    simpa [tauRadius] using htauUpper.le
  have hySupported : ‖(y : ℂ)‖ ≤ supportedYRadius := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyPos]
    exact hyUpper.le.trans (by norm_num [supportedYRadius])
  have hbranch : tauBranchOfLip hLip (y : ℂ) = (tau : ℂ) := by
    apply tauBranchOfLip_unique hLip hySupported htauMem
    unfold thetaOfTau
    rw [hfp, hthetaParam]
  change (((Real.log 2 : ℂ) / 2 * tauBranchOfLip hLip (y : ℂ)).re) = e8Q y
  rw [hbranch]
  have hcomplex : (Real.log 2 : ℂ) / 2 * (tau : ℂ) = (x : ℂ) := by
    have hr : Real.log 2 / 2 * tau = x := by
      dsimp [tau]
      field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    exact_mod_cast hr
  rw [hcomplex]
  rfl

theorem realAgreementOnOrigin_of_lipschitz
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc) :
    RealAgreementOnOrigin (quantitativeCertificateOfLipschitz hLip) := by
  intro y hyRange hyUpper
  exact realAgreementBelowAnchor_of_lipschitz hLip y hyRange
    (hyUpper.trans_lt (by norm_num))

theorem realAgreementOnOrigin_of_globalDerivativeBound
    (hAggregate : GlobalDerivativeBound) :
    RealAgreementOnOrigin (certificateOfGlobalDerivativeBound hAggregate) := by
  simpa only [certificateOfGlobalDerivativeBound,
    quantitativeCertificate_of_expr_bound,
    tauDiscInverseCertificateOfExprBound,
    quantitativeCertificateOfLipschitz] using
    realAgreementOnOrigin_of_lipschitz
      (E8ThetaTauAnalytic.thetaTauRemainder_lipschitz_of_deriv_bound
      (E8ThetaTauDerivativeFormula.final_derivative_bound_of_expr_bound hAggregate))

#print axioms six_fifths_le_e8Theta_logTwo_div_five
#print axioms realAgreementBelowAnchor_of_lipschitz
#print axioms realAgreementOnOrigin_of_lipschitz
#print axioms realAgreementOnOrigin_of_globalDerivativeBound

end GeneralCK.Certificates.E8TauDiscRealAgreement

end


