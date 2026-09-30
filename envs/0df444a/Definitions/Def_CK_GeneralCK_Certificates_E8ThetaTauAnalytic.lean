-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ThetaTauAnalytic
-- name    : CK_GeneralCK_Certificates_E8ThetaTauAnalytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:12:09.012656+00:00
-- url     : https://prove2.me/theorems/609a0ab4-8dde-48bf-a891-20339e675182
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ThetaTauAnalytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ThetaTauAnalytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ThetaTauAnalytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ThetaTauAnalytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ThetaTauAnalytic.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TauInverseContraction
import Definitions.Def_CK_GeneralCK_Certificates_MixedConstants
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.MeanValue

-- ===== source module GeneralCK.Certificates.E8ThetaTauAnalytic =====
section

/-! Holomorphy of the concrete `thetaOfTau` map on the inversion disc. -/

namespace GeneralCK.Certificates.E8ThetaTauAnalytic

open Metric Set
open E8AnalyticGerm
open Reflection.ComplexEntropy
open Reflection.ComplexGlobalAnalytic
open E8TauInverseContraction

theorem norm_fixedPointOnDisc_le {tau : ℂ} (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    ‖fixedPointOnDisc tau‖ ≤ (1103 / 2500 : ℝ) := by
  have htau' : ‖tau‖ < (7 / 10 : ℝ) := htau.trans_lt (by norm_num)
  have hc := fixedPointOnDisc_mem_ball htau'
  have hc' : ‖fixedPointOnDisc tau‖ ≤ (4 / 5 : ℝ) := by
    exact (show ‖fixedPointOnDisc tau‖ < (4 / 5 : ℝ) by
      simpa [mem_ball, dist_zero_right] using hc).le
  rw [fixedPointOnDisc_fixed htau', norm_mul]
  calc
    ‖tau‖ * ‖entropyExt (fixedPointOnDisc tau)‖ ≤
        (2 / 5 : ℝ) * (1103 / 1000 : ℝ) := by
      gcongr
      exact norm_entropyExt_le hc'
    _ = 1103 / 2500 := by norm_num

theorem biasBExt_ne_on_half_disc {c : ℂ} (hc : ‖c‖ ≤ (1103 / 2500 : ℝ)) :
    biasBExt c ≠ 0 := by
  have hsq : ‖-(c ^ 2)‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_neg, norm_pow]
    calc
      ‖c‖ ^ 2 ≤ (1103 / 2500 : ℝ) ^ 2 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hlog := Complex.norm_log_one_add_half_le_self hsq
  have hlog' : ‖Complex.log (1 - c ^ 2) / 2‖ < (69 / 100 : ℝ) := by
    rw [show 1 - c ^ 2 = 1 + -(c ^ 2) by ring, norm_div]
    have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [htwo]
    calc
      ‖Complex.log (1 + -(c ^ 2))‖ / 2 ≤
          ((3 / 2 : ℝ) * ‖-(c ^ 2)‖) / 2 := by gcongr
      _ ≤ ((3 / 2 : ℝ) * ((1103 / 2500 : ℝ) ^ 2)) / 2 := by
        gcongr
        simpa [norm_neg, norm_pow] using
          (pow_le_pow_left₀ (norm_nonneg c) hc 2)
      _ < 69 / 100 := by norm_num
  intro hzero
  have heq : (Real.log 2 : ℂ) = Complex.log (1 - c ^ 2) / 2 := by
    unfold biasBExt at hzero
    exact sub_eq_zero.mp hzero
  have hnorm := congrArg norm heq
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos (by norm_num))] at hnorm
  linarith [Certificates.Mixed.log_two_gt_69]

theorem analyticAt_thetaParam_on_disc {c : ℂ}
    (hc : ‖c‖ ≤ (1103 / 2500 : ℝ)) : AnalyticAt ℂ thetaParam c := by
  have hc1 : ‖c‖ < 1 := hc.trans_lt (by norm_num)
  have hp : 1 + c ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one hc1
  have hm : 1 - c ∈ Complex.slitPlane := by
    simpa [sub_eq_add_neg] using
      Complex.mem_slitPlane_of_norm_lt_one (show ‖-c‖ < 1 by simpa using hc1)
  have hs : 1 - c ^ 2 ∈ Complex.slitPlane := by
    have : ‖-(c ^ 2)‖ < 1 := by
      rw [norm_neg, norm_pow]
      exact (pow_lt_one₀ (norm_nonneg c) hc1 (by norm_num))
    simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one this
  have hA : AnalyticAt ℂ atanhExt c := by
    unfold atanhExt
    exact ((((analyticAt_const.add analyticAt_id).clog hp).sub
      ((analyticAt_const.sub analyticAt_id).clog hm)).div analyticAt_const (by norm_num))
  have hB : AnalyticAt ℂ biasBExt c := by
    unfold biasBExt
    exact analyticAt_const.sub
      ((((analyticAt_const.sub (analyticAt_id.pow 2)).clog hs).div
        analyticAt_const (by norm_num)))
  have hE := Reflection.ComplexContactGerm.analyticAt_entropyExt hc1
  have hden : (1 - c ^ 2) * biasBExt c ≠ 0 := by
    apply mul_ne_zero
    · intro hz
      have heq : c ^ 2 = 1 := (sub_eq_zero.mp hz).symm
      have hn := congrArg norm heq
      rw [norm_pow, norm_one] at hn
      nlinarith [norm_nonneg c]
    · exact biasBExt_ne_on_half_disc hc
  unfold thetaParam
  exact analyticAt_const.mul (hA.add
    ((analyticAt_id.mul hE).div
      ((analyticAt_const.sub (analyticAt_id.pow 2)).mul hB) hden))

theorem analyticOnNhd_thetaOfTau :
    AnalyticOnNhd ℂ thetaOfTau (ball 0 (2 / 5 : ℝ)) := by
  intro tau htau
  have htauNorm : ‖tau‖ ≤ (2 / 5 : ℝ) :=
    (show ‖tau‖ < (2 / 5 : ℝ) by
      simpa [mem_ball, dist_zero_right] using htau).le
  exact (analyticAt_thetaParam_on_disc (norm_fixedPointOnDisc_le htauNorm)).comp
    (analyticAt_fixedPointOnDisc
      (htauNorm.trans_lt (by norm_num)))

theorem analyticAt_thetaOfTau_of_norm_le {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) : AnalyticAt ℂ thetaOfTau tau := by
  exact (analyticAt_thetaParam_on_disc (norm_fixedPointOnDisc_le htau)).comp
    (analyticAt_fixedPointOnDisc (htau.trans_lt (by norm_num)))

theorem analyticAt_thetaTauRemainder_of_norm_le {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    AnalyticAt ℂ thetaTauRemainder tau := by
  unfold thetaTauRemainder
  exact (analyticAt_thetaOfTau_of_norm_le htau).sub
    (analyticAt_const.mul analyticAt_id)

/-- The final global Lipschitz premise follows from a pointwise scalar
derivative estimate, a form suitable for interval evaluation. -/
theorem thetaTauRemainder_lipschitz_of_deriv_bound
    (hderiv : ∀ tau : ℂ, ‖tau‖ ≤ (2 / 5 : ℝ) →
      ‖deriv thetaTauRemainder tau‖ ≤ (1 : ℝ)) :
    LipschitzOnWith (1 : NNReal) thetaTauRemainder
      (closedBall 0 (2 / 5 : ℝ)) := by
  apply (convex_closedBall 0 (2 / 5 : ℝ)).lipschitzOnWith_of_nnnorm_fderiv_le
    (𝕜 := ℂ)
  · intro tau htau
    exact (analyticAt_thetaTauRemainder_of_norm_le (by
      simpa [mem_closedBall, dist_zero_right] using htau)).differentiableAt
  · intro tau htau
    have h := hderiv tau (by
      simpa [mem_closedBall, dist_zero_right] using htau)
    rw [norm_deriv_eq_norm_fderiv] at h
    exact_mod_cast h

end GeneralCK.Certificates.E8ThetaTauAnalytic

end


