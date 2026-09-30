-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8AnalyticRealBridge
-- name    : CK_GeneralCK_PureGapE8AnalyticRealBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:50:36.929369+00:00
-- url     : https://prove2.me/theorems/67f2543c-2ce4-4a55-b901-ca34ffda57c2
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8AnalyticRealBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8AnalyticRealBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8AnalyticRealBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8AnalyticRealBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8AnalyticRealBridge.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8AnalyticGerm
import Definitions.Def_CK_GeneralCK_CorrectionHessianNatural
import Definitions.Def_CK_GeneralCK_ReflectionComplexRealBridge
import Definitions.Def_CK_GeneralCK_ReflectionRegularContact
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.PureGapE8AnalyticRealBridge =====
section

/-!
# Real parametrization underlying the analytic E8 inverse germ

This file identifies the stable bias-coordinate formulas with the existing
radial definition of `e8Theta`.  It is the real-axis input needed to identify
the separate analytic germ with the positive, choice-defined inverse `e8Q`.
-/

namespace GeneralCK.E8AnalyticGerm

open Set Filter Function
open Reflection Certificates.Reflection








theorem radialContact_two_mul_xParamReal {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    radialContact (2 * xParamReal c) 1 = (1 - c) / 2 := by
  have hE : 0 < biasE c := biasE_pos_wide (by linarith) hc1
  have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : 0 < H ((1 - c) / 2) := H_pos (by linarith) (by linarith)
  have hz : 0 < 2 * xParamReal c := by
    unfold xParamReal
    positivity
  apply radialContact_eq_of_equation hz (by norm_num)
  · linarith
  · linarith
  have hp := Correction.Natural.biasE_probability
    (v := (1 - c) / 2) (by linarith) (by linarith)
  rw [show 1 - 2 * ((1 - c) / 2) = c by ring] at hp
  unfold xParamReal
  rw [hp, Certificates.Mixed.hn_eq_H_mul_log]
  field_simp [hE.ne', hH.ne']
  ring

/-- Exact stable parametrization of the manuscript slope on `0 < c < 1`. -/
theorem e8Theta_xParamReal {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    e8Theta (xParamReal c) = thetaParamReal c := by
  have hx : 0 < xParamReal c := by
    unfold xParamReal
    have hE : 0 < biasE c := biasE_pos_wide (by linarith) hc1
    have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hFs := Correction.Natural.Fs_contact
    (z := 2 * xParamReal c) (h := 1) (by positivity) (by norm_num)
  rw [radialContact_two_mul_xParamReal hc hc1,
    show 1 - 2 * ((1 - c) / 2) = c by ring] at hFs
  have hk : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hB : biasB c ≠ 0 := (biasB_pos hc hc1).ne'
  have hcden : 1 - c ^ 2 ≠ 0 := by nlinarith
  calc
    e8Theta (xParamReal c) = Correction.Natural.Fs c / Real.log 2 := by
      unfold e8Theta
      rw [hFs]
      field_simp [hk]
    _ = thetaParamReal c := by
      unfold Correction.Natural.Fs thetaParamReal
      field_simp [hk, hB, hcden]
      ring

/-- Therefore the global positive inverse recovers the stable contact coordinate. -/
theorem e8Q_thetaParamReal {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    e8Q (thetaParamReal c) = xParamReal c := by
  rw [← e8Theta_xParamReal hc hc1]
  exact e8Q_e8Theta (by
    unfold xParamReal
    have hE : 0 < biasE c := biasE_pos_wide (by linarith) hc1
    have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity)

theorem atanhExt_ofReal {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    atanhExt (c : ℂ) = (SmallMean.A c : ℂ) := by
  have hp : 0 ≤ 1 + c := by linarith
  have hm : 0 ≤ 1 - c := by linarith
  have hp0 : 1 + c ≠ 0 := by linarith
  have hm0 : 1 - c ≠ 0 := by linarith
  unfold atanhExt SmallMean.A
  rw [show 1 + (c : ℂ) = ((1 + c : ℝ) : ℂ) by norm_num,
    show 1 - (c : ℂ) = ((1 - c : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_log hp, ← Complex.ofReal_log hm, Real.log_div hp0 hm0]
  norm_num

theorem biasBExt_ofReal {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    biasBExt (c : ℂ) = (biasB c : ℂ) := by
  have hnonneg : 0 ≤ 1 - c ^ 2 := by nlinarith
  unfold biasBExt biasB
  rw [show 1 - (c : ℂ) ^ 2 = ((1 - c * c : ℝ) : ℂ) by
      norm_num [pow_two],
    ← Complex.ofReal_log (by simpa [pow_two] using hnonneg)]
  norm_num [pow_two]

/-- Both stable complex formulas restrict exactly to their real counterparts. -/
theorem param_ofReal {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    thetaParam (c : ℂ) = (thetaParamReal c : ℂ) ∧
      xParam (c : ℂ) = (xParamReal c : ℂ) := by
  rw [thetaParam, xParam, thetaParamReal, xParamReal,
    atanhExt_ofReal hc0 hc1, biasBExt_ofReal hc0 hc1,
    Reflection.ComplexRealBridge.entropyExt_ofReal hc0 hc1]
  constructor <;> push_cast <;> ring

/-- On all sufficiently small positive slopes in the stable parametrization,
the analytic germ agrees exactly with the choice-defined positive inverse. -/
theorem eventually_qGerm_eq_e8Q_param :
    ∀ᶠ c in nhdsWithin (0 : ℝ) (Ioi 0),
      qGerm (thetaParamReal c : ℂ) = (e8Q (thetaParamReal c) : ℂ) := by
  have hleft := analyticAt_thetaParam.hasStrictDerivAt.eventually_left_inverse
    (by
      rw [hasDerivAt_thetaParam_zero.deriv]
      exact div_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))))
  change ∀ᶠ z in nhds (0 : ℂ), biasGerm (thetaParam z) = z at hleft
  have hcast : Tendsto ((↑) : ℝ → ℂ) (nhds (0 : ℝ)) (nhds (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  have hpull : Filter.Eventually
      (fun c : ℝ => biasGerm (thetaParam (c : ℂ)) = (c : ℂ)) (nhds 0) :=
    hcast.eventually hleft
  have hsmall : Filter.Eventually (fun c : ℝ => c ∈ Ioo (-1) 1) (nhds 0) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hpull' := hpull.filter_mono
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0)
  have hsmall' := hsmall.filter_mono
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0)
  filter_upwards [self_mem_nhdsWithin, hpull', hsmall'] with c hcpos hfix hc
  rcases param_ofReal hc.1 hc.2 with ⟨htheta, hx⟩
  rw [← htheta, qGerm, hfix, hx]
  exact_mod_cast (e8Q_thetaParamReal hcpos hc.2).symm

end GeneralCK.E8AnalyticGerm

end


