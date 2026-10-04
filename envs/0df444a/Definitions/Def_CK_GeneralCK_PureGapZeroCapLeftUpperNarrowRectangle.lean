-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperNarrowRectangle
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperNarrowRectangle
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T02:38:52.476813+00:00
-- url     : https://prove2.me/theorems/daa87068-da4e-425a-bc7f-302a4052d0c8
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperNarrowRectangle` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperNarrowRectangle` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperNarrowRectangle` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperNarrowRectangle (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperNarrowRectangle.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperRadialReduction
import Definitions.Def_CK_GeneralCK_RadialConvexity
import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanBounds

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperNarrowRectangle =====
section

/-! An additive, bounded zero-cap left-upper certificate candidate.
All logarithmic comparisons are exact integer-power witnesses. This source
must be compiled and audited before the rectangle is counted as proved. -/

namespace GeneralCK
open Set
namespace ZeroCapLeftUpperNarrow

private theorem log_seven_le : Real.log 7 ≤ (211 / 75 : ℝ) * Real.log 2 := by
  have hp : (7 : ℝ) ^ (75 : ℕ) ≤ (2 : ℝ) ^ (211 : ℕ) := by norm_num
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (7 : ℝ) ^ (75 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  linarith

private theorem log_three_ge : (31 / 20 : ℝ) * Real.log 2 ≤ Real.log 3 := by
  have hp : (2 : ℝ) ^ (31 : ℕ) ≤ (3 : ℝ) ^ (20 : ℕ) := by norm_num
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (31 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  linarith

private theorem log_three_le : Real.log 3 ≤ (119 / 75 : ℝ) * Real.log 2 := by
  have hp : (3 : ℝ) ^ (75 : ℕ) ≤ (2 : ℝ) ^ (119 : ℕ) := by norm_num
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (3 : ℝ) ^ (75 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  linarith

private theorem log_six_ge : (31 / 12 : ℝ) * Real.log 2 ≤ Real.log 6 := by
  have hp : (2 : ℝ) ^ (31 : ℕ) ≤ (6 : ℝ) ^ (12 : ℕ) := by norm_num
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (31 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  linarith

private theorem log_odds_ge : (11 / 4 : ℝ) * Real.log 2 ≤ Real.log (447 / 65 : ℝ) := by
  have hp : (2 : ℝ) ^ (11 : ℕ) ≤ (447 / 65 : ℝ) ^ (4 : ℕ) := by norm_num
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (11 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  linarith

private theorem J_eighth_le : J (1 / 8) ≤ (211 / 75 : ℝ) := by
  unfold J
  have harg : ((1 - (1 / 8 : ℝ)) / (1 / 8)) = 7 := by norm_num
  rw [harg]
  exact (div_le_iff₀ log_two_pos).2 (by nlinarith only [log_seven_le])

private theorem J_quarter_ge : (31 / 20 : ℝ) ≤ J (1 / 4) := by
  unfold J
  have harg : ((1 - (1 / 4 : ℝ)) / (1 / 4)) = 3 := by norm_num
  rw [harg]
  exact (le_div_iff₀ log_two_pos).2 (by nlinarith only [log_three_ge])

private theorem J_endpoint_ge : (11 / 4 : ℝ) ≤ J (65 / 512) := by
  unfold J
  have harg : ((1 - (65 / 512 : ℝ)) / (65 / 512)) = 447 / 65 := by norm_num
  rw [harg]
  exact (le_div_iff₀ log_two_pos).2 (by nlinarith only [log_odds_ge])

private theorem H_quarter_lower : (81 / 100 : ℝ) ≤ H (1 / 4) := by
  have he := Certificates.SmallMean.entropy_log_identity (1 / 4 : ℝ)
  have h4 : -Real.log (1 / 4 : ℝ) = 2 * Real.log 2 := by
    rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ (2 : ℕ))⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    ring
  have h3 : -Real.log (1 - (1 / 4 : ℝ)) =
      2 * Real.log 2 - Real.log 3 := by
    rw [show 1 - (1 / 4 : ℝ) = (3 : ℝ) / 4 by norm_num,
      Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    ring
  rw [h4, h3] at he
  have hmul : (81 / 100 : ℝ) * Real.log 2 ≤ H (1 / 4) * Real.log 2 := by
    nlinarith only [he, log_three_le]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hmul)

private theorem H_seventh_upper : H (1 / 7) ≤ (629 / 1050 : ℝ) := by
  have he := Certificates.SmallMean.entropy_log_identity (1 / 7 : ℝ)
  have h7 : -Real.log (1 / 7 : ℝ) = Real.log 7 := by
    rw [show (1 / 7 : ℝ) = (7 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have h6 : -Real.log (1 - (1 / 7 : ℝ)) = Real.log 7 - Real.log 6 := by
    rw [show 1 - (1 / 7 : ℝ) = (6 : ℝ) / 7 by norm_num,
      Real.log_div (by norm_num : (6 : ℝ) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0)]
    ring
  rw [h7, h6] at he
  have hmul : H (1 / 7) * Real.log 2 ≤ (629 / 1050 : ℝ) * Real.log 2 := by
    nlinarith only [he, log_seven_le, log_six_ge]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hmul)

private theorem F_chord {d z h : ℝ} (hd : 0 ≤ d) (hz : 0 < z)
    (hdz : d ≤ z) (hh : 0 < h) : F d h ≤ (d / z) * F z h := by
  let t : ℝ := d / z
  have ht : 0 ≤ t := div_nonneg hd hz.le
  have ht1 : t ≤ 1 := (div_le_one hz).2 hdz
  have hsum : (1 - t) + t = 1 := by ring
  have hc := (convexOn_F_radius hh).2
    (show (0 : ℝ) ∈ Ici 0 by simp) (show z ∈ Ici 0 by simpa using hz.le)
    (by linarith : 0 ≤ 1 - t) ht hsum
  have hFzero : F 0 h = 0 := by simp [F]
  simp only [smul_eq_mul, mul_zero, zero_add, hFzero, zero_mul, add_zero] at hc
  have htz : t * z = d := by
    dsimp [t]
    exact div_mul_cancel₀ d hz.ne'
  rw [htz] at hc
  simpa only [t] using hc

theorem leftUpper_on_narrow_rectangle {a b : ℝ}
    (ha : 1 / 8 ≤ a) (ha' : a ≤ 129 / 1024)
    (hb : 129 / 1024 ≤ b) (hb' : b ≤ 65 / 512)
    (hab : a < b) :
    0 ≤ canonicalPureGap a (1 / 2) (H a) (H b) := by
  have ha0 : 0 < a := by linarith
  have hbhalf : b < 1 / 2 := by linarith
  let h : ℝ := (H a + H b) / 2
  let z : ℝ := 1 / 2 - a
  let d : ℝ := b - a
  have hh : 0 < h := by
    dsimp [h]
    linarith [H_pos ha0 (by linarith : a < 1), H_pos (ha0.trans hab) (by linarith : b < 1)]
  have hz : 0 < z := by dsimp [z]; linarith
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hdz : d ≤ z := by dsimp [d, z]; linarith
  have hbound : h ≤ H (1 / 7) := by
    have haH : H a ≤ H b := H_strictMonoOn.monotoneOn
      ⟨ha0.le, by linarith⟩ ⟨(ha0.trans hab).le, by linarith⟩ hab.le
    have hbH : H b ≤ H (1 / 7) := H_strictMonoOn.monotoneOn
      ⟨(ha0.trans hab).le, by linarith⟩ ⟨by norm_num, by norm_num⟩
      (by linarith)
    dsimp [h]
    linarith
  have hthree : h ≤ 3 / 5 := by linarith [H_seventh_upper]
  have hzmin : 383 / 1024 ≤ z := by dsimp [z]; linarith
  have hcontact : radialContact z h ≤ 1 / 4 := by
    apply (radialContact_le_iff hz hh (by norm_num) (by norm_num)).2
    have hq := H_quarter_lower
    have hprod : (383 / 1024 : ℝ) * (81 / 100) ≤ z * H (1 / 4) :=
      mul_le_mul hzmin hq (by norm_num) hz.le
    linarith
  have hF : (11873 / 20480 : ℝ) ≤ F z h := by
    have hv : 0 < radialContact z h := radialContact_pos hz hh
    have hJ : J (1 / 4) ≤ J (radialContact z h) :=
      J_antitone hv (by norm_num) hcontact
    have hj : (31 / 20 : ℝ) ≤ J (radialContact z h) :=
      J_quarter_ge.trans hJ
    simp only [F, hz.ne', ↓reduceIte]
    have hprod : (383 / 1024 : ℝ) * (31 / 20) ≤
        z * J (radialContact z h) :=
      mul_le_mul hzmin hj (by norm_num) hz.le
    linarith
  have hratio : d / z ≤ 2 / 383 := by
    have hdmax : d ≤ 1 / 512 := by dsimp [d]; linarith
    apply (div_le_iff₀ hz).2
    nlinarith only [hdmax, hzmin]
  have hFsmall := F_chord hd hz hdz hh
  have hradial : (5921 / 5120 : ℝ) ≤ 2 * F z h - F d h := by
    have hFn : 0 ≤ F z h := F_nonneg hz.le hh
    have hratioF := mul_le_mul_of_nonneg_right hratio hFn
    linarith only [hFsmall, hratioF, hF]
  have hHmin : H (1 / 8) ≤ h := by
    have hHa : H (1 / 8) ≤ H a := H_strictMonoOn.monotoneOn
      ⟨by norm_num, by norm_num⟩ ⟨ha0.le, by linarith⟩ ha
    have hHb : H a ≤ H b := H_strictMonoOn.monotoneOn
      ⟨ha0.le, by linarith⟩ ⟨(ha0.trans hab).le, by linarith⟩ hab.le
    dsimp [h]
    linarith
  have hEtaUpper : eta h ≤ 211 / 100 := by
    have hEta : eta h ≤ eta (H (1 / 8)) := eta_antitoneOn
      ⟨H_pos (by norm_num) (by norm_num), H_le_one (1 / 8)⟩
      ⟨hh, hbound.trans (H_seventh_upper.trans (by norm_num))⟩ hHmin
    have he : eta (H (1 / 8)) = (3 / 4) * J (1 / 8) := by
      rw [eta_eq_profile (H_nonneg (by norm_num) (by norm_num)) (H_le_one (1 / 8)),
        entropyInverse_H_lower (by norm_num) (by norm_num)]
      ring
    rw [he] at hEta
    nlinarith only [hEta, J_eighth_le]
  have hEtaLower : (2101 / 2048 : ℝ) ≤ eta (H b) / 2 := by
    have hHb : H b ≤ H (65 / 512) := H_strictMonoOn.monotoneOn
      ⟨(ha0.trans hab).le, by linarith⟩ ⟨by norm_num, by norm_num⟩ hb'
    have hEta : eta (H (65 / 512)) ≤ eta (H b) := eta_antitoneOn
      ⟨H_pos (ha0.trans hab) (by linarith), H_le_one b⟩
      ⟨H_pos (by norm_num) (by norm_num), H_le_one (65 / 512)⟩ hHb
    have he : eta (H (65 / 512)) = (191 / 256) * J (65 / 512) := by
      rw [eta_eq_profile (H_nonneg (by norm_num) (by norm_num))
        (H_le_one (65 / 512)), entropyInverse_H_lower (by norm_num) (by norm_num)]
      ring
    rw [he] at hEta
    nlinarith only [hEta, J_endpoint_ge]
  have hCost : 0 ≤ interiorCost a b := by
    have hJ : J b ≤ J a := J_antitone ha0 hbhalf.le hab.le
    unfold interiorCost
    exact div_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hJ)) (by norm_num)
  have hIdentity := canonicalPureGap_leftUpper_radial_eq ha0 hab hbhalf
  rw [hIdentity]
  dsimp [h, z, d] at hradial hEtaUpper hEtaLower
  nlinarith only [hCost, hradial, hEtaUpper, hEtaLower]

end ZeroCapLeftUpperNarrow

#print axioms GeneralCK.ZeroCapLeftUpperNarrow.leftUpper_on_narrow_rectangle

end GeneralCK

end


