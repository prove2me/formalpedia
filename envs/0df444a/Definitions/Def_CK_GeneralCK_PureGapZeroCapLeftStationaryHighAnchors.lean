-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryHighAnchors
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryHighAnchors
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:31:04.793421+00:00
-- url     : https://prove2.me/theorems/4f617738-29eb-4552-8ddd-363c707c28c6
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryHighAnchors` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryHighAnchors` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryHighAnchors` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryHighAnchors (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryHighAnchors.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryLowRangeEnvelope

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryHighAnchors =====
section

/-! Higher normalized slope anchors from contacts at one eighth and one
sixteenth. Every numerical comparison reduces to rational arithmetic or an
integer-power logarithm comparison. -/

namespace GeneralCK.ZeroCapLeftStationaryHighAnchors

open Certificates.Mixed ZeroCapLeftStationaryThetaBracket

theorem log_seven_lower : (14 / 5 : ℝ) * Real.log 2 ≤ Real.log 7 := by
  have hp : (2 : ℝ) ^ (14 : ℕ) ≤ (7 : ℝ) ^ (5 : ℕ) := by norm_num
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (14 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem log_seven_upper : Real.log 7 ≤ (45 / 16 : ℝ) * Real.log 2 := by
  have hp : (7 : ℝ) ^ (16 : ℕ) ≤ (2 : ℝ) ^ (45 : ℕ) := by norm_num
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (7 : ℝ) ^ (16 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem log_fifteen_lower : (39 / 10 : ℝ) * Real.log 2 ≤ Real.log 15 := by
  have hp : (2 : ℝ) ^ (39 : ℕ) ≤ (15 : ℝ) ^ (10 : ℕ) := by norm_num
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (39 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem log_fifteen_upper : Real.log 15 ≤ 4 * Real.log 2 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 15)
    (by norm_num : (15 : ℝ) ≤ 2 ^ (4 : ℕ))
  rw [Real.log_pow] at h
  exact h

theorem entropy_eighth_identity :
    H (1 / 8) * Real.log 2 = 3 * Real.log 2 - (7 / 8) * Real.log 7 := by
  have h := Certificates.SmallMean.entropy_log_identity (1 / 8 : ℝ)
  have hA : -Real.log (1 / 8 : ℝ) = 3 * Real.log 2 := by
    rw [show (1 / 8 : ℝ) = ((2 : ℝ) ^ (3 : ℕ))⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    ring
  have hB : -Real.log (1 - (1 / 8 : ℝ)) = 3 * Real.log 2 - Real.log 7 := by
    rw [show 1 - (1 / 8 : ℝ) = 7 / (2 ^ (3 : ℕ)) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    ring
  rw [hA, hB] at h
  linarith only [h]

theorem entropy_sixteenth_identity :
    H (1 / 16) * Real.log 2 = 4 * Real.log 2 - (15 / 16) * Real.log 15 := by
  have h := Certificates.SmallMean.entropy_log_identity (1 / 16 : ℝ)
  have hA : -Real.log (1 / 16 : ℝ) = 4 * Real.log 2 := by
    rw [show (1 / 16 : ℝ) = ((2 : ℝ) ^ (4 : ℕ))⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    ring
  have hB : -Real.log (1 - (1 / 16 : ℝ)) = 4 * Real.log 2 - Real.log 15 := by
    rw [show 1 - (1 / 16 : ℝ) = 15 / (2 ^ (4 : ℕ)) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    ring
  rw [hA, hB] at h
  linarith only [h]

theorem entropy_eighth_lower : (69 / 128 : ℝ) ≤ H (1 / 8) := by
  have hm : (69 / 128 : ℝ) * Real.log 2 ≤ H (1 / 8) * Real.log 2 := by
    linarith only [entropy_eighth_identity, log_seven_upper]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hm)

theorem entropy_sixteenth_upper : H (1 / 16) ≤ (11 / 32 : ℝ) := by
  have hm : H (1 / 16) * Real.log 2 ≤ (11 / 32 : ℝ) * Real.log 2 := by
    linarith only [entropy_sixteenth_identity, log_fifteen_lower]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hm)

theorem kap_eighth_upper : kap (1 / 8) ≤ (694 / 625 : ℝ) := by
  have hL : Real.log 2 ≤ (347 / 500 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hk : kap (1 / 8) = 3 * Real.log 2 - Real.log 7 / 2 := by
    unfold kap
    rw [show (1 / 8 : ℝ) * (1 - 1 / 8) = 7 / 2 ^ (6 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    ring
  rw [hk]
  linarith only [log_seven_lower, hL]

theorem kap_sixteenth_lower : (693 / 500 : ℝ) ≤ kap (1 / 16) := by
  have hL : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hk : kap (1 / 16) = 4 * Real.log 2 - Real.log 15 / 2 := by
    unfold kap
    rw [show (1 / 16 : ℝ) * (1 - 1 / 16) = 15 / 2 ^ (8 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    ring
  rw [hk]
  linarith only [log_fifteen_upper, hL]

theorem radialSlope_eighth_formula :
    radialSlope (1 / 8) = Real.log 7 / Real.log 2 +
      (24 / 7) * H (1 / 8) / kap (1 / 8) := by
  have hJ : J (1 / 8) = Real.log 7 / Real.log 2 := by norm_num [J]
  have hk : kap (1 / 8) ≠ 0 := (kap_pos (by norm_num) (by norm_num)).ne'
  unfold radialSlope
  rw [hJ, hn_eq_H_mul_log]
  field_simp [log_two_pos.ne', hk]
  ring

theorem radialSlope_sixteenth_formula :
    radialSlope (1 / 16) = Real.log 15 / Real.log 2 +
      (112 / 15) * H (1 / 16) / kap (1 / 16) := by
  have hJ : J (1 / 16) = Real.log 15 / Real.log 2 := by norm_num [J]
  have hk : kap (1 / 16) ≠ 0 := (kap_pos (by norm_num) (by norm_num)).ne'
  unfold radialSlope
  rw [hJ, hn_eq_H_mul_log]
  field_simp [log_two_pos.ne', hk]
  ring

theorem radialSlope_eighth_lower : (89 / 20 : ℝ) ≤ radialSlope (1 / 8) := by
  have hk : 0 < kap (1 / 8) := kap_pos (by norm_num) (by norm_num)
  have hpart : (33 / 20 : ℝ) ≤ (24 / 7) * H (1 / 8) / kap (1 / 8) := by
    apply (le_div_iff₀ hk).mpr
    linarith only [entropy_eighth_lower, kap_eighth_upper]
  have hJ : (14 / 5 : ℝ) ≤ Real.log 7 / Real.log 2 :=
    (le_div_iff₀ log_two_pos).mpr log_seven_lower
  rw [radialSlope_eighth_formula]
  linarith only [hpart, hJ]

theorem radialSlope_sixteenth_upper : radialSlope (1 / 16) ≤ (59 / 10 : ℝ) := by
  have hk : 0 < kap (1 / 16) := kap_pos (by norm_num) (by norm_num)
  have hpart : (112 / 15) * H (1 / 16) / kap (1 / 16) ≤ (19 / 10 : ℝ) := by
    apply (div_le_iff₀ hk).mpr
    linarith only [entropy_sixteenth_upper, kap_sixteenth_lower]
  have hJ : Real.log 15 / Real.log 2 ≤ (4 : ℝ) :=
    (div_le_iff₀ log_two_pos).mpr log_fifteen_upper
  rw [radialSlope_sixteenth_formula]
  linarith only [hpart, hJ]

theorem theta_seven_tenths_lower : (89 / 20 : ℝ) ≤ e8Theta (7 / 10) := by
  have hc : radialContact (2 * (7 / 10)) 1 ≤ (1 / 8 : ℝ) :=
    contact_upper_of_entropy_lower (by norm_num) (by norm_num) (by norm_num)
      entropy_eighth_lower (by norm_num)
  exact radialSlope_eighth_lower.trans
    (e8Theta_lower_of_contact_upper (by norm_num) (by norm_num) (by norm_num) hc)

theorem theta_five_quarters_upper : e8Theta (5 / 4) ≤ (59 / 10 : ℝ) := by
  have hc : (1 / 16 : ℝ) ≤ radialContact (2 * (5 / 4)) 1 :=
    contact_lower_of_entropy_upper (by norm_num) (by norm_num) (by norm_num)
      entropy_sixteenth_upper (by norm_num)
  exact (e8Theta_upper_of_contact_lower (by norm_num) (by norm_num)
    (by norm_num) hc).trans radialSlope_sixteenth_upper

#print axioms log_seven_lower
#print axioms log_seven_upper
#print axioms log_fifteen_lower
#print axioms log_fifteen_upper
#print axioms entropy_eighth_lower
#print axioms entropy_sixteenth_upper
#print axioms radialSlope_eighth_lower
#print axioms radialSlope_sixteenth_upper
#print axioms theta_seven_tenths_lower
#print axioms theta_five_quarters_upper

end GeneralCK.ZeroCapLeftStationaryHighAnchors

end


