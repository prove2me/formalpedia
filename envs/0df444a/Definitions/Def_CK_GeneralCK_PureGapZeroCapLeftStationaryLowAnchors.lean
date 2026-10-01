-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryLowAnchors
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryLowAnchors
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:28:21.917576+00:00
-- url     : https://prove2.me/theorems/8d246eff-cb07-4e42-9ad3-8cad01bcb539
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryLowAnchors` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryLowAnchors` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryLowAnchors` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryLowAnchors (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryLowAnchors.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryRayEnvelope

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryLowAnchors =====
section

/-! Two additional upper slope anchors obtained from elementary integer-power
logarithm comparisons and the exact contacts at one third and one quarter. -/

namespace GeneralCK.ZeroCapLeftStationaryLowAnchors

open Certificates.Mixed ZeroCapLeftStationaryThetaBracket

theorem log_three_lower : (11 / 7 : ℝ) * Real.log 2 ≤ Real.log 3 := by
  have hp : (2 : ℝ) ^ (11 : ℕ) ≤ (3 : ℝ) ^ (7 : ℕ) := by norm_num
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (11 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem log_three_upper : Real.log 3 ≤ (119 / 75 : ℝ) * Real.log 2 := by
  have hp : (3 : ℝ) ^ (75 : ℕ) ≤ (2 : ℝ) ^ (119 : ℕ) := by norm_num
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (3 : ℝ) ^ (75 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem entropy_third_identity :
    H (1 / 3) * Real.log 2 = Real.log 3 - (2 / 3) * Real.log 2 := by
  have h := Certificates.SmallMean.entropy_log_identity (1 / 3 : ℝ)
  have hA : -Real.log (1 / 3 : ℝ) = Real.log 3 := by
    rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have hB : -Real.log (1 - (1 / 3 : ℝ)) = Real.log 3 - Real.log 2 := by
    rw [show 1 - (1 / 3 : ℝ) = 2 / 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
    ring
  rw [hA, hB] at h
  linarith only [h]

theorem entropy_quarter_identity :
    H (1 / 4) * Real.log 2 = 2 * Real.log 2 - (3 / 4) * Real.log 3 := by
  have h := Certificates.SmallMean.entropy_log_identity (1 / 4 : ℝ)
  have hA : -Real.log (1 / 4 : ℝ) = 2 * Real.log 2 := by
    rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ (2 : ℕ))⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    ring
  have hB : -Real.log (1 - (1 / 4 : ℝ)) = 2 * Real.log 2 - Real.log 3 := by
    rw [show 1 - (1 / 4 : ℝ) = 3 / (2 ^ (2 : ℕ)) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    ring
  rw [hA, hB] at h
  linarith only [h]

theorem entropy_third_upper : H (1 / 3) ≤ (23 / 25 : ℝ) := by
  have hm : H (1 / 3) * Real.log 2 ≤ (23 / 25 : ℝ) * Real.log 2 := by
    linarith only [entropy_third_identity, log_three_upper]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hm)

theorem entropy_quarter_upper : H (1 / 4) ≤ (23 / 28 : ℝ) := by
  have hm : H (1 / 4) * Real.log 2 ≤ (23 / 28 : ℝ) * Real.log 2 := by
    linarith only [entropy_quarter_identity, log_three_lower]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hm)

theorem kap_third_identity : kap (1 / 3) = Real.log 3 - Real.log 2 / 2 := by
  unfold kap
  rw [show (1 / 3 : ℝ) * (1 - 1 / 3) = 2 / 3 ^ (2 : ℕ) by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  ring

theorem kap_quarter_identity : kap (1 / 4) = 2 * Real.log 2 - Real.log 3 / 2 := by
  unfold kap
  rw [show (1 / 4 : ℝ) * (1 - 1 / 4) = 3 / 2 ^ (4 : ℕ) by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  ring

theorem kap_third_lower : (297 / 400 : ℝ) ≤ kap (1 / 3) := by
  have hL : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  rw [kap_third_identity]
  linarith only [log_three_lower, hL]

theorem kap_quarter_lower : (41811 / 50000 : ℝ) ≤ kap (1 / 4) := by
  have hL : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  rw [kap_quarter_identity]
  linarith only [log_three_upper, hL]

theorem radialSlope_third_formula :
    radialSlope (1 / 3) = 1 + (3 / 4) * H (1 / 3) / kap (1 / 3) := by
  have hJ : J (1 / 3) = 1 := by norm_num [J, log_two_pos.ne']
  have hk : kap (1 / 3) ≠ 0 := (kap_pos (by norm_num) (by norm_num)).ne'
  unfold radialSlope
  rw [hJ, hn_eq_H_mul_log]
  field_simp [log_two_pos.ne', hk]
  ring

theorem radialSlope_quarter_formula :
    radialSlope (1 / 4) = Real.log 3 / Real.log 2 +
      (4 / 3) * H (1 / 4) / kap (1 / 4) := by
  have hJ : J (1 / 4) = Real.log 3 / Real.log 2 := by norm_num [J]
  have hk : kap (1 / 4) ≠ 0 := (kap_pos (by norm_num) (by norm_num)).ne'
  unfold radialSlope
  rw [hJ, hn_eq_H_mul_log]
  field_simp [log_two_pos.ne', hk]
  ring

theorem radialSlope_third_upper : radialSlope (1 / 3) ≤ (193 / 100 : ℝ) := by
  have hk : 0 < kap (1 / 3) := kap_pos (by norm_num) (by norm_num)
  have hpart : (3 / 4) * H (1 / 3) / kap (1 / 3) ≤ (93 / 100 : ℝ) := by
    apply (div_le_iff₀ hk).mpr
    linarith only [entropy_third_upper, kap_third_lower]
  rw [radialSlope_third_formula]
  linarith only [hpart]

theorem radialSlope_quarter_upper : radialSlope (1 / 4) ≤ (29 / 10 : ℝ) := by
  have hk : 0 < kap (1 / 4) := kap_pos (by norm_num) (by norm_num)
  have hpart : (4 / 3) * H (1 / 4) / kap (1 / 4) ≤ (197 / 150 : ℝ) := by
    apply (div_le_iff₀ hk).mpr
    linarith only [entropy_quarter_upper, kap_quarter_lower]
  have hJ : Real.log 3 / Real.log 2 ≤ (119 / 75 : ℝ) :=
    (div_le_iff₀ log_two_pos).mpr log_three_upper
  rw [radialSlope_quarter_formula]
  linarith only [hpart, hJ]

theorem theta_nine_fiftieths_upper : e8Theta (9 / 50) ≤ (193 / 100 : ℝ) := by
  have hc : (1 / 3 : ℝ) ≤ radialContact (2 * (9 / 50)) 1 :=
    contact_lower_of_entropy_upper (by norm_num) (by norm_num) (by norm_num)
      entropy_third_upper (by norm_num)
  exact (e8Theta_upper_of_contact_lower (by norm_num) (by norm_num)
    (by norm_num) hc).trans radialSlope_third_upper

theorem theta_three_tenths_upper : e8Theta (3 / 10) ≤ (29 / 10 : ℝ) := by
  have hc : (1 / 4 : ℝ) ≤ radialContact (2 * (3 / 10)) 1 :=
    contact_lower_of_entropy_upper (by norm_num) (by norm_num) (by norm_num)
      entropy_quarter_upper (by norm_num)
  exact (e8Theta_upper_of_contact_lower (by norm_num) (by norm_num)
    (by norm_num) hc).trans radialSlope_quarter_upper

#print axioms log_three_lower
#print axioms log_three_upper
#print axioms entropy_third_upper
#print axioms entropy_quarter_upper
#print axioms radialSlope_third_upper
#print axioms radialSlope_quarter_upper
#print axioms theta_nine_fiftieths_upper
#print axioms theta_three_tenths_upper

end GeneralCK.ZeroCapLeftStationaryLowAnchors

end


