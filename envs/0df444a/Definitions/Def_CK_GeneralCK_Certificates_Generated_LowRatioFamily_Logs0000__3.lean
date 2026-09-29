-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0000__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0000__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:18:07.938662+00:00
-- url     : https://prove2.me/theorems/be534eff-3580-4ab1-9f4a-78241c5c490c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0000 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0001, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0000 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0001, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0002)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0000 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0001, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0002)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0000 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0001, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0002) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0000 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0001, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0002).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0000 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (27969779 / 200000000) ≤ -Real.log (10000 / 11501) ∧
    -Real.log (10000 / 11501) ≤ (2185139 / 15625000) := by
  have h := checkLog_sound (w := (1501 / 21501)) (n := 12)
    (lo := (27969779 / 200000000)) (hi := (2185139 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11501 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11501 / 10000) = 1/(10000 / 11501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27969779 / 200000000) (2185139 / 15625000) (Real.log (11501 / 10000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11501 / 10000) = -Real.log (10000 / 11501) := by
    rw [show ((11501 / 10000) : ℝ) = ((10000 / 11501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (162636583 / 1000000000) ≤ -Real.log (8499 / 10000) ∧
    -Real.log (8499 / 10000) ≤ (20329573 / 125000000) := by
  have h := checkLog_sound (w := (1501 / 18499)) (n := 12)
    (lo := (162636583 / 1000000000)) (hi := (20329573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8499) = 1/(8499 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-20329573 / 125000000) (-162636583 / 1000000000) (Real.log (8499 / 10000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (69880971 / 500000000) ≤ -Real.log (20 / 23) ∧
    -Real.log (20 / 23) ≤ (139761943 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 43)) (n := 12)
    (lo := (69880971 / 500000000)) (hi := (139761943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 20) = 1/(20 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (69880971 / 500000000) (139761943 / 1000000000) (Real.log (23 / 20)) := by
  have h := reflection_log_3_neg
  have he : Real.log (23 / 20) = -Real.log (20 / 23) := by
    rw [show ((23 / 20) : ℝ) = ((20 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (162518929 / 1000000000) ≤ -Real.log (17 / 20) ∧
    -Real.log (17 / 20) ≤ (16251893 / 100000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 17) = 1/(17 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-16251893 / 100000000) (-162518929 / 1000000000) (Real.log (17 / 20)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18761 / 125000000) ≤ -Real.log (10000000 / 10001501) ∧
    -Real.log (10000000 / 10001501) ≤ (150089 / 1000000000) := by
  have h := checkLog_sound (w := (1501 / 20001501)) (n := 12)
    (lo := (18761 / 125000000)) (hi := (150089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001501 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001501 / 10000000) = 1/(10000000 / 10001501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18761 / 125000000) (150089 / 1000000000) (Real.log (10001501 / 10000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (10001501 / 10000000) = -Real.log (10000000 / 10001501) := by
    rw [show ((10001501 / 10000000) : ℝ) = ((10000000 / 10001501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (150111 / 1000000000) ≤ -Real.log (9998499 / 10000000) ∧
    -Real.log (9998499 / 10000000) ≤ (4691 / 31250000) := by
  have h := checkLog_sound (w := (1501 / 19998499)) (n := 12)
    (lo := (150111 / 1000000000)) (hi := (4691 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998499) = 1/(9998499 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4691 / 31250000) (-150111 / 1000000000) (Real.log (9998499 / 10000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7 : Bounds 0 0 (Real.log 1) := by norm_num [Bounds]

theorem reflection_log_8_neg : (36267761 / 500000000) ≤ -Real.log (1000000 / 1075231) ∧
    -Real.log (1000000 / 1075231) ≤ (72535523 / 1000000000) := by
  have h := checkLog_sound (w := (75231 / 2075231)) (n := 12)
    (lo := (36267761 / 500000000)) (hi := (72535523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075231 / 1000000) = 1/(1000000 / 1075231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (36267761 / 500000000) (72535523 / 1000000000) (Real.log (1075231 / 1000000)) := by
  have h := reflection_log_8_neg
  have he : Real.log (1075231 / 1000000) = -Real.log (1000000 / 1075231) := by
    rw [show ((1075231 / 1000000) : ℝ) = ((1000000 / 1075231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9_neg : (39105651 / 500000000) ≤ -Real.log (924769 / 1000000) ∧
    -Real.log (924769 / 1000000) ≤ (78211303 / 1000000000) := by
  have h := checkLog_sound (w := (75231 / 1924769)) (n := 12)
    (lo := (39105651 / 500000000)) (hi := (78211303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924769) = 1/(924769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (-78211303 / 1000000000) (-39105651 / 500000000) (Real.log (924769 / 1000000)) := by
  have h := reflection_log_9_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10_neg : (72722441 / 1000000000) ≤ -Real.log (125000 / 134429) ∧
    -Real.log (125000 / 134429) ≤ (36361221 / 500000000) := by
  have h := checkLog_sound (w := (9429 / 259429)) (n := 12)
    (lo := (72722441 / 1000000000)) (hi := (36361221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134429 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134429 / 125000) = 1/(125000 / 134429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (72722441 / 1000000000) (36361221 / 500000000) (Real.log (134429 / 125000)) := by
  have h := reflection_log_10_neg
  have he : Real.log (134429 / 125000) = -Real.log (125000 / 134429) := by
    rw [show ((134429 / 125000) : ℝ) = ((125000 / 134429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11_neg : (78428677 / 1000000000) ≤ -Real.log (115571 / 125000) ∧
    -Real.log (115571 / 125000) ≤ (39214339 / 500000000) := by
  have h := checkLog_sound (w := (9429 / 240571)) (n := 12)
    (lo := (78428677 / 1000000000)) (hi := (39214339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115571) = 1/(115571 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (-39214339 / 500000000) (-78428677 / 1000000000) (Real.log (115571 / 125000)) := by
  have h := reflection_log_11_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12_neg : (1426559 / 250000000) ≤ -Real.log (15536093959 / 15625000000) ∧
    -Real.log (15536093959 / 15625000000) ≤ (5706237 / 1000000000) := by
  have h := checkLog_sound (w := (88906041 / 31161093959)) (n := 12)
    (lo := (1426559 / 250000000)) (hi := (5706237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15536093959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15536093959) = 1/(15536093959 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5706237 / 1000000000) (-1426559 / 250000000) (Real.log (15536093959 / 15625000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (283789 / 50000000) ≤ -Real.log (994340296639 / 1000000000000) ∧
    -Real.log (994340296639 / 1000000000000) ≤ (5675781 / 1000000000) := by
  have h := checkLog_sound (w := (5659703361 / 1994340296639)) (n := 12)
    (lo := (283789 / 50000000)) (hi := (5675781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994340296639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994340296639) = 1/(994340296639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (-5675781 / 1000000000) (-283789 / 50000000) (Real.log (994340296639 / 1000000000000)) := by
  have h := reflection_log_13_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14_neg : (18843353 / 125000000) ≤ -Real.log (100000000000 / 116270225321) ∧
    -Real.log (100000000000 / 116270225321) ≤ (6029873 / 40000000) := by
  have h := checkLog_sound (w := (16270225321 / 216270225321)) (n := 12)
    (lo := (18843353 / 125000000)) (hi := (6029873 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116270225321 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116270225321 / 100000000000) = 1/(100000000000 / 116270225321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (18843353 / 125000000) (6029873 / 40000000) (Real.log (116270225321 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (116270225321 / 100000000000) = -Real.log (100000000000 / 116270225321) := by
    rw [show ((116270225321 / 100000000000) : ℝ) = ((100000000000 / 116270225321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (75575559 / 500000000) ≤ -Real.log (250000000000 / 290793105537) ∧
    -Real.log (250000000000 / 290793105537) ≤ (151151119 / 1000000000) := by
  have h := checkLog_sound (w := (40793105537 / 540793105537)) (n := 12)
    (lo := (75575559 / 500000000)) (hi := (151151119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290793105537 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290793105537 / 250000000000) = 1/(250000000000 / 290793105537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (75575559 / 500000000) (151151119 / 1000000000) (Real.log (290793105537 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (290793105537 / 250000000000) = -Real.log (250000000000 / 290793105537) := by
    rw [show ((290793105537 / 250000000000) : ℝ) = ((250000000000 / 290793105537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (302280871 / 1000000000) ≤ -Real.log (100000000000 / 135294117647) ∧
    -Real.log (100000000000 / 135294117647) ≤ (37785109 / 125000000) := by
  have h := checkLog_sound (w := (35294117647 / 235294117647)) (n := 12)
    (lo := (302280871 / 1000000000)) (hi := (37785109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135294117647 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135294117647 / 100000000000) = 1/(100000000000 / 135294117647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (302280871 / 1000000000) (37785109 / 125000000) (Real.log (135294117647 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (135294117647 / 100000000000) = -Real.log (100000000000 / 135294117647) := by
    rw [show ((135294117647 / 100000000000) : ℝ) = ((100000000000 / 135294117647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (151242739 / 500000000) ≤ -Real.log (250000000000 / 338304506413) ∧
    -Real.log (250000000000 / 338304506413) ≤ (302485479 / 1000000000) := by
  have h := checkLog_sound (w := (88304506413 / 588304506413)) (n := 12)
    (lo := (151242739 / 500000000)) (hi := (302485479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338304506413 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338304506413 / 250000000000) = 1/(250000000000 / 338304506413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (151242739 / 500000000) (302485479 / 1000000000) (Real.log (338304506413 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (338304506413 / 250000000000) = -Real.log (250000000000 / 338304506413) := by
    rw [show ((338304506413 / 250000000000) : ℝ) = ((250000000000 / 338304506413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (874599 / 6250000) ≤ -Real.log (5000 / 5751) ∧
    -Real.log (5000 / 5751) ≤ (139935841 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 10751)) (n := 12)
    (lo := (874599 / 6250000)) (hi := (139935841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5751 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5751 / 5000) = 1/(5000 / 5751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (874599 / 6250000) (139935841 / 1000000000) (Real.log (5751 / 5000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5751 / 5000) = -Real.log (5000 / 5751) := by
    rw [show ((5751 / 5000) : ℝ) = ((5000 / 5751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (162754251 / 1000000000) ≤ -Real.log (4249 / 5000) ∧
    -Real.log (4249 / 5000) ≤ (40688563 / 250000000) := by
  have h := checkLog_sound (w := (751 / 9249)) (n := 12)
    (lo := (162754251 / 1000000000)) (hi := (40688563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4249) = 1/(4249 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40688563 / 250000000) (-162754251 / 1000000000) (Real.log (4249 / 5000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37547 / 250000000) ≤ -Real.log (5000000 / 5000751) ∧
    -Real.log (5000000 / 5000751) ≤ (150189 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 10000751)) (n := 12)
    (lo := (37547 / 250000000)) (hi := (150189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000751 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000751 / 5000000) = 1/(5000000 / 5000751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (37547 / 250000000) (150189 / 1000000000) (Real.log (5000751 / 5000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5000751 / 5000000) = -Real.log (5000000 / 5000751) := by
    rw [show ((5000751 / 5000000) : ℝ) = ((5000000 / 5000751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_21_neg : (150211 / 1000000000) ≤ -Real.log (4999249 / 5000000) ∧
    -Real.log (4999249 / 5000000) ≤ (37553 / 250000000) := by
  have h := checkLog_sound (w := (751 / 9999249)) (n := 12)
    (lo := (150211 / 1000000000)) (hi := (37553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999249) = 1/(4999249 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_21 : Bounds (-37553 / 250000000) (-150211 / 1000000000) (Real.log (4999249 / 5000000)) := by
  have h := reflection_log_21_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_22_neg : (9072869 / 125000000) ≤ -Real.log (500000 / 537641) ∧
    -Real.log (500000 / 537641) ≤ (72582953 / 1000000000) := by
  have h := checkLog_sound (w := (37641 / 1037641)) (n := 12)
    (lo := (9072869 / 125000000)) (hi := (72582953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537641 / 500000) = 1/(500000 / 537641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_22 : Bounds (9072869 / 125000000) (72582953 / 1000000000) (Real.log (537641 / 500000)) := by
  have h := reflection_log_22_neg
  have he : Real.log (537641 / 500000) = -Real.log (500000 / 537641) := by
    rw [show ((537641 / 500000) : ℝ) = ((500000 / 537641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_23_neg : (19566613 / 250000000) ≤ -Real.log (462359 / 500000) ∧
    -Real.log (462359 / 500000) ≤ (78266453 / 1000000000) := by
  have h := checkLog_sound (w := (37641 / 962359)) (n := 12)
    (lo := (19566613 / 250000000)) (hi := (78266453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 462359) = 1/(462359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_23 : Bounds (-78266453 / 1000000000) (-19566613 / 250000000) (Real.log (462359 / 500000)) := by
  have h := reflection_log_23_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_24_neg : (36384931 / 500000000) ≤ -Real.log (1000000 / 1075483) ∧
    -Real.log (1000000 / 1075483) ≤ (72769863 / 1000000000) := by
  have h := checkLog_sound (w := (75483 / 2075483)) (n := 12)
    (lo := (36384931 / 500000000)) (hi := (72769863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075483 / 1000000) = 1/(1000000 / 1075483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_24 : Bounds (36384931 / 500000000) (72769863 / 1000000000) (Real.log (1075483 / 1000000)) := by
  have h := reflection_log_24_neg
  have he : Real.log (1075483 / 1000000) = -Real.log (1000000 / 1075483) := by
    rw [show ((1075483 / 1000000) : ℝ) = ((1000000 / 1075483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_25_neg : (122631 / 1562500) ≤ -Real.log (924517 / 1000000) ∧
    -Real.log (924517 / 1000000) ≤ (78483841 / 1000000000) := by
  have h := checkLog_sound (w := (75483 / 1924517)) (n := 12)
    (lo := (122631 / 1562500)) (hi := (78483841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924517) = 1/(924517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_25 : Bounds (-78483841 / 1000000000) (-122631 / 1562500) (Real.log (924517 / 1000000)) := by
  have h := reflection_log_25_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_26_neg : (5713977 / 1000000000) ≤ -Real.log (994302316711 / 1000000000000) ∧
    -Real.log (994302316711 / 1000000000000) ≤ (2856989 / 500000000) := by
  have h := checkLog_sound (w := (5697683289 / 1994302316711)) (n := 12)
    (lo := (5713977 / 1000000000)) (hi := (2856989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994302316711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994302316711) = 1/(994302316711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_26 : Bounds (-2856989 / 500000000) (-5713977 / 1000000000) (Real.log (994302316711 / 1000000000000)) := by
  have h := reflection_log_26_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_27_neg : (11367 / 2000000) ≤ -Real.log (248583155119 / 250000000000) ∧
    -Real.log (248583155119 / 250000000000) ≤ (5683501 / 1000000000) := by
  have h := checkLog_sound (w := (1416844881 / 498583155119)) (n := 12)
    (lo := (11367 / 2000000)) (hi := (5683501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248583155119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248583155119) = 1/(248583155119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_27 : Bounds (-5683501 / 1000000000) (-11367 / 2000000) (Real.log (248583155119 / 250000000000)) := by
  have h := reflection_log_27_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_28_neg : (30169881 / 200000000) ≤ -Real.log (500000000000 / 581410765227) ∧
    -Real.log (500000000000 / 581410765227) ≤ (75424703 / 500000000) := by
  have h := checkLog_sound (w := (81410765227 / 1081410765227)) (n := 12)
    (lo := (30169881 / 200000000)) (hi := (75424703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581410765227 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581410765227 / 500000000000) = 1/(500000000000 / 581410765227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_28 : Bounds (30169881 / 200000000) (75424703 / 500000000) (Real.log (581410765227 / 500000000000)) := by
  have h := reflection_log_28_neg
  have he : Real.log (581410765227 / 500000000000) = -Real.log (500000000000 / 581410765227) := by
    rw [show ((581410765227 / 500000000000) : ℝ) = ((500000000000 / 581410765227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_29_neg : (151253703 / 1000000000) ≤ -Real.log (500000000000 / 581645875631) ∧
    -Real.log (500000000000 / 581645875631) ≤ (18906713 / 125000000) := by
  have h := checkLog_sound (w := (81645875631 / 1081645875631)) (n := 12)
    (lo := (151253703 / 1000000000)) (hi := (18906713 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581645875631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581645875631 / 500000000000) = 1/(500000000000 / 581645875631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_29 : Bounds (151253703 / 1000000000) (18906713 / 125000000) (Real.log (581645875631 / 500000000000)) := by
  have h := reflection_log_29_neg
  have he : Real.log (581645875631 / 500000000000) = -Real.log (500000000000 / 581645875631) := by
    rw [show ((581645875631 / 500000000000) : ℝ) = ((500000000000 / 581645875631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_30_neg : (151242739 / 500000000) ≤ -Real.log (20000000000 / 27064360513) ∧
    -Real.log (20000000000 / 27064360513) ≤ (302485479 / 1000000000) := by
  have h := checkLog_sound (w := (7064360513 / 47064360513)) (n := 12)
    (lo := (151242739 / 500000000)) (hi := (302485479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27064360513 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27064360513 / 20000000000) = 1/(20000000000 / 27064360513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_30 : Bounds (151242739 / 500000000) (302485479 / 1000000000) (Real.log (27064360513 / 20000000000)) := by
  have h := reflection_log_30_neg
  have he : Real.log (27064360513 / 20000000000) = -Real.log (20000000000 / 27064360513) := by
    rw [show ((27064360513 / 20000000000) : ℝ) = ((20000000000 / 27064360513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_31_neg : (302690091 / 1000000000) ≤ -Real.log (500000000000 / 676747469993) ∧
    -Real.log (500000000000 / 676747469993) ≤ (75672523 / 250000000) := by
  have h := checkLog_sound (w := (176747469993 / 1176747469993)) (n := 12)
    (lo := (302690091 / 1000000000)) (hi := (75672523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676747469993 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676747469993 / 500000000000) = 1/(500000000000 / 676747469993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_31 : Bounds (302690091 / 1000000000) (75672523 / 250000000) (Real.log (676747469993 / 500000000000)) := by
  have h := reflection_log_31_neg
  have he : Real.log (676747469993 / 500000000000) = -Real.log (500000000000 / 676747469993) := by
    rw [show ((676747469993 / 500000000000) : ℝ) = ((500000000000 / 676747469993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_32_neg : (140022777 / 1000000000) ≤ -Real.log (10000 / 11503) ∧
    -Real.log (10000 / 11503) ≤ (70011389 / 500000000) := by
  have h := checkLog_sound (w := (1503 / 21503)) (n := 12)
    (lo := (140022777 / 1000000000)) (hi := (70011389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11503 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11503 / 10000) = 1/(10000 / 11503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_32 : Bounds (140022777 / 1000000000) (70011389 / 500000000) (Real.log (11503 / 10000)) := by
  have h := reflection_log_32_neg
  have he : Real.log (11503 / 10000) = -Real.log (10000 / 11503) := by
    rw [show ((11503 / 10000) : ℝ) = ((10000 / 11503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_33_neg : (40717983 / 250000000) ≤ -Real.log (8497 / 10000) ∧
    -Real.log (8497 / 10000) ≤ (162871933 / 1000000000) := by
  have h := checkLog_sound (w := (1503 / 18497)) (n := 12)
    (lo := (40717983 / 250000000)) (hi := (162871933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8497) = 1/(8497 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_33 : Bounds (-162871933 / 1000000000) (-40717983 / 250000000) (Real.log (8497 / 10000)) := by
  have h := reflection_log_33_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_34_neg : (9393 / 62500000) ≤ -Real.log (10000000 / 10001503) ∧
    -Real.log (10000000 / 10001503) ≤ (150289 / 1000000000) := by
  have h := checkLog_sound (w := (1503 / 20001503)) (n := 12)
    (lo := (9393 / 62500000)) (hi := (150289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001503 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001503 / 10000000) = 1/(10000000 / 10001503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_34 : Bounds (9393 / 62500000) (150289 / 1000000000) (Real.log (10001503 / 10000000)) := by
  have h := reflection_log_34_neg
  have he : Real.log (10001503 / 10000000) = -Real.log (10000000 / 10001503) := by
    rw [show ((10001503 / 10000000) : ℝ) = ((10000000 / 10001503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_35_neg : (150311 / 1000000000) ≤ -Real.log (9998497 / 10000000) ∧
    -Real.log (9998497 / 10000000) ≤ (18789 / 125000000) := by
  have h := checkLog_sound (w := (1503 / 19998497)) (n := 12)
    (lo := (150311 / 1000000000)) (hi := (18789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998497) = 1/(9998497 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_35 : Bounds (-18789 / 125000000) (-150311 / 1000000000) (Real.log (9998497 / 10000000)) := by
  have h := reflection_log_35_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_36_neg : (72629451 / 1000000000) ≤ -Real.log (250000 / 268833) ∧
    -Real.log (250000 / 268833) ≤ (18157363 / 250000000) := by
  have h := checkLog_sound (w := (18833 / 518833)) (n := 12)
    (lo := (72629451 / 1000000000)) (hi := (18157363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268833 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(268833 / 250000) = 1/(250000 / 268833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_36 : Bounds (72629451 / 1000000000) (18157363 / 250000000) (Real.log (268833 / 250000)) := by
  have h := reflection_log_36_neg
  have he : Real.log (268833 / 250000) = -Real.log (250000 / 268833) := by
    rw [show ((268833 / 250000) : ℝ) = ((250000 / 268833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_37_neg : (19580131 / 250000000) ≤ -Real.log (231167 / 250000) ∧
    -Real.log (231167 / 250000) ≤ (3132821 / 40000000) := by
  have h := checkLog_sound (w := (18833 / 481167)) (n := 12)
    (lo := (19580131 / 250000000)) (hi := (3132821 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 231167) = 1/(231167 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_37 : Bounds (-3132821 / 40000000) (-19580131 / 250000000) (Real.log (231167 / 250000)) := by
  have h := reflection_log_37_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_38_neg : (36408641 / 500000000) ≤ -Real.log (500000 / 537767) ∧
    -Real.log (500000 / 537767) ≤ (72817283 / 1000000000) := by
  have h := checkLog_sound (w := (37767 / 1037767)) (n := 12)
    (lo := (36408641 / 500000000)) (hi := (72817283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537767 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537767 / 500000) = 1/(500000 / 537767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_38 : Bounds (36408641 / 500000000) (72817283 / 1000000000) (Real.log (537767 / 500000)) := by
  have h := reflection_log_38_neg
  have he : Real.log (537767 / 500000) = -Real.log (500000 / 537767) := by
    rw [show ((537767 / 500000) : ℝ) = ((500000 / 537767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_39_neg : (15707801 / 200000000) ≤ -Real.log (462233 / 500000) ∧
    -Real.log (462233 / 500000) ≤ (39269503 / 500000000) := by
  have h := checkLog_sound (w := (37767 / 962233)) (n := 12)
    (lo := (15707801 / 200000000)) (hi := (39269503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 462233) = 1/(462233 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_39 : Bounds (-39269503 / 500000000) (-15707801 / 200000000) (Real.log (462233 / 500000)) := by
  have h := reflection_log_39_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_40_neg : (5721723 / 1000000000) ≤ -Real.log (248573653711 / 250000000000) ∧
    -Real.log (248573653711 / 250000000000) ≤ (1430431 / 250000000) := by
  have h := checkLog_sound (w := (1426346289 / 498573653711)) (n := 12)
    (lo := (5721723 / 1000000000)) (hi := (1430431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248573653711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248573653711) = 1/(248573653711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_40 : Bounds (-1430431 / 250000000) (-5721723 / 1000000000) (Real.log (248573653711 / 250000000000)) := by
  have h := reflection_log_40_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_41_neg : (5691073 / 1000000000) ≤ -Real.log (62145318111 / 62500000000) ∧
    -Real.log (62145318111 / 62500000000) ≤ (2845537 / 500000000) := by
  have h := checkLog_sound (w := (354681889 / 124645318111)) (n := 12)
    (lo := (5691073 / 1000000000)) (hi := (2845537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62145318111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62145318111) = 1/(62145318111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_41 : Bounds (-2845537 / 500000000) (-5691073 / 1000000000) (Real.log (62145318111 / 62500000000)) := by
  have h := reflection_log_41_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_42_neg : (6037999 / 40000000) ≤ -Real.log (500000000000 / 581469240851) ∧
    -Real.log (500000000000 / 581469240851) ≤ (18868747 / 125000000) := by
  have h := checkLog_sound (w := (81469240851 / 1081469240851)) (n := 12)
    (lo := (6037999 / 40000000)) (hi := (18868747 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581469240851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581469240851 / 500000000000) = 1/(500000000000 / 581469240851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_42 : Bounds (6037999 / 40000000) (18868747 / 125000000) (Real.log (581469240851 / 500000000000)) := by
  have h := reflection_log_42_neg
  have he : Real.log (581469240851 / 500000000000) = -Real.log (500000000000 / 581469240851) := by
    rw [show ((581469240851 / 500000000000) : ℝ) = ((500000000000 / 581469240851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_43_neg : (151356287 / 1000000000) ≤ -Real.log (50000000000 / 58170554677) ∧
    -Real.log (50000000000 / 58170554677) ≤ (1182471 / 7812500) := by
  have h := checkLog_sound (w := (8170554677 / 108170554677)) (n := 12)
    (lo := (151356287 / 1000000000)) (hi := (1182471 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58170554677 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58170554677 / 50000000000) = 1/(50000000000 / 58170554677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_43 : Bounds (151356287 / 1000000000) (1182471 / 7812500) (Real.log (58170554677 / 50000000000)) := by
  have h := reflection_log_43_neg
  have he : Real.log (58170554677 / 50000000000) = -Real.log (50000000000 / 58170554677) := by
    rw [show ((58170554677 / 50000000000) : ℝ) = ((50000000000 / 58170554677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_44_neg : (302690091 / 1000000000) ≤ -Real.log (62500000000 / 84593433749) ∧
    -Real.log (62500000000 / 84593433749) ≤ (75672523 / 250000000) := by
  have h := checkLog_sound (w := (22093433749 / 147093433749)) (n := 12)
    (lo := (302690091 / 1000000000)) (hi := (75672523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84593433749 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84593433749 / 62500000000) = 1/(62500000000 / 84593433749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_44 : Bounds (302690091 / 1000000000) (75672523 / 250000000) (Real.log (84593433749 / 62500000000)) := by
  have h := reflection_log_44_neg
  have he : Real.log (84593433749 / 62500000000) = -Real.log (62500000000 / 84593433749) := by
    rw [show ((84593433749 / 62500000000) : ℝ) = ((62500000000 / 84593433749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_45_neg : (30289471 / 100000000) ≤ -Real.log (500000000000 / 676885959751) ∧
    -Real.log (500000000000 / 676885959751) ≤ (302894711 / 1000000000) := by
  have h := checkLog_sound (w := (176885959751 / 1176885959751)) (n := 12)
    (lo := (30289471 / 100000000)) (hi := (302894711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676885959751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676885959751 / 500000000000) = 1/(500000000000 / 676885959751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_45 : Bounds (30289471 / 100000000) (302894711 / 1000000000) (Real.log (676885959751 / 500000000000)) := by
  have h := reflection_log_45_neg
  have he : Real.log (676885959751 / 500000000000) = -Real.log (500000000000 / 676885959751) := by
    rw [show ((676885959751 / 500000000000) : ℝ) = ((500000000000 / 676885959751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_46_neg : (140109707 / 1000000000) ≤ -Real.log (625 / 719) ∧
    -Real.log (625 / 719) ≤ (35027427 / 250000000) := by
  have h := checkLog_sound (w := (47 / 672)) (n := 12)
    (lo := (140109707 / 1000000000)) (hi := (35027427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719 / 625) = 1/(625 / 719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_46 : Bounds (140109707 / 1000000000) (35027427 / 250000000) (Real.log (719 / 625)) := by
  have h := reflection_log_46_neg
  have he : Real.log (719 / 625) = -Real.log (625 / 719) := by
    rw [show ((719 / 625) : ℝ) = ((625 / 719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_47_neg : (40747407 / 250000000) ≤ -Real.log (531 / 625) ∧
    -Real.log (531 / 625) ≤ (162989629 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 578)) (n := 12)
    (lo := (40747407 / 250000000)) (hi := (162989629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 531) = 1/(531 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_47 : Bounds (-162989629 / 1000000000) (-40747407 / 250000000) (Real.log (531 / 625)) := by
  have h := reflection_log_47_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_48_neg : (37597 / 250000000) ≤ -Real.log (312500 / 312547) ∧
    -Real.log (312500 / 312547) ≤ (150389 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 625047)) (n := 12)
    (lo := (37597 / 250000000)) (hi := (150389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312547 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312547 / 312500) = 1/(312500 / 312547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_48 : Bounds (37597 / 250000000) (150389 / 1000000000) (Real.log (312547 / 312500)) := by
  have h := reflection_log_48_neg
  have he : Real.log (312547 / 312500) = -Real.log (312500 / 312547) := by
    rw [show ((312547 / 312500) : ℝ) = ((312500 / 312547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_49_neg : (150411 / 1000000000) ≤ -Real.log (312453 / 312500) ∧
    -Real.log (312453 / 312500) ≤ (37603 / 250000000) := by
  have h := checkLog_sound (w := (47 / 624953)) (n := 12)
    (lo := (150411 / 1000000000)) (hi := (37603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312453) = 1/(312453 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_49 : Bounds (-37603 / 250000000) (-150411 / 1000000000) (Real.log (312453 / 312500)) := by
  have h := reflection_log_49_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_50_neg : (72676877 / 1000000000) ≤ -Real.log (1000000 / 1075383) ∧
    -Real.log (1000000 / 1075383) ≤ (36338439 / 500000000) := by
  have h := checkLog_sound (w := (75383 / 2075383)) (n := 12)
    (lo := (72676877 / 1000000000)) (hi := (36338439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075383 / 1000000) = 1/(1000000 / 1075383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_50 : Bounds (72676877 / 1000000000) (36338439 / 500000000) (Real.log (1075383 / 1000000)) := by
  have h := reflection_log_50_neg
  have he : Real.log (1075383 / 1000000) = -Real.log (1000000 / 1075383) := by
    rw [show ((1075383 / 1000000) : ℝ) = ((1000000 / 1075383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_51_neg : (78375681 / 1000000000) ≤ -Real.log (924617 / 1000000) ∧
    -Real.log (924617 / 1000000) ≤ (39187841 / 500000000) := by
  have h := checkLog_sound (w := (75383 / 1924617)) (n := 12)
    (lo := (78375681 / 1000000000)) (hi := (39187841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924617) = 1/(924617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_51 : Bounds (-39187841 / 500000000) (-78375681 / 1000000000) (Real.log (924617 / 1000000)) := by
  have h := reflection_log_51_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_52_neg : (72863769 / 1000000000) ≤ -Real.log (15625 / 16806) ∧
    -Real.log (15625 / 16806) ≤ (7286377 / 100000000) := by
  have h := checkLog_sound (w := (1181 / 32431)) (n := 12)
    (lo := (72863769 / 1000000000)) (hi := (7286377 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16806 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16806 / 15625) = 1/(15625 / 16806) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_52 : Bounds (72863769 / 1000000000) (7286377 / 100000000) (Real.log (16806 / 15625)) := by
  have h := reflection_log_52_neg
  have he : Real.log (16806 / 15625) = -Real.log (15625 / 16806) := by
    rw [show ((16806 / 15625) : ℝ) = ((15625 / 16806) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_53_neg : (19648273 / 250000000) ≤ -Real.log (14444 / 15625) ∧
    -Real.log (14444 / 15625) ≤ (78593093 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 30069)) (n := 12)
    (lo := (19648273 / 250000000)) (hi := (78593093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14444) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14444) = 1/(14444 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_53 : Bounds (-78593093 / 1000000000) (-19648273 / 250000000) (Real.log (14444 / 15625)) := by
  have h := reflection_log_53_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_54_neg : (2864661 / 500000000) ≤ -Real.log (242745864 / 244140625) ∧
    -Real.log (242745864 / 244140625) ≤ (5729323 / 1000000000) := by
  have h := checkLog_sound (w := (1394761 / 486886489)) (n := 12)
    (lo := (2864661 / 500000000)) (hi := (5729323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242745864) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242745864) = 1/(242745864 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_54 : Bounds (-5729323 / 1000000000) (-2864661 / 500000000) (Real.log (242745864 / 244140625)) := by
  have h := reflection_log_54_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_55_neg : (1424701 / 250000000) ≤ -Real.log (994317403311 / 1000000000000) ∧
    -Real.log (994317403311 / 1000000000000) ≤ (1139761 / 200000000) := by
  have h := checkLog_sound (w := (5682596689 / 1994317403311)) (n := 12)
    (lo := (1424701 / 250000000)) (hi := (1139761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994317403311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994317403311) = 1/(994317403311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_55 : Bounds (-1139761 / 200000000) (-1424701 / 250000000) (Real.log (994317403311 / 1000000000000)) := by
  have h := reflection_log_55_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_56_neg : (75526279 / 500000000) ≤ -Real.log (500000000000 / 581528892503) ∧
    -Real.log (500000000000 / 581528892503) ≤ (151052559 / 1000000000) := by
  have h := checkLog_sound (w := (81528892503 / 1081528892503)) (n := 12)
    (lo := (75526279 / 500000000)) (hi := (151052559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581528892503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581528892503 / 500000000000) = 1/(500000000000 / 581528892503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_56 : Bounds (75526279 / 500000000) (151052559 / 1000000000) (Real.log (581528892503 / 500000000000)) := by
  have h := reflection_log_56_neg
  have he : Real.log (581528892503 / 500000000000) = -Real.log (500000000000 / 581528892503) := by
    rw [show ((581528892503 / 500000000000) : ℝ) = ((500000000000 / 581528892503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_57_neg : (75728431 / 500000000) ≤ -Real.log (500000000000 / 581764054279) ∧
    -Real.log (500000000000 / 581764054279) ≤ (151456863 / 1000000000) := by
  have h := checkLog_sound (w := (81764054279 / 1081764054279)) (n := 12)
    (lo := (75728431 / 500000000)) (hi := (151456863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581764054279 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581764054279 / 500000000000) = 1/(500000000000 / 581764054279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_57 : Bounds (75728431 / 500000000) (151456863 / 1000000000) (Real.log (581764054279 / 500000000000)) := by
  have h := reflection_log_57_neg
  have he : Real.log (581764054279 / 500000000000) = -Real.log (500000000000 / 581764054279) := by
    rw [show ((581764054279 / 500000000000) : ℝ) = ((500000000000 / 581764054279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_58_neg : (30289471 / 100000000) ≤ -Real.log (2000000000 / 2707543839) ∧
    -Real.log (2000000000 / 2707543839) ≤ (302894711 / 1000000000) := by
  have h := checkLog_sound (w := (707543839 / 4707543839)) (n := 12)
    (lo := (30289471 / 100000000)) (hi := (302894711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2707543839 / 2000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2707543839 / 2000000000) = 1/(2000000000 / 2707543839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_58 : Bounds (30289471 / 100000000) (302894711 / 1000000000) (Real.log (2707543839 / 2000000000)) := by
  have h := reflection_log_58_neg
  have he : Real.log (2707543839 / 2000000000) = -Real.log (2000000000 / 2707543839) := by
    rw [show ((2707543839 / 2000000000) : ℝ) = ((2000000000 / 2707543839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_59_neg : (37887417 / 125000000) ≤ -Real.log (50000000000 / 67702448211) ∧
    -Real.log (50000000000 / 67702448211) ≤ (303099337 / 1000000000) := by
  have h := checkLog_sound (w := (17702448211 / 117702448211)) (n := 12)
    (lo := (37887417 / 125000000)) (hi := (303099337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67702448211 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67702448211 / 50000000000) = 1/(50000000000 / 67702448211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_59 : Bounds (37887417 / 125000000) (303099337 / 1000000000) (Real.log (67702448211 / 50000000000)) := by
  have h := reflection_log_59_neg
  have he : Real.log (67702448211 / 50000000000) = -Real.log (50000000000 / 67702448211) := by
    rw [show ((67702448211 / 50000000000) : ℝ) = ((50000000000 / 67702448211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_60_neg : (14019663 / 100000000) ≤ -Real.log (2000 / 2301) ∧
    -Real.log (2000 / 2301) ≤ (140196631 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 4301)) (n := 12)
    (lo := (14019663 / 100000000)) (hi := (140196631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2301 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2301 / 2000) = 1/(2000 / 2301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_60 : Bounds (14019663 / 100000000) (140196631 / 1000000000) (Real.log (2301 / 2000)) := by
  have h := reflection_log_60_neg
  have he : Real.log (2301 / 2000) = -Real.log (2000 / 2301) := by
    rw [show ((2301 / 2000) : ℝ) = ((2000 / 2301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_61_neg : (163107337 / 1000000000) ≤ -Real.log (1699 / 2000) ∧
    -Real.log (1699 / 2000) ≤ (81553669 / 500000000) := by
  have h := checkLog_sound (w := (301 / 3699)) (n := 12)
    (lo := (163107337 / 1000000000)) (hi := (81553669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1699) = 1/(1699 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_61 : Bounds (-81553669 / 500000000) (-163107337 / 1000000000) (Real.log (1699 / 2000)) := by
  have h := reflection_log_61_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_62_neg : (18811 / 125000000) ≤ -Real.log (2000000 / 2000301) ∧
    -Real.log (2000000 / 2000301) ≤ (150489 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 4000301)) (n := 12)
    (lo := (18811 / 125000000)) (hi := (150489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000301 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000301 / 2000000) = 1/(2000000 / 2000301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_62 : Bounds (18811 / 125000000) (150489 / 1000000000) (Real.log (2000301 / 2000000)) := by
  have h := reflection_log_62_neg
  have he : Real.log (2000301 / 2000000) = -Real.log (2000000 / 2000301) := by
    rw [show ((2000301 / 2000000) : ℝ) = ((2000000 / 2000301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_63_neg : (150511 / 1000000000) ≤ -Real.log (1999699 / 2000000) ∧
    -Real.log (1999699 / 2000000) ≤ (9407 / 62500000) := by
  have h := checkLog_sound (w := (301 / 3999699)) (n := 12)
    (lo := (150511 / 1000000000)) (hi := (9407 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999699) = 1/(1999699 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_63 : Bounds (-9407 / 62500000) (-150511 / 1000000000) (Real.log (1999699 / 2000000)) := by
  have h := reflection_log_63_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0001 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_64_neg : (72723371 / 1000000000) ≤ -Real.log (1000000 / 1075433) ∧
    -Real.log (1000000 / 1075433) ≤ (18180843 / 250000000) := by
  have h := checkLog_sound (w := (75433 / 2075433)) (n := 12)
    (lo := (72723371 / 1000000000)) (hi := (18180843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075433 / 1000000) = 1/(1000000 / 1075433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_64 : Bounds (72723371 / 1000000000) (18180843 / 250000000) (Real.log (1075433 / 1000000)) := by
  have h := reflection_log_64_neg
  have he : Real.log (1075433 / 1000000) = -Real.log (1000000 / 1075433) := by
    rw [show ((1075433 / 1000000) : ℝ) = ((1000000 / 1075433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_65_neg : (78429759 / 1000000000) ≤ -Real.log (924567 / 1000000) ∧
    -Real.log (924567 / 1000000) ≤ (245093 / 3125000) := by
  have h := checkLog_sound (w := (75433 / 1924567)) (n := 12)
    (lo := (78429759 / 1000000000)) (hi := (245093 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924567) = 1/(924567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_65 : Bounds (-245093 / 3125000) (-78429759 / 1000000000) (Real.log (924567 / 1000000)) := by
  have h := reflection_log_65_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_66_neg : (4556949 / 62500000) ≤ -Real.log (200000 / 215127) ∧
    -Real.log (200000 / 215127) ≤ (14582237 / 200000000) := by
  have h := checkLog_sound (w := (15127 / 415127)) (n := 12)
    (lo := (4556949 / 62500000)) (hi := (14582237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215127 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215127 / 200000) = 1/(200000 / 215127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_66 : Bounds (4556949 / 62500000) (14582237 / 200000000) (Real.log (215127 / 200000)) := by
  have h := reflection_log_66_neg
  have he : Real.log (215127 / 200000) = -Real.log (200000 / 215127) := by
    rw [show ((215127 / 200000) : ℝ) = ((200000 / 215127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_67_neg : (78648263 / 1000000000) ≤ -Real.log (184873 / 200000) ∧
    -Real.log (184873 / 200000) ≤ (9831033 / 125000000) := by
  have h := checkLog_sound (w := (15127 / 384873)) (n := 12)
    (lo := (78648263 / 1000000000)) (hi := (9831033 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184873) = 1/(184873 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_67 : Bounds (-9831033 / 125000000) (-78648263 / 1000000000) (Real.log (184873 / 200000)) := by
  have h := reflection_log_67_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_68_neg : (2868539 / 500000000) ≤ -Real.log (39771173871 / 40000000000) ∧
    -Real.log (39771173871 / 40000000000) ≤ (5737079 / 1000000000) := by
  have h := checkLog_sound (w := (228826129 / 79771173871)) (n := 12)
    (lo := (2868539 / 500000000)) (hi := (5737079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39771173871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39771173871) = 1/(39771173871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_68 : Bounds (-5737079 / 1000000000) (-2868539 / 500000000) (Real.log (39771173871 / 40000000000)) := by
  have h := reflection_log_68_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_69_neg : (5706387 / 1000000000) ≤ -Real.log (994309862511 / 1000000000000) ∧
    -Real.log (994309862511 / 1000000000000) ≤ (1426597 / 250000000) := by
  have h := checkLog_sound (w := (5690137489 / 1994309862511)) (n := 12)
    (lo := (5706387 / 1000000000)) (hi := (1426597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994309862511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994309862511) = 1/(994309862511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_69 : Bounds (-1426597 / 250000000) (-5706387 / 1000000000) (Real.log (994309862511 / 1000000000000)) := by
  have h := reflection_log_69_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_70_neg : (15115313 / 100000000) ≤ -Real.log (500000000000 / 581587380903) ∧
    -Real.log (500000000000 / 581587380903) ≤ (151153131 / 1000000000) := by
  have h := checkLog_sound (w := (81587380903 / 1081587380903)) (n := 12)
    (lo := (15115313 / 100000000)) (hi := (151153131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581587380903 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581587380903 / 500000000000) = 1/(500000000000 / 581587380903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_70 : Bounds (15115313 / 100000000) (151153131 / 1000000000) (Real.log (581587380903 / 500000000000)) := by
  have h := reflection_log_70_neg
  have he : Real.log (581587380903 / 500000000000) = -Real.log (500000000000 / 581587380903) := by
    rw [show ((581587380903 / 500000000000) : ℝ) = ((500000000000 / 581587380903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_71_neg : (18944931 / 125000000) ≤ -Real.log (500000000000 / 581823738459) ∧
    -Real.log (500000000000 / 581823738459) ≤ (151559449 / 1000000000) := by
  have h := checkLog_sound (w := (81823738459 / 1081823738459)) (n := 12)
    (lo := (18944931 / 125000000)) (hi := (151559449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581823738459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581823738459 / 500000000000) = 1/(500000000000 / 581823738459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_71 : Bounds (18944931 / 125000000) (151559449 / 1000000000) (Real.log (581823738459 / 500000000000)) := by
  have h := reflection_log_71_neg
  have he : Real.log (581823738459 / 500000000000) = -Real.log (500000000000 / 581823738459) := by
    rw [show ((581823738459 / 500000000000) : ℝ) = ((500000000000 / 581823738459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_72_neg : (37887417 / 125000000) ≤ -Real.log (500000000000 / 677024482109) ∧
    -Real.log (500000000000 / 677024482109) ≤ (303099337 / 1000000000) := by
  have h := checkLog_sound (w := (177024482109 / 1177024482109)) (n := 12)
    (lo := (37887417 / 125000000)) (hi := (303099337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677024482109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677024482109 / 500000000000) = 1/(500000000000 / 677024482109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_72 : Bounds (37887417 / 125000000) (303099337 / 1000000000) (Real.log (677024482109 / 500000000000)) := by
  have h := reflection_log_72_neg
  have he : Real.log (677024482109 / 500000000000) = -Real.log (500000000000 / 677024482109) := by
    rw [show ((677024482109 / 500000000000) : ℝ) = ((500000000000 / 677024482109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_73_neg : (9478249 / 31250000) ≤ -Real.log (500000000000 / 677163037081) ∧
    -Real.log (500000000000 / 677163037081) ≤ (303303969 / 1000000000) := by
  have h := checkLog_sound (w := (177163037081 / 1177163037081)) (n := 12)
    (lo := (9478249 / 31250000)) (hi := (303303969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677163037081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677163037081 / 500000000000) = 1/(500000000000 / 677163037081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_73 : Bounds (9478249 / 31250000) (303303969 / 1000000000) (Real.log (677163037081 / 500000000000)) := by
  have h := reflection_log_73_neg
  have he : Real.log (677163037081 / 500000000000) = -Real.log (500000000000 / 677163037081) := by
    rw [show ((677163037081 / 500000000000) : ℝ) = ((500000000000 / 677163037081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_74_neg : (28056709 / 200000000) ≤ -Real.log (5000 / 5753) ∧
    -Real.log (5000 / 5753) ≤ (70141773 / 500000000) := by
  have h := checkLog_sound (w := (753 / 10753)) (n := 12)
    (lo := (28056709 / 200000000)) (hi := (70141773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5753 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5753 / 5000) = 1/(5000 / 5753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_74 : Bounds (28056709 / 200000000) (70141773 / 500000000) (Real.log (5753 / 5000)) := by
  have h := reflection_log_74_neg
  have he : Real.log (5753 / 5000) = -Real.log (5000 / 5753) := by
    rw [show ((5753 / 5000) : ℝ) = ((5000 / 5753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_75_neg : (163225061 / 1000000000) ≤ -Real.log (4247 / 5000) ∧
    -Real.log (4247 / 5000) ≤ (81612531 / 500000000) := by
  have h := checkLog_sound (w := (753 / 9247)) (n := 12)
    (lo := (163225061 / 1000000000)) (hi := (81612531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4247) = 1/(4247 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_75 : Bounds (-81612531 / 500000000) (-163225061 / 1000000000) (Real.log (4247 / 5000)) := by
  have h := reflection_log_75_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_76_neg : (37647 / 250000000) ≤ -Real.log (5000000 / 5000753) ∧
    -Real.log (5000000 / 5000753) ≤ (150589 / 1000000000) := by
  have h := checkLog_sound (w := (753 / 10000753)) (n := 12)
    (lo := (37647 / 250000000)) (hi := (150589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000753 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000753 / 5000000) = 1/(5000000 / 5000753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_76 : Bounds (37647 / 250000000) (150589 / 1000000000) (Real.log (5000753 / 5000000)) := by
  have h := reflection_log_76_neg
  have he : Real.log (5000753 / 5000000) = -Real.log (5000000 / 5000753) := by
    rw [show ((5000753 / 5000000) : ℝ) = ((5000000 / 5000753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_77_neg : (150611 / 1000000000) ≤ -Real.log (4999247 / 5000000) ∧
    -Real.log (4999247 / 5000000) ≤ (37653 / 250000000) := by
  have h := checkLog_sound (w := (753 / 9999247)) (n := 12)
    (lo := (150611 / 1000000000)) (hi := (37653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999247) = 1/(4999247 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_77 : Bounds (-37653 / 250000000) (-150611 / 1000000000) (Real.log (4999247 / 5000000)) := by
  have h := reflection_log_77_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_78_neg : (9096349 / 125000000) ≤ -Real.log (250000 / 268871) ∧
    -Real.log (250000 / 268871) ≤ (72770793 / 1000000000) := by
  have h := checkLog_sound (w := (18871 / 518871)) (n := 12)
    (lo := (9096349 / 125000000)) (hi := (72770793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268871 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(268871 / 250000) = 1/(250000 / 268871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_78 : Bounds (9096349 / 125000000) (72770793 / 1000000000) (Real.log (268871 / 250000)) := by
  have h := reflection_log_78_neg
  have he : Real.log (268871 / 250000) = -Real.log (250000 / 268871) := by
    rw [show ((268871 / 250000) : ℝ) = ((250000 / 268871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_79_neg : (78484921 / 1000000000) ≤ -Real.log (231129 / 250000) ∧
    -Real.log (231129 / 250000) ≤ (39242461 / 500000000) := by
  have h := checkLog_sound (w := (18871 / 481129)) (n := 12)
    (lo := (78484921 / 1000000000)) (hi := (39242461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 231129) = 1/(231129 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_79 : Bounds (-39242461 / 500000000) (-78484921 / 1000000000) (Real.log (231129 / 250000)) := by
  have h := reflection_log_79_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_80_neg : (72958597 / 1000000000) ≤ -Real.log (500000 / 537843) ∧
    -Real.log (500000 / 537843) ≤ (36479299 / 500000000) := by
  have h := checkLog_sound (w := (37843 / 1037843)) (n := 12)
    (lo := (72958597 / 1000000000)) (hi := (36479299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537843 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537843 / 500000) = 1/(500000 / 537843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_80 : Bounds (72958597 / 1000000000) (36479299 / 500000000) (Real.log (537843 / 500000)) := by
  have h := reflection_log_80_neg
  have he : Real.log (537843 / 500000) = -Real.log (500000 / 537843) := by
    rw [show ((537843 / 500000) : ℝ) = ((500000 / 537843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_81_neg : (39351719 / 500000000) ≤ -Real.log (462157 / 500000) ∧
    -Real.log (462157 / 500000) ≤ (78703439 / 1000000000) := by
  have h := checkLog_sound (w := (37843 / 962157)) (n := 12)
    (lo := (39351719 / 500000000)) (hi := (78703439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 462157) = 1/(462157 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_81 : Bounds (-78703439 / 1000000000) (-39351719 / 500000000) (Real.log (462157 / 500000)) := by
  have h := reflection_log_81_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_82_neg : (143621 / 25000000) ≤ -Real.log (248567907351 / 250000000000) ∧
    -Real.log (248567907351 / 250000000000) ≤ (5744841 / 1000000000) := by
  have h := checkLog_sound (w := (1432092649 / 498567907351)) (n := 12)
    (lo := (143621 / 25000000)) (hi := (5744841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248567907351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248567907351) = 1/(248567907351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_82 : Bounds (-5744841 / 1000000000) (-143621 / 25000000) (Real.log (248567907351 / 250000000000)) := by
  have h := reflection_log_82_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_83_neg : (357133 / 62500000) ≤ -Real.log (62143885359 / 62500000000) ∧
    -Real.log (62143885359 / 62500000000) ≤ (5714129 / 1000000000) := by
  have h := checkLog_sound (w := (356114641 / 124643885359)) (n := 12)
    (lo := (357133 / 62500000)) (hi := (5714129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62143885359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62143885359) = 1/(62143885359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_83 : Bounds (-5714129 / 1000000000) (-357133 / 62500000) (Real.log (62143885359 / 62500000000)) := by
  have h := reflection_log_83_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_84_neg : (75627857 / 500000000) ≤ -Real.log (500000000000 / 581647045589) ∧
    -Real.log (500000000000 / 581647045589) ≤ (30251143 / 200000000) := by
  have h := checkLog_sound (w := (81647045589 / 1081647045589)) (n := 12)
    (lo := (75627857 / 500000000)) (hi := (30251143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581647045589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581647045589 / 500000000000) = 1/(500000000000 / 581647045589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_84 : Bounds (75627857 / 500000000) (30251143 / 200000000) (Real.log (581647045589 / 500000000000)) := by
  have h := reflection_log_84_neg
  have he : Real.log (581647045589 / 500000000000) = -Real.log (500000000000 / 581647045589) := by
    rw [show ((581647045589 / 500000000000) : ℝ) = ((500000000000 / 581647045589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_85_neg : (30332407 / 200000000) ≤ -Real.log (20000000000 / 23275337169) ∧
    -Real.log (20000000000 / 23275337169) ≤ (37915509 / 250000000) := by
  have h := checkLog_sound (w := (3275337169 / 43275337169)) (n := 12)
    (lo := (30332407 / 200000000)) (hi := (37915509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23275337169 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23275337169 / 20000000000) = 1/(20000000000 / 23275337169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_85 : Bounds (30332407 / 200000000) (37915509 / 250000000) (Real.log (23275337169 / 20000000000)) := by
  have h := reflection_log_85_neg
  have he : Real.log (23275337169 / 20000000000) = -Real.log (20000000000 / 23275337169) := by
    rw [show ((23275337169 / 20000000000) : ℝ) = ((20000000000 / 23275337169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_86_neg : (9478249 / 31250000) ≤ -Real.log (12500000000 / 16929075927) ∧
    -Real.log (12500000000 / 16929075927) ≤ (303303969 / 1000000000) := by
  have h := checkLog_sound (w := (4429075927 / 29429075927)) (n := 12)
    (lo := (9478249 / 31250000)) (hi := (303303969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16929075927 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16929075927 / 12500000000) = 1/(12500000000 / 16929075927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_86 : Bounds (9478249 / 31250000) (303303969 / 1000000000) (Real.log (16929075927 / 12500000000)) := by
  have h := reflection_log_86_neg
  have he : Real.log (16929075927 / 12500000000) = -Real.log (12500000000 / 16929075927) := by
    rw [show ((16929075927 / 12500000000) : ℝ) = ((12500000000 / 16929075927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_87_neg : (151754303 / 500000000) ≤ -Real.log (500000000000 / 677301624677) ∧
    -Real.log (500000000000 / 677301624677) ≤ (303508607 / 1000000000) := by
  have h := checkLog_sound (w := (177301624677 / 1177301624677)) (n := 12)
    (lo := (151754303 / 500000000)) (hi := (303508607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677301624677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677301624677 / 500000000000) = 1/(500000000000 / 677301624677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_87 : Bounds (151754303 / 500000000) (303508607 / 1000000000) (Real.log (677301624677 / 500000000000)) := by
  have h := reflection_log_87_neg
  have he : Real.log (677301624677 / 500000000000) = -Real.log (500000000000 / 677301624677) := by
    rw [show ((677301624677 / 500000000000) : ℝ) = ((500000000000 / 677301624677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_88_neg : (35092613 / 250000000) ≤ -Real.log (10000 / 11507) ∧
    -Real.log (10000 / 11507) ≤ (140370453 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 21507)) (n := 12)
    (lo := (35092613 / 250000000)) (hi := (140370453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11507 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11507 / 10000) = 1/(10000 / 11507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_88 : Bounds (35092613 / 250000000) (140370453 / 1000000000) (Real.log (11507 / 10000)) := by
  have h := reflection_log_88_neg
  have he : Real.log (11507 / 10000) = -Real.log (10000 / 11507) := by
    rw [show ((11507 / 10000) : ℝ) = ((10000 / 11507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_89_neg : (81671399 / 500000000) ≤ -Real.log (8493 / 10000) ∧
    -Real.log (8493 / 10000) ≤ (163342799 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 18493)) (n := 12)
    (lo := (81671399 / 500000000)) (hi := (163342799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8493) = 1/(8493 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_89 : Bounds (-163342799 / 1000000000) (-81671399 / 500000000) (Real.log (8493 / 10000)) := by
  have h := reflection_log_89_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_90_neg : (4709 / 31250000) ≤ -Real.log (10000000 / 10001507) ∧
    -Real.log (10000000 / 10001507) ≤ (150689 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 20001507)) (n := 12)
    (lo := (4709 / 31250000)) (hi := (150689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001507 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001507 / 10000000) = 1/(10000000 / 10001507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_90 : Bounds (4709 / 31250000) (150689 / 1000000000) (Real.log (10001507 / 10000000)) := by
  have h := reflection_log_90_neg
  have he : Real.log (10001507 / 10000000) = -Real.log (10000000 / 10001507) := by
    rw [show ((10001507 / 10000000) : ℝ) = ((10000000 / 10001507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_91_neg : (150711 / 1000000000) ≤ -Real.log (9998493 / 10000000) ∧
    -Real.log (9998493 / 10000000) ≤ (18839 / 125000000) := by
  have h := checkLog_sound (w := (1507 / 19998493)) (n := 12)
    (lo := (150711 / 1000000000)) (hi := (18839 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998493) = 1/(9998493 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_91 : Bounds (-18839 / 125000000) (-150711 / 1000000000) (Real.log (9998493 / 10000000)) := by
  have h := reflection_log_91_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_92_neg : (18204553 / 250000000) ≤ -Real.log (200000 / 215107) ∧
    -Real.log (200000 / 215107) ≤ (72818213 / 1000000000) := by
  have h := checkLog_sound (w := (15107 / 415107)) (n := 12)
    (lo := (18204553 / 250000000)) (hi := (72818213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215107 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215107 / 200000) = 1/(200000 / 215107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_92 : Bounds (18204553 / 250000000) (72818213 / 1000000000) (Real.log (215107 / 200000)) := by
  have h := reflection_log_92_neg
  have he : Real.log (215107 / 200000) = -Real.log (200000 / 215107) := by
    rw [show ((215107 / 200000) : ℝ) = ((200000 / 215107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_93_neg : (78540087 / 1000000000) ≤ -Real.log (184893 / 200000) ∧
    -Real.log (184893 / 200000) ≤ (9817511 / 125000000) := by
  have h := checkLog_sound (w := (15107 / 384893)) (n := 12)
    (lo := (78540087 / 1000000000)) (hi := (9817511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184893) = 1/(184893 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_93 : Bounds (-9817511 / 125000000) (-78540087 / 1000000000) (Real.log (184893 / 200000)) := by
  have h := reflection_log_93_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_94_neg : (36502539 / 500000000) ≤ -Real.log (125000 / 134467) ∧
    -Real.log (125000 / 134467) ≤ (73005079 / 1000000000) := by
  have h := checkLog_sound (w := (9467 / 259467)) (n := 12)
    (lo := (36502539 / 500000000)) (hi := (73005079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134467 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134467 / 125000) = 1/(125000 / 134467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_94 : Bounds (36502539 / 500000000) (73005079 / 1000000000) (Real.log (134467 / 125000)) := by
  have h := reflection_log_94_neg
  have he : Real.log (134467 / 125000) = -Real.log (125000 / 134467) := by
    rw [show ((134467 / 125000) : ℝ) = ((125000 / 134467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_95_neg : (78757533 / 1000000000) ≤ -Real.log (115533 / 125000) ∧
    -Real.log (115533 / 125000) ≤ (39378767 / 500000000) := by
  have h := checkLog_sound (w := (9467 / 240533)) (n := 12)
    (lo := (78757533 / 1000000000)) (hi := (39378767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115533) = 1/(115533 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_95 : Bounds (-39378767 / 500000000) (-78757533 / 1000000000) (Real.log (115533 / 125000)) := by
  have h := reflection_log_95_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_96_neg : (1150491 / 200000000) ≤ -Real.log (15535375911 / 15625000000) ∧
    -Real.log (15535375911 / 15625000000) ≤ (719057 / 125000000) := by
  have h := checkLog_sound (w := (89624089 / 31160375911)) (n := 12)
    (lo := (1150491 / 200000000)) (hi := (719057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15535375911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15535375911) = 1/(15535375911 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_96 : Bounds (-719057 / 125000000) (-1150491 / 200000000) (Real.log (15535375911 / 15625000000)) := by
  have h := reflection_log_96_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_97_neg : (2860937 / 500000000) ≤ -Real.log (39771778551 / 40000000000) ∧
    -Real.log (39771778551 / 40000000000) ≤ (1831 / 320000) := by
  have h := checkLog_sound (w := (228221449 / 79771778551)) (n := 12)
    (lo := (2860937 / 500000000)) (hi := (1831 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39771778551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39771778551) = 1/(39771778551 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_97 : Bounds (-1831 / 320000) (-2860937 / 500000000) (Real.log (39771778551 / 40000000000)) := by
  have h := reflection_log_97_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_98_neg : (151358299 / 1000000000) ≤ -Real.log (500000000000 / 581706716857) ∧
    -Real.log (500000000000 / 581706716857) ≤ (1513583 / 10000000) := by
  have h := checkLog_sound (w := (81706716857 / 1081706716857)) (n := 12)
    (lo := (151358299 / 1000000000)) (hi := (1513583 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581706716857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581706716857 / 500000000000) = 1/(500000000000 / 581706716857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_98 : Bounds (151358299 / 1000000000) (1513583 / 10000000) (Real.log (581706716857 / 500000000000)) := by
  have h := reflection_log_98_neg
  have he : Real.log (581706716857 / 500000000000) = -Real.log (500000000000 / 581706716857) := by
    rw [show ((581706716857 / 500000000000) : ℝ) = ((500000000000 / 581706716857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_99_neg : (37940653 / 250000000) ≤ -Real.log (250000000000 / 290970977989) ∧
    -Real.log (250000000000 / 290970977989) ≤ (151762613 / 1000000000) := by
  have h := checkLog_sound (w := (40970977989 / 540970977989)) (n := 12)
    (lo := (37940653 / 250000000)) (hi := (151762613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290970977989 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290970977989 / 250000000000) = 1/(250000000000 / 290970977989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_99 : Bounds (37940653 / 250000000) (151762613 / 1000000000) (Real.log (290970977989 / 250000000000)) := by
  have h := reflection_log_99_neg
  have he : Real.log (290970977989 / 250000000000) = -Real.log (250000000000 / 290970977989) := by
    rw [show ((290970977989 / 250000000000) : ℝ) = ((250000000000 / 290970977989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_100_neg : (151754303 / 500000000) ≤ -Real.log (125000000000 / 169325406169) ∧
    -Real.log (125000000000 / 169325406169) ≤ (303508607 / 1000000000) := by
  have h := checkLog_sound (w := (44325406169 / 294325406169)) (n := 12)
    (lo := (151754303 / 500000000)) (hi := (303508607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169325406169 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169325406169 / 125000000000) = 1/(125000000000 / 169325406169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_100 : Bounds (151754303 / 500000000) (303508607 / 1000000000) (Real.log (169325406169 / 125000000000)) := by
  have h := reflection_log_100_neg
  have he : Real.log (169325406169 / 125000000000) = -Real.log (125000000000 / 169325406169) := by
    rw [show ((169325406169 / 125000000000) : ℝ) = ((125000000000 / 169325406169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_101_neg : (303713251 / 1000000000) ≤ -Real.log (125000000000 / 169360061227) ∧
    -Real.log (125000000000 / 169360061227) ≤ (75928313 / 250000000) := by
  have h := checkLog_sound (w := (44360061227 / 294360061227)) (n := 12)
    (lo := (303713251 / 1000000000)) (hi := (75928313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169360061227 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169360061227 / 125000000000) = 1/(125000000000 / 169360061227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_101 : Bounds (303713251 / 1000000000) (75928313 / 250000000) (Real.log (169360061227 / 125000000000)) := by
  have h := reflection_log_101_neg
  have he : Real.log (169360061227 / 125000000000) = -Real.log (125000000000 / 169360061227) := by
    rw [show ((169360061227 / 125000000000) : ℝ) = ((125000000000 / 169360061227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_102_neg : (17557169 / 125000000) ≤ -Real.log (2500 / 2877) ∧
    -Real.log (2500 / 2877) ≤ (140457353 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 5377)) (n := 12)
    (lo := (17557169 / 125000000)) (hi := (140457353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2877 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2877 / 2500) = 1/(2500 / 2877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_102 : Bounds (17557169 / 125000000) (140457353 / 1000000000) (Real.log (2877 / 2500)) := by
  have h := reflection_log_102_neg
  have he : Real.log (2877 / 2500) = -Real.log (2500 / 2877) := by
    rw [show ((2877 / 2500) : ℝ) = ((2500 / 2877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_103_neg : (163460549 / 1000000000) ≤ -Real.log (2123 / 2500) ∧
    -Real.log (2123 / 2500) ≤ (3269211 / 20000000) := by
  have h := checkLog_sound (w := (377 / 4623)) (n := 12)
    (lo := (163460549 / 1000000000)) (hi := (3269211 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2123) = 1/(2123 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_103 : Bounds (-3269211 / 20000000) (-163460549 / 1000000000) (Real.log (2123 / 2500)) := by
  have h := reflection_log_103_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_104_neg : (37697 / 250000000) ≤ -Real.log (2500000 / 2500377) ∧
    -Real.log (2500000 / 2500377) ≤ (150789 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 5000377)) (n := 12)
    (lo := (37697 / 250000000)) (hi := (150789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500377 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500377 / 2500000) = 1/(2500000 / 2500377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_104 : Bounds (37697 / 250000000) (150789 / 1000000000) (Real.log (2500377 / 2500000)) := by
  have h := reflection_log_104_neg
  have he : Real.log (2500377 / 2500000) = -Real.log (2500000 / 2500377) := by
    rw [show ((2500377 / 2500000) : ℝ) = ((2500000 / 2500377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_105_neg : (150811 / 1000000000) ≤ -Real.log (2499623 / 2500000) ∧
    -Real.log (2499623 / 2500000) ≤ (37703 / 250000000) := by
  have h := checkLog_sound (w := (377 / 4999623)) (n := 12)
    (lo := (150811 / 1000000000)) (hi := (37703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499623) = 1/(2499623 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_105 : Bounds (-37703 / 250000000) (-150811 / 1000000000) (Real.log (2499623 / 2500000)) := by
  have h := reflection_log_105_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_106_neg : (72864699 / 1000000000) ≤ -Real.log (200000 / 215117) ∧
    -Real.log (200000 / 215117) ≤ (728647 / 10000000) := by
  have h := checkLog_sound (w := (15117 / 415117)) (n := 12)
    (lo := (72864699 / 1000000000)) (hi := (728647 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215117 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215117 / 200000) = 1/(200000 / 215117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_106 : Bounds (72864699 / 1000000000) (728647 / 10000000) (Real.log (215117 / 200000)) := by
  have h := reflection_log_106_neg
  have he : Real.log (215117 / 200000) = -Real.log (200000 / 215117) := by
    rw [show ((215117 / 200000) : ℝ) = ((200000 / 215117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_107_neg : (78594173 / 1000000000) ≤ -Real.log (184883 / 200000) ∧
    -Real.log (184883 / 200000) ≤ (39297087 / 500000000) := by
  have h := checkLog_sound (w := (15117 / 384883)) (n := 12)
    (lo := (78594173 / 1000000000)) (hi := (39297087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184883) = 1/(184883 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_107 : Bounds (-39297087 / 500000000) (-78594173 / 1000000000) (Real.log (184883 / 200000)) := by
  have h := reflection_log_107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_108_neg : (36526243 / 500000000) ≤ -Real.log (1000000 / 1075787) ∧
    -Real.log (1000000 / 1075787) ≤ (73052487 / 1000000000) := by
  have h := checkLog_sound (w := (75787 / 2075787)) (n := 12)
    (lo := (36526243 / 500000000)) (hi := (73052487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075787 / 1000000) = 1/(1000000 / 1075787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_108 : Bounds (36526243 / 500000000) (73052487 / 1000000000) (Real.log (1075787 / 1000000)) := by
  have h := reflection_log_108_neg
  have he : Real.log (1075787 / 1000000) = -Real.log (1000000 / 1075787) := by
    rw [show ((1075787 / 1000000) : ℝ) = ((1000000 / 1075787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_109_neg : (39406357 / 500000000) ≤ -Real.log (924213 / 1000000) ∧
    -Real.log (924213 / 1000000) ≤ (15762543 / 200000000) := by
  have h := checkLog_sound (w := (75787 / 1924213)) (n := 12)
    (lo := (39406357 / 500000000)) (hi := (15762543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924213) = 1/(924213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_109 : Bounds (-15762543 / 200000000) (-39406357 / 500000000) (Real.log (924213 / 1000000)) := by
  have h := reflection_log_109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_110_neg : (5760227 / 1000000000) ≤ -Real.log (994256330631 / 1000000000000) ∧
    -Real.log (994256330631 / 1000000000000) ≤ (1440057 / 250000000) := by
  have h := checkLog_sound (w := (5743669369 / 1994256330631)) (n := 12)
    (lo := (5760227 / 1000000000)) (hi := (1440057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994256330631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994256330631) = 1/(994256330631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_110 : Bounds (-1440057 / 250000000) (-5760227 / 1000000000) (Real.log (994256330631 / 1000000000000)) := by
  have h := reflection_log_110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_111_neg : (2864737 / 500000000) ≤ -Real.log (39771476311 / 40000000000) ∧
    -Real.log (39771476311 / 40000000000) ≤ (229179 / 40000000) := by
  have h := checkLog_sound (w := (228523689 / 79771476311)) (n := 12)
    (lo := (2864737 / 500000000)) (hi := (229179 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39771476311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39771476311) = 1/(39771476311 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_111 : Bounds (-229179 / 40000000) (-2864737 / 500000000) (Real.log (39771476311 / 40000000000)) := by
  have h := reflection_log_111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_112_neg : (151458873 / 1000000000) ≤ -Real.log (500000000000 / 581765224493) ∧
    -Real.log (500000000000 / 581765224493) ≤ (75729437 / 500000000) := by
  have h := checkLog_sound (w := (81765224493 / 1081765224493)) (n := 12)
    (lo := (151458873 / 1000000000)) (hi := (75729437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581765224493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581765224493 / 500000000000) = 1/(500000000000 / 581765224493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_112 : Bounds (151458873 / 1000000000) (75729437 / 500000000) (Real.log (581765224493 / 500000000000)) := by
  have h := reflection_log_112_neg
  have he : Real.log (581765224493 / 500000000000) = -Real.log (500000000000 / 581765224493) := by
    rw [show ((581765224493 / 500000000000) : ℝ) = ((500000000000 / 581765224493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_113_neg : (151865201 / 1000000000) ≤ -Real.log (500000000000 / 582001659791) ∧
    -Real.log (500000000000 / 582001659791) ≤ (75932601 / 500000000) := by
  have h := checkLog_sound (w := (82001659791 / 1082001659791)) (n := 12)
    (lo := (151865201 / 1000000000)) (hi := (75932601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582001659791 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582001659791 / 500000000000) = 1/(500000000000 / 582001659791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_113 : Bounds (151865201 / 1000000000) (75932601 / 500000000) (Real.log (582001659791 / 500000000000)) := by
  have h := reflection_log_113_neg
  have he : Real.log (582001659791 / 500000000000) = -Real.log (500000000000 / 582001659791) := by
    rw [show ((582001659791 / 500000000000) : ℝ) = ((500000000000 / 582001659791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_114_neg : (303713251 / 1000000000) ≤ -Real.log (500000000000 / 677440244907) ∧
    -Real.log (500000000000 / 677440244907) ≤ (75928313 / 250000000) := by
  have h := checkLog_sound (w := (177440244907 / 1177440244907)) (n := 12)
    (lo := (303713251 / 1000000000)) (hi := (75928313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677440244907 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677440244907 / 500000000000) = 1/(500000000000 / 677440244907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_114 : Bounds (303713251 / 1000000000) (75928313 / 250000000) (Real.log (677440244907 / 500000000000)) := by
  have h := reflection_log_114_neg
  have he : Real.log (677440244907 / 500000000000) = -Real.log (500000000000 / 677440244907) := by
    rw [show ((677440244907 / 500000000000) : ℝ) = ((500000000000 / 677440244907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_115_neg : (303917901 / 1000000000) ≤ -Real.log (500000000000 / 677578897787) ∧
    -Real.log (500000000000 / 677578897787) ≤ (151958951 / 500000000) := by
  have h := checkLog_sound (w := (177578897787 / 1177578897787)) (n := 12)
    (lo := (303917901 / 1000000000)) (hi := (151958951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677578897787 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677578897787 / 500000000000) = 1/(500000000000 / 677578897787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_115 : Bounds (303917901 / 1000000000) (151958951 / 500000000) (Real.log (677578897787 / 500000000000)) := by
  have h := reflection_log_115_neg
  have he : Real.log (677578897787 / 500000000000) = -Real.log (500000000000 / 677578897787) := by
    rw [show ((677578897787 / 500000000000) : ℝ) = ((500000000000 / 677578897787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_116_neg : (35136061 / 250000000) ≤ -Real.log (10000 / 11509) ∧
    -Real.log (10000 / 11509) ≤ (28108849 / 200000000) := by
  have h := checkLog_sound (w := (1509 / 21509)) (n := 12)
    (lo := (35136061 / 250000000)) (hi := (28108849 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11509 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11509 / 10000) = 1/(10000 / 11509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_116 : Bounds (35136061 / 250000000) (28108849 / 200000000) (Real.log (11509 / 10000)) := by
  have h := reflection_log_116_neg
  have he : Real.log (11509 / 10000) = -Real.log (10000 / 11509) := by
    rw [show ((11509 / 10000) : ℝ) = ((10000 / 11509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_117_neg : (163578313 / 1000000000) ≤ -Real.log (8491 / 10000) ∧
    -Real.log (8491 / 10000) ≤ (81789157 / 500000000) := by
  have h := checkLog_sound (w := (1509 / 18491)) (n := 12)
    (lo := (163578313 / 1000000000)) (hi := (81789157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8491) = 1/(8491 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_117 : Bounds (-81789157 / 500000000) (-163578313 / 1000000000) (Real.log (8491 / 10000)) := by
  have h := reflection_log_117_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_118_neg : (18861 / 125000000) ≤ -Real.log (10000000 / 10001509) ∧
    -Real.log (10000000 / 10001509) ≤ (150889 / 1000000000) := by
  have h := checkLog_sound (w := (1509 / 20001509)) (n := 12)
    (lo := (18861 / 125000000)) (hi := (150889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001509 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001509 / 10000000) = 1/(10000000 / 10001509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_118 : Bounds (18861 / 125000000) (150889 / 1000000000) (Real.log (10001509 / 10000000)) := by
  have h := reflection_log_118_neg
  have he : Real.log (10001509 / 10000000) = -Real.log (10000000 / 10001509) := by
    rw [show ((10001509 / 10000000) : ℝ) = ((10000000 / 10001509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_119_neg : (150911 / 1000000000) ≤ -Real.log (9998491 / 10000000) ∧
    -Real.log (9998491 / 10000000) ≤ (1179 / 7812500) := by
  have h := checkLog_sound (w := (1509 / 19998491)) (n := 12)
    (lo := (150911 / 1000000000)) (hi := (1179 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998491) = 1/(9998491 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_119 : Bounds (-1179 / 7812500) (-150911 / 1000000000) (Real.log (9998491 / 10000000)) := by
  have h := reflection_log_119_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_120_neg : (36456057 / 500000000) ≤ -Real.log (250000 / 268909) ∧
    -Real.log (250000 / 268909) ≤ (14582423 / 200000000) := by
  have h := checkLog_sound (w := (18909 / 518909)) (n := 12)
    (lo := (36456057 / 500000000)) (hi := (14582423 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268909 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(268909 / 250000) = 1/(250000 / 268909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_120 : Bounds (36456057 / 500000000) (14582423 / 200000000) (Real.log (268909 / 250000)) := by
  have h := reflection_log_120_neg
  have he : Real.log (268909 / 250000) = -Real.log (250000 / 268909) := by
    rw [show ((268909 / 250000) : ℝ) = ((250000 / 268909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_121_neg : (15729869 / 200000000) ≤ -Real.log (231091 / 250000) ∧
    -Real.log (231091 / 250000) ≤ (39324673 / 500000000) := by
  have h := checkLog_sound (w := (18909 / 481091)) (n := 12)
    (lo := (15729869 / 200000000)) (hi := (39324673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 231091) = 1/(231091 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_121 : Bounds (-39324673 / 500000000) (-15729869 / 200000000) (Real.log (231091 / 250000)) := by
  have h := reflection_log_121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_122_neg : (18274973 / 250000000) ≤ -Real.log (500000 / 537919) ∧
    -Real.log (500000 / 537919) ≤ (73099893 / 1000000000) := by
  have h := checkLog_sound (w := (37919 / 1037919)) (n := 12)
    (lo := (18274973 / 250000000)) (hi := (73099893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537919 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537919 / 500000) = 1/(500000 / 537919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_122 : Bounds (18274973 / 250000000) (73099893 / 1000000000) (Real.log (537919 / 500000)) := by
  have h := reflection_log_122_neg
  have he : Real.log (537919 / 500000) = -Real.log (500000 / 537919) := by
    rw [show ((537919 / 500000) : ℝ) = ((500000 / 537919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_123_neg : (39433949 / 500000000) ≤ -Real.log (462081 / 500000) ∧
    -Real.log (462081 / 500000) ≤ (78867899 / 1000000000) := by
  have h := checkLog_sound (w := (37919 / 962081)) (n := 12)
    (lo := (39433949 / 500000000)) (hi := (78867899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 462081) = 1/(462081 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_123 : Bounds (-78867899 / 1000000000) (-39433949 / 500000000) (Real.log (462081 / 500000)) := by
  have h := reflection_log_123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_124_neg : (1153601 / 200000000) ≤ -Real.log (248562149439 / 250000000000) ∧
    -Real.log (248562149439 / 250000000000) ≤ (2884003 / 500000000) := by
  have h := checkLog_sound (w := (1437850561 / 498562149439)) (n := 12)
    (lo := (1153601 / 200000000)) (hi := (2884003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248562149439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248562149439) = 1/(248562149439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_124 : Bounds (-2884003 / 500000000) (-1153601 / 200000000) (Real.log (248562149439 / 250000000000)) := by
  have h := reflection_log_124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_125_neg : (573723 / 100000000) ≤ -Real.log (62142449719 / 62500000000) ∧
    -Real.log (62142449719 / 62500000000) ≤ (5737231 / 1000000000) := by
  have h := checkLog_sound (w := (357550281 / 124642449719)) (n := 12)
    (lo := (573723 / 100000000)) (hi := (5737231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62142449719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62142449719) = 1/(62142449719 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_125 : Bounds (-5737231 / 1000000000) (-573723 / 100000000) (Real.log (62142449719 / 62500000000)) := by
  have h := reflection_log_125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_126_neg : (7578073 / 50000000) ≤ -Real.log (250000000000 / 290912454401) ∧
    -Real.log (250000000000 / 290912454401) ≤ (151561461 / 1000000000) := by
  have h := checkLog_sound (w := (40912454401 / 540912454401)) (n := 12)
    (lo := (7578073 / 50000000)) (hi := (151561461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290912454401 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290912454401 / 250000000000) = 1/(250000000000 / 290912454401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_126 : Bounds (7578073 / 50000000) (151561461 / 1000000000) (Real.log (290912454401 / 250000000000)) := by
  have h := reflection_log_126_neg
  have he : Real.log (290912454401 / 250000000000) = -Real.log (250000000000 / 290912454401) := by
    rw [show ((290912454401 / 250000000000) : ℝ) = ((250000000000 / 290912454401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_127_neg : (15196779 / 100000000) ≤ -Real.log (500000000000 / 582061370193) ∧
    -Real.log (500000000000 / 582061370193) ≤ (151967791 / 1000000000) := by
  have h := checkLog_sound (w := (82061370193 / 1082061370193)) (n := 12)
    (lo := (15196779 / 100000000)) (hi := (151967791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582061370193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582061370193 / 500000000000) = 1/(500000000000 / 582061370193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_127 : Bounds (15196779 / 100000000) (151967791 / 1000000000) (Real.log (582061370193 / 500000000000)) := by
  have h := reflection_log_127_neg
  have he : Real.log (582061370193 / 500000000000) = -Real.log (500000000000 / 582061370193) := by
    rw [show ((582061370193 / 500000000000) : ℝ) = ((500000000000 / 582061370193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0002 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_128_neg : (303917901 / 1000000000) ≤ -Real.log (250000000000 / 338789448893) ∧
    -Real.log (250000000000 / 338789448893) ≤ (151958951 / 500000000) := by
  have h := checkLog_sound (w := (88789448893 / 588789448893)) (n := 12)
    (lo := (303917901 / 1000000000)) (hi := (151958951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338789448893 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338789448893 / 250000000000) = 1/(250000000000 / 338789448893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_128 : Bounds (303917901 / 1000000000) (151958951 / 500000000) (Real.log (338789448893 / 250000000000)) := by
  have h := reflection_log_128_neg
  have he : Real.log (338789448893 / 250000000000) = -Real.log (250000000000 / 338789448893) := by
    rw [show ((338789448893 / 250000000000) : ℝ) = ((250000000000 / 338789448893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_129_neg : (152061279 / 500000000) ≤ -Real.log (125000000000 / 169429395831) ∧
    -Real.log (125000000000 / 169429395831) ≤ (304122559 / 1000000000) := by
  have h := checkLog_sound (w := (44429395831 / 294429395831)) (n := 12)
    (lo := (152061279 / 500000000)) (hi := (304122559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169429395831 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169429395831 / 125000000000) = 1/(125000000000 / 169429395831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_129 : Bounds (152061279 / 500000000) (304122559 / 1000000000) (Real.log (169429395831 / 125000000000)) := by
  have h := reflection_log_129_neg
  have he : Real.log (169429395831 / 125000000000) = -Real.log (125000000000 / 169429395831) := by
    rw [show ((169429395831 / 125000000000) : ℝ) = ((125000000000 / 169429395831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_130_neg : (140631129 / 1000000000) ≤ -Real.log (1000 / 1151) ∧
    -Real.log (1000 / 1151) ≤ (14063113 / 100000000) := by
  have h := checkLog_sound (w := (151 / 2151)) (n := 12)
    (lo := (140631129 / 1000000000)) (hi := (14063113 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151 / 1000) = 1/(1000 / 1151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_130 : Bounds (140631129 / 1000000000) (14063113 / 100000000) (Real.log (1151 / 1000)) := by
  have h := reflection_log_130_neg
  have he : Real.log (1151 / 1000) = -Real.log (1000 / 1151) := by
    rw [show ((1151 / 1000) : ℝ) = ((1000 / 1151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_131_neg : (40924023 / 250000000) ≤ -Real.log (849 / 1000) ∧
    -Real.log (849 / 1000) ≤ (163696093 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 1849)) (n := 12)
    (lo := (40924023 / 250000000)) (hi := (163696093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 849) = 1/(849 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_131 : Bounds (-163696093 / 1000000000) (-40924023 / 250000000) (Real.log (849 / 1000)) := by
  have h := reflection_log_131_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_132_neg : (37747 / 250000000) ≤ -Real.log (1000000 / 1000151) ∧
    -Real.log (1000000 / 1000151) ≤ (150989 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 2000151)) (n := 12)
    (lo := (37747 / 250000000)) (hi := (150989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000151 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000151 / 1000000) = 1/(1000000 / 1000151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_132 : Bounds (37747 / 250000000) (150989 / 1000000000) (Real.log (1000151 / 1000000)) := by
  have h := reflection_log_132_neg
  have he : Real.log (1000151 / 1000000) = -Real.log (1000000 / 1000151) := by
    rw [show ((1000151 / 1000000) : ℝ) = ((1000000 / 1000151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_133_neg : (151011 / 1000000000) ≤ -Real.log (999849 / 1000000) ∧
    -Real.log (999849 / 1000000) ≤ (37753 / 250000000) := by
  have h := checkLog_sound (w := (151 / 1999849)) (n := 12)
    (lo := (151011 / 1000000000)) (hi := (37753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999849) = 1/(999849 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_133 : Bounds (-37753 / 250000000) (-151011 / 1000000000) (Real.log (999849 / 1000000)) := by
  have h := reflection_log_133_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_134_neg : (73146367 / 1000000000) ≤ -Real.log (62500 / 67243) ∧
    -Real.log (62500 / 67243) ≤ (142864 / 1953125) := by
  have h := checkLog_sound (w := (4743 / 129743)) (n := 12)
    (lo := (73146367 / 1000000000)) (hi := (142864 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67243 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67243 / 62500) = 1/(62500 / 67243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_134 : Bounds (73146367 / 1000000000) (142864 / 1953125) (Real.log (67243 / 62500)) := by
  have h := reflection_log_134_neg
  have he : Real.log (67243 / 62500) = -Real.log (62500 / 67243) := by
    rw [show ((67243 / 62500) : ℝ) = ((62500 / 67243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_135_neg : (39461001 / 500000000) ≤ -Real.log (57757 / 62500) ∧
    -Real.log (57757 / 62500) ≤ (78922003 / 1000000000) := by
  have h := checkLog_sound (w := (4743 / 120257)) (n := 12)
    (lo := (39461001 / 500000000)) (hi := (78922003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57757) = 1/(57757 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_135 : Bounds (-78922003 / 1000000000) (-39461001 / 500000000) (Real.log (57757 / 62500)) := by
  have h := reflection_log_135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_136_neg : (1155127 / 200000000) ≤ -Real.log (3883753951 / 3906250000) ∧
    -Real.log (3883753951 / 3906250000) ≤ (1443909 / 250000000) := by
  have h := checkLog_sound (w := (22496049 / 7790003951)) (n := 12)
    (lo := (1155127 / 200000000)) (hi := (1443909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3883753951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3883753951) = 1/(3883753951 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_136 : Bounds (-1443909 / 250000000) (-1155127 / 200000000) (Real.log (3883753951 / 3906250000)) := by
  have h := reflection_log_136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_137_neg : (30332407 / 200000000) ≤ -Real.log (62500000000 / 72735428653) ∧
    -Real.log (62500000000 / 72735428653) ≤ (37915509 / 250000000) := by
  have h := checkLog_sound (w := (10235428653 / 135235428653)) (n := 12)
    (lo := (30332407 / 200000000)) (hi := (37915509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72735428653 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72735428653 / 62500000000) = 1/(62500000000 / 72735428653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_137 : Bounds (30332407 / 200000000) (37915509 / 250000000) (Real.log (72735428653 / 62500000000)) := by
  have h := reflection_log_137_neg
  have he : Real.log (72735428653 / 62500000000) = -Real.log (62500000000 / 72735428653) := by
    rw [show ((72735428653 / 62500000000) : ℝ) = ((62500000000 / 72735428653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_138_neg : (152068369 / 1000000000) ≤ -Real.log (500000000000 / 582119916201) ∧
    -Real.log (500000000000 / 582119916201) ≤ (15206837 / 100000000) := by
  have h := checkLog_sound (w := (82119916201 / 1082119916201)) (n := 12)
    (lo := (152068369 / 1000000000)) (hi := (15206837 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582119916201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582119916201 / 500000000000) = 1/(500000000000 / 582119916201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_138 : Bounds (152068369 / 1000000000) (15206837 / 100000000) (Real.log (582119916201 / 500000000000)) := by
  have h := reflection_log_138_neg
  have he : Real.log (582119916201 / 500000000000) = -Real.log (500000000000 / 582119916201) := by
    rw [show ((582119916201 / 500000000000) : ℝ) = ((500000000000 / 582119916201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_139_neg : (152061279 / 500000000) ≤ -Real.log (500000000000 / 677717583323) ∧
    -Real.log (500000000000 / 677717583323) ≤ (304122559 / 1000000000) := by
  have h := checkLog_sound (w := (177717583323 / 1177717583323)) (n := 12)
    (lo := (152061279 / 500000000)) (hi := (304122559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677717583323 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677717583323 / 500000000000) = 1/(500000000000 / 677717583323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_139 : Bounds (152061279 / 500000000) (304122559 / 1000000000) (Real.log (677717583323 / 500000000000)) := by
  have h := reflection_log_139_neg
  have he : Real.log (677717583323 / 500000000000) = -Real.log (500000000000 / 677717583323) := by
    rw [show ((677717583323 / 500000000000) : ℝ) = ((500000000000 / 677717583323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_140_neg : (152163611 / 500000000) ≤ -Real.log (125000000000 / 169464075383) ∧
    -Real.log (125000000000 / 169464075383) ≤ (304327223 / 1000000000) := by
  have h := checkLog_sound (w := (44464075383 / 294464075383)) (n := 12)
    (lo := (152163611 / 500000000)) (hi := (304327223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169464075383 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169464075383 / 125000000000) = 1/(125000000000 / 169464075383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_140 : Bounds (152163611 / 500000000) (304327223 / 1000000000) (Real.log (169464075383 / 125000000000)) := by
  have h := reflection_log_140_neg
  have he : Real.log (169464075383 / 125000000000) = -Real.log (125000000000 / 169464075383) := by
    rw [show ((169464075383 / 125000000000) : ℝ) = ((125000000000 / 169464075383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_141_neg : (70359003 / 500000000) ≤ -Real.log (10000 / 11511) ∧
    -Real.log (10000 / 11511) ≤ (140718007 / 1000000000) := by
  have h := checkLog_sound (w := (1511 / 21511)) (n := 12)
    (lo := (70359003 / 500000000)) (hi := (140718007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11511 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11511 / 10000) = 1/(10000 / 11511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_141 : Bounds (70359003 / 500000000) (140718007 / 1000000000) (Real.log (11511 / 10000)) := by
  have h := reflection_log_141_neg
  have he : Real.log (11511 / 10000) = -Real.log (10000 / 11511) := by
    rw [show ((11511 / 10000) : ℝ) = ((10000 / 11511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_142_neg : (32762777 / 200000000) ≤ -Real.log (8489 / 10000) ∧
    -Real.log (8489 / 10000) ≤ (81906943 / 500000000) := by
  have h := checkLog_sound (w := (1511 / 18489)) (n := 12)
    (lo := (32762777 / 200000000)) (hi := (81906943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8489) = 1/(8489 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_142 : Bounds (-81906943 / 500000000) (-32762777 / 200000000) (Real.log (8489 / 10000)) := by
  have h := reflection_log_142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_143_neg : (9443 / 62500000) ≤ -Real.log (10000000 / 10001511) ∧
    -Real.log (10000000 / 10001511) ≤ (151089 / 1000000000) := by
  have h := checkLog_sound (w := (1511 / 20001511)) (n := 12)
    (lo := (9443 / 62500000)) (hi := (151089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001511 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001511 / 10000000) = 1/(10000000 / 10001511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_143 : Bounds (9443 / 62500000) (151089 / 1000000000) (Real.log (10001511 / 10000000)) := by
  have h := reflection_log_143_neg
  have he : Real.log (10001511 / 10000000) = -Real.log (10000000 / 10001511) := by
    rw [show ((10001511 / 10000000) : ℝ) = ((10000000 / 10001511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_144_neg : (151111 / 1000000000) ≤ -Real.log (9998489 / 10000000) ∧
    -Real.log (9998489 / 10000000) ≤ (18889 / 125000000) := by
  have h := checkLog_sound (w := (1511 / 19998489)) (n := 12)
    (lo := (151111 / 1000000000)) (hi := (18889 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998489) = 1/(9998489 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_144 : Bounds (-18889 / 125000000) (-151111 / 1000000000) (Real.log (9998489 / 10000000)) := by
  have h := reflection_log_144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_145_neg : (9125751 / 125000000) ≤ -Real.log (1000000 / 1075737) ∧
    -Real.log (1000000 / 1075737) ≤ (73006009 / 1000000000) := by
  have h := checkLog_sound (w := (75737 / 2075737)) (n := 12)
    (lo := (9125751 / 125000000)) (hi := (73006009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075737 / 1000000) = 1/(1000000 / 1075737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_145 : Bounds (9125751 / 125000000) (73006009 / 1000000000) (Real.log (1075737 / 1000000)) := by
  have h := reflection_log_145_neg
  have he : Real.log (1075737 / 1000000) = -Real.log (1000000 / 1075737) := by
    rw [show ((1075737 / 1000000) : ℝ) = ((1000000 / 1075737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_146_neg : (15751723 / 200000000) ≤ -Real.log (924263 / 1000000) ∧
    -Real.log (924263 / 1000000) ≤ (9844827 / 125000000) := by
  have h := checkLog_sound (w := (75737 / 1924263)) (n := 12)
    (lo := (15751723 / 200000000)) (hi := (9844827 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924263) = 1/(924263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_146 : Bounds (-9844827 / 125000000) (-15751723 / 200000000) (Real.log (924263 / 1000000)) := by
  have h := reflection_log_146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_147_neg : (9149221 / 125000000) ≤ -Real.log (1000000 / 1075939) ∧
    -Real.log (1000000 / 1075939) ≤ (73193769 / 1000000000) := by
  have h := checkLog_sound (w := (75939 / 2075939)) (n := 12)
    (lo := (9149221 / 125000000)) (hi := (73193769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075939 / 1000000) = 1/(1000000 / 1075939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_147 : Bounds (9149221 / 125000000) (73193769 / 1000000000) (Real.log (1075939 / 1000000)) := by
  have h := reflection_log_147_neg
  have he : Real.log (1075939 / 1000000) = -Real.log (1000000 / 1075939) := by
    rw [show ((1075939 / 1000000) : ℝ) = ((1000000 / 1075939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_148_neg : (9872149 / 125000000) ≤ -Real.log (924061 / 1000000) ∧
    -Real.log (924061 / 1000000) ≤ (78977193 / 1000000000) := by
  have h := checkLog_sound (w := (75939 / 1924061)) (n := 12)
    (lo := (9872149 / 125000000)) (hi := (78977193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924061) = 1/(924061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_148 : Bounds (-78977193 / 1000000000) (-9872149 / 125000000) (Real.log (924061 / 1000000)) := by
  have h := reflection_log_148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_149_neg : (5783423 / 1000000000) ≤ -Real.log (994233268279 / 1000000000000) ∧
    -Real.log (994233268279 / 1000000000000) ≤ (45183 / 7812500) := by
  have h := checkLog_sound (w := (5766731721 / 1994233268279)) (n := 12)
    (lo := (5783423 / 1000000000)) (hi := (45183 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994233268279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994233268279) = 1/(994233268279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_149 : Bounds (-45183 / 7812500) (-5783423 / 1000000000) (Real.log (994233268279 / 1000000000000)) := by
  have h := reflection_log_149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_150_neg : (5752607 / 1000000000) ≤ -Real.log (994263906831 / 1000000000000) ∧
    -Real.log (994263906831 / 1000000000000) ≤ (179769 / 31250000) := by
  have h := checkLog_sound (w := (5736093169 / 1994263906831)) (n := 12)
    (lo := (5752607 / 1000000000)) (hi := (179769 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994263906831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994263906831) = 1/(994263906831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_150 : Bounds (-179769 / 31250000) (-5752607 / 1000000000) (Real.log (994263906831 / 1000000000000)) := by
  have h := reflection_log_150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_151_neg : (151764623 / 1000000000) ≤ -Real.log (500000000000 / 581943126577) ∧
    -Real.log (500000000000 / 581943126577) ≤ (9485289 / 62500000) := by
  have h := checkLog_sound (w := (81943126577 / 1081943126577)) (n := 12)
    (lo := (151764623 / 1000000000)) (hi := (9485289 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581943126577 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581943126577 / 500000000000) = 1/(500000000000 / 581943126577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_151 : Bounds (151764623 / 1000000000) (9485289 / 62500000) (Real.log (581943126577 / 500000000000)) := by
  have h := reflection_log_151_neg
  have he : Real.log (581943126577 / 500000000000) = -Real.log (500000000000 / 581943126577) := by
    rw [show ((581943126577 / 500000000000) : ℝ) = ((500000000000 / 581943126577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_152_neg : (1902137 / 12500000) ≤ -Real.log (62500000000 / 72772454957) ∧
    -Real.log (62500000000 / 72772454957) ≤ (152170961 / 1000000000) := by
  have h := checkLog_sound (w := (10272454957 / 135272454957)) (n := 12)
    (lo := (1902137 / 12500000)) (hi := (152170961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72772454957 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72772454957 / 62500000000) = 1/(62500000000 / 72772454957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_152 : Bounds (1902137 / 12500000) (152170961 / 1000000000) (Real.log (72772454957 / 62500000000)) := by
  have h := reflection_log_152_neg
  have he : Real.log (72772454957 / 62500000000) = -Real.log (62500000000 / 72772454957) := by
    rw [show ((72772454957 / 62500000000) : ℝ) = ((62500000000 / 72772454957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_153_neg : (152163611 / 500000000) ≤ -Real.log (500000000000 / 677856301531) ∧
    -Real.log (500000000000 / 677856301531) ≤ (304327223 / 1000000000) := by
  have h := checkLog_sound (w := (177856301531 / 1177856301531)) (n := 12)
    (lo := (152163611 / 500000000)) (hi := (304327223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677856301531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677856301531 / 500000000000) = 1/(500000000000 / 677856301531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_153 : Bounds (152163611 / 500000000) (304327223 / 1000000000) (Real.log (677856301531 / 500000000000)) := by
  have h := reflection_log_153_neg
  have he : Real.log (677856301531 / 500000000000) = -Real.log (500000000000 / 677856301531) := by
    rw [show ((677856301531 / 500000000000) : ℝ) = ((500000000000 / 677856301531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_154_neg : (76132973 / 250000000) ≤ -Real.log (500000000000 / 677995052421) ∧
    -Real.log (500000000000 / 677995052421) ≤ (304531893 / 1000000000) := by
  have h := checkLog_sound (w := (177995052421 / 1177995052421)) (n := 12)
    (lo := (76132973 / 250000000)) (hi := (304531893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677995052421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677995052421 / 500000000000) = 1/(500000000000 / 677995052421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_154 : Bounds (76132973 / 250000000) (304531893 / 1000000000) (Real.log (677995052421 / 500000000000)) := by
  have h := reflection_log_154_neg
  have he : Real.log (677995052421 / 500000000000) = -Real.log (500000000000 / 677995052421) := by
    rw [show ((677995052421 / 500000000000) : ℝ) = ((500000000000 / 677995052421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_155_neg : (35201219 / 250000000) ≤ -Real.log (1250 / 1439) ∧
    -Real.log (1250 / 1439) ≤ (140804877 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 2689)) (n := 12)
    (lo := (35201219 / 250000000)) (hi := (140804877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439 / 1250) = 1/(1250 / 1439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_155 : Bounds (35201219 / 250000000) (140804877 / 1000000000) (Real.log (1439 / 1250)) := by
  have h := reflection_log_155_neg
  have he : Real.log (1439 / 1250) = -Real.log (1250 / 1439) := by
    rw [show ((1439 / 1250) : ℝ) = ((1250 / 1439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_156_neg : (163931691 / 1000000000) ≤ -Real.log (1061 / 1250) ∧
    -Real.log (1061 / 1250) ≤ (40982923 / 250000000) := by
  have h := checkLog_sound (w := (189 / 2311)) (n := 12)
    (lo := (163931691 / 1000000000)) (hi := (40982923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1061) = 1/(1061 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_156 : Bounds (-40982923 / 250000000) (-163931691 / 1000000000) (Real.log (1061 / 1250)) := by
  have h := reflection_log_156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_157_neg : (37797 / 250000000) ≤ -Real.log (1250000 / 1250189) ∧
    -Real.log (1250000 / 1250189) ≤ (151189 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 2500189)) (n := 12)
    (lo := (37797 / 250000000)) (hi := (151189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250189 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250189 / 1250000) = 1/(1250000 / 1250189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_157 : Bounds (37797 / 250000000) (151189 / 1000000000) (Real.log (1250189 / 1250000)) := by
  have h := reflection_log_157_neg
  have he : Real.log (1250189 / 1250000) = -Real.log (1250000 / 1250189) := by
    rw [show ((1250189 / 1250000) : ℝ) = ((1250000 / 1250189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_158_neg : (151211 / 1000000000) ≤ -Real.log (1249811 / 1250000) ∧
    -Real.log (1249811 / 1250000) ≤ (37803 / 250000000) := by
  have h := checkLog_sound (w := (189 / 2499811)) (n := 12)
    (lo := (151211 / 1000000000)) (hi := (37803 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249811) = 1/(1249811 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_158 : Bounds (-37803 / 250000000) (-151211 / 1000000000) (Real.log (1249811 / 1250000)) := by
  have h := reflection_log_158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_159_neg : (4577573 / 62500000) ≤ -Real.log (100000 / 107599) ∧
    -Real.log (100000 / 107599) ≤ (73241169 / 1000000000) := by
  have h := checkLog_sound (w := (7599 / 207599)) (n := 12)
    (lo := (4577573 / 62500000)) (hi := (73241169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107599 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107599 / 100000) = 1/(100000 / 107599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_159 : Bounds (4577573 / 62500000) (73241169 / 1000000000) (Real.log (107599 / 100000)) := by
  have h := reflection_log_159_neg
  have he : Real.log (107599 / 100000) = -Real.log (100000 / 107599) := by
    rw [show ((107599 / 100000) : ℝ) = ((100000 / 107599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_160_neg : (1234881 / 15625000) ≤ -Real.log (92401 / 100000) ∧
    -Real.log (92401 / 100000) ≤ (15806477 / 200000000) := by
  have h := checkLog_sound (w := (7599 / 192401)) (n := 12)
    (lo := (1234881 / 15625000)) (hi := (15806477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92401) = 1/(92401 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_160 : Bounds (-15806477 / 200000000) (-1234881 / 15625000) (Real.log (92401 / 100000)) := by
  have h := reflection_log_160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_161_neg : (361951 / 62500000) ≤ -Real.log (9942255199 / 10000000000) ∧
    -Real.log (9942255199 / 10000000000) ≤ (5791217 / 1000000000) := by
  have h := checkLog_sound (w := (57744801 / 19942255199)) (n := 12)
    (lo := (361951 / 62500000)) (hi := (5791217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9942255199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9942255199) = 1/(9942255199 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_161 : Bounds (-5791217 / 1000000000) (-361951 / 62500000) (Real.log (9942255199 / 10000000000)) := by
  have h := reflection_log_161_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_162_neg : (151865201 / 1000000000) ≤ -Real.log (50000000000 / 58200165979) ∧
    -Real.log (50000000000 / 58200165979) ≤ (75932601 / 500000000) := by
  have h := checkLog_sound (w := (8200165979 / 108200165979)) (n := 12)
    (lo := (151865201 / 1000000000)) (hi := (75932601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58200165979 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58200165979 / 50000000000) = 1/(50000000000 / 58200165979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_162 : Bounds (151865201 / 1000000000) (75932601 / 500000000) (Real.log (58200165979 / 50000000000)) := by
  have h := reflection_log_162_neg
  have he : Real.log (58200165979 / 50000000000) = -Real.log (50000000000 / 58200165979) := by
    rw [show ((58200165979 / 50000000000) : ℝ) = ((50000000000 / 58200165979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_163_neg : (9517097 / 62500000) ≤ -Real.log (62500000000 / 72779921213) ∧
    -Real.log (62500000000 / 72779921213) ≤ (152273553 / 1000000000) := by
  have h := checkLog_sound (w := (10279921213 / 135279921213)) (n := 12)
    (lo := (9517097 / 62500000)) (hi := (152273553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72779921213 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72779921213 / 62500000000) = 1/(62500000000 / 72779921213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_163 : Bounds (9517097 / 62500000) (152273553 / 1000000000) (Real.log (72779921213 / 62500000000)) := by
  have h := reflection_log_163_neg
  have he : Real.log (72779921213 / 62500000000) = -Real.log (62500000000 / 72779921213) := by
    rw [show ((72779921213 / 62500000000) : ℝ) = ((62500000000 / 72779921213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_164_neg : (76132973 / 250000000) ≤ -Real.log (25000000000 / 33899752621) ∧
    -Real.log (25000000000 / 33899752621) ≤ (304531893 / 1000000000) := by
  have h := checkLog_sound (w := (8899752621 / 58899752621)) (n := 12)
    (lo := (76132973 / 250000000)) (hi := (304531893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33899752621 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33899752621 / 25000000000) = 1/(25000000000 / 33899752621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_164 : Bounds (76132973 / 250000000) (304531893 / 1000000000) (Real.log (33899752621 / 25000000000)) := by
  have h := reflection_log_164_neg
  have he : Real.log (33899752621 / 25000000000) = -Real.log (25000000000 / 33899752621) := by
    rw [show ((33899752621 / 25000000000) : ℝ) = ((25000000000 / 33899752621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_165_neg : (38092071 / 125000000) ≤ -Real.log (125000000000 / 169533459001) ∧
    -Real.log (125000000000 / 169533459001) ≤ (304736569 / 1000000000) := by
  have h := checkLog_sound (w := (44533459001 / 294533459001)) (n := 12)
    (lo := (38092071 / 125000000)) (hi := (304736569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169533459001 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169533459001 / 125000000000) = 1/(125000000000 / 169533459001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_165 : Bounds (38092071 / 125000000) (304736569 / 1000000000) (Real.log (169533459001 / 125000000000)) := by
  have h := reflection_log_165_neg
  have he : Real.log (169533459001 / 125000000000) = -Real.log (125000000000 / 169533459001) := by
    rw [show ((169533459001 / 125000000000) : ℝ) = ((125000000000 / 169533459001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_166_neg : (70445869 / 500000000) ≤ -Real.log (10000 / 11513) ∧
    -Real.log (10000 / 11513) ≤ (140891739 / 1000000000) := by
  have h := checkLog_sound (w := (1513 / 21513)) (n := 12)
    (lo := (70445869 / 500000000)) (hi := (140891739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11513 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11513 / 10000) = 1/(10000 / 11513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_166 : Bounds (70445869 / 500000000) (140891739 / 1000000000) (Real.log (11513 / 10000)) := by
  have h := reflection_log_166_neg
  have he : Real.log (11513 / 10000) = -Real.log (10000 / 11513) := by
    rw [show ((11513 / 10000) : ℝ) = ((10000 / 11513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_167_neg : (20506189 / 125000000) ≤ -Real.log (8487 / 10000) ∧
    -Real.log (8487 / 10000) ≤ (164049513 / 1000000000) := by
  have h := checkLog_sound (w := (1513 / 18487)) (n := 12)
    (lo := (20506189 / 125000000)) (hi := (164049513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8487) = 1/(8487 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_167 : Bounds (-164049513 / 1000000000) (-20506189 / 125000000) (Real.log (8487 / 10000)) := by
  have h := reflection_log_167_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_168_neg : (18911 / 125000000) ≤ -Real.log (10000000 / 10001513) ∧
    -Real.log (10000000 / 10001513) ≤ (151289 / 1000000000) := by
  have h := checkLog_sound (w := (1513 / 20001513)) (n := 12)
    (lo := (18911 / 125000000)) (hi := (151289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001513 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001513 / 10000000) = 1/(10000000 / 10001513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_168 : Bounds (18911 / 125000000) (151289 / 1000000000) (Real.log (10001513 / 10000000)) := by
  have h := reflection_log_168_neg
  have he : Real.log (10001513 / 10000000) = -Real.log (10000000 / 10001513) := by
    rw [show ((10001513 / 10000000) : ℝ) = ((10000000 / 10001513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_169_neg : (151311 / 1000000000) ≤ -Real.log (9998487 / 10000000) ∧
    -Real.log (9998487 / 10000000) ≤ (9457 / 62500000) := by
  have h := checkLog_sound (w := (1513 / 19998487)) (n := 12)
    (lo := (151311 / 1000000000)) (hi := (9457 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998487) = 1/(9998487 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_169 : Bounds (-9457 / 62500000) (-151311 / 1000000000) (Real.log (9998487 / 10000000)) := by
  have h := reflection_log_169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_170_neg : (14657527 / 200000000) ≤ -Real.log (25000 / 26901) ∧
    -Real.log (25000 / 26901) ≤ (18321909 / 250000000) := by
  have h := checkLog_sound (w := (1901 / 51901)) (n := 12)
    (lo := (14657527 / 200000000)) (hi := (18321909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26901 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26901 / 25000) = 1/(25000 / 26901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_170 : Bounds (14657527 / 200000000) (18321909 / 250000000) (Real.log (26901 / 25000)) := by
  have h := reflection_log_170_neg
  have he : Real.log (26901 / 25000) = -Real.log (25000 / 26901) := by
    rw [show ((26901 / 25000) : ℝ) = ((25000 / 26901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_171_neg : (39543249 / 500000000) ≤ -Real.log (23099 / 25000) ∧
    -Real.log (23099 / 25000) ≤ (79086499 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 48099)) (n := 12)
    (lo := (39543249 / 500000000)) (hi := (79086499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 23099) = 1/(23099 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_171 : Bounds (-79086499 / 1000000000) (-39543249 / 500000000) (Real.log (23099 / 25000)) := by
  have h := reflection_log_171_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_172_neg : (2899431 / 500000000) ≤ -Real.log (621386199 / 625000000) ∧
    -Real.log (621386199 / 625000000) ≤ (5798863 / 1000000000) := by
  have h := checkLog_sound (w := (3613801 / 1246386199)) (n := 12)
    (lo := (2899431 / 500000000)) (hi := (5798863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 621386199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 621386199) = 1/(621386199 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_172 : Bounds (-5798863 / 1000000000) (-2899431 / 500000000) (Real.log (621386199 / 625000000)) := by
  have h := reflection_log_172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_173_neg : (15196779 / 100000000) ≤ -Real.log (31250000000 / 36378835637) ∧
    -Real.log (31250000000 / 36378835637) ≤ (151967791 / 1000000000) := by
  have h := checkLog_sound (w := (5128835637 / 67628835637)) (n := 12)
    (lo := (15196779 / 100000000)) (hi := (151967791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36378835637 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36378835637 / 31250000000) = 1/(31250000000 / 36378835637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_173 : Bounds (15196779 / 100000000) (151967791 / 1000000000) (Real.log (36378835637 / 31250000000)) := by
  have h := reflection_log_173_neg
  have he : Real.log (36378835637 / 31250000000) = -Real.log (31250000000 / 36378835637) := by
    rw [show ((36378835637 / 31250000000) : ℝ) = ((31250000000 / 36378835637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_174_neg : (76187067 / 500000000) ≤ -Real.log (3906250000 / 4549202617) ∧
    -Real.log (3906250000 / 4549202617) ≤ (30474827 / 200000000) := by
  have h := checkLog_sound (w := (642952617 / 8455452617)) (n := 12)
    (lo := (76187067 / 500000000)) (hi := (30474827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4549202617 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4549202617 / 3906250000) = 1/(3906250000 / 4549202617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_174 : Bounds (76187067 / 500000000) (30474827 / 200000000) (Real.log (4549202617 / 3906250000)) := by
  have h := reflection_log_174_neg
  have he : Real.log (4549202617 / 3906250000) = -Real.log (3906250000 / 4549202617) := by
    rw [show ((4549202617 / 3906250000) : ℝ) = ((3906250000 / 4549202617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_175_neg : (38092071 / 125000000) ≤ -Real.log (500000000000 / 678133836003) ∧
    -Real.log (500000000000 / 678133836003) ≤ (304736569 / 1000000000) := by
  have h := checkLog_sound (w := (178133836003 / 1178133836003)) (n := 12)
    (lo := (38092071 / 125000000)) (hi := (304736569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678133836003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678133836003 / 500000000000) = 1/(500000000000 / 678133836003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_175 : Bounds (38092071 / 125000000) (304736569 / 1000000000) (Real.log (678133836003 / 500000000000)) := by
  have h := reflection_log_175_neg
  have he : Real.log (678133836003 / 500000000000) = -Real.log (500000000000 / 678133836003) := by
    rw [show ((678133836003 / 500000000000) : ℝ) = ((500000000000 / 678133836003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_176_neg : (243953 / 800000) ≤ -Real.log (125000000000 / 169568163073) ∧
    -Real.log (125000000000 / 169568163073) ≤ (304941251 / 1000000000) := by
  have h := checkLog_sound (w := (44568163073 / 294568163073)) (n := 12)
    (lo := (243953 / 800000)) (hi := (304941251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169568163073 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169568163073 / 125000000000) = 1/(125000000000 / 169568163073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_176 : Bounds (243953 / 800000) (304941251 / 1000000000) (Real.log (169568163073 / 125000000000)) := by
  have h := reflection_log_176_neg
  have he : Real.log (169568163073 / 125000000000) = -Real.log (125000000000 / 169568163073) := by
    rw [show ((169568163073 / 125000000000) : ℝ) = ((125000000000 / 169568163073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_177_neg : (140978593 / 1000000000) ≤ -Real.log (5000 / 5757) ∧
    -Real.log (5000 / 5757) ≤ (70489297 / 500000000) := by
  have h := checkLog_sound (w := (757 / 10757)) (n := 12)
    (lo := (140978593 / 1000000000)) (hi := (70489297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5757 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5757 / 5000) = 1/(5000 / 5757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_177 : Bounds (140978593 / 1000000000) (70489297 / 500000000) (Real.log (5757 / 5000)) := by
  have h := reflection_log_177_neg
  have he : Real.log (5757 / 5000) = -Real.log (5000 / 5757) := by
    rw [show ((5757 / 5000) : ℝ) = ((5000 / 5757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_178_neg : (82083673 / 500000000) ≤ -Real.log (4243 / 5000) ∧
    -Real.log (4243 / 5000) ≤ (164167347 / 1000000000) := by
  have h := checkLog_sound (w := (757 / 9243)) (n := 12)
    (lo := (82083673 / 500000000)) (hi := (164167347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4243) = 1/(4243 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_178 : Bounds (-164167347 / 1000000000) (-82083673 / 500000000) (Real.log (4243 / 5000)) := by
  have h := reflection_log_178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_179_neg : (37847 / 250000000) ≤ -Real.log (5000000 / 5000757) ∧
    -Real.log (5000000 / 5000757) ≤ (151389 / 1000000000) := by
  have h := checkLog_sound (w := (757 / 10000757)) (n := 12)
    (lo := (37847 / 250000000)) (hi := (151389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000757 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000757 / 5000000) = 1/(5000000 / 5000757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_179 : Bounds (37847 / 250000000) (151389 / 1000000000) (Real.log (5000757 / 5000000)) := by
  have h := reflection_log_179_neg
  have he : Real.log (5000757 / 5000000) = -Real.log (5000000 / 5000757) := by
    rw [show ((5000757 / 5000000) : ℝ) = ((5000000 / 5000757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_180_neg : (151411 / 1000000000) ≤ -Real.log (4999243 / 5000000) ∧
    -Real.log (4999243 / 5000000) ≤ (37853 / 250000000) := by
  have h := checkLog_sound (w := (757 / 9999243)) (n := 12)
    (lo := (151411 / 1000000000)) (hi := (37853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999243) = 1/(4999243 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_180 : Bounds (-37853 / 250000000) (-151411 / 1000000000) (Real.log (4999243 / 5000000)) := by
  have h := reflection_log_180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_181_neg : (2285853 / 31250000) ≤ -Real.log (1000000 / 1075889) ∧
    -Real.log (1000000 / 1075889) ≤ (73147297 / 1000000000) := by
  have h := checkLog_sound (w := (75889 / 2075889)) (n := 12)
    (lo := (2285853 / 31250000)) (hi := (73147297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075889 / 1000000) = 1/(1000000 / 1075889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_181 : Bounds (2285853 / 31250000) (73147297 / 1000000000) (Real.log (1075889 / 1000000)) := by
  have h := reflection_log_181_neg
  have he : Real.log (1075889 / 1000000) = -Real.log (1000000 / 1075889) := by
    rw [show ((1075889 / 1000000) : ℝ) = ((1000000 / 1075889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_182_neg : (19730771 / 250000000) ≤ -Real.log (924111 / 1000000) ∧
    -Real.log (924111 / 1000000) ≤ (15784617 / 200000000) := by
  have h := checkLog_sound (w := (75889 / 1924111)) (n := 12)
    (lo := (19730771 / 250000000)) (hi := (15784617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924111) = 1/(924111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_182 : Bounds (-15784617 / 200000000) (-19730771 / 250000000) (Real.log (924111 / 1000000)) := by
  have h := reflection_log_182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_183_neg : (7333503 / 100000000) ≤ -Real.log (1000000 / 1076091) ∧
    -Real.log (1000000 / 1076091) ≤ (73335031 / 1000000000) := by
  have h := checkLog_sound (w := (76091 / 2076091)) (n := 12)
    (lo := (7333503 / 100000000)) (hi := (73335031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076091 / 1000000) = 1/(1000000 / 1076091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_183 : Bounds (7333503 / 100000000) (73335031 / 1000000000) (Real.log (1076091 / 1000000)) := by
  have h := reflection_log_183_neg
  have he : Real.log (1076091 / 1000000) = -Real.log (1000000 / 1076091) := by
    rw [show ((1076091 / 1000000) : ℝ) = ((1000000 / 1076091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_184_neg : (79141697 / 1000000000) ≤ -Real.log (923909 / 1000000) ∧
    -Real.log (923909 / 1000000) ≤ (39570849 / 500000000) := by
  have h := checkLog_sound (w := (76091 / 1923909)) (n := 12)
    (lo := (79141697 / 1000000000)) (hi := (39570849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923909) = 1/(923909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_184 : Bounds (-39570849 / 500000000) (-79141697 / 1000000000) (Real.log (923909 / 1000000)) := by
  have h := reflection_log_184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_185_neg : (2903333 / 500000000) ≤ -Real.log (994210159719 / 1000000000000) ∧
    -Real.log (994210159719 / 1000000000000) ≤ (5806667 / 1000000000) := by
  have h := checkLog_sound (w := (5789840281 / 1994210159719)) (n := 12)
    (lo := (2903333 / 500000000)) (hi := (5806667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994210159719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994210159719) = 1/(994210159719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_185 : Bounds (-5806667 / 1000000000) (-2903333 / 500000000) (Real.log (994210159719 / 1000000000000)) := by
  have h := reflection_log_185_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_186_neg : (1443947 / 250000000) ≤ -Real.log (994240859679 / 1000000000000) ∧
    -Real.log (994240859679 / 1000000000000) ≤ (5775789 / 1000000000) := by
  have h := checkLog_sound (w := (5759140321 / 1994240859679)) (n := 12)
    (lo := (1443947 / 250000000)) (hi := (5775789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994240859679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994240859679) = 1/(994240859679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_186 : Bounds (-5775789 / 1000000000) (-1443947 / 250000000) (Real.log (994240859679 / 1000000000000)) := by
  have h := reflection_log_186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_187_neg : (152070381 / 1000000000) ≤ -Real.log (100000000000 / 116424217437) ∧
    -Real.log (100000000000 / 116424217437) ≤ (76035191 / 500000000) := by
  have h := checkLog_sound (w := (16424217437 / 216424217437)) (n := 12)
    (lo := (152070381 / 1000000000)) (hi := (76035191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116424217437 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116424217437 / 100000000000) = 1/(100000000000 / 116424217437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_187 : Bounds (152070381 / 1000000000) (76035191 / 500000000) (Real.log (116424217437 / 100000000000)) := by
  have h := reflection_log_187_neg
  have he : Real.log (116424217437 / 100000000000) = -Real.log (100000000000 / 116424217437) := by
    rw [show ((116424217437 / 100000000000) : ℝ) = ((100000000000 / 116424217437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_188_neg : (152476727 / 1000000000) ≤ -Real.log (125000000000 / 145589419521) ∧
    -Real.log (125000000000 / 145589419521) ≤ (19059591 / 125000000) := by
  have h := checkLog_sound (w := (20589419521 / 270589419521)) (n := 12)
    (lo := (152476727 / 1000000000)) (hi := (19059591 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145589419521 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145589419521 / 125000000000) = 1/(125000000000 / 145589419521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_188 : Bounds (152476727 / 1000000000) (19059591 / 125000000) (Real.log (145589419521 / 125000000000)) := by
  have h := reflection_log_188_neg
  have he : Real.log (145589419521 / 125000000000) = -Real.log (125000000000 / 145589419521) := by
    rw [show ((145589419521 / 125000000000) : ℝ) = ((125000000000 / 145589419521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_189_neg : (243953 / 800000) ≤ -Real.log (500000000000 / 678272652291) ∧
    -Real.log (500000000000 / 678272652291) ≤ (304941251 / 1000000000) := by
  have h := checkLog_sound (w := (178272652291 / 1178272652291)) (n := 12)
    (lo := (243953 / 800000)) (hi := (304941251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678272652291 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678272652291 / 500000000000) = 1/(500000000000 / 678272652291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_189 : Bounds (243953 / 800000) (304941251 / 1000000000) (Real.log (678272652291 / 500000000000)) := by
  have h := reflection_log_189_neg
  have he : Real.log (678272652291 / 500000000000) = -Real.log (500000000000 / 678272652291) := by
    rw [show ((678272652291 / 500000000000) : ℝ) = ((500000000000 / 678272652291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_190_neg : (305145939 / 1000000000) ≤ -Real.log (500000000000 / 678411501297) ∧
    -Real.log (500000000000 / 678411501297) ≤ (15257297 / 50000000) := by
  have h := checkLog_sound (w := (178411501297 / 1178411501297)) (n := 12)
    (lo := (305145939 / 1000000000)) (hi := (15257297 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678411501297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678411501297 / 500000000000) = 1/(500000000000 / 678411501297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_190 : Bounds (305145939 / 1000000000) (15257297 / 50000000) (Real.log (678411501297 / 500000000000)) := by
  have h := reflection_log_190_neg
  have he : Real.log (678411501297 / 500000000000) = -Real.log (500000000000 / 678411501297) := by
    rw [show ((678411501297 / 500000000000) : ℝ) = ((500000000000 / 678411501297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_191_neg : (881659 / 6250000) ≤ -Real.log (2000 / 2303) ∧
    -Real.log (2000 / 2303) ≤ (141065441 / 1000000000) := by
  have h := checkLog_sound (w := (303 / 4303)) (n := 12)
    (lo := (881659 / 6250000)) (hi := (141065441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2303 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2303 / 2000) = 1/(2000 / 2303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_191 : Bounds (881659 / 6250000) (141065441 / 1000000000) (Real.log (2303 / 2000)) := by
  have h := reflection_log_191_neg
  have he : Real.log (2303 / 2000) = -Real.log (2000 / 2303) := by
    rw [show ((2303 / 2000) : ℝ) = ((2000 / 2303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


