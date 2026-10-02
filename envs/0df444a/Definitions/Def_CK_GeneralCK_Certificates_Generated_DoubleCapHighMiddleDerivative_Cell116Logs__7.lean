-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell116Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell116Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:35:29.805033+00:00
-- url     : https://prove2.me/theorems/87bb39b7-10da-4c1e-aa94-765dfaba76e9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell116Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell117…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell116Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell117Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell118Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell119Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell120Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell121Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell122Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell116Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell117Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell118Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell119Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell120Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell121Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell122Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell116Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell117Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell118Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell119Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell120Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell121Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell122Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell116Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell117Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell118Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell119Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell120Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell121Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell122Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell116Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell116
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (276536203 / 1000000000) ≤ -Real.log (5120 / 6751) ∧
    -Real.log (5120 / 6751) ≤ (69134051 / 250000000) := by
  have h := checkLog_sound (w := (1631 / 11871)) (n := 12)
    (lo := (276536203 / 1000000000)) (hi := (69134051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6751 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6751 / 5120) = 1/(5120 / 6751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (276536203 / 1000000000) (69134051 / 250000000) (Real.log (6751 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6751 / 5120) = -Real.log (5120 / 6751) := by
    rw [show ((6751 / 5120) : ℝ) = ((5120 / 6751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (95884819 / 250000000) ≤ -Real.log (3489 / 5120) ∧
    -Real.log (3489 / 5120) ≤ (383539277 / 1000000000) := by
  have h := checkLog_sound (w := (1631 / 8609)) (n := 12)
    (lo := (95884819 / 250000000)) (hi := (383539277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3489) = 1/(3489 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-383539277 / 1000000000) (-95884819 / 250000000) (Real.log (3489 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11043669 / 40000000) ≤ -Real.log (1280 / 1687) ∧
    -Real.log (1280 / 1687) ≤ (138045863 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2967)) (n := 12)
    (lo := (11043669 / 40000000)) (hi := (138045863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1687 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1687 / 1280) = 1/(1280 / 1687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11043669 / 40000000) (138045863 / 500000000) (Real.log (1687 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1687 / 1280) = -Real.log (1280 / 1687) := by
    rw [show ((1687 / 1280) : ℝ) = ((1280 / 1687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (382679801 / 1000000000) ≤ -Real.log (873 / 1280) ∧
    -Real.log (873 / 1280) ≤ (191339901 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2153)) (n := 12)
    (lo := (382679801 / 1000000000)) (hi := (191339901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 873) = 1/(873 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-191339901 / 500000000) (-382679801 / 1000000000) (Real.log (873 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (101807451 / 500000000) ≤ -Real.log (500000 / 612913) ∧
    -Real.log (500000 / 612913) ≤ (203614903 / 1000000000) := by
  have h := checkLog_sound (w := (112913 / 1112913)) (n := 12)
    (lo := (101807451 / 500000000)) (hi := (203614903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612913 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612913 / 500000) = 1/(500000 / 612913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (101807451 / 500000000) (203614903 / 1000000000) (Real.log (612913 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (612913 / 500000) = -Real.log (500000 / 612913) := by
    rw [show ((612913 / 500000) : ℝ) = ((500000 / 612913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (7998707 / 31250000) ≤ -Real.log (387087 / 500000) ∧
    -Real.log (387087 / 500000) ≤ (2047669 / 8000000) := by
  have h := checkLog_sound (w := (112913 / 887087)) (n := 12)
    (lo := (7998707 / 31250000)) (hi := (2047669 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387087) = 1/(387087 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2047669 / 8000000) (-7998707 / 31250000) (Real.log (387087 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (40791657 / 200000000) ≤ -Real.log (1000000 / 1226247) ∧
    -Real.log (1000000 / 1226247) ≤ (101979143 / 500000000) := by
  have h := checkLog_sound (w := (226247 / 2226247)) (n := 12)
    (lo := (40791657 / 200000000)) (hi := (101979143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226247 / 1000000) = 1/(1000000 / 1226247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (40791657 / 200000000) (101979143 / 500000000) (Real.log (1226247 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1226247 / 1000000) = -Real.log (1000000 / 1226247) := by
    rw [show ((1226247 / 1000000) : ℝ) = ((1000000 / 1226247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (256502577 / 1000000000) ≤ -Real.log (773753 / 1000000) ∧
    -Real.log (773753 / 1000000) ≤ (128251289 / 500000000) := by
  have h := checkLog_sound (w := (226247 / 1773753)) (n := 12)
    (lo := (256502577 / 1000000000)) (hi := (128251289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773753) = 1/(773753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-128251289 / 500000000) (-256502577 / 1000000000) (Real.log (773753 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (150118561 / 1000000000) ≤ -Real.log (250000 / 290493) ∧
    -Real.log (250000 / 290493) ≤ (75059281 / 500000000) := by
  have h := checkLog_sound (w := (40493 / 540493)) (n := 12)
    (lo := (150118561 / 1000000000)) (hi := (75059281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290493 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290493 / 250000) = 1/(250000 / 290493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (150118561 / 1000000000) (75059281 / 500000000) (Real.log (290493 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (290493 / 250000) = -Real.log (250000 / 290493) := by
    rw [show ((290493 / 250000) : ℝ) = ((250000 / 290493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (88351883 / 500000000) ≤ -Real.log (209507 / 250000) ∧
    -Real.log (209507 / 250000) ≤ (176703767 / 1000000000) := by
  have h := checkLog_sound (w := (40493 / 459507)) (n := 12)
    (lo := (88351883 / 500000000)) (hi := (176703767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 209507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 209507) = 1/(209507 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-176703767 / 1000000000) (-88351883 / 500000000) (Real.log (209507 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (75193087 / 500000000) ≤ -Real.log (1000000 / 1162283) ∧
    -Real.log (1000000 / 1162283) ≤ (6015447 / 40000000) := by
  have h := checkLog_sound (w := (162283 / 2162283)) (n := 12)
    (lo := (75193087 / 500000000)) (hi := (6015447 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1162283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1162283 / 1000000) = 1/(1000000 / 1162283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (75193087 / 500000000) (6015447 / 40000000) (Real.log (1162283 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1162283 / 1000000) = -Real.log (1000000 / 1162283) := by
    rw [show ((1162283 / 1000000) : ℝ) = ((1000000 / 1162283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (691699 / 3906250) ≤ -Real.log (837717 / 1000000) ∧
    -Real.log (837717 / 1000000) ≤ (35414989 / 200000000) := by
  have h := checkLog_sound (w := (162283 / 1837717)) (n := 12)
    (lo := (691699 / 3906250)) (hi := (35414989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 837717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 837717) = 1/(837717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-35414989 / 200000000) (-691699 / 3906250) (Real.log (837717 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (329385763 / 500000000) ≤ -Real.log (500000000000 / 966208476517) ∧
    -Real.log (500000000000 / 966208476517) ≤ (658771527 / 1000000000) := by
  have h := checkLog_sound (w := (466208476517 / 1466208476517)) (n := 12)
    (lo := (329385763 / 500000000)) (hi := (658771527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((966208476517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(966208476517 / 500000000000) = 1/(500000000000 / 966208476517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (329385763 / 500000000) (658771527 / 1000000000) (Real.log (966208476517 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (966208476517 / 500000000000) = -Real.log (500000000000 / 966208476517) := by
    rw [show ((966208476517 / 500000000000) : ℝ) = ((500000000000 / 966208476517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (660075479 / 1000000000) ≤ -Real.log (6250000000 / 12093364861) ∧
    -Real.log (6250000000 / 12093364861) ≤ (16501887 / 25000000) := by
  have h := checkLog_sound (w := (5843364861 / 18343364861)) (n := 12)
    (lo := (660075479 / 1000000000)) (hi := (16501887 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12093364861 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12093364861 / 6250000000) = 1/(6250000000 / 12093364861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (660075479 / 1000000000) (16501887 / 25000000) (Real.log (12093364861 / 6250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (12093364861 / 6250000000) = -Real.log (6250000000 / 12093364861) := by
    rw [show ((12093364861 / 6250000000) : ℝ) = ((6250000000 / 12093364861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (229786763 / 500000000) ≤ -Real.log (500000000000 / 791699282073) ∧
    -Real.log (500000000000 / 791699282073) ≤ (459573527 / 1000000000) := by
  have h := checkLog_sound (w := (291699282073 / 1291699282073)) (n := 12)
    (lo := (229786763 / 500000000)) (hi := (459573527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791699282073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791699282073 / 500000000000) = 1/(500000000000 / 791699282073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (229786763 / 500000000) (459573527 / 1000000000) (Real.log (791699282073 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (791699282073 / 500000000000) = -Real.log (500000000000 / 791699282073) := by
    rw [show ((791699282073 / 500000000000) : ℝ) = ((500000000000 / 791699282073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (460460863 / 1000000000) ≤ -Real.log (500000000000 / 792402097311) ∧
    -Real.log (500000000000 / 792402097311) ≤ (7194701 / 15625000) := by
  have h := checkLog_sound (w := (292402097311 / 1292402097311)) (n := 12)
    (lo := (460460863 / 1000000000)) (hi := (7194701 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792402097311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792402097311 / 500000000000) = 1/(500000000000 / 792402097311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (460460863 / 1000000000) (7194701 / 15625000) (Real.log (792402097311 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (792402097311 / 500000000000) = -Real.log (500000000000 / 792402097311) := by
    rw [show ((792402097311 / 500000000000) : ℝ) = ((500000000000 / 792402097311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (326822327 / 1000000000) ≤ -Real.log (100000000000 / 138655510317) ∧
    -Real.log (100000000000 / 138655510317) ≤ (40852791 / 125000000) := by
  have h := checkLog_sound (w := (38655510317 / 238655510317)) (n := 12)
    (lo := (326822327 / 1000000000)) (hi := (40852791 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138655510317 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138655510317 / 100000000000) = 1/(100000000000 / 138655510317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (326822327 / 1000000000) (40852791 / 125000000) (Real.log (138655510317 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (138655510317 / 100000000000) = -Real.log (100000000000 / 138655510317) := by
    rw [show ((138655510317 / 100000000000) : ℝ) = ((100000000000 / 138655510317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (163730559 / 500000000) ≤ -Real.log (500000000000 / 693720552407) ∧
    -Real.log (500000000000 / 693720552407) ≤ (327461119 / 1000000000) := by
  have h := checkLog_sound (w := (193720552407 / 1193720552407)) (n := 12)
    (lo := (163730559 / 500000000)) (hi := (327461119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693720552407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693720552407 / 500000000000) = 1/(500000000000 / 693720552407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (163730559 / 500000000) (327461119 / 1000000000) (Real.log (693720552407 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (693720552407 / 500000000000) = -Real.log (500000000000 / 693720552407) := by
    rw [show ((693720552407 / 500000000000) : ℝ) = ((500000000000 / 693720552407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (26688769 / 1000000000) ≤ -Real.log (973664227911 / 1000000000000) ∧
    -Real.log (973664227911 / 1000000000000) ≤ (2668877 / 100000000) := by
  have h := checkLog_sound (w := (26335772089 / 1973664227911)) (n := 12)
    (lo := (26688769 / 1000000000)) (hi := (2668877 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973664227911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973664227911) = 1/(973664227911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2668877 / 100000000) (-26688769 / 1000000000) (Real.log (973664227911 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6646301 / 250000000) ≤ -Real.log (60860316951 / 62500000000) ∧
    -Real.log (60860316951 / 62500000000) ≤ (5317041 / 200000000) := by
  have h := checkLog_sound (w := (1639683049 / 123360316951)) (n := 12)
    (lo := (6646301 / 250000000)) (hi := (5317041 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60860316951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60860316951) = 1/(60860316951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5317041 / 200000000) (-6646301 / 250000000) (Real.log (60860316951 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell116

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell117Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell117
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (138490241 / 500000000) ≤ -Real.log (2560 / 3377) ∧
    -Real.log (2560 / 3377) ≤ (276980483 / 1000000000) := by
  have h := checkLog_sound (w := (817 / 5937)) (n := 12)
    (lo := (138490241 / 500000000)) (hi := (276980483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3377 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3377 / 2560) = 1/(2560 / 3377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (138490241 / 500000000) (276980483 / 1000000000) (Real.log (3377 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3377 / 2560) = -Real.log (2560 / 3377) := by
    rw [show ((3377 / 2560) : ℝ) = ((2560 / 3377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (384399491 / 1000000000) ≤ -Real.log (1743 / 2560) ∧
    -Real.log (1743 / 2560) ≤ (96099873 / 250000000) := by
  have h := checkLog_sound (w := (817 / 4303)) (n := 12)
    (lo := (384399491 / 1000000000)) (hi := (96099873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1743) = 1/(1743 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-96099873 / 250000000) (-384399491 / 1000000000) (Real.log (1743 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (276536203 / 1000000000) ≤ -Real.log (5120 / 6751) ∧
    -Real.log (5120 / 6751) ≤ (69134051 / 250000000) := by
  have h := checkLog_sound (w := (1631 / 11871)) (n := 12)
    (lo := (276536203 / 1000000000)) (hi := (69134051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6751 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6751 / 5120) = 1/(5120 / 6751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (276536203 / 1000000000) (69134051 / 250000000) (Real.log (6751 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6751 / 5120) = -Real.log (5120 / 6751) := by
    rw [show ((6751 / 5120) : ℝ) = ((5120 / 6751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (95884819 / 250000000) ≤ -Real.log (3489 / 5120) ∧
    -Real.log (3489 / 5120) ≤ (383539277 / 1000000000) := by
  have h := checkLog_sound (w := (1631 / 8609)) (n := 12)
    (lo := (95884819 / 250000000)) (hi := (383539277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3489) = 1/(3489 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-383539277 / 1000000000) (-95884819 / 250000000) (Real.log (3489 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (203957469 / 1000000000) ≤ -Real.log (500000 / 613123) ∧
    -Real.log (500000 / 613123) ≤ (20395747 / 100000000) := by
  have h := checkLog_sound (w := (113123 / 1113123)) (n := 12)
    (lo := (203957469 / 1000000000)) (hi := (20395747 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613123 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613123 / 500000) = 1/(500000 / 613123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (203957469 / 1000000000) (20395747 / 100000000) (Real.log (613123 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613123 / 500000) = -Real.log (500000 / 613123) := by
    rw [show ((613123 / 500000) : ℝ) = ((500000 / 613123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (51300257 / 200000000) ≤ -Real.log (386877 / 500000) ∧
    -Real.log (386877 / 500000) ≤ (128250643 / 500000000) := by
  have h := checkLog_sound (w := (113123 / 886877)) (n := 12)
    (lo := (51300257 / 200000000)) (hi := (128250643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386877) = 1/(386877 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-128250643 / 500000000) (-51300257 / 200000000) (Real.log (386877 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (40860147 / 200000000) ≤ -Real.log (1000000 / 1226667) ∧
    -Real.log (1000000 / 1226667) ≤ (3192199 / 15625000) := by
  have h := checkLog_sound (w := (226667 / 2226667)) (n := 12)
    (lo := (40860147 / 200000000)) (hi := (3192199 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226667 / 1000000) = 1/(1000000 / 1226667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (40860147 / 200000000) (3192199 / 15625000) (Real.log (1226667 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1226667 / 1000000) = -Real.log (1000000 / 1226667) := by
    rw [show ((1226667 / 1000000) : ℝ) = ((1000000 / 1226667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (128522767 / 500000000) ≤ -Real.log (773333 / 1000000) ∧
    -Real.log (773333 / 1000000) ≤ (51409107 / 200000000) := by
  have h := checkLog_sound (w := (226667 / 1773333)) (n := 12)
    (lo := (128522767 / 500000000)) (hi := (51409107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773333) = 1/(773333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-51409107 / 200000000) (-128522767 / 500000000) (Real.log (773333 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75192657 / 500000000) ≤ -Real.log (500000 / 581141) ∧
    -Real.log (500000 / 581141) ≤ (30077063 / 200000000) := by
  have h := checkLog_sound (w := (81141 / 1081141)) (n := 12)
    (lo := (75192657 / 500000000)) (hi := (30077063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581141 / 500000) = 1/(500000 / 581141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75192657 / 500000000) (30077063 / 200000000) (Real.log (581141 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (581141 / 500000) = -Real.log (500000 / 581141) := by
    rw [show ((581141 / 500000) : ℝ) = ((500000 / 581141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (141659 / 800000) ≤ -Real.log (418859 / 500000) ∧
    -Real.log (418859 / 500000) ≤ (177073751 / 1000000000) := by
  have h := checkLog_sound (w := (81141 / 918859)) (n := 12)
    (lo := (141659 / 800000)) (hi := (177073751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418859) = 1/(418859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-177073751 / 1000000000) (-141659 / 800000) (Real.log (418859 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (30130571 / 200000000) ≤ -Real.log (1000000 / 1162593) ∧
    -Real.log (1000000 / 1162593) ≤ (18831607 / 125000000) := by
  have h := checkLog_sound (w := (162593 / 2162593)) (n := 12)
    (lo := (30130571 / 200000000)) (hi := (18831607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1162593 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1162593 / 1000000) = 1/(1000000 / 1162593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (30130571 / 200000000) (18831607 / 125000000) (Real.log (1162593 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1162593 / 1000000) = -Real.log (1000000 / 1162593) := by
    rw [show ((1162593 / 1000000) : ℝ) = ((1000000 / 1162593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (88722533 / 500000000) ≤ -Real.log (837407 / 1000000) ∧
    -Real.log (837407 / 1000000) ≤ (177445067 / 1000000000) := by
  have h := checkLog_sound (w := (162593 / 1837407)) (n := 12)
    (lo := (88722533 / 500000000)) (hi := (177445067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 837407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 837407) = 1/(837407 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-177445067 / 1000000000) (-88722533 / 500000000) (Real.log (837407 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (660075479 / 1000000000) ≤ -Real.log (500000000000 / 967469188879) ∧
    -Real.log (500000000000 / 967469188879) ≤ (16501887 / 25000000) := by
  have h := checkLog_sound (w := (467469188879 / 1467469188879)) (n := 12)
    (lo := (660075479 / 1000000000)) (hi := (16501887 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((967469188879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(967469188879 / 500000000000) = 1/(500000000000 / 967469188879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (660075479 / 1000000000) (16501887 / 25000000) (Real.log (967469188879 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (967469188879 / 500000000000) = -Real.log (500000000000 / 967469188879) := by
    rw [show ((967469188879 / 500000000000) : ℝ) = ((500000000000 / 967469188879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (330689987 / 500000000) ≤ -Real.log (250000000000 / 484366035571) ∧
    -Real.log (250000000000 / 484366035571) ≤ (26455199 / 40000000) := by
  have h := checkLog_sound (w := (234366035571 / 734366035571)) (n := 12)
    (lo := (330689987 / 500000000)) (hi := (26455199 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484366035571 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(484366035571 / 250000000000) = 1/(250000000000 / 484366035571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (330689987 / 500000000) (26455199 / 40000000) (Real.log (484366035571 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (484366035571 / 250000000000) = -Real.log (250000000000 / 484366035571) := by
    rw [show ((484366035571 / 250000000000) : ℝ) = ((250000000000 / 484366035571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (92091751 / 200000000) ≤ -Real.log (500000000000 / 792400427009) ∧
    -Real.log (500000000000 / 792400427009) ≤ (115114689 / 250000000) := by
  have h := checkLog_sound (w := (292400427009 / 1292400427009)) (n := 12)
    (lo := (92091751 / 200000000)) (hi := (115114689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792400427009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792400427009 / 500000000000) = 1/(500000000000 / 792400427009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (92091751 / 200000000) (115114689 / 250000000) (Real.log (792400427009 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (792400427009 / 500000000000) = -Real.log (500000000000 / 792400427009) := by
    rw [show ((792400427009 / 500000000000) : ℝ) = ((500000000000 / 792400427009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (461346269 / 1000000000) ≤ -Real.log (500000000000 / 793104005649) ∧
    -Real.log (500000000000 / 793104005649) ≤ (46134627 / 100000000) := by
  have h := checkLog_sound (w := (293104005649 / 1293104005649)) (n := 12)
    (lo := (461346269 / 1000000000)) (hi := (46134627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793104005649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793104005649 / 500000000000) = 1/(500000000000 / 793104005649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (461346269 / 1000000000) (46134627 / 100000000) (Real.log (793104005649 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (793104005649 / 500000000000) = -Real.log (500000000000 / 793104005649) := by
    rw [show ((793104005649 / 500000000000) : ℝ) = ((500000000000 / 793104005649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (40932383 / 125000000) ≤ -Real.log (500000000000 / 693719127439) ∧
    -Real.log (500000000000 / 693719127439) ≤ (65491813 / 200000000) := by
  have h := checkLog_sound (w := (193719127439 / 1193719127439)) (n := 12)
    (lo := (40932383 / 125000000)) (hi := (65491813 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693719127439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693719127439 / 500000000000) = 1/(500000000000 / 693719127439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (40932383 / 125000000) (65491813 / 200000000) (Real.log (693719127439 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (693719127439 / 500000000000) = -Real.log (500000000000 / 693719127439) := by
    rw [show ((693719127439 / 500000000000) : ℝ) = ((500000000000 / 693719127439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (328097921 / 1000000000) ≤ -Real.log (500000000000 / 694162456249) ∧
    -Real.log (500000000000 / 694162456249) ≤ (164048961 / 500000000) := by
  have h := checkLog_sound (w := (194162456249 / 1194162456249)) (n := 12)
    (lo := (328097921 / 1000000000)) (hi := (164048961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694162456249 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694162456249 / 500000000000) = 1/(500000000000 / 694162456249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (328097921 / 1000000000) (164048961 / 500000000) (Real.log (694162456249 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (694162456249 / 500000000000) = -Real.log (500000000000 / 694162456249) := by
    rw [show ((694162456249 / 500000000000) : ℝ) = ((500000000000 / 694162456249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2679221 / 100000000) ≤ -Real.log (973563516351 / 1000000000000) ∧
    -Real.log (973563516351 / 1000000000000) ≤ (26792211 / 1000000000) := by
  have h := checkLog_sound (w := (26436483649 / 1973563516351)) (n := 12)
    (lo := (2679221 / 100000000)) (hi := (26792211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973563516351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973563516351) = 1/(973563516351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26792211 / 1000000000) (-2679221 / 100000000) (Real.log (973563516351 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6672109 / 250000000) ≤ -Real.log (243416138119 / 250000000000) ∧
    -Real.log (243416138119 / 250000000000) ≤ (26688437 / 1000000000) := by
  have h := checkLog_sound (w := (6583861881 / 493416138119)) (n := 12)
    (lo := (6672109 / 250000000)) (hi := (26688437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243416138119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243416138119) = 1/(243416138119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26688437 / 1000000000) (-6672109 / 250000000) (Real.log (243416138119 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell117

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell118Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell118
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (55484913 / 200000000) ≤ -Real.log (5120 / 6757) ∧
    -Real.log (5120 / 6757) ≤ (138712283 / 500000000) := by
  have h := checkLog_sound (w := (1637 / 11877)) (n := 12)
    (lo := (55484913 / 200000000)) (hi := (138712283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6757 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6757 / 5120) = 1/(5120 / 6757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (55484913 / 200000000) (138712283 / 500000000) (Real.log (6757 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6757 / 5120) = -Real.log (5120 / 6757) := by
    rw [show ((6757 / 5120) : ℝ) = ((5120 / 6757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (385260447 / 1000000000) ≤ -Real.log (3483 / 5120) ∧
    -Real.log (3483 / 5120) ≤ (12039389 / 31250000) := by
  have h := checkLog_sound (w := (1637 / 8603)) (n := 12)
    (lo := (385260447 / 1000000000)) (hi := (12039389 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3483) = 1/(3483 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12039389 / 31250000) (-385260447 / 1000000000) (Real.log (3483 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (138490241 / 500000000) ≤ -Real.log (2560 / 3377) ∧
    -Real.log (2560 / 3377) ≤ (276980483 / 1000000000) := by
  have h := checkLog_sound (w := (817 / 5937)) (n := 12)
    (lo := (138490241 / 500000000)) (hi := (276980483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3377 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3377 / 2560) = 1/(2560 / 3377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (138490241 / 500000000) (276980483 / 1000000000) (Real.log (3377 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3377 / 2560) = -Real.log (2560 / 3377) := by
    rw [show ((3377 / 2560) : ℝ) = ((2560 / 3377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (384399491 / 1000000000) ≤ -Real.log (1743 / 2560) ∧
    -Real.log (1743 / 2560) ≤ (96099873 / 250000000) := by
  have h := checkLog_sound (w := (817 / 4303)) (n := 12)
    (lo := (384399491 / 1000000000)) (hi := (96099873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1743) = 1/(1743 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-96099873 / 250000000) (-384399491 / 1000000000) (Real.log (1743 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2553749 / 12500000) ≤ -Real.log (500000 / 613333) ∧
    -Real.log (500000 / 613333) ≤ (204299921 / 1000000000) := by
  have h := checkLog_sound (w := (113333 / 1113333)) (n := 12)
    (lo := (2553749 / 12500000)) (hi := (204299921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613333 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613333 / 500000) = 1/(500000 / 613333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2553749 / 12500000) (204299921 / 1000000000) (Real.log (613333 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613333 / 500000) = -Real.log (500000 / 613333) := by
    rw [show ((613333 / 500000) : ℝ) = ((500000 / 613333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3213053 / 12500000) ≤ -Real.log (386667 / 500000) ∧
    -Real.log (386667 / 500000) ≤ (257044241 / 1000000000) := by
  have h := checkLog_sound (w := (113333 / 886667)) (n := 12)
    (lo := (3213053 / 12500000)) (hi := (257044241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386667) = 1/(386667 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-257044241 / 1000000000) (-3213053 / 12500000) (Real.log (386667 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (204643067 / 1000000000) ≤ -Real.log (1000000 / 1227087) ∧
    -Real.log (1000000 / 1227087) ≤ (51160767 / 250000000) := by
  have h := checkLog_sound (w := (227087 / 2227087)) (n := 12)
    (lo := (204643067 / 1000000000)) (hi := (51160767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227087 / 1000000) = 1/(1000000 / 1227087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (204643067 / 1000000000) (51160767 / 250000000) (Real.log (1227087 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1227087 / 1000000) = -Real.log (1000000 / 1227087) := by
    rw [show ((1227087 / 1000000) : ℝ) = ((1000000 / 1227087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (51517757 / 200000000) ≤ -Real.log (772913 / 1000000) ∧
    -Real.log (772913 / 1000000) ≤ (128794393 / 500000000) := by
  have h := checkLog_sound (w := (227087 / 1772913)) (n := 12)
    (lo := (51517757 / 200000000)) (hi := (128794393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772913) = 1/(772913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-128794393 / 500000000) (-51517757 / 200000000) (Real.log (772913 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (30130399 / 200000000) ≤ -Real.log (31250 / 36331) ∧
    -Real.log (31250 / 36331) ≤ (37662999 / 250000000) := by
  have h := checkLog_sound (w := (5081 / 67581)) (n := 12)
    (lo := (30130399 / 200000000)) (hi := (37662999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36331 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36331 / 31250) = 1/(31250 / 36331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (30130399 / 200000000) (37662999 / 250000000) (Real.log (36331 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (36331 / 31250) = -Real.log (31250 / 36331) := by
    rw [show ((36331 / 31250) : ℝ) = ((31250 / 36331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (5545121 / 31250000) ≤ -Real.log (26169 / 31250) ∧
    -Real.log (26169 / 31250) ≤ (177443873 / 1000000000) := by
  have h := checkLog_sound (w := (5081 / 57419)) (n := 12)
    (lo := (5545121 / 31250000)) (hi := (177443873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 26169) = 1/(26169 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-177443873 / 1000000000) (-5545121 / 31250000) (Real.log (26169 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (30183893 / 200000000) ≤ -Real.log (1000000 / 1162903) ∧
    -Real.log (1000000 / 1162903) ≤ (75459733 / 500000000) := by
  have h := checkLog_sound (w := (162903 / 2162903)) (n := 12)
    (lo := (30183893 / 200000000)) (hi := (75459733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1162903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1162903 / 1000000) = 1/(1000000 / 1162903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (30183893 / 200000000) (75459733 / 500000000) (Real.log (1162903 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1162903 / 1000000) = -Real.log (1000000 / 1162903) := by
    rw [show ((1162903 / 1000000) : ℝ) = ((1000000 / 1162903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7112613 / 40000000) ≤ -Real.log (837097 / 1000000) ∧
    -Real.log (837097 / 1000000) ≤ (88907663 / 500000000) := by
  have h := checkLog_sound (w := (162903 / 1837097)) (n := 12)
    (lo := (7112613 / 40000000)) (hi := (88907663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 837097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 837097) = 1/(837097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-88907663 / 500000000) (-7112613 / 40000000) (Real.log (837097 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (330689987 / 500000000) ≤ -Real.log (500000000000 / 968732071141) ∧
    -Real.log (500000000000 / 968732071141) ≤ (26455199 / 40000000) := by
  have h := checkLog_sound (w := (468732071141 / 1468732071141)) (n := 12)
    (lo := (330689987 / 500000000)) (hi := (26455199 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((968732071141 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(968732071141 / 500000000000) = 1/(500000000000 / 968732071141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (330689987 / 500000000) (26455199 / 40000000) (Real.log (968732071141 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (968732071141 / 500000000000) = -Real.log (500000000000 / 968732071141) := by
    rw [show ((968732071141 / 500000000000) : ℝ) = ((500000000000 / 968732071141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (662685013 / 1000000000) ≤ -Real.log (31250000000 / 60624820557) ∧
    -Real.log (31250000000 / 60624820557) ≤ (331342507 / 500000000) := by
  have h := checkLog_sound (w := (29374820557 / 91874820557)) (n := 12)
    (lo := (662685013 / 1000000000)) (hi := (331342507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60624820557 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60624820557 / 31250000000) = 1/(31250000000 / 60624820557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (662685013 / 1000000000) (331342507 / 500000000) (Real.log (60624820557 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (60624820557 / 31250000000) = -Real.log (31250000000 / 60624820557) := by
    rw [show ((60624820557 / 31250000000) : ℝ) = ((31250000000 / 60624820557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (2883401 / 6250000) ≤ -Real.log (125000000000 / 198275583383) ∧
    -Real.log (125000000000 / 198275583383) ≤ (461344161 / 1000000000) := by
  have h := checkLog_sound (w := (73275583383 / 323275583383)) (n := 12)
    (lo := (2883401 / 6250000)) (hi := (461344161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198275583383 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198275583383 / 125000000000) = 1/(125000000000 / 198275583383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (2883401 / 6250000) (461344161 / 1000000000) (Real.log (198275583383 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (198275583383 / 125000000000) = -Real.log (125000000000 / 198275583383) := by
    rw [show ((198275583383 / 125000000000) : ℝ) = ((125000000000 / 198275583383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (462231853 / 1000000000) ≤ -Real.log (500000000000 / 793806676819) ∧
    -Real.log (500000000000 / 793806676819) ≤ (231115927 / 500000000) := by
  have h := checkLog_sound (w := (293806676819 / 1293806676819)) (n := 12)
    (lo := (462231853 / 1000000000)) (hi := (231115927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793806676819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793806676819 / 500000000000) = 1/(500000000000 / 793806676819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (462231853 / 1000000000) (231115927 / 500000000) (Real.log (793806676819 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (793806676819 / 500000000000) = -Real.log (500000000000 / 793806676819) := by
    rw [show ((793806676819 / 500000000000) : ℝ) = ((500000000000 / 793806676819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (328095867 / 1000000000) ≤ -Real.log (250000000000 / 347080515113) ∧
    -Real.log (250000000000 / 347080515113) ≤ (82023967 / 250000000) := by
  have h := checkLog_sound (w := (97080515113 / 597080515113)) (n := 12)
    (lo := (328095867 / 1000000000)) (hi := (82023967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347080515113 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347080515113 / 250000000000) = 1/(250000000000 / 347080515113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (328095867 / 1000000000) (82023967 / 250000000) (Real.log (347080515113 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (347080515113 / 250000000000) = -Real.log (250000000000 / 347080515113) := by
    rw [show ((347080515113 / 250000000000) : ℝ) = ((250000000000 / 347080515113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (32873479 / 100000000) ≤ -Real.log (50000000000 / 69460468739) ∧
    -Real.log (50000000000 / 69460468739) ≤ (328734791 / 1000000000) := by
  have h := checkLog_sound (w := (19460468739 / 119460468739)) (n := 12)
    (lo := (32873479 / 100000000)) (hi := (328734791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69460468739 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69460468739 / 50000000000) = 1/(50000000000 / 69460468739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (32873479 / 100000000) (328734791 / 1000000000) (Real.log (69460468739 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (69460468739 / 50000000000) = -Real.log (50000000000 / 69460468739) := by
    rw [show ((69460468739 / 50000000000) : ℝ) = ((50000000000 / 69460468739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1344793 / 50000000) ≤ -Real.log (973462612591 / 1000000000000) ∧
    -Real.log (973462612591 / 1000000000000) ≤ (26895861 / 1000000000) := by
  have h := checkLog_sound (w := (26537387409 / 1973462612591)) (n := 12)
    (lo := (1344793 / 50000000)) (hi := (26895861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973462612591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973462612591) = 1/(973462612591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26895861 / 1000000000) (-1344793 / 50000000) (Real.log (973462612591 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6697969 / 250000000) ≤ -Real.log (950745939 / 976562500) ∧
    -Real.log (950745939 / 976562500) ≤ (26791877 / 1000000000) := by
  have h := checkLog_sound (w := (25816561 / 1927308439)) (n := 12)
    (lo := (6697969 / 250000000)) (hi := (26791877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 950745939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 950745939) = 1/(950745939 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26791877 / 1000000000) (-6697969 / 250000000) (Real.log (950745939 / 976562500)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell118

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell119Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell119
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (277868451 / 1000000000) ≤ -Real.log (128 / 169) ∧
    -Real.log (128 / 169) ≤ (69467113 / 250000000) := by
  have h := checkLog_sound (w := (41 / 297)) (n := 12)
    (lo := (277868451 / 1000000000)) (hi := (69467113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169 / 128) = 1/(128 / 169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (277868451 / 1000000000) (69467113 / 250000000) (Real.log (169 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (169 / 128) = -Real.log (128 / 169) := by
    rw [show ((169 / 128) : ℝ) = ((128 / 169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (77224429 / 200000000) ≤ -Real.log (87 / 128) ∧
    -Real.log (87 / 128) ≤ (193061073 / 500000000) := by
  have h := checkLog_sound (w := (41 / 215)) (n := 12)
    (lo := (77224429 / 200000000)) (hi := (193061073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 87) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 87) = 1/(87 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-193061073 / 500000000) (-77224429 / 200000000) (Real.log (87 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (55484913 / 200000000) ≤ -Real.log (5120 / 6757) ∧
    -Real.log (5120 / 6757) ≤ (138712283 / 500000000) := by
  have h := checkLog_sound (w := (1637 / 11877)) (n := 12)
    (lo := (55484913 / 200000000)) (hi := (138712283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6757 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6757 / 5120) = 1/(5120 / 6757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (55484913 / 200000000) (138712283 / 500000000) (Real.log (6757 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6757 / 5120) = -Real.log (5120 / 6757) := by
    rw [show ((6757 / 5120) : ℝ) = ((5120 / 6757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (385260447 / 1000000000) ≤ -Real.log (3483 / 5120) ∧
    -Real.log (3483 / 5120) ≤ (12039389 / 31250000) := by
  have h := checkLog_sound (w := (1637 / 8603)) (n := 12)
    (lo := (385260447 / 1000000000)) (hi := (12039389 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3483) = 1/(3483 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12039389 / 31250000) (-385260447 / 1000000000) (Real.log (3483 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (51160563 / 250000000) ≤ -Real.log (500000 / 613543) ∧
    -Real.log (500000 / 613543) ≤ (204642253 / 1000000000) := by
  have h := checkLog_sound (w := (113543 / 1113543)) (n := 12)
    (lo := (51160563 / 250000000)) (hi := (204642253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613543 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613543 / 500000) = 1/(500000 / 613543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (51160563 / 250000000) (204642253 / 1000000000) (Real.log (613543 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613543 / 500000) = -Real.log (500000 / 613543) := by
    rw [show ((613543 / 500000) : ℝ) = ((500000 / 613543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (257587491 / 1000000000) ≤ -Real.log (386457 / 500000) ∧
    -Real.log (386457 / 500000) ≤ (64396873 / 250000000) := by
  have h := checkLog_sound (w := (113543 / 886457)) (n := 12)
    (lo := (257587491 / 1000000000)) (hi := (64396873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386457) = 1/(386457 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-64396873 / 250000000) (-257587491 / 1000000000) (Real.log (386457 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (204985283 / 1000000000) ≤ -Real.log (1000000 / 1227507) ∧
    -Real.log (1000000 / 1227507) ≤ (51246321 / 250000000) := by
  have h := checkLog_sound (w := (227507 / 2227507)) (n := 12)
    (lo := (204985283 / 1000000000)) (hi := (51246321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227507 / 1000000) = 1/(1000000 / 1227507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (204985283 / 1000000000) (51246321 / 250000000) (Real.log (1227507 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1227507 / 1000000) = -Real.log (1000000 / 1227507) := by
    rw [show ((1227507 / 1000000) : ℝ) = ((1000000 / 1227507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (258132331 / 1000000000) ≤ -Real.log (772493 / 1000000) ∧
    -Real.log (772493 / 1000000) ≤ (64533083 / 250000000) := by
  have h := checkLog_sound (w := (227507 / 1772493)) (n := 12)
    (lo := (258132331 / 1000000000)) (hi := (64533083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772493) = 1/(772493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-64533083 / 250000000) (-258132331 / 1000000000) (Real.log (772493 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (30183721 / 200000000) ≤ -Real.log (500000 / 581451) ∧
    -Real.log (500000 / 581451) ≤ (75459303 / 500000000) := by
  have h := checkLog_sound (w := (81451 / 1081451)) (n := 12)
    (lo := (30183721 / 200000000)) (hi := (75459303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581451 / 500000) = 1/(500000 / 581451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (30183721 / 200000000) (75459303 / 500000000) (Real.log (581451 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (581451 / 500000) = -Real.log (500000 / 581451) := by
    rw [show ((581451 / 500000) : ℝ) = ((500000 / 581451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (17781413 / 100000000) ≤ -Real.log (418549 / 500000) ∧
    -Real.log (418549 / 500000) ≤ (177814131 / 1000000000) := by
  have h := checkLog_sound (w := (81451 / 918549)) (n := 12)
    (lo := (17781413 / 100000000)) (hi := (177814131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418549) = 1/(418549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-177814131 / 1000000000) (-17781413 / 100000000) (Real.log (418549 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (151186003 / 1000000000) ≤ -Real.log (1000000 / 1163213) ∧
    -Real.log (1000000 / 1163213) ≤ (37796501 / 250000000) := by
  have h := checkLog_sound (w := (163213 / 2163213)) (n := 12)
    (lo := (151186003 / 1000000000)) (hi := (37796501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163213 / 1000000) = 1/(1000000 / 1163213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (151186003 / 1000000000) (37796501 / 250000000) (Real.log (1163213 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1163213 / 1000000) = -Real.log (1000000 / 1163213) := by
    rw [show ((1163213 / 1000000) : ℝ) = ((1000000 / 1163213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (178185721 / 1000000000) ≤ -Real.log (836787 / 1000000) ∧
    -Real.log (836787 / 1000000) ≤ (89092861 / 500000000) := by
  have h := checkLog_sound (w := (163213 / 1836787)) (n := 12)
    (lo := (178185721 / 1000000000)) (hi := (89092861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 836787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 836787) = 1/(836787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89092861 / 500000000) (-178185721 / 1000000000) (Real.log (836787 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (662685013 / 1000000000) ≤ -Real.log (500000000000 / 969997128911) ∧
    -Real.log (500000000000 / 969997128911) ≤ (331342507 / 500000000) := by
  have h := checkLog_sound (w := (469997128911 / 1469997128911)) (n := 12)
    (lo := (662685013 / 1000000000)) (hi := (331342507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((969997128911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(969997128911 / 500000000000) = 1/(500000000000 / 969997128911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (662685013 / 1000000000) (331342507 / 500000000) (Real.log (969997128911 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (969997128911 / 500000000000) = -Real.log (500000000000 / 969997128911) := by
    rw [show ((969997128911 / 500000000000) : ℝ) = ((500000000000 / 969997128911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (165997649 / 250000000) ≤ -Real.log (500000000000 / 971264367817) ∧
    -Real.log (500000000000 / 971264367817) ≤ (663990597 / 1000000000) := by
  have h := checkLog_sound (w := (471264367817 / 1471264367817)) (n := 12)
    (lo := (165997649 / 250000000)) (hi := (663990597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971264367817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971264367817 / 500000000000) = 1/(500000000000 / 971264367817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (165997649 / 250000000) (663990597 / 1000000000) (Real.log (971264367817 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (971264367817 / 500000000000) = -Real.log (500000000000 / 971264367817) := by
    rw [show ((971264367817 / 500000000000) : ℝ) = ((500000000000 / 971264367817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (28889359 / 62500000) ≤ -Real.log (100000000000 / 158761000577) ∧
    -Real.log (100000000000 / 158761000577) ≤ (92445949 / 200000000) := by
  have h := checkLog_sound (w := (58761000577 / 258761000577)) (n := 12)
    (lo := (28889359 / 62500000)) (hi := (92445949 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158761000577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158761000577 / 100000000000) = 1/(100000000000 / 158761000577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (28889359 / 62500000) (92445949 / 200000000) (Real.log (158761000577 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (158761000577 / 100000000000) = -Real.log (100000000000 / 158761000577) := by
    rw [show ((158761000577 / 100000000000) : ℝ) = ((100000000000 / 158761000577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (92623523 / 200000000) ≤ -Real.log (250000000000 / 397255056033) ∧
    -Real.log (250000000000 / 397255056033) ≤ (28944851 / 62500000) := by
  have h := checkLog_sound (w := (147255056033 / 647255056033)) (n := 12)
    (lo := (92623523 / 200000000)) (hi := (28944851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397255056033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397255056033 / 250000000000) = 1/(250000000000 / 397255056033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (92623523 / 200000000) (28944851 / 62500000) (Real.log (397255056033 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (397255056033 / 250000000000) = -Real.log (250000000000 / 397255056033) := by
    rw [show ((397255056033 / 250000000000) : ℝ) = ((250000000000 / 397255056033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (65746547 / 200000000) ≤ -Real.log (500000000000 / 694603260311) ∧
    -Real.log (500000000000 / 694603260311) ≤ (5136449 / 15625000) := by
  have h := checkLog_sound (w := (194603260311 / 1194603260311)) (n := 12)
    (lo := (65746547 / 200000000)) (hi := (5136449 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694603260311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694603260311 / 500000000000) = 1/(500000000000 / 694603260311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (65746547 / 200000000) (5136449 / 15625000) (Real.log (694603260311 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (694603260311 / 500000000000) = -Real.log (500000000000 / 694603260311) := by
    rw [show ((694603260311 / 500000000000) : ℝ) = ((500000000000 / 694603260311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (82342931 / 250000000) ≤ -Real.log (500000000000 / 695047246193) ∧
    -Real.log (500000000000 / 695047246193) ≤ (13174869 / 40000000) := by
  have h := checkLog_sound (w := (195047246193 / 1195047246193)) (n := 12)
    (lo := (82342931 / 250000000)) (hi := (13174869 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695047246193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695047246193 / 500000000000) = 1/(500000000000 / 695047246193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (82342931 / 250000000) (13174869 / 40000000) (Real.log (695047246193 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (695047246193 / 500000000000) = -Real.log (500000000000 / 695047246193) := by
    rw [show ((695047246193 / 500000000000) : ℝ) = ((500000000000 / 695047246193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (26999717 / 1000000000) ≤ -Real.log (973361516631 / 1000000000000) ∧
    -Real.log (973361516631 / 1000000000000) ≤ (13499859 / 500000000) := by
  have h := checkLog_sound (w := (26638483369 / 1973361516631)) (n := 12)
    (lo := (26999717 / 1000000000)) (hi := (13499859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973361516631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973361516631) = 1/(973361516631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-13499859 / 500000000) (-26999717 / 1000000000) (Real.log (973361516631 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1075821 / 40000000) ≤ -Real.log (243365734599 / 250000000000) ∧
    -Real.log (243365734599 / 250000000000) ≤ (13447763 / 500000000) := by
  have h := checkLog_sound (w := (6634265401 / 493365734599)) (n := 12)
    (lo := (1075821 / 40000000)) (hi := (13447763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243365734599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243365734599) = 1/(243365734599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-13447763 / 500000000) (-1075821 / 40000000) (Real.log (243365734599 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell119

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell120Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell120
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (278312139 / 1000000000) ≤ -Real.log (5120 / 6763) ∧
    -Real.log (5120 / 6763) ≤ (13915607 / 50000000) := by
  have h := checkLog_sound (w := (1643 / 11883)) (n := 12)
    (lo := (278312139 / 1000000000)) (hi := (13915607 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6763 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6763 / 5120) = 1/(5120 / 6763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (278312139 / 1000000000) (13915607 / 50000000) (Real.log (6763 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6763 / 5120) = -Real.log (5120 / 6763) := by
    rw [show ((6763 / 5120) : ℝ) = ((5120 / 6763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (193492293 / 500000000) ≤ -Real.log (3477 / 5120) ∧
    -Real.log (3477 / 5120) ≤ (386984587 / 1000000000) := by
  have h := checkLog_sound (w := (1643 / 8597)) (n := 12)
    (lo := (193492293 / 500000000)) (hi := (386984587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3477) = 1/(3477 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-386984587 / 1000000000) (-193492293 / 500000000) (Real.log (3477 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (277868451 / 1000000000) ≤ -Real.log (128 / 169) ∧
    -Real.log (128 / 169) ≤ (69467113 / 250000000) := by
  have h := checkLog_sound (w := (41 / 297)) (n := 12)
    (lo := (277868451 / 1000000000)) (hi := (69467113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169 / 128) = 1/(128 / 169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (277868451 / 1000000000) (69467113 / 250000000) (Real.log (169 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (169 / 128) = -Real.log (128 / 169) := by
    rw [show ((169 / 128) : ℝ) = ((128 / 169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (77224429 / 200000000) ≤ -Real.log (87 / 128) ∧
    -Real.log (87 / 128) ≤ (193061073 / 500000000) := by
  have h := checkLog_sound (w := (41 / 215)) (n := 12)
    (lo := (77224429 / 200000000)) (hi := (193061073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 87) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 87) = 1/(87 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-193061073 / 500000000) (-77224429 / 200000000) (Real.log (87 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (51246117 / 250000000) ≤ -Real.log (500000 / 613753) ∧
    -Real.log (500000 / 613753) ≤ (204984469 / 1000000000) := by
  have h := checkLog_sound (w := (113753 / 1113753)) (n := 12)
    (lo := (51246117 / 250000000)) (hi := (204984469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613753 / 500000) = 1/(500000 / 613753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (51246117 / 250000000) (204984469 / 1000000000) (Real.log (613753 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613753 / 500000) = -Real.log (500000 / 613753) := by
    rw [show ((613753 / 500000) : ℝ) = ((500000 / 613753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (258131037 / 1000000000) ≤ -Real.log (386247 / 500000) ∧
    -Real.log (386247 / 500000) ≤ (129065519 / 500000000) := by
  have h := checkLog_sound (w := (113753 / 886247)) (n := 12)
    (lo := (258131037 / 1000000000)) (hi := (129065519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386247) = 1/(386247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-129065519 / 500000000) (-258131037 / 1000000000) (Real.log (386247 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (205327381 / 1000000000) ≤ -Real.log (1000000 / 1227927) ∧
    -Real.log (1000000 / 1227927) ≤ (102663691 / 500000000) := by
  have h := checkLog_sound (w := (227927 / 2227927)) (n := 12)
    (lo := (205327381 / 1000000000)) (hi := (102663691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227927 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227927 / 1000000) = 1/(1000000 / 1227927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (205327381 / 1000000000) (102663691 / 500000000) (Real.log (1227927 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1227927 / 1000000) = -Real.log (1000000 / 1227927) := by
    rw [show ((1227927 / 1000000) : ℝ) = ((1000000 / 1227927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (258676173 / 1000000000) ≤ -Real.log (772073 / 1000000) ∧
    -Real.log (772073 / 1000000) ≤ (129338087 / 500000000) := by
  have h := checkLog_sound (w := (227927 / 1772073)) (n := 12)
    (lo := (258676173 / 1000000000)) (hi := (129338087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772073) = 1/(772073 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-129338087 / 500000000) (-258676173 / 1000000000) (Real.log (772073 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18898143 / 125000000) ≤ -Real.log (250000 / 290803) ∧
    -Real.log (250000 / 290803) ≤ (30237029 / 200000000) := by
  have h := checkLog_sound (w := (40803 / 540803)) (n := 12)
    (lo := (18898143 / 125000000)) (hi := (30237029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290803 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290803 / 250000) = 1/(250000 / 290803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18898143 / 125000000) (30237029 / 200000000) (Real.log (290803 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (290803 / 250000) = -Real.log (250000 / 290803) := by
    rw [show ((290803 / 250000) : ℝ) = ((250000 / 290803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89092263 / 500000000) ≤ -Real.log (209197 / 250000) ∧
    -Real.log (209197 / 250000) ≤ (178184527 / 1000000000) := by
  have h := checkLog_sound (w := (40803 / 459197)) (n := 12)
    (lo := (89092263 / 500000000)) (hi := (178184527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 209197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 209197) = 1/(209197 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-178184527 / 1000000000) (-89092263 / 500000000) (Real.log (209197 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (151452471 / 1000000000) ≤ -Real.log (1000000 / 1163523) ∧
    -Real.log (1000000 / 1163523) ≤ (18931559 / 125000000) := by
  have h := checkLog_sound (w := (163523 / 2163523)) (n := 12)
    (lo := (151452471 / 1000000000)) (hi := (18931559 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163523 / 1000000) = 1/(1000000 / 1163523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (151452471 / 1000000000) (18931559 / 125000000) (Real.log (1163523 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1163523 / 1000000) = -Real.log (1000000 / 1163523) := by
    rw [show ((1163523 / 1000000) : ℝ) = ((1000000 / 1163523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (89278127 / 500000000) ≤ -Real.log (836477 / 1000000) ∧
    -Real.log (836477 / 1000000) ≤ (35711251 / 200000000) := by
  have h := checkLog_sound (w := (163523 / 1836477)) (n := 12)
    (lo := (89278127 / 500000000)) (hi := (35711251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 836477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 836477) = 1/(836477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-35711251 / 200000000) (-89278127 / 500000000) (Real.log (836477 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (165997649 / 250000000) ≤ -Real.log (62500000000 / 121408045977) ∧
    -Real.log (62500000000 / 121408045977) ≤ (663990597 / 1000000000) := by
  have h := checkLog_sound (w := (58908045977 / 183908045977)) (n := 12)
    (lo := (165997649 / 250000000)) (hi := (663990597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121408045977 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121408045977 / 62500000000) = 1/(62500000000 / 121408045977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (165997649 / 250000000) (663990597 / 1000000000) (Real.log (121408045977 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (121408045977 / 62500000000) = -Real.log (62500000000 / 121408045977) := by
    rw [show ((121408045977 / 62500000000) : ℝ) = ((62500000000 / 121408045977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (26611869 / 40000000) ≤ -Real.log (500000000000 / 972533793501) ∧
    -Real.log (500000000000 / 972533793501) ≤ (332648363 / 500000000) := by
  have h := checkLog_sound (w := (472533793501 / 1472533793501)) (n := 12)
    (lo := (26611869 / 40000000)) (hi := (332648363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972533793501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972533793501 / 500000000000) = 1/(500000000000 / 972533793501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (26611869 / 40000000) (332648363 / 500000000) (Real.log (972533793501 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (972533793501 / 500000000000) = -Real.log (500000000000 / 972533793501) := by
    rw [show ((972533793501 / 500000000000) : ℝ) = ((500000000000 / 972533793501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (92623101 / 200000000) ≤ -Real.log (500000000000 / 794508436311) ∧
    -Real.log (500000000000 / 794508436311) ≤ (231557753 / 500000000) := by
  have h := checkLog_sound (w := (294508436311 / 1294508436311)) (n := 12)
    (lo := (92623101 / 200000000)) (hi := (231557753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794508436311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794508436311 / 500000000000) = 1/(500000000000 / 794508436311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (92623101 / 200000000) (231557753 / 500000000) (Real.log (794508436311 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (794508436311 / 500000000000) = -Real.log (500000000000 / 794508436311) := by
    rw [show ((794508436311 / 500000000000) : ℝ) = ((500000000000 / 794508436311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (92800711 / 200000000) ≤ -Real.log (500000000000 / 795214312637) ∧
    -Real.log (500000000000 / 795214312637) ≤ (116000889 / 250000000) := by
  have h := checkLog_sound (w := (295214312637 / 1295214312637)) (n := 12)
    (lo := (92800711 / 200000000)) (hi := (116000889 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795214312637 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795214312637 / 500000000000) = 1/(500000000000 / 795214312637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (92800711 / 200000000) (116000889 / 250000000) (Real.log (795214312637 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (795214312637 / 500000000000) = -Real.log (500000000000 / 795214312637) := by
    rw [show ((795214312637 / 500000000000) : ℝ) = ((500000000000 / 795214312637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (32936967 / 100000000) ≤ -Real.log (62500000000 / 86880727257) ∧
    -Real.log (62500000000 / 86880727257) ≤ (329369671 / 1000000000) := by
  have h := checkLog_sound (w := (24380727257 / 149380727257)) (n := 12)
    (lo := (32936967 / 100000000)) (hi := (329369671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86880727257 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86880727257 / 62500000000) = 1/(62500000000 / 86880727257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (32936967 / 100000000) (329369671 / 1000000000) (Real.log (86880727257 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (86880727257 / 62500000000) = -Real.log (62500000000 / 86880727257) := by
    rw [show ((86880727257 / 62500000000) : ℝ) = ((62500000000 / 86880727257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (13200349 / 40000000) ≤ -Real.log (500000000000 / 695490133023) ∧
    -Real.log (500000000000 / 695490133023) ≤ (165004363 / 500000000) := by
  have h := checkLog_sound (w := (195490133023 / 1195490133023)) (n := 12)
    (lo := (13200349 / 40000000)) (hi := (165004363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695490133023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695490133023 / 500000000000) = 1/(500000000000 / 695490133023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (13200349 / 40000000) (165004363 / 500000000) (Real.log (695490133023 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (695490133023 / 500000000000) = -Real.log (500000000000 / 695490133023) := by
    rw [show ((695490133023 / 500000000000) : ℝ) = ((500000000000 / 695490133023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (13551891 / 500000000) ≤ -Real.log (973260228471 / 1000000000000) ∧
    -Real.log (973260228471 / 1000000000000) ≤ (27103783 / 1000000000) := by
  have h := checkLog_sound (w := (26739771529 / 1973260228471)) (n := 12)
    (lo := (13551891 / 500000000)) (hi := (27103783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973260228471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973260228471) = 1/(973260228471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-27103783 / 1000000000) (-13551891 / 500000000) (Real.log (973260228471 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (13499691 / 500000000) ≤ -Real.log (60835115191 / 62500000000) ∧
    -Real.log (60835115191 / 62500000000) ≤ (26999383 / 1000000000) := by
  have h := checkLog_sound (w := (1664884809 / 123335115191)) (n := 12)
    (lo := (13499691 / 500000000)) (hi := (26999383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60835115191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60835115191) = 1/(60835115191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26999383 / 1000000000) (-13499691 / 500000000) (Real.log (60835115191 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell120

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell121Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell121
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (278755631 / 1000000000) ≤ -Real.log (2560 / 3383) ∧
    -Real.log (2560 / 3383) ≤ (17422227 / 62500000) := by
  have h := checkLog_sound (w := (823 / 5943)) (n := 12)
    (lo := (278755631 / 1000000000)) (hi := (17422227 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3383 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3383 / 2560) = 1/(2560 / 3383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (278755631 / 1000000000) (17422227 / 62500000) (Real.log (3383 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3383 / 2560) = -Real.log (2560 / 3383) := by
    rw [show ((3383 / 2560) : ℝ) = ((2560 / 3383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (387847771 / 1000000000) ≤ -Real.log (1737 / 2560) ∧
    -Real.log (1737 / 2560) ≤ (96961943 / 250000000) := by
  have h := checkLog_sound (w := (823 / 4297)) (n := 12)
    (lo := (387847771 / 1000000000)) (hi := (96961943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1737) = 1/(1737 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-96961943 / 250000000) (-387847771 / 1000000000) (Real.log (1737 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (278312139 / 1000000000) ≤ -Real.log (5120 / 6763) ∧
    -Real.log (5120 / 6763) ≤ (13915607 / 50000000) := by
  have h := checkLog_sound (w := (1643 / 11883)) (n := 12)
    (lo := (278312139 / 1000000000)) (hi := (13915607 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6763 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6763 / 5120) = 1/(5120 / 6763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (278312139 / 1000000000) (13915607 / 50000000) (Real.log (6763 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6763 / 5120) = -Real.log (5120 / 6763) := by
    rw [show ((6763 / 5120) : ℝ) = ((5120 / 6763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (193492293 / 500000000) ≤ -Real.log (3477 / 5120) ∧
    -Real.log (3477 / 5120) ≤ (386984587 / 1000000000) := by
  have h := checkLog_sound (w := (1643 / 8597)) (n := 12)
    (lo := (193492293 / 500000000)) (hi := (386984587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3477) = 1/(3477 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-386984587 / 1000000000) (-193492293 / 500000000) (Real.log (3477 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (205326567 / 1000000000) ≤ -Real.log (500000 / 613963) ∧
    -Real.log (500000 / 613963) ≤ (25665821 / 125000000) := by
  have h := checkLog_sound (w := (113963 / 1113963)) (n := 12)
    (lo := (205326567 / 1000000000)) (hi := (25665821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613963 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613963 / 500000) = 1/(500000 / 613963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (205326567 / 1000000000) (25665821 / 125000000) (Real.log (613963 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613963 / 500000) = -Real.log (500000 / 613963) := by
    rw [show ((613963 / 500000) : ℝ) = ((500000 / 613963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (129337439 / 500000000) ≤ -Real.log (386037 / 500000) ∧
    -Real.log (386037 / 500000) ≤ (258674879 / 1000000000) := by
  have h := checkLog_sound (w := (113963 / 886037)) (n := 12)
    (lo := (129337439 / 500000000)) (hi := (258674879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386037) = 1/(386037 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-258674879 / 1000000000) (-129337439 / 500000000) (Real.log (386037 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (205670177 / 1000000000) ≤ -Real.log (250000 / 307087) ∧
    -Real.log (250000 / 307087) ≤ (102835089 / 500000000) := by
  have h := checkLog_sound (w := (57087 / 557087)) (n := 12)
    (lo := (205670177 / 1000000000)) (hi := (102835089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307087 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307087 / 250000) = 1/(250000 / 307087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (205670177 / 1000000000) (102835089 / 500000000) (Real.log (307087 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (307087 / 250000) = -Real.log (250000 / 307087) := by
    rw [show ((307087 / 250000) : ℝ) = ((250000 / 307087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (259221607 / 1000000000) ≤ -Real.log (192913 / 250000) ∧
    -Real.log (192913 / 250000) ≤ (32402701 / 125000000) := by
  have h := checkLog_sound (w := (57087 / 442913)) (n := 12)
    (lo := (259221607 / 1000000000)) (hi := (32402701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192913) = 1/(192913 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-32402701 / 125000000) (-259221607 / 1000000000) (Real.log (192913 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (37862903 / 250000000) ≤ -Real.log (500000 / 581761) ∧
    -Real.log (500000 / 581761) ≤ (151451613 / 1000000000) := by
  have h := checkLog_sound (w := (81761 / 1081761)) (n := 12)
    (lo := (37862903 / 250000000)) (hi := (151451613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581761 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581761 / 500000) = 1/(500000 / 581761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (37862903 / 250000000) (151451613 / 1000000000) (Real.log (581761 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (581761 / 500000) = -Real.log (500000 / 581761) := by
    rw [show ((581761 / 500000) : ℝ) = ((500000 / 581761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89277529 / 500000000) ≤ -Real.log (418239 / 500000) ∧
    -Real.log (418239 / 500000) ≤ (178555059 / 1000000000) := by
  have h := checkLog_sound (w := (81761 / 918239)) (n := 12)
    (lo := (89277529 / 500000000)) (hi := (178555059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418239) = 1/(418239 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-178555059 / 1000000000) (-89277529 / 500000000) (Real.log (418239 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37929717 / 250000000) ≤ -Real.log (1000000 / 1163833) ∧
    -Real.log (1000000 / 1163833) ≤ (151718869 / 1000000000) := by
  have h := checkLog_sound (w := (163833 / 2163833)) (n := 12)
    (lo := (37929717 / 250000000)) (hi := (151718869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163833 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163833 / 1000000) = 1/(1000000 / 1163833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37929717 / 250000000) (151718869 / 1000000000) (Real.log (1163833 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1163833 / 1000000) = -Real.log (1000000 / 1163833) := by
    rw [show ((1163833 / 1000000) : ℝ) = ((1000000 / 1163833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7157077 / 40000000) ≤ -Real.log (836167 / 1000000) ∧
    -Real.log (836167 / 1000000) ≤ (89463463 / 500000000) := by
  have h := checkLog_sound (w := (163833 / 1836167)) (n := 12)
    (lo := (7157077 / 40000000)) (hi := (89463463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 836167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 836167) = 1/(836167 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89463463 / 500000000) (-7157077 / 40000000) (Real.log (836167 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26611869 / 40000000) ≤ -Real.log (1000000000 / 1945067587) ∧
    -Real.log (1000000000 / 1945067587) ≤ (332648363 / 500000000) := by
  have h := checkLog_sound (w := (945067587 / 2945067587)) (n := 12)
    (lo := (26611869 / 40000000)) (hi := (332648363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1945067587 / 1000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1945067587 / 1000000000) = 1/(1000000000 / 1945067587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26611869 / 40000000) (332648363 / 500000000) (Real.log (1945067587 / 1000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1945067587 / 1000000000) = -Real.log (1000000000 / 1945067587) := by
    rw [show ((1945067587 / 1000000000) : ℝ) = ((1000000000 / 1945067587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (333301701 / 500000000) ≤ -Real.log (50000000000 / 97380541163) ∧
    -Real.log (50000000000 / 97380541163) ≤ (666603403 / 1000000000) := by
  have h := checkLog_sound (w := (47380541163 / 147380541163)) (n := 12)
    (lo := (333301701 / 500000000)) (hi := (666603403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97380541163 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97380541163 / 50000000000) = 1/(50000000000 / 97380541163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (333301701 / 500000000) (666603403 / 1000000000) (Real.log (97380541163 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (97380541163 / 50000000000) = -Real.log (50000000000 / 97380541163) := by
    rw [show ((97380541163 / 50000000000) : ℝ) = ((50000000000 / 97380541163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (92800289 / 200000000) ≤ -Real.log (250000000000 / 397606317529) ∧
    -Real.log (250000000000 / 397606317529) ≤ (232000723 / 500000000) := by
  have h := checkLog_sound (w := (147606317529 / 647606317529)) (n := 12)
    (lo := (92800289 / 200000000)) (hi := (232000723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397606317529 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397606317529 / 250000000000) = 1/(250000000000 / 397606317529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (92800289 / 200000000) (232000723 / 500000000) (Real.log (397606317529 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (397606317529 / 250000000000) = -Real.log (250000000000 / 397606317529) := by
    rw [show ((397606317529 / 250000000000) : ℝ) = ((250000000000 / 397606317529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (58111473 / 125000000) ≤ -Real.log (500000000000 / 795920959189) ∧
    -Real.log (500000000000 / 795920959189) ≤ (92978357 / 200000000) := by
  have h := checkLog_sound (w := (295920959189 / 1295920959189)) (n := 12)
    (lo := (58111473 / 125000000)) (hi := (92978357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795920959189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795920959189 / 500000000000) = 1/(500000000000 / 795920959189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (58111473 / 125000000) (92978357 / 200000000) (Real.log (795920959189 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (795920959189 / 500000000000) = -Real.log (500000000000 / 795920959189) := by
    rw [show ((795920959189 / 500000000000) : ℝ) = ((500000000000 / 795920959189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (330006671 / 1000000000) ≤ -Real.log (500000000000 / 695488703827) ∧
    -Real.log (500000000000 / 695488703827) ≤ (20625417 / 62500000) := by
  have h := checkLog_sound (w := (195488703827 / 1195488703827)) (n := 12)
    (lo := (330006671 / 1000000000)) (hi := (20625417 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695488703827 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695488703827 / 500000000000) = 1/(500000000000 / 695488703827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (330006671 / 1000000000) (20625417 / 62500000) (Real.log (695488703827 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (695488703827 / 500000000000) = -Real.log (500000000000 / 695488703827) := by
    rw [show ((695488703827 / 500000000000) : ℝ) = ((500000000000 / 695488703827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (330645793 / 1000000000) ≤ -Real.log (500000000000 / 695933348243) ∧
    -Real.log (500000000000 / 695933348243) ≤ (165322897 / 500000000) := by
  have h := checkLog_sound (w := (195933348243 / 1195933348243)) (n := 12)
    (lo := (330645793 / 1000000000)) (hi := (165322897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695933348243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695933348243 / 500000000000) = 1/(500000000000 / 695933348243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (330645793 / 1000000000) (165322897 / 500000000) (Real.log (695933348243 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (695933348243 / 500000000000) = -Real.log (500000000000 / 695933348243) := by
    rw [show ((695933348243 / 500000000000) : ℝ) = ((500000000000 / 695933348243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3401007 / 125000000) ≤ -Real.log (973158748111 / 1000000000000) ∧
    -Real.log (973158748111 / 1000000000000) ≤ (27208057 / 1000000000) := by
  have h := checkLog_sound (w := (26841251889 / 1973158748111)) (n := 12)
    (lo := (3401007 / 125000000)) (hi := (27208057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973158748111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973158748111) = 1/(973158748111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-27208057 / 1000000000) (-3401007 / 125000000) (Real.log (973158748111 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (13551723 / 500000000) ≤ -Real.log (243315138879 / 250000000000) ∧
    -Real.log (243315138879 / 250000000000) ≤ (27103447 / 1000000000) := by
  have h := checkLog_sound (w := (6684861121 / 493315138879)) (n := 12)
    (lo := (13551723 / 500000000)) (hi := (27103447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243315138879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243315138879) = 1/(243315138879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-27103447 / 1000000000) (-13551723 / 500000000) (Real.log (243315138879 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell121

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell122Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell122
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (139599463 / 500000000) ≤ -Real.log (5120 / 6769) ∧
    -Real.log (5120 / 6769) ≤ (279198927 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 11889)) (n := 12)
    (lo := (139599463 / 500000000)) (hi := (279198927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6769 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6769 / 5120) = 1/(5120 / 6769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (139599463 / 500000000) (279198927 / 1000000000) (Real.log (6769 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6769 / 5120) = -Real.log (5120 / 6769) := by
    rw [show ((6769 / 5120) : ℝ) = ((5120 / 6769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (194355851 / 500000000) ≤ -Real.log (3471 / 5120) ∧
    -Real.log (3471 / 5120) ≤ (388711703 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 8591)) (n := 12)
    (lo := (194355851 / 500000000)) (hi := (388711703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3471) = 1/(3471 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-388711703 / 1000000000) (-194355851 / 500000000) (Real.log (3471 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (278755631 / 1000000000) ≤ -Real.log (2560 / 3383) ∧
    -Real.log (2560 / 3383) ≤ (17422227 / 62500000) := by
  have h := checkLog_sound (w := (823 / 5943)) (n := 12)
    (lo := (278755631 / 1000000000)) (hi := (17422227 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3383 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3383 / 2560) = 1/(2560 / 3383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (278755631 / 1000000000) (17422227 / 62500000) (Real.log (3383 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3383 / 2560) = -Real.log (2560 / 3383) := by
    rw [show ((3383 / 2560) : ℝ) = ((2560 / 3383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (387847771 / 1000000000) ≤ -Real.log (1737 / 2560) ∧
    -Real.log (1737 / 2560) ≤ (96961943 / 250000000) := by
  have h := checkLog_sound (w := (823 / 4297)) (n := 12)
    (lo := (387847771 / 1000000000)) (hi := (96961943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1737) = 1/(1737 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-96961943 / 250000000) (-387847771 / 1000000000) (Real.log (1737 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (205669363 / 1000000000) ≤ -Real.log (1000000 / 1228347) ∧
    -Real.log (1000000 / 1228347) ≤ (51417341 / 250000000) := by
  have h := checkLog_sound (w := (228347 / 2228347)) (n := 12)
    (lo := (205669363 / 1000000000)) (hi := (51417341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228347 / 1000000) = 1/(1000000 / 1228347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (205669363 / 1000000000) (51417341 / 250000000) (Real.log (1228347 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1228347 / 1000000) = -Real.log (1000000 / 1228347) := by
    rw [show ((1228347 / 1000000) : ℝ) = ((1000000 / 1228347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (259220311 / 1000000000) ≤ -Real.log (771653 / 1000000) ∧
    -Real.log (771653 / 1000000) ≤ (32402539 / 125000000) := by
  have h := checkLog_sound (w := (228347 / 1771653)) (n := 12)
    (lo := (259220311 / 1000000000)) (hi := (32402539 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 771653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 771653) = 1/(771653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-32402539 / 125000000) (-259220311 / 1000000000) (Real.log (771653 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (206012041 / 1000000000) ≤ -Real.log (31250 / 38399) ∧
    -Real.log (31250 / 38399) ≤ (103006021 / 500000000) := by
  have h := checkLog_sound (w := (7149 / 69649)) (n := 12)
    (lo := (206012041 / 1000000000)) (hi := (103006021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38399 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38399 / 31250) = 1/(31250 / 38399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (206012041 / 1000000000) (103006021 / 500000000) (Real.log (38399 / 31250)) := by
  have h := reflection_log_7_neg
  have he : Real.log (38399 / 31250) = -Real.log (31250 / 38399) := by
    rw [show ((38399 / 31250) : ℝ) = ((31250 / 38399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (129883021 / 500000000) ≤ -Real.log (24101 / 31250) ∧
    -Real.log (24101 / 31250) ≤ (259766043 / 1000000000) := by
  have h := checkLog_sound (w := (7149 / 55351)) (n := 12)
    (lo := (129883021 / 500000000)) (hi := (259766043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24101) = 1/(24101 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-259766043 / 1000000000) (-129883021 / 500000000) (Real.log (24101 / 31250)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18964751 / 125000000) ≤ -Real.log (125000 / 145479) ∧
    -Real.log (125000 / 145479) ≤ (151718009 / 1000000000) := by
  have h := checkLog_sound (w := (20479 / 270479)) (n := 12)
    (lo := (18964751 / 125000000)) (hi := (151718009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145479 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145479 / 125000) = 1/(125000 / 145479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18964751 / 125000000) (151718009 / 1000000000) (Real.log (145479 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (145479 / 125000) = -Real.log (125000 / 145479) := by
    rw [show ((145479 / 125000) : ℝ) = ((125000 / 145479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (178925729 / 1000000000) ≤ -Real.log (104521 / 125000) ∧
    -Real.log (104521 / 125000) ≤ (17892573 / 100000000) := by
  have h := checkLog_sound (w := (20479 / 229521)) (n := 12)
    (lo := (178925729 / 1000000000)) (hi := (17892573 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104521) = 1/(104521 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-17892573 / 100000000) (-178925729 / 1000000000) (Real.log (104521 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37996513 / 250000000) ≤ -Real.log (62500 / 72759) ∧
    -Real.log (62500 / 72759) ≤ (151986053 / 1000000000) := by
  have h := checkLog_sound (w := (10259 / 135259)) (n := 12)
    (lo := (37996513 / 250000000)) (hi := (151986053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72759 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72759 / 62500) = 1/(62500 / 72759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37996513 / 250000000) (151986053 / 1000000000) (Real.log (72759 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (72759 / 62500) = -Real.log (62500 / 72759) := by
    rw [show ((72759 / 62500) : ℝ) = ((62500 / 72759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (179298929 / 1000000000) ≤ -Real.log (52241 / 62500) ∧
    -Real.log (52241 / 62500) ≤ (17929893 / 100000000) := by
  have h := checkLog_sound (w := (10259 / 114741)) (n := 12)
    (lo := (179298929 / 1000000000)) (hi := (17929893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 52241) = 1/(52241 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-17929893 / 100000000) (-179298929 / 1000000000) (Real.log (52241 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (333301701 / 500000000) ≤ -Real.log (500000000000 / 973805411629) ∧
    -Real.log (500000000000 / 973805411629) ≤ (666603403 / 1000000000) := by
  have h := checkLog_sound (w := (473805411629 / 1473805411629)) (n := 12)
    (lo := (333301701 / 500000000)) (hi := (666603403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973805411629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973805411629 / 500000000000) = 1/(500000000000 / 973805411629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (333301701 / 500000000) (666603403 / 1000000000) (Real.log (973805411629 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (973805411629 / 500000000000) = -Real.log (500000000000 / 973805411629) := by
    rw [show ((973805411629 / 500000000000) : ℝ) = ((500000000000 / 973805411629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (166977657 / 250000000) ≤ -Real.log (500000000000 / 975079227889) ∧
    -Real.log (500000000000 / 975079227889) ≤ (667910629 / 1000000000) := by
  have h := checkLog_sound (w := (475079227889 / 1475079227889)) (n := 12)
    (lo := (166977657 / 250000000)) (hi := (667910629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((975079227889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(975079227889 / 500000000000) = 1/(500000000000 / 975079227889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (166977657 / 250000000) (667910629 / 1000000000) (Real.log (975079227889 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (975079227889 / 500000000000) = -Real.log (500000000000 / 975079227889) := by
    rw [show ((975079227889 / 500000000000) : ℝ) = ((500000000000 / 975079227889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (232444837 / 500000000) ≤ -Real.log (500000000000 / 795919279779) ∧
    -Real.log (500000000000 / 795919279779) ≤ (18595587 / 40000000) := by
  have h := checkLog_sound (w := (295919279779 / 1295919279779)) (n := 12)
    (lo := (232444837 / 500000000)) (hi := (18595587 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795919279779 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795919279779 / 500000000000) = 1/(500000000000 / 795919279779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (232444837 / 500000000) (18595587 / 40000000) (Real.log (795919279779 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (795919279779 / 500000000000) = -Real.log (500000000000 / 795919279779) := by
    rw [show ((795919279779 / 500000000000) : ℝ) = ((500000000000 / 795919279779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (116444521 / 250000000) ≤ -Real.log (125000000000 / 199156673997) ∧
    -Real.log (125000000000 / 199156673997) ≤ (93155617 / 200000000) := by
  have h := checkLog_sound (w := (74156673997 / 324156673997)) (n := 12)
    (lo := (116444521 / 250000000)) (hi := (93155617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199156673997 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199156673997 / 125000000000) = 1/(125000000000 / 199156673997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (116444521 / 250000000) (93155617 / 200000000) (Real.log (199156673997 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (199156673997 / 125000000000) = -Real.log (125000000000 / 199156673997) := by
    rw [show ((199156673997 / 125000000000) : ℝ) = ((125000000000 / 199156673997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (165321869 / 500000000) ≤ -Real.log (500000000000 / 695931917987) ∧
    -Real.log (500000000000 / 695931917987) ≤ (330643739 / 1000000000) := by
  have h := checkLog_sound (w := (195931917987 / 1195931917987)) (n := 12)
    (lo := (165321869 / 500000000)) (hi := (330643739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695931917987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695931917987 / 500000000000) = 1/(500000000000 / 695931917987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (165321869 / 500000000) (330643739 / 1000000000) (Real.log (695931917987 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (695931917987 / 500000000000) = -Real.log (500000000000 / 695931917987) := by
    rw [show ((695931917987 / 500000000000) : ℝ) = ((500000000000 / 695931917987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (165642491 / 500000000) ≤ -Real.log (500000000000 / 696378323539) ∧
    -Real.log (500000000000 / 696378323539) ≤ (331284983 / 1000000000) := by
  have h := checkLog_sound (w := (196378323539 / 1196378323539)) (n := 12)
    (lo := (165642491 / 500000000)) (hi := (331284983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696378323539 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696378323539 / 500000000000) = 1/(500000000000 / 696378323539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (165642491 / 500000000) (331284983 / 1000000000) (Real.log (696378323539 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (696378323539 / 500000000000) = -Real.log (500000000000 / 696378323539) := by
    rw [show ((696378323539 / 500000000000) : ℝ) = ((500000000000 / 696378323539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6828219 / 250000000) ≤ -Real.log (3801002919 / 3906250000) ∧
    -Real.log (3801002919 / 3906250000) ≤ (27312877 / 1000000000) := by
  have h := checkLog_sound (w := (105247081 / 7707252919)) (n := 12)
    (lo := (6828219 / 250000000)) (hi := (27312877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3801002919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3801002919) = 1/(3801002919 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-27312877 / 1000000000) (-6828219 / 250000000) (Real.log (3801002919 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (680193 / 25000000) ≤ -Real.log (15205610559 / 15625000000) ∧
    -Real.log (15205610559 / 15625000000) ≤ (27207721 / 1000000000) := by
  have h := checkLog_sound (w := (419389441 / 30830610559)) (n := 12)
    (lo := (680193 / 25000000)) (hi := (27207721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15205610559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15205610559) = 1/(15205610559 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-27207721 / 1000000000) (-680193 / 25000000) (Real.log (15205610559 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell122

end


