-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell075Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell075Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T18:13:27.939344+00:00
-- url     : https://prove2.me/theorems/96e79ddd-fc6c-4a84-ad7f-85ff4c5afbf8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell075Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell076…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell075Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell076Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell077Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell078Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell079Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell080Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell081Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell075Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell076Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell077Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell078Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell079Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell080Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell081Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell075Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell076Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell077Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell078Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell079Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell080Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell081Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell075Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell076Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell077Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell078Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell079Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell080Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell081Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell075Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell075
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

theorem reflection_log_1_neg : (12907433 / 50000000) ≤ -Real.log (1280 / 1657) ∧
    -Real.log (1280 / 1657) ≤ (258148661 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 2937)) (n := 12)
    (lo := (12907433 / 50000000)) (hi := (258148661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1657 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1657 / 1280) = 1/(1280 / 1657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12907433 / 50000000) (258148661 / 1000000000) (Real.log (1657 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1657 / 1280) = -Real.log (1280 / 1657) := by
    rw [show ((1657 / 1280) : ℝ) = ((1280 / 1657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (348892803 / 1000000000) ≤ -Real.log (903 / 1280) ∧
    -Real.log (903 / 1280) ≤ (87223201 / 250000000) := by
  have h := checkLog_sound (w := (377 / 2183)) (n := 12)
    (lo := (348892803 / 1000000000)) (hi := (87223201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 903) = 1/(903 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-87223201 / 250000000) (-348892803 / 1000000000) (Real.log (903 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (64423983 / 250000000) ≤ -Real.log (1024 / 1325) ∧
    -Real.log (1024 / 1325) ≤ (257695933 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 2349)) (n := 12)
    (lo := (64423983 / 250000000)) (hi := (257695933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325 / 1024) = 1/(1024 / 1325) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (64423983 / 250000000) (257695933 / 1000000000) (Real.log (1325 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1325 / 1024) = -Real.log (1024 / 1325) := by
    rw [show ((1325 / 1024) : ℝ) = ((1024 / 1325) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (348062583 / 1000000000) ≤ -Real.log (723 / 1024) ∧
    -Real.log (723 / 1024) ≤ (43507823 / 125000000) := by
  have h := checkLog_sound (w := (301 / 1747)) (n := 12)
    (lo := (348062583 / 1000000000)) (hi := (43507823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 723) = 1/(723 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-43507823 / 125000000) (-348062583 / 1000000000) (Real.log (723 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (47371251 / 250000000) ≤ -Real.log (1000000 / 1208627) ∧
    -Real.log (1000000 / 1208627) ≤ (37897001 / 200000000) := by
  have h := checkLog_sound (w := (208627 / 2208627)) (n := 12)
    (lo := (47371251 / 250000000)) (hi := (37897001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208627 / 1000000) = 1/(1000000 / 1208627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (47371251 / 250000000) (37897001 / 200000000) (Real.log (1208627 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1208627 / 1000000) = -Real.log (1000000 / 1208627) := by
    rw [show ((1208627 / 1000000) : ℝ) = ((1000000 / 1208627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (233985867 / 1000000000) ≤ -Real.log (791373 / 1000000) ∧
    -Real.log (791373 / 1000000) ≤ (58496467 / 250000000) := by
  have h := checkLog_sound (w := (208627 / 1791373)) (n := 12)
    (lo := (233985867 / 1000000000)) (hi := (58496467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791373) = 1/(791373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-58496467 / 250000000) (-233985867 / 1000000000) (Real.log (791373 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (37966489 / 200000000) ≤ -Real.log (1000000 / 1209047) ∧
    -Real.log (1000000 / 1209047) ≤ (94916223 / 500000000) := by
  have h := checkLog_sound (w := (209047 / 2209047)) (n := 12)
    (lo := (37966489 / 200000000)) (hi := (94916223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209047 / 1000000) = 1/(1000000 / 1209047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (37966489 / 200000000) (94916223 / 500000000) (Real.log (1209047 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1209047 / 1000000) = -Real.log (1000000 / 1209047) := by
    rw [show ((1209047 / 1000000) : ℝ) = ((1000000 / 1209047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (234516731 / 1000000000) ≤ -Real.log (790953 / 1000000) ∧
    -Real.log (790953 / 1000000) ≤ (58629183 / 250000000) := by
  have h := checkLog_sound (w := (209047 / 1790953)) (n := 12)
    (lo := (234516731 / 1000000000)) (hi := (58629183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790953) = 1/(790953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-58629183 / 250000000) (-234516731 / 1000000000) (Real.log (790953 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139172203 / 1000000000) ≤ -Real.log (500000 / 574661) ∧
    -Real.log (500000 / 574661) ≤ (34793051 / 250000000) := by
  have h := checkLog_sound (w := (74661 / 1074661)) (n := 12)
    (lo := (139172203 / 1000000000)) (hi := (34793051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574661 / 500000) = 1/(500000 / 574661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139172203 / 1000000000) (34793051 / 250000000) (Real.log (574661 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (574661 / 500000) = -Real.log (500000 / 574661) := by
    rw [show ((574661 / 500000) : ℝ) = ((500000 / 574661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (25269 / 156250) ≤ -Real.log (425339 / 500000) ∧
    -Real.log (425339 / 500000) ≤ (161721601 / 1000000000) := by
  have h := checkLog_sound (w := (74661 / 925339)) (n := 12)
    (lo := (25269 / 156250)) (hi := (161721601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425339) = 1/(425339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-161721601 / 1000000000) (-25269 / 156250) (Real.log (425339 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (139441021 / 1000000000) ≤ -Real.log (1000000 / 1149631) ∧
    -Real.log (1000000 / 1149631) ≤ (69720511 / 500000000) := by
  have h := checkLog_sound (w := (149631 / 2149631)) (n := 12)
    (lo := (139441021 / 1000000000)) (hi := (69720511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1149631 / 1000000) = 1/(1000000 / 1149631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (139441021 / 1000000000) (69720511 / 500000000) (Real.log (1149631 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1149631 / 1000000) = -Real.log (1000000 / 1149631) := by
    rw [show ((1149631 / 1000000) : ℝ) = ((1000000 / 1149631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (81042453 / 500000000) ≤ -Real.log (850369 / 1000000) ∧
    -Real.log (850369 / 1000000) ≤ (162084907 / 1000000000) := by
  have h := checkLog_sound (w := (149631 / 1850369)) (n := 12)
    (lo := (81042453 / 500000000)) (hi := (162084907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 850369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 850369) = 1/(850369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-162084907 / 1000000000) (-81042453 / 500000000) (Real.log (850369 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (151439629 / 250000000) ≤ -Real.log (1250000000 / 2290802213) ∧
    -Real.log (1250000000 / 2290802213) ≤ (605758517 / 1000000000) := by
  have h := checkLog_sound (w := (1040802213 / 3540802213)) (n := 12)
    (lo := (151439629 / 250000000)) (hi := (605758517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2290802213 / 1250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2290802213 / 1250000000) = 1/(1250000000 / 2290802213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (151439629 / 250000000) (605758517 / 1000000000) (Real.log (2290802213 / 1250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (2290802213 / 1250000000) = -Real.log (1250000000 / 2290802213) := by
    rw [show ((2290802213 / 1250000000) : ℝ) = ((1250000000 / 2290802213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (75880183 / 125000000) ≤ -Real.log (500000000000 / 917497231451) ∧
    -Real.log (500000000000 / 917497231451) ≤ (121408293 / 200000000) := by
  have h := checkLog_sound (w := (417497231451 / 1417497231451)) (n := 12)
    (lo := (75880183 / 125000000)) (hi := (121408293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917497231451 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917497231451 / 500000000000) = 1/(500000000000 / 917497231451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (75880183 / 125000000) (121408293 / 200000000) (Real.log (917497231451 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (917497231451 / 500000000000) = -Real.log (500000000000 / 917497231451) := by
    rw [show ((917497231451 / 500000000000) : ℝ) = ((500000000000 / 917497231451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (423470871 / 1000000000) ≤ -Real.log (500000000000 / 763626633711) ∧
    -Real.log (500000000000 / 763626633711) ≤ (52933859 / 125000000) := by
  have h := checkLog_sound (w := (263626633711 / 1263626633711)) (n := 12)
    (lo := (423470871 / 1000000000)) (hi := (52933859 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((763626633711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(763626633711 / 500000000000) = 1/(500000000000 / 763626633711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (423470871 / 1000000000) (52933859 / 125000000) (Real.log (763626633711 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (763626633711 / 500000000000) = -Real.log (500000000000 / 763626633711) := by
    rw [show ((763626633711 / 500000000000) : ℝ) = ((500000000000 / 763626633711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (424349177 / 1000000000) ≤ -Real.log (31250000000 / 47768601611) ∧
    -Real.log (31250000000 / 47768601611) ≤ (212174589 / 500000000) := by
  have h := checkLog_sound (w := (16518601611 / 79018601611)) (n := 12)
    (lo := (424349177 / 1000000000)) (hi := (212174589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47768601611 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47768601611 / 31250000000) = 1/(31250000000 / 47768601611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (424349177 / 1000000000) (212174589 / 500000000) (Real.log (47768601611 / 31250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (47768601611 / 31250000000) = -Real.log (31250000000 / 47768601611) := by
    rw [show ((47768601611 / 31250000000) : ℝ) = ((31250000000 / 47768601611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (300893803 / 1000000000) ≤ -Real.log (125000000000 / 168883231963) ∧
    -Real.log (125000000000 / 168883231963) ≤ (75223451 / 250000000) := by
  have h := checkLog_sound (w := (43883231963 / 293883231963)) (n := 12)
    (lo := (300893803 / 1000000000)) (hi := (75223451 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168883231963 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168883231963 / 125000000000) = 1/(125000000000 / 168883231963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (300893803 / 1000000000) (75223451 / 250000000) (Real.log (168883231963 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (168883231963 / 125000000000) = -Real.log (125000000000 / 168883231963) := by
    rw [show ((168883231963 / 125000000000) : ℝ) = ((125000000000 / 168883231963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (301525927 / 1000000000) ≤ -Real.log (500000000000 / 675960083211) ∧
    -Real.log (500000000000 / 675960083211) ≤ (37690741 / 125000000) := by
  have h := checkLog_sound (w := (175960083211 / 1175960083211)) (n := 12)
    (lo := (301525927 / 1000000000)) (hi := (37690741 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675960083211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675960083211 / 500000000000) = 1/(500000000000 / 675960083211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (301525927 / 1000000000) (37690741 / 125000000) (Real.log (675960083211 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (675960083211 / 500000000000) = -Real.log (500000000000 / 675960083211) := by
    rw [show ((675960083211 / 500000000000) : ℝ) = ((500000000000 / 675960083211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5660971 / 250000000) ≤ -Real.log (977610563839 / 1000000000000) ∧
    -Real.log (977610563839 / 1000000000000) ≤ (4528777 / 200000000) := by
  have h := checkLog_sound (w := (22389436161 / 1977610563839)) (n := 12)
    (lo := (5660971 / 250000000)) (hi := (4528777 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977610563839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977610563839) = 1/(977610563839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4528777 / 200000000) (-5660971 / 250000000) (Real.log (977610563839 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (22549397 / 1000000000) ≤ -Real.log (244425735079 / 250000000000) ∧
    -Real.log (244425735079 / 250000000000) ≤ (11274699 / 500000000) := by
  have h := checkLog_sound (w := (5574264921 / 494425735079)) (n := 12)
    (lo := (22549397 / 1000000000)) (hi := (11274699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244425735079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244425735079) = 1/(244425735079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-11274699 / 500000000) (-22549397 / 1000000000) (Real.log (244425735079 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell075

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell076Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell076
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

theorem reflection_log_1_neg : (258601183 / 1000000000) ≤ -Real.log (5120 / 6631) ∧
    -Real.log (5120 / 6631) ≤ (8081287 / 31250000) := by
  have h := checkLog_sound (w := (1511 / 11751)) (n := 12)
    (lo := (258601183 / 1000000000)) (hi := (8081287 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6631 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6631 / 5120) = 1/(5120 / 6631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (258601183 / 1000000000) (8081287 / 31250000) (Real.log (6631 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6631 / 5120) = -Real.log (5120 / 6631) := by
    rw [show ((6631 / 5120) : ℝ) = ((5120 / 6631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (349723713 / 1000000000) ≤ -Real.log (3609 / 5120) ∧
    -Real.log (3609 / 5120) ≤ (174861857 / 500000000) := by
  have h := checkLog_sound (w := (1511 / 8729)) (n := 12)
    (lo := (349723713 / 1000000000)) (hi := (174861857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3609) = 1/(3609 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-174861857 / 500000000) (-349723713 / 1000000000) (Real.log (3609 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12907433 / 50000000) ≤ -Real.log (1280 / 1657) ∧
    -Real.log (1280 / 1657) ≤ (258148661 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 2937)) (n := 12)
    (lo := (12907433 / 50000000)) (hi := (258148661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1657 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1657 / 1280) = 1/(1280 / 1657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12907433 / 50000000) (258148661 / 1000000000) (Real.log (1657 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1657 / 1280) = -Real.log (1280 / 1657) := by
    rw [show ((1657 / 1280) : ℝ) = ((1280 / 1657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (348892803 / 1000000000) ≤ -Real.log (903 / 1280) ∧
    -Real.log (903 / 1280) ≤ (87223201 / 250000000) := by
  have h := checkLog_sound (w := (377 / 2183)) (n := 12)
    (lo := (348892803 / 1000000000)) (hi := (87223201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 903) = 1/(903 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-87223201 / 250000000) (-348892803 / 1000000000) (Real.log (903 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (189830791 / 1000000000) ≤ -Real.log (200000 / 241809) ∧
    -Real.log (200000 / 241809) ≤ (23728849 / 125000000) := by
  have h := checkLog_sound (w := (41809 / 441809)) (n := 12)
    (lo := (189830791 / 1000000000)) (hi := (23728849 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241809 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241809 / 200000) = 1/(200000 / 241809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (189830791 / 1000000000) (23728849 / 125000000) (Real.log (241809 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (241809 / 200000) = -Real.log (200000 / 241809) := by
    rw [show ((241809 / 200000) : ℝ) = ((200000 / 241809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (117257101 / 500000000) ≤ -Real.log (158191 / 200000) ∧
    -Real.log (158191 / 200000) ≤ (234514203 / 1000000000) := by
  have h := checkLog_sound (w := (41809 / 358191)) (n := 12)
    (lo := (117257101 / 500000000)) (hi := (234514203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158191) = 1/(158191 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-234514203 / 1000000000) (-117257101 / 500000000) (Real.log (158191 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (190178939 / 1000000000) ≤ -Real.log (500000 / 604733) ∧
    -Real.log (500000 / 604733) ≤ (9508947 / 50000000) := by
  have h := checkLog_sound (w := (104733 / 1104733)) (n := 12)
    (lo := (190178939 / 1000000000)) (hi := (9508947 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604733 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604733 / 500000) = 1/(500000 / 604733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (190178939 / 1000000000) (9508947 / 50000000) (Real.log (604733 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (604733 / 500000) = -Real.log (500000 / 604733) := by
    rw [show ((604733 / 500000) : ℝ) = ((500000 / 604733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58761653 / 250000000) ≤ -Real.log (395267 / 500000) ∧
    -Real.log (395267 / 500000) ≤ (235046613 / 1000000000) := by
  have h := checkLog_sound (w := (104733 / 895267)) (n := 12)
    (lo := (58761653 / 250000000)) (hi := (235046613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 395267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 395267) = 1/(395267 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-235046613 / 1000000000) (-58761653 / 250000000) (Real.log (395267 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139440151 / 1000000000) ≤ -Real.log (100000 / 114963) ∧
    -Real.log (100000 / 114963) ≤ (17430019 / 125000000) := by
  have h := checkLog_sound (w := (14963 / 214963)) (n := 12)
    (lo := (139440151 / 1000000000)) (hi := (17430019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114963 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114963 / 100000) = 1/(100000 / 114963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139440151 / 1000000000) (17430019 / 125000000) (Real.log (114963 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (114963 / 100000) = -Real.log (100000 / 114963) := by
    rw [show ((114963 / 100000) : ℝ) = ((100000 / 114963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (16208373 / 100000000) ≤ -Real.log (85037 / 100000) ∧
    -Real.log (85037 / 100000) ≤ (162083731 / 1000000000) := by
  have h := checkLog_sound (w := (14963 / 185037)) (n := 12)
    (lo := (16208373 / 100000000)) (hi := (162083731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85037) = 1/(85037 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-162083731 / 1000000000) (-16208373 / 100000000) (Real.log (85037 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (139708027 / 1000000000) ≤ -Real.log (500000 / 574969) ∧
    -Real.log (500000 / 574969) ≤ (34927007 / 250000000) := by
  have h := checkLog_sound (w := (74969 / 1074969)) (n := 12)
    (lo := (139708027 / 1000000000)) (hi := (34927007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574969 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574969 / 500000) = 1/(500000 / 574969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (139708027 / 1000000000) (34927007 / 250000000) (Real.log (574969 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (574969 / 500000) = -Real.log (500000 / 574969) := by
    rw [show ((574969 / 500000) : ℝ) = ((500000 / 574969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (16244599 / 100000000) ≤ -Real.log (425031 / 500000) ∧
    -Real.log (425031 / 500000) ≤ (162445991 / 1000000000) := by
  have h := checkLog_sound (w := (74969 / 925031)) (n := 12)
    (lo := (16244599 / 100000000)) (hi := (162445991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425031) = 1/(425031 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-162445991 / 1000000000) (-16244599 / 100000000) (Real.log (425031 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (75880183 / 125000000) ≤ -Real.log (10000000000 / 18349944629) ∧
    -Real.log (10000000000 / 18349944629) ≤ (121408293 / 200000000) := by
  have h := checkLog_sound (w := (8349944629 / 28349944629)) (n := 12)
    (lo := (75880183 / 125000000)) (hi := (121408293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18349944629 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18349944629 / 10000000000) = 1/(10000000000 / 18349944629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (75880183 / 125000000) (121408293 / 200000000) (Real.log (18349944629 / 10000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (18349944629 / 10000000000) = -Real.log (10000000000 / 18349944629) := by
    rw [show ((18349944629 / 10000000000) : ℝ) = ((10000000000 / 18349944629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (19010153 / 31250000) ≤ -Real.log (500000000000 / 918675533389) ∧
    -Real.log (500000000000 / 918675533389) ≤ (608324897 / 1000000000) := by
  have h := checkLog_sound (w := (418675533389 / 1418675533389)) (n := 12)
    (lo := (19010153 / 31250000)) (hi := (608324897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918675533389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918675533389 / 500000000000) = 1/(500000000000 / 918675533389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (19010153 / 31250000) (608324897 / 1000000000) (Real.log (918675533389 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (918675533389 / 500000000000) = -Real.log (500000000000 / 918675533389) := by
    rw [show ((918675533389 / 500000000000) : ℝ) = ((500000000000 / 918675533389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (212172497 / 500000000) ≤ -Real.log (250000000000 / 382147214443) ∧
    -Real.log (250000000000 / 382147214443) ≤ (84868999 / 200000000) := by
  have h := checkLog_sound (w := (132147214443 / 632147214443)) (n := 12)
    (lo := (212172497 / 500000000)) (hi := (84868999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382147214443 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382147214443 / 250000000000) = 1/(250000000000 / 382147214443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (212172497 / 500000000) (84868999 / 200000000) (Real.log (382147214443 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (382147214443 / 250000000000) = -Real.log (250000000000 / 382147214443) := by
    rw [show ((382147214443 / 250000000000) : ℝ) = ((250000000000 / 382147214443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (26576597 / 62500000) ≤ -Real.log (250000000000 / 382483865337) ∧
    -Real.log (250000000000 / 382483865337) ≤ (425225553 / 1000000000) := by
  have h := checkLog_sound (w := (132483865337 / 632483865337)) (n := 12)
    (lo := (26576597 / 62500000)) (hi := (425225553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382483865337 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382483865337 / 250000000000) = 1/(250000000000 / 382483865337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (26576597 / 62500000) (425225553 / 1000000000) (Real.log (382483865337 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (382483865337 / 250000000000) = -Real.log (250000000000 / 382483865337) := by
    rw [show ((382483865337 / 250000000000) : ℝ) = ((250000000000 / 382483865337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (301523881 / 1000000000) ≤ -Real.log (50000000000 / 67595870033) ∧
    -Real.log (50000000000 / 67595870033) ≤ (150761941 / 500000000) := by
  have h := checkLog_sound (w := (17595870033 / 117595870033)) (n := 12)
    (lo := (301523881 / 1000000000)) (hi := (150761941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67595870033 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67595870033 / 50000000000) = 1/(50000000000 / 67595870033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (301523881 / 1000000000) (150761941 / 500000000) (Real.log (67595870033 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (67595870033 / 50000000000) = -Real.log (50000000000 / 67595870033) := by
    rw [show ((67595870033 / 50000000000) : ℝ) = ((50000000000 / 67595870033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (151077009 / 500000000) ≤ -Real.log (250000000000 / 338192390673) ∧
    -Real.log (250000000000 / 338192390673) ≤ (302154019 / 1000000000) := by
  have h := checkLog_sound (w := (88192390673 / 588192390673)) (n := 12)
    (lo := (151077009 / 500000000)) (hi := (302154019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338192390673 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338192390673 / 250000000000) = 1/(250000000000 / 338192390673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (151077009 / 500000000) (302154019 / 1000000000) (Real.log (338192390673 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (338192390673 / 250000000000) = -Real.log (250000000000 / 338192390673) := by
    rw [show ((338192390673 / 250000000000) : ℝ) = ((250000000000 / 338192390673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22737963 / 1000000000) ≤ -Real.log (244379649039 / 250000000000) ∧
    -Real.log (244379649039 / 250000000000) ≤ (5684491 / 250000000) := by
  have h := checkLog_sound (w := (5620350961 / 494379649039)) (n := 12)
    (lo := (22737963 / 1000000000)) (hi := (5684491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244379649039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244379649039) = 1/(244379649039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5684491 / 250000000) (-22737963 / 1000000000) (Real.log (244379649039 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (11321789 / 500000000) ≤ -Real.log (9776108631 / 10000000000) ∧
    -Real.log (9776108631 / 10000000000) ≤ (22643579 / 1000000000) := by
  have h := checkLog_sound (w := (223891369 / 19776108631)) (n := 12)
    (lo := (11321789 / 500000000)) (hi := (22643579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9776108631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9776108631) = 1/(9776108631 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22643579 / 1000000000) (-11321789 / 500000000) (Real.log (9776108631 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell076

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell077Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell077
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

theorem reflection_log_1_neg : (259053501 / 1000000000) ≤ -Real.log (2560 / 3317) ∧
    -Real.log (2560 / 3317) ≤ (129526751 / 500000000) := by
  have h := checkLog_sound (w := (757 / 5877)) (n := 12)
    (lo := (259053501 / 1000000000)) (hi := (129526751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3317 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3317 / 2560) = 1/(2560 / 3317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (259053501 / 1000000000) (129526751 / 500000000) (Real.log (3317 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3317 / 2560) = -Real.log (2560 / 3317) := by
    rw [show ((3317 / 2560) : ℝ) = ((2560 / 3317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (175277657 / 500000000) ≤ -Real.log (1803 / 2560) ∧
    -Real.log (1803 / 2560) ≤ (70111063 / 200000000) := by
  have h := checkLog_sound (w := (757 / 4363)) (n := 12)
    (lo := (175277657 / 500000000)) (hi := (70111063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1803) = 1/(1803 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-70111063 / 200000000) (-175277657 / 500000000) (Real.log (1803 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (258601183 / 1000000000) ≤ -Real.log (5120 / 6631) ∧
    -Real.log (5120 / 6631) ≤ (8081287 / 31250000) := by
  have h := checkLog_sound (w := (1511 / 11751)) (n := 12)
    (lo := (258601183 / 1000000000)) (hi := (8081287 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6631 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6631 / 5120) = 1/(5120 / 6631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (258601183 / 1000000000) (8081287 / 31250000) (Real.log (6631 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6631 / 5120) = -Real.log (5120 / 6631) := by
    rw [show ((6631 / 5120) : ℝ) = ((5120 / 6631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (349723713 / 1000000000) ≤ -Real.log (3609 / 5120) ∧
    -Real.log (3609 / 5120) ≤ (174861857 / 500000000) := by
  have h := checkLog_sound (w := (1511 / 8729)) (n := 12)
    (lo := (349723713 / 1000000000)) (hi := (174861857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3609) = 1/(3609 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-174861857 / 500000000) (-349723713 / 1000000000) (Real.log (3609 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (190178113 / 1000000000) ≤ -Real.log (200000 / 241893) ∧
    -Real.log (200000 / 241893) ≤ (95089057 / 500000000) := by
  have h := checkLog_sound (w := (41893 / 441893)) (n := 12)
    (lo := (190178113 / 1000000000)) (hi := (95089057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241893 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241893 / 200000) = 1/(200000 / 241893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (190178113 / 1000000000) (95089057 / 500000000) (Real.log (241893 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (241893 / 200000) = -Real.log (200000 / 241893) := by
    rw [show ((241893 / 200000) : ℝ) = ((200000 / 241893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (235045347 / 1000000000) ≤ -Real.log (158107 / 200000) ∧
    -Real.log (158107 / 200000) ≤ (58761337 / 250000000) := by
  have h := checkLog_sound (w := (41893 / 358107)) (n := 12)
    (lo := (235045347 / 1000000000)) (hi := (58761337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158107) = 1/(158107 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-58761337 / 250000000) (-235045347 / 1000000000) (Real.log (158107 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (190525313 / 1000000000) ≤ -Real.log (200000 / 241977) ∧
    -Real.log (200000 / 241977) ≤ (95262657 / 500000000) := by
  have h := checkLog_sound (w := (41977 / 441977)) (n := 12)
    (lo := (190525313 / 1000000000)) (hi := (95262657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241977 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241977 / 200000) = 1/(200000 / 241977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (190525313 / 1000000000) (95262657 / 500000000) (Real.log (241977 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (241977 / 200000) = -Real.log (200000 / 241977) := by
    rw [show ((241977 / 200000) : ℝ) = ((200000 / 241977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (117788387 / 500000000) ≤ -Real.log (158023 / 200000) ∧
    -Real.log (158023 / 200000) ≤ (9423071 / 40000000) := by
  have h := checkLog_sound (w := (41977 / 358023)) (n := 12)
    (lo := (117788387 / 500000000)) (hi := (9423071 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158023) = 1/(158023 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9423071 / 40000000) (-117788387 / 500000000) (Real.log (158023 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (69853579 / 500000000) ≤ -Real.log (1000000 / 1149937) ∧
    -Real.log (1000000 / 1149937) ≤ (139707159 / 1000000000) := by
  have h := checkLog_sound (w := (149937 / 2149937)) (n := 12)
    (lo := (69853579 / 500000000)) (hi := (139707159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149937 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1149937 / 1000000) = 1/(1000000 / 1149937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (69853579 / 500000000) (139707159 / 1000000000) (Real.log (1149937 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1149937 / 1000000) = -Real.log (1000000 / 1149937) := by
    rw [show ((1149937 / 1000000) : ℝ) = ((1000000 / 1149937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81222407 / 500000000) ≤ -Real.log (850063 / 1000000) ∧
    -Real.log (850063 / 1000000) ≤ (32488963 / 200000000) := by
  have h := checkLog_sound (w := (149937 / 1850063)) (n := 12)
    (lo := (81222407 / 500000000)) (hi := (32488963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 850063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 850063) = 1/(850063 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-32488963 / 200000000) (-81222407 / 500000000) (Real.log (850063 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (139974963 / 1000000000) ≤ -Real.log (200000 / 230049) ∧
    -Real.log (200000 / 230049) ≤ (34993741 / 250000000) := by
  have h := checkLog_sound (w := (30049 / 430049)) (n := 12)
    (lo := (139974963 / 1000000000)) (hi := (34993741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230049 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230049 / 200000) = 1/(200000 / 230049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (139974963 / 1000000000) (34993741 / 250000000) (Real.log (230049 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (230049 / 200000) = -Real.log (200000 / 230049) := by
    rw [show ((230049 / 200000) : ℝ) = ((200000 / 230049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (81403603 / 500000000) ≤ -Real.log (169951 / 200000) ∧
    -Real.log (169951 / 200000) ≤ (162807207 / 1000000000) := by
  have h := checkLog_sound (w := (30049 / 369951)) (n := 12)
    (lo := (81403603 / 500000000)) (hi := (162807207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169951) = 1/(169951 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-162807207 / 1000000000) (-81403603 / 500000000) (Real.log (169951 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (19010153 / 31250000) ≤ -Real.log (125000000000 / 229668883347) ∧
    -Real.log (125000000000 / 229668883347) ≤ (608324897 / 1000000000) := by
  have h := checkLog_sound (w := (104668883347 / 354668883347)) (n := 12)
    (lo := (19010153 / 31250000)) (hi := (608324897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229668883347 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229668883347 / 125000000000) = 1/(125000000000 / 229668883347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (19010153 / 31250000) (608324897 / 1000000000) (Real.log (229668883347 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (229668883347 / 125000000000) = -Real.log (125000000000 / 229668883347) := by
    rw [show ((229668883347 / 125000000000) : ℝ) = ((125000000000 / 229668883347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (121921763 / 200000000) ≤ -Real.log (62500000000 / 114981974487) ∧
    -Real.log (62500000000 / 114981974487) ≤ (38100551 / 62500000) := by
  have h := checkLog_sound (w := (52481974487 / 177481974487)) (n := 12)
    (lo := (121921763 / 200000000)) (hi := (38100551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114981974487 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114981974487 / 62500000000) = 1/(62500000000 / 114981974487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (121921763 / 200000000) (38100551 / 62500000) (Real.log (114981974487 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (114981974487 / 62500000000) = -Real.log (62500000000 / 114981974487) := by
    rw [show ((114981974487 / 62500000000) : ℝ) = ((62500000000 / 114981974487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (21261173 / 50000000) ≤ -Real.log (500000000000 / 764966130531) ∧
    -Real.log (500000000000 / 764966130531) ≤ (425223461 / 1000000000) := by
  have h := checkLog_sound (w := (264966130531 / 1264966130531)) (n := 12)
    (lo := (21261173 / 50000000)) (hi := (425223461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764966130531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764966130531 / 500000000000) = 1/(500000000000 / 764966130531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21261173 / 50000000) (425223461 / 1000000000) (Real.log (764966130531 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (764966130531 / 500000000000) = -Real.log (500000000000 / 764966130531) := by
    rw [show ((764966130531 / 500000000000) : ℝ) = ((500000000000 / 764966130531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53262761 / 125000000) ≤ -Real.log (31250000000 / 47852409143) ∧
    -Real.log (31250000000 / 47852409143) ≤ (426102089 / 1000000000) := by
  have h := checkLog_sound (w := (16602409143 / 79102409143)) (n := 12)
    (lo := (53262761 / 125000000)) (hi := (426102089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47852409143 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47852409143 / 31250000000) = 1/(31250000000 / 47852409143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (53262761 / 125000000) (426102089 / 1000000000) (Real.log (47852409143 / 31250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (47852409143 / 31250000000) = -Real.log (31250000000 / 47852409143) := by
    rw [show ((47852409143 / 31250000000) : ℝ) = ((31250000000 / 47852409143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (75537993 / 250000000) ≤ -Real.log (100000000000 / 135276679493) ∧
    -Real.log (100000000000 / 135276679493) ≤ (302151973 / 1000000000) := by
  have h := checkLog_sound (w := (35276679493 / 235276679493)) (n := 12)
    (lo := (75537993 / 250000000)) (hi := (302151973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135276679493 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135276679493 / 100000000000) = 1/(100000000000 / 135276679493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (75537993 / 250000000) (302151973 / 1000000000) (Real.log (135276679493 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (135276679493 / 100000000000) = -Real.log (100000000000 / 135276679493) := by
    rw [show ((135276679493 / 100000000000) : ℝ) = ((100000000000 / 135276679493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (302782169 / 1000000000) ≤ -Real.log (500000000000 / 676809786351) ∧
    -Real.log (500000000000 / 676809786351) ≤ (30278217 / 100000000) := by
  have h := checkLog_sound (w := (176809786351 / 1176809786351)) (n := 12)
    (lo := (302782169 / 1000000000)) (hi := (30278217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676809786351 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676809786351 / 500000000000) = 1/(500000000000 / 676809786351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (302782169 / 1000000000) (30278217 / 100000000) (Real.log (676809786351 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (676809786351 / 500000000000) = -Real.log (500000000000 / 676809786351) := by
    rw [show ((676809786351 / 500000000000) : ℝ) = ((500000000000 / 676809786351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22832243 / 1000000000) ≤ -Real.log (39097057599 / 40000000000) ∧
    -Real.log (39097057599 / 40000000000) ≤ (5708061 / 250000000) := by
  have h := checkLog_sound (w := (902942401 / 79097057599)) (n := 12)
    (lo := (22832243 / 1000000000)) (hi := (5708061 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39097057599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39097057599) = 1/(39097057599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5708061 / 250000000) (-22832243 / 1000000000) (Real.log (39097057599 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2842207 / 125000000) ≤ -Real.log (977518896031 / 1000000000000) ∧
    -Real.log (977518896031 / 1000000000000) ≤ (22737657 / 1000000000) := by
  have h := checkLog_sound (w := (22481103969 / 1977518896031)) (n := 12)
    (lo := (2842207 / 125000000)) (hi := (22737657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977518896031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977518896031) = 1/(977518896031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22737657 / 1000000000) (-2842207 / 125000000) (Real.log (977518896031 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell077

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell078Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell078
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

theorem reflection_log_1_neg : (51901123 / 200000000) ≤ -Real.log (5120 / 6637) ∧
    -Real.log (5120 / 6637) ≤ (16219101 / 62500000) := by
  have h := checkLog_sound (w := (1517 / 11757)) (n := 12)
    (lo := (51901123 / 200000000)) (hi := (16219101 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6637 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6637 / 5120) = 1/(5120 / 6637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (51901123 / 200000000) (16219101 / 62500000) (Real.log (6637 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6637 / 5120) = -Real.log (5120 / 6637) := by
    rw [show ((6637 / 5120) : ℝ) = ((5120 / 6637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (351387607 / 1000000000) ≤ -Real.log (3603 / 5120) ∧
    -Real.log (3603 / 5120) ≤ (43923451 / 125000000) := by
  have h := checkLog_sound (w := (1517 / 8723)) (n := 12)
    (lo := (351387607 / 1000000000)) (hi := (43923451 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3603) = 1/(3603 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-43923451 / 125000000) (-351387607 / 1000000000) (Real.log (3603 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (259053501 / 1000000000) ≤ -Real.log (2560 / 3317) ∧
    -Real.log (2560 / 3317) ≤ (129526751 / 500000000) := by
  have h := checkLog_sound (w := (757 / 5877)) (n := 12)
    (lo := (259053501 / 1000000000)) (hi := (129526751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3317 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3317 / 2560) = 1/(2560 / 3317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (259053501 / 1000000000) (129526751 / 500000000) (Real.log (3317 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3317 / 2560) = -Real.log (2560 / 3317) := by
    rw [show ((3317 / 2560) : ℝ) = ((2560 / 3317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (175277657 / 500000000) ≤ -Real.log (1803 / 2560) ∧
    -Real.log (1803 / 2560) ≤ (70111063 / 200000000) := by
  have h := checkLog_sound (w := (757 / 4363)) (n := 12)
    (lo := (175277657 / 500000000)) (hi := (70111063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1803) = 1/(1803 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-70111063 / 200000000) (-175277657 / 500000000) (Real.log (1803 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (190524487 / 1000000000) ≤ -Real.log (250000 / 302471) ∧
    -Real.log (250000 / 302471) ≤ (23815561 / 125000000) := by
  have h := checkLog_sound (w := (52471 / 552471)) (n := 12)
    (lo := (190524487 / 1000000000)) (hi := (23815561 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302471 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302471 / 250000) = 1/(250000 / 302471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (190524487 / 1000000000) (23815561 / 125000000) (Real.log (302471 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (302471 / 250000) = -Real.log (250000 / 302471) := by
    rw [show ((302471 / 250000) : ℝ) = ((250000 / 302471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (58893877 / 250000000) ≤ -Real.log (197529 / 250000) ∧
    -Real.log (197529 / 250000) ≤ (235575509 / 1000000000) := by
  have h := checkLog_sound (w := (52471 / 447529)) (n := 12)
    (lo := (58893877 / 250000000)) (hi := (235575509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197529) = 1/(197529 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-235575509 / 1000000000) (-58893877 / 250000000) (Real.log (197529 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (190871567 / 1000000000) ≤ -Real.log (15625 / 18911) ∧
    -Real.log (15625 / 18911) ≤ (11929473 / 62500000) := by
  have h := checkLog_sound (w := (1643 / 17268)) (n := 12)
    (lo := (190871567 / 1000000000)) (hi := (11929473 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18911 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18911 / 15625) = 1/(15625 / 18911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (190871567 / 1000000000) (11929473 / 62500000) (Real.log (18911 / 15625)) := by
  have h := reflection_log_7_neg
  have he : Real.log (18911 / 15625) = -Real.log (15625 / 18911) := by
    rw [show ((18911 / 15625) : ℝ) = ((15625 / 18911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (236107217 / 1000000000) ≤ -Real.log (12339 / 15625) ∧
    -Real.log (12339 / 15625) ≤ (118053609 / 500000000) := by
  have h := checkLog_sound (w := (1643 / 13982)) (n := 12)
    (lo := (236107217 / 1000000000)) (hi := (118053609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12339) = 1/(12339 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-118053609 / 500000000) (-236107217 / 1000000000) (Real.log (12339 / 15625)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139974093 / 1000000000) ≤ -Real.log (250000 / 287561) ∧
    -Real.log (250000 / 287561) ≤ (69987047 / 500000000) := by
  have h := checkLog_sound (w := (37561 / 537561)) (n := 12)
    (lo := (139974093 / 1000000000)) (hi := (69987047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287561 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287561 / 250000) = 1/(250000 / 287561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139974093 / 1000000000) (69987047 / 500000000) (Real.log (287561 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (287561 / 250000) = -Real.log (250000 / 287561) := by
    rw [show ((287561 / 250000) : ℝ) = ((250000 / 287561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (162806029 / 1000000000) ≤ -Real.log (212439 / 250000) ∧
    -Real.log (212439 / 250000) ≤ (16280603 / 100000000) := by
  have h := checkLog_sound (w := (37561 / 462439)) (n := 12)
    (lo := (162806029 / 1000000000)) (hi := (16280603 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212439) = 1/(212439 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-16280603 / 100000000) (-162806029 / 1000000000) (Real.log (212439 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17530337 / 125000000) ≤ -Real.log (1000000 / 1150553) ∧
    -Real.log (1000000 / 1150553) ≤ (140242697 / 1000000000) := by
  have h := checkLog_sound (w := (150553 / 2150553)) (n := 12)
    (lo := (17530337 / 125000000)) (hi := (140242697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150553 / 1000000) = 1/(1000000 / 1150553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17530337 / 125000000) (140242697 / 1000000000) (Real.log (1150553 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1150553 / 1000000) = -Real.log (1000000 / 1150553) := by
    rw [show ((1150553 / 1000000) : ℝ) = ((1000000 / 1150553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (163169729 / 1000000000) ≤ -Real.log (849447 / 1000000) ∧
    -Real.log (849447 / 1000000) ≤ (16316973 / 100000000) := by
  have h := checkLog_sound (w := (150553 / 1849447)) (n := 12)
    (lo := (163169729 / 1000000000)) (hi := (16316973 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849447) = 1/(849447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-16316973 / 100000000) (-163169729 / 1000000000) (Real.log (849447 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (121921763 / 200000000) ≤ -Real.log (100000000000 / 183971159179) ∧
    -Real.log (100000000000 / 183971159179) ≤ (38100551 / 62500000) := by
  have h := checkLog_sound (w := (83971159179 / 283971159179)) (n := 12)
    (lo := (121921763 / 200000000)) (hi := (38100551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183971159179 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183971159179 / 100000000000) = 1/(100000000000 / 183971159179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (121921763 / 200000000) (38100551 / 62500000) (Real.log (183971159179 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (183971159179 / 100000000000) = -Real.log (100000000000 / 183971159179) := by
    rw [show ((183971159179 / 100000000000) : ℝ) = ((100000000000 / 183971159179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (305446611 / 500000000) ≤ -Real.log (500000000000 / 921038023869) ∧
    -Real.log (500000000000 / 921038023869) ≤ (610893223 / 1000000000) := by
  have h := checkLog_sound (w := (421038023869 / 1421038023869)) (n := 12)
    (lo := (305446611 / 500000000)) (hi := (610893223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921038023869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921038023869 / 500000000000) = 1/(500000000000 / 921038023869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (305446611 / 500000000) (610893223 / 1000000000) (Real.log (921038023869 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (921038023869 / 500000000000) = -Real.log (500000000000 / 921038023869) := by
    rw [show ((921038023869 / 500000000000) : ℝ) = ((500000000000 / 921038023869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (106524999 / 250000000) ≤ -Real.log (7812500000 / 11963077257) ∧
    -Real.log (7812500000 / 11963077257) ≤ (426099997 / 1000000000) := by
  have h := checkLog_sound (w := (4150577257 / 19775577257)) (n := 12)
    (lo := (106524999 / 250000000)) (hi := (426099997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11963077257 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11963077257 / 7812500000) = 1/(7812500000 / 11963077257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (106524999 / 250000000) (426099997 / 1000000000) (Real.log (11963077257 / 7812500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (11963077257 / 7812500000) = -Real.log (7812500000 / 11963077257) := by
    rw [show ((11963077257 / 7812500000) : ℝ) = ((7812500000 / 11963077257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (85395757 / 200000000) ≤ -Real.log (400000000 / 613048059) ∧
    -Real.log (400000000 / 613048059) ≤ (213489393 / 500000000) := by
  have h := checkLog_sound (w := (213048059 / 1013048059)) (n := 12)
    (lo := (85395757 / 200000000)) (hi := (213489393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613048059 / 400000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613048059 / 400000000) = 1/(400000000 / 613048059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (85395757 / 200000000) (213489393 / 500000000) (Real.log (613048059 / 400000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (613048059 / 400000000) = -Real.log (400000000 / 613048059) := by
    rw [show ((613048059 / 400000000) : ℝ) = ((400000000 / 613048059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (302780123 / 1000000000) ≤ -Real.log (50000000000 / 67680840147) ∧
    -Real.log (50000000000 / 67680840147) ≤ (75695031 / 250000000) := by
  have h := checkLog_sound (w := (17680840147 / 117680840147)) (n := 12)
    (lo := (302780123 / 1000000000)) (hi := (75695031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67680840147 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67680840147 / 50000000000) = 1/(50000000000 / 67680840147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (302780123 / 1000000000) (75695031 / 250000000) (Real.log (67680840147 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (67680840147 / 50000000000) = -Real.log (50000000000 / 67680840147) := by
    rw [show ((67680840147 / 50000000000) : ℝ) = ((50000000000 / 67680840147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (12136497 / 40000000) ≤ -Real.log (500000000000 / 677236484443) ∧
    -Real.log (500000000000 / 677236484443) ≤ (151706213 / 500000000) := by
  have h := checkLog_sound (w := (177236484443 / 1177236484443)) (n := 12)
    (lo := (12136497 / 40000000)) (hi := (151706213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677236484443 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677236484443 / 500000000000) = 1/(500000000000 / 677236484443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (12136497 / 40000000) (151706213 / 500000000) (Real.log (677236484443 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (677236484443 / 500000000000) = -Real.log (500000000000 / 677236484443) := by
    rw [show ((677236484443 / 500000000000) : ℝ) = ((500000000000 / 677236484443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22927033 / 1000000000) ≤ -Real.log (977333794191 / 1000000000000) ∧
    -Real.log (977333794191 / 1000000000000) ≤ (11463517 / 500000000) := by
  have h := checkLog_sound (w := (22666205809 / 1977333794191)) (n := 12)
    (lo := (22927033 / 1000000000)) (hi := (11463517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977333794191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977333794191) = 1/(977333794191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-11463517 / 500000000) (-22927033 / 1000000000) (Real.log (977333794191 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4566387 / 200000000) ≤ -Real.log (61089171279 / 62500000000) ∧
    -Real.log (61089171279 / 62500000000) ≤ (356749 / 15625000) := by
  have h := checkLog_sound (w := (1410828721 / 123589171279)) (n := 12)
    (lo := (4566387 / 200000000)) (hi := (356749 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61089171279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61089171279) = 1/(61089171279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-356749 / 15625000) (-4566387 / 200000000) (Real.log (61089171279 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell078

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell079Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell079
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

theorem reflection_log_1_neg : (64989381 / 250000000) ≤ -Real.log (64 / 83) ∧
    -Real.log (64 / 83) ≤ (10398301 / 40000000) := by
  have h := checkLog_sound (w := (19 / 147)) (n := 12)
    (lo := (64989381 / 250000000)) (hi := (10398301 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83 / 64) = 1/(64 / 83) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (64989381 / 250000000) (10398301 / 40000000) (Real.log (83 / 64)) := by
  have h := reflection_log_1_neg
  have he : Real.log (83 / 64) = -Real.log (64 / 83) := by
    rw [show ((83 / 64) : ℝ) = ((64 / 83) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (352220593 / 1000000000) ≤ -Real.log (45 / 64) ∧
    -Real.log (45 / 64) ≤ (176110297 / 500000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 45) = 1/(45 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-176110297 / 500000000) (-352220593 / 1000000000) (Real.log (45 / 64)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (51901123 / 200000000) ≤ -Real.log (5120 / 6637) ∧
    -Real.log (5120 / 6637) ≤ (16219101 / 62500000) := by
  have h := checkLog_sound (w := (1517 / 11757)) (n := 12)
    (lo := (51901123 / 200000000)) (hi := (16219101 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6637 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6637 / 5120) = 1/(5120 / 6637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (51901123 / 200000000) (16219101 / 62500000) (Real.log (6637 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6637 / 5120) = -Real.log (5120 / 6637) := by
    rw [show ((6637 / 5120) : ℝ) = ((5120 / 6637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (351387607 / 1000000000) ≤ -Real.log (3603 / 5120) ∧
    -Real.log (3603 / 5120) ≤ (43923451 / 125000000) := by
  have h := checkLog_sound (w := (1517 / 8723)) (n := 12)
    (lo := (351387607 / 1000000000)) (hi := (43923451 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3603) = 1/(3603 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-43923451 / 125000000) (-351387607 / 1000000000) (Real.log (3603 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (190870741 / 1000000000) ≤ -Real.log (1000000 / 1210303) ∧
    -Real.log (1000000 / 1210303) ≤ (95435371 / 500000000) := by
  have h := checkLog_sound (w := (210303 / 2210303)) (n := 12)
    (lo := (190870741 / 1000000000)) (hi := (95435371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210303 / 1000000) = 1/(1000000 / 1210303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (190870741 / 1000000000) (95435371 / 500000000) (Real.log (1210303 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1210303 / 1000000) = -Real.log (1000000 / 1210303) := by
    rw [show ((1210303 / 1000000) : ℝ) = ((1000000 / 1210303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (236105951 / 1000000000) ≤ -Real.log (789697 / 1000000) ∧
    -Real.log (789697 / 1000000) ≤ (7378311 / 31250000) := by
  have h := checkLog_sound (w := (210303 / 1789697)) (n := 12)
    (lo := (236105951 / 1000000000)) (hi := (7378311 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789697) = 1/(789697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-7378311 / 31250000) (-236105951 / 1000000000) (Real.log (789697 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (191217701 / 1000000000) ≤ -Real.log (1000000 / 1210723) ∧
    -Real.log (1000000 / 1210723) ≤ (95608851 / 500000000) := by
  have h := checkLog_sound (w := (210723 / 2210723)) (n := 12)
    (lo := (191217701 / 1000000000)) (hi := (95608851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210723 / 1000000) = 1/(1000000 / 1210723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (191217701 / 1000000000) (95608851 / 500000000) (Real.log (1210723 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1210723 / 1000000) = -Real.log (1000000 / 1210723) := by
    rw [show ((1210723 / 1000000) : ℝ) = ((1000000 / 1210723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (118318971 / 500000000) ≤ -Real.log (789277 / 1000000) ∧
    -Real.log (789277 / 1000000) ≤ (236637943 / 1000000000) := by
  have h := checkLog_sound (w := (210723 / 1789277)) (n := 12)
    (lo := (118318971 / 500000000)) (hi := (236637943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789277) = 1/(789277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-236637943 / 1000000000) (-118318971 / 500000000) (Real.log (789277 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (140241827 / 1000000000) ≤ -Real.log (125000 / 143819) ∧
    -Real.log (125000 / 143819) ≤ (35060457 / 250000000) := by
  have h := checkLog_sound (w := (18819 / 268819)) (n := 12)
    (lo := (140241827 / 1000000000)) (hi := (35060457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143819 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143819 / 125000) = 1/(125000 / 143819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (140241827 / 1000000000) (35060457 / 250000000) (Real.log (143819 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (143819 / 125000) = -Real.log (125000 / 143819) := by
    rw [show ((143819 / 125000) : ℝ) = ((125000 / 143819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (20396069 / 125000000) ≤ -Real.log (106181 / 125000) ∧
    -Real.log (106181 / 125000) ≤ (163168553 / 1000000000) := by
  have h := checkLog_sound (w := (18819 / 231181)) (n := 12)
    (lo := (20396069 / 125000000)) (hi := (163168553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106181) = 1/(106181 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-163168553 / 1000000000) (-20396069 / 125000000) (Real.log (106181 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (8781843 / 62500000) ≤ -Real.log (50000 / 57543) ∧
    -Real.log (50000 / 57543) ≤ (140509489 / 1000000000) := by
  have h := checkLog_sound (w := (7543 / 107543)) (n := 12)
    (lo := (8781843 / 62500000)) (hi := (140509489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57543 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57543 / 50000) = 1/(50000 / 57543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (8781843 / 62500000) (140509489 / 1000000000) (Real.log (57543 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (57543 / 50000) = -Real.log (50000 / 57543) := by
    rw [show ((57543 / 50000) : ℝ) = ((50000 / 57543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (81765603 / 500000000) ≤ -Real.log (42457 / 50000) ∧
    -Real.log (42457 / 50000) ≤ (163531207 / 1000000000) := by
  have h := checkLog_sound (w := (7543 / 92457)) (n := 12)
    (lo := (81765603 / 500000000)) (hi := (163531207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42457) = 1/(42457 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-163531207 / 1000000000) (-81765603 / 500000000) (Real.log (42457 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (305446611 / 500000000) ≤ -Real.log (125000000000 / 230259505967) ∧
    -Real.log (125000000000 / 230259505967) ≤ (610893223 / 1000000000) := by
  have h := checkLog_sound (w := (105259505967 / 355259505967)) (n := 12)
    (lo := (305446611 / 500000000)) (hi := (610893223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230259505967 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230259505967 / 125000000000) = 1/(125000000000 / 230259505967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (305446611 / 500000000) (610893223 / 1000000000) (Real.log (230259505967 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (230259505967 / 125000000000) = -Real.log (125000000000 / 230259505967) := by
    rw [show ((230259505967 / 125000000000) : ℝ) = ((125000000000 / 230259505967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (306089059 / 500000000) ≤ -Real.log (500000000000 / 922222222223) ∧
    -Real.log (500000000000 / 922222222223) ≤ (612178119 / 1000000000) := by
  have h := checkLog_sound (w := (422222222223 / 1422222222223)) (n := 12)
    (lo := (306089059 / 500000000)) (hi := (612178119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((922222222223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(922222222223 / 500000000000) = 1/(500000000000 / 922222222223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (306089059 / 500000000) (612178119 / 1000000000) (Real.log (922222222223 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (922222222223 / 500000000000) = -Real.log (500000000000 / 922222222223) := by
    rw [show ((922222222223 / 500000000000) : ℝ) = ((500000000000 / 922222222223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (106744173 / 250000000) ≤ -Real.log (50000000000 / 76630847021) ∧
    -Real.log (50000000000 / 76630847021) ≤ (426976693 / 1000000000) := by
  have h := checkLog_sound (w := (26630847021 / 126630847021)) (n := 12)
    (lo := (106744173 / 250000000)) (hi := (426976693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76630847021 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76630847021 / 50000000000) = 1/(50000000000 / 76630847021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (106744173 / 250000000) (426976693 / 1000000000) (Real.log (76630847021 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (76630847021 / 50000000000) = -Real.log (50000000000 / 76630847021) := by
    rw [show ((76630847021 / 50000000000) : ℝ) = ((50000000000 / 76630847021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (106963911 / 250000000) ≤ -Real.log (250000000000 / 383491157097) ∧
    -Real.log (250000000000 / 383491157097) ≤ (85571129 / 200000000) := by
  have h := checkLog_sound (w := (133491157097 / 633491157097)) (n := 12)
    (lo := (106963911 / 250000000)) (hi := (85571129 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383491157097 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383491157097 / 250000000000) = 1/(250000000000 / 383491157097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (106963911 / 250000000) (85571129 / 200000000) (Real.log (383491157097 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (383491157097 / 250000000000) = -Real.log (250000000000 / 383491157097) := by
    rw [show ((383491157097 / 250000000000) : ℝ) = ((250000000000 / 383491157097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (303410379 / 1000000000) ≤ -Real.log (250000000000 / 338617549279) ∧
    -Real.log (250000000000 / 338617549279) ≤ (15170519 / 50000000) := by
  have h := checkLog_sound (w := (88617549279 / 588617549279)) (n := 12)
    (lo := (303410379 / 1000000000)) (hi := (15170519 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338617549279 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338617549279 / 250000000000) = 1/(250000000000 / 338617549279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (303410379 / 1000000000) (15170519 / 50000000) (Real.log (338617549279 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (338617549279 / 250000000000) = -Real.log (250000000000 / 338617549279) := by
    rw [show ((338617549279 / 250000000000) : ℝ) = ((250000000000 / 338617549279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (60808139 / 200000000) ≤ -Real.log (500000000000 / 677662105189) ∧
    -Real.log (500000000000 / 677662105189) ≤ (38005087 / 125000000) := by
  have h := checkLog_sound (w := (177662105189 / 1177662105189)) (n := 12)
    (lo := (60808139 / 200000000)) (hi := (38005087 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677662105189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677662105189 / 500000000000) = 1/(500000000000 / 677662105189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (60808139 / 200000000) (38005087 / 125000000) (Real.log (677662105189 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (677662105189 / 500000000000) = -Real.log (500000000000 / 677662105189) := by
    rw [show ((677662105189 / 500000000000) : ℝ) = ((500000000000 / 677662105189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (23021717 / 1000000000) ≤ -Real.log (2443103151 / 2500000000) ∧
    -Real.log (2443103151 / 2500000000) ≤ (11510859 / 500000000) := by
  have h := checkLog_sound (w := (56896849 / 4943103151)) (n := 12)
    (lo := (23021717 / 1000000000)) (hi := (11510859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2443103151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2443103151) = 1/(2443103151 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-11510859 / 500000000) (-23021717 / 1000000000) (Real.log (2443103151 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (917069 / 40000000) ≤ -Real.log (15270845239 / 15625000000) ∧
    -Real.log (15270845239 / 15625000000) ≤ (11463363 / 500000000) := by
  have h := checkLog_sound (w := (354154761 / 30895845239)) (n := 12)
    (lo := (917069 / 40000000)) (hi := (11463363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15270845239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15270845239) = 1/(15270845239 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-11463363 / 500000000) (-917069 / 40000000) (Real.log (15270845239 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell079

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell080Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell080
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

theorem reflection_log_1_neg : (260409229 / 1000000000) ≤ -Real.log (5120 / 6643) ∧
    -Real.log (5120 / 6643) ≤ (26040923 / 100000000) := by
  have h := checkLog_sound (w := (1523 / 11763)) (n := 12)
    (lo := (260409229 / 1000000000)) (hi := (26040923 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6643 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6643 / 5120) = 1/(5120 / 6643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (260409229 / 1000000000) (26040923 / 100000000) (Real.log (6643 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6643 / 5120) = -Real.log (5120 / 6643) := by
    rw [show ((6643 / 5120) : ℝ) = ((5120 / 6643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (176527137 / 500000000) ≤ -Real.log (3597 / 5120) ∧
    -Real.log (3597 / 5120) ≤ (14122171 / 40000000) := by
  have h := checkLog_sound (w := (1523 / 8717)) (n := 12)
    (lo := (176527137 / 500000000)) (hi := (14122171 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3597) = 1/(3597 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-14122171 / 40000000) (-176527137 / 500000000) (Real.log (3597 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (64989381 / 250000000) ≤ -Real.log (64 / 83) ∧
    -Real.log (64 / 83) ≤ (10398301 / 40000000) := by
  have h := checkLog_sound (w := (19 / 147)) (n := 12)
    (lo := (64989381 / 250000000)) (hi := (10398301 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83 / 64) = 1/(64 / 83) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (64989381 / 250000000) (10398301 / 40000000) (Real.log (83 / 64)) := by
  have h := reflection_log_3_neg
  have he : Real.log (83 / 64) = -Real.log (64 / 83) := by
    rw [show ((83 / 64) : ℝ) = ((64 / 83) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (352220593 / 1000000000) ≤ -Real.log (45 / 64) ∧
    -Real.log (45 / 64) ≤ (176110297 / 500000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 45) = 1/(45 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-176110297 / 500000000) (-352220593 / 1000000000) (Real.log (45 / 64)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (305947 / 1600000) ≤ -Real.log (500000 / 605361) ∧
    -Real.log (500000 / 605361) ≤ (47804219 / 250000000) := by
  have h := checkLog_sound (w := (105361 / 1105361)) (n := 12)
    (lo := (305947 / 1600000)) (hi := (47804219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605361 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605361 / 500000) = 1/(500000 / 605361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (305947 / 1600000) (47804219 / 250000000) (Real.log (605361 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (605361 / 500000) = -Real.log (500000 / 605361) := by
    rw [show ((605361 / 500000) : ℝ) = ((500000 / 605361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9465467 / 40000000) ≤ -Real.log (394639 / 500000) ∧
    -Real.log (394639 / 500000) ≤ (59159169 / 250000000) := by
  have h := checkLog_sound (w := (105361 / 894639)) (n := 12)
    (lo := (9465467 / 40000000)) (hi := (59159169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394639) = 1/(394639 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-59159169 / 250000000) (-9465467 / 40000000) (Real.log (394639 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (47890929 / 250000000) ≤ -Real.log (500000 / 605571) ∧
    -Real.log (500000 / 605571) ≤ (191563717 / 1000000000) := by
  have h := checkLog_sound (w := (105571 / 1105571)) (n := 12)
    (lo := (47890929 / 250000000)) (hi := (191563717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605571 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605571 / 500000) = 1/(500000 / 605571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (47890929 / 250000000) (191563717 / 1000000000) (Real.log (605571 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (605571 / 500000) = -Real.log (500000 / 605571) := by
    rw [show ((605571 / 500000) : ℝ) = ((500000 / 605571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (59292237 / 250000000) ≤ -Real.log (394429 / 500000) ∧
    -Real.log (394429 / 500000) ≤ (237168949 / 1000000000) := by
  have h := checkLog_sound (w := (105571 / 894429)) (n := 12)
    (lo := (59292237 / 250000000)) (hi := (237168949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394429) = 1/(394429 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-237168949 / 1000000000) (-59292237 / 250000000) (Real.log (394429 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (7025431 / 50000000) ≤ -Real.log (1000000 / 1150859) ∧
    -Real.log (1000000 / 1150859) ≤ (140508621 / 1000000000) := by
  have h := checkLog_sound (w := (150859 / 2150859)) (n := 12)
    (lo := (7025431 / 50000000)) (hi := (140508621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150859 / 1000000) = 1/(1000000 / 1150859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (7025431 / 50000000) (140508621 / 1000000000) (Real.log (1150859 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1150859 / 1000000) = -Real.log (1000000 / 1150859) := by
    rw [show ((1150859 / 1000000) : ℝ) = ((1000000 / 1150859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (40882507 / 250000000) ≤ -Real.log (849141 / 1000000) ∧
    -Real.log (849141 / 1000000) ≤ (163530029 / 1000000000) := by
  have h := checkLog_sound (w := (150859 / 1849141)) (n := 12)
    (lo := (40882507 / 250000000)) (hi := (163530029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849141) = 1/(849141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-163530029 / 1000000000) (-40882507 / 250000000) (Real.log (849141 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (140777079 / 1000000000) ≤ -Real.log (15625 / 17987) ∧
    -Real.log (15625 / 17987) ≤ (3519427 / 25000000) := by
  have h := checkLog_sound (w := (1181 / 16806)) (n := 12)
    (lo := (140777079 / 1000000000)) (hi := (3519427 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17987 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17987 / 15625) = 1/(15625 / 17987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (140777079 / 1000000000) (3519427 / 25000000) (Real.log (17987 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (17987 / 15625) = -Real.log (15625 / 17987) := by
    rw [show ((17987 / 15625) : ℝ) = ((15625 / 17987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (20486749 / 125000000) ≤ -Real.log (13263 / 15625) ∧
    -Real.log (13263 / 15625) ≤ (163893993 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 14444)) (n := 12)
    (lo := (20486749 / 125000000)) (hi := (163893993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13263) = 1/(13263 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-163893993 / 1000000000) (-20486749 / 125000000) (Real.log (13263 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (306089059 / 500000000) ≤ -Real.log (250000000000 / 461111111111) ∧
    -Real.log (250000000000 / 461111111111) ≤ (612178119 / 1000000000) := by
  have h := checkLog_sound (w := (211111111111 / 711111111111)) (n := 12)
    (lo := (306089059 / 500000000)) (hi := (612178119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461111111111 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461111111111 / 250000000000) = 1/(250000000000 / 461111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (306089059 / 500000000) (612178119 / 1000000000) (Real.log (461111111111 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (461111111111 / 250000000000) = -Real.log (250000000000 / 461111111111) := by
    rw [show ((461111111111 / 250000000000) : ℝ) = ((250000000000 / 461111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (613463503 / 1000000000) ≤ -Real.log (250000000000 / 461704197943) ∧
    -Real.log (250000000000 / 461704197943) ≤ (38341469 / 62500000) := by
  have h := checkLog_sound (w := (211704197943 / 711704197943)) (n := 12)
    (lo := (613463503 / 1000000000)) (hi := (38341469 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461704197943 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461704197943 / 250000000000) = 1/(250000000000 / 461704197943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (613463503 / 1000000000) (38341469 / 62500000) (Real.log (461704197943 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (461704197943 / 250000000000) = -Real.log (250000000000 / 461704197943) := by
    rw [show ((461704197943 / 250000000000) : ℝ) = ((250000000000 / 461704197943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (427853551 / 1000000000) ≤ -Real.log (500000000000 / 766980708951) ∧
    -Real.log (500000000000 / 766980708951) ≤ (26740847 / 62500000) := by
  have h := checkLog_sound (w := (266980708951 / 1266980708951)) (n := 12)
    (lo := (427853551 / 1000000000)) (hi := (26740847 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((766980708951 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(766980708951 / 500000000000) = 1/(500000000000 / 766980708951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (427853551 / 1000000000) (26740847 / 62500000) (Real.log (766980708951 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (766980708951 / 500000000000) = -Real.log (500000000000 / 766980708951) := by
    rw [show ((766980708951 / 500000000000) : ℝ) = ((500000000000 / 766980708951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (85746533 / 200000000) ≤ -Real.log (125000000000 / 191913817189) ∧
    -Real.log (125000000000 / 191913817189) ≤ (214366333 / 500000000) := by
  have h := checkLog_sound (w := (66913817189 / 316913817189)) (n := 12)
    (lo := (85746533 / 200000000)) (hi := (214366333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191913817189 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191913817189 / 125000000000) = 1/(125000000000 / 191913817189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (85746533 / 200000000) (214366333 / 500000000) (Real.log (191913817189 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (191913817189 / 125000000000) = -Real.log (125000000000 / 191913817189) := by
    rw [show ((191913817189 / 125000000000) : ℝ) = ((125000000000 / 191913817189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (38004831 / 125000000) ≤ -Real.log (250000000000 / 338830359151) ∧
    -Real.log (250000000000 / 338830359151) ≤ (304038649 / 1000000000) := by
  have h := checkLog_sound (w := (88830359151 / 588830359151)) (n := 12)
    (lo := (38004831 / 125000000)) (hi := (304038649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338830359151 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338830359151 / 250000000000) = 1/(250000000000 / 338830359151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (38004831 / 125000000) (304038649 / 1000000000) (Real.log (338830359151 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (338830359151 / 250000000000) = -Real.log (250000000000 / 338830359151) := by
    rw [show ((338830359151 / 250000000000) : ℝ) = ((250000000000 / 338830359151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (304671071 / 1000000000) ≤ -Real.log (5000000000 / 6780894217) ∧
    -Real.log (5000000000 / 6780894217) ≤ (9520971 / 31250000) := by
  have h := checkLog_sound (w := (1780894217 / 11780894217)) (n := 12)
    (lo := (304671071 / 1000000000)) (hi := (9520971 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6780894217 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6780894217 / 5000000000) = 1/(5000000000 / 6780894217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (304671071 / 1000000000) (9520971 / 31250000) (Real.log (6780894217 / 5000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (6780894217 / 5000000000) = -Real.log (5000000000 / 6780894217) := by
    rw [show ((6780894217 / 5000000000) : ℝ) = ((5000000000 / 6780894217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1444807 / 62500000) ≤ -Real.log (238561581 / 244140625) ∧
    -Real.log (238561581 / 244140625) ≤ (23116913 / 1000000000) := by
  have h := checkLog_sound (w := (2789522 / 241351103)) (n := 12)
    (lo := (1444807 / 62500000)) (hi := (23116913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 238561581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 238561581) = 1/(238561581 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23116913 / 1000000000) (-1444807 / 62500000) (Real.log (238561581 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (719419 / 31250000) ≤ -Real.log (977241562119 / 1000000000000) ∧
    -Real.log (977241562119 / 1000000000000) ≤ (23021409 / 1000000000) := by
  have h := checkLog_sound (w := (22758437881 / 1977241562119)) (n := 12)
    (lo := (719419 / 31250000)) (hi := (23021409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977241562119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977241562119) = 1/(977241562119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-23021409 / 1000000000) (-719419 / 31250000) (Real.log (977241562119 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell080

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell081Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell081
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

theorem reflection_log_1_neg : (26086073 / 100000000) ≤ -Real.log (2560 / 3323) ∧
    -Real.log (2560 / 3323) ≤ (260860731 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 5883)) (n := 12)
    (lo := (26086073 / 100000000)) (hi := (260860731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3323 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3323 / 2560) = 1/(2560 / 3323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (26086073 / 100000000) (260860731 / 1000000000) (Real.log (3323 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3323 / 2560) = -Real.log (2560 / 3323) := by
    rw [show ((3323 / 2560) : ℝ) = ((2560 / 3323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (7077773 / 20000000) ≤ -Real.log (1797 / 2560) ∧
    -Real.log (1797 / 2560) ≤ (353888651 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 4357)) (n := 12)
    (lo := (7077773 / 20000000)) (hi := (353888651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1797) = 1/(1797 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-353888651 / 1000000000) (-7077773 / 20000000) (Real.log (1797 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (260409229 / 1000000000) ≤ -Real.log (5120 / 6643) ∧
    -Real.log (5120 / 6643) ≤ (26040923 / 100000000) := by
  have h := checkLog_sound (w := (1523 / 11763)) (n := 12)
    (lo := (260409229 / 1000000000)) (hi := (26040923 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6643 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6643 / 5120) = 1/(5120 / 6643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (260409229 / 1000000000) (26040923 / 100000000) (Real.log (6643 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6643 / 5120) = -Real.log (5120 / 6643) := by
    rw [show ((6643 / 5120) : ℝ) = ((5120 / 6643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (176527137 / 500000000) ≤ -Real.log (3597 / 5120) ∧
    -Real.log (3597 / 5120) ≤ (14122171 / 40000000) := by
  have h := checkLog_sound (w := (1523 / 8717)) (n := 12)
    (lo := (176527137 / 500000000)) (hi := (14122171 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3597) = 1/(3597 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-14122171 / 40000000) (-176527137 / 500000000) (Real.log (3597 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19156289 / 100000000) ≤ -Real.log (1000000 / 1211141) ∧
    -Real.log (1000000 / 1211141) ≤ (191562891 / 1000000000) := by
  have h := checkLog_sound (w := (211141 / 2211141)) (n := 12)
    (lo := (19156289 / 100000000)) (hi := (191562891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211141 / 1000000) = 1/(1000000 / 1211141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19156289 / 100000000) (191562891 / 1000000000) (Real.log (1211141 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1211141 / 1000000) = -Real.log (1000000 / 1211141) := by
    rw [show ((1211141 / 1000000) : ℝ) = ((1000000 / 1211141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (237167681 / 1000000000) ≤ -Real.log (788859 / 1000000) ∧
    -Real.log (788859 / 1000000) ≤ (118583841 / 500000000) := by
  have h := checkLog_sound (w := (211141 / 1788859)) (n := 12)
    (lo := (237167681 / 1000000000)) (hi := (118583841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788859) = 1/(788859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-118583841 / 500000000) (-237167681 / 1000000000) (Real.log (788859 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (47977609 / 250000000) ≤ -Real.log (500000 / 605781) ∧
    -Real.log (500000 / 605781) ≤ (191910437 / 1000000000) := by
  have h := checkLog_sound (w := (105781 / 1105781)) (n := 12)
    (lo := (47977609 / 250000000)) (hi := (191910437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605781 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605781 / 500000) = 1/(500000 / 605781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (47977609 / 250000000) (191910437 / 1000000000) (Real.log (605781 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (605781 / 500000) = -Real.log (500000 / 605781) := by
    rw [show ((605781 / 500000) : ℝ) = ((500000 / 605781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (47540301 / 200000000) ≤ -Real.log (394219 / 500000) ∧
    -Real.log (394219 / 500000) ≤ (118850753 / 500000000) := by
  have h := checkLog_sound (w := (105781 / 894219)) (n := 12)
    (lo := (47540301 / 200000000)) (hi := (118850753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394219) = 1/(394219 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-118850753 / 500000000) (-47540301 / 200000000) (Real.log (394219 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (14077621 / 100000000) ≤ -Real.log (1000000 / 1151167) ∧
    -Real.log (1000000 / 1151167) ≤ (140776211 / 1000000000) := by
  have h := checkLog_sound (w := (151167 / 2151167)) (n := 12)
    (lo := (14077621 / 100000000)) (hi := (140776211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151167 / 1000000) = 1/(1000000 / 1151167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (14077621 / 100000000) (140776211 / 1000000000) (Real.log (1151167 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1151167 / 1000000) = -Real.log (1000000 / 1151167) := by
    rw [show ((1151167 / 1000000) : ℝ) = ((1000000 / 1151167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81946407 / 500000000) ≤ -Real.log (848833 / 1000000) ∧
    -Real.log (848833 / 1000000) ≤ (32778563 / 200000000) := by
  have h := checkLog_sound (w := (151167 / 1848833)) (n := 12)
    (lo := (81946407 / 500000000)) (hi := (32778563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 848833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 848833) = 1/(848833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-32778563 / 200000000) (-81946407 / 500000000) (Real.log (848833 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (141044597 / 1000000000) ≤ -Real.log (250000 / 287869) ∧
    -Real.log (250000 / 287869) ≤ (70522299 / 500000000) := by
  have h := checkLog_sound (w := (37869 / 537869)) (n := 12)
    (lo := (141044597 / 1000000000)) (hi := (70522299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287869 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287869 / 250000) = 1/(250000 / 287869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (141044597 / 1000000000) (70522299 / 500000000) (Real.log (287869 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (287869 / 250000) = -Real.log (250000 / 287869) := by
    rw [show ((287869 / 250000) : ℝ) = ((250000 / 287869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (164256909 / 1000000000) ≤ -Real.log (212131 / 250000) ∧
    -Real.log (212131 / 250000) ≤ (16425691 / 100000000) := by
  have h := checkLog_sound (w := (37869 / 462131)) (n := 12)
    (lo := (164256909 / 1000000000)) (hi := (16425691 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212131) = 1/(212131 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-16425691 / 100000000) (-164256909 / 1000000000) (Real.log (212131 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (613463503 / 1000000000) ≤ -Real.log (100000000000 / 184681679177) ∧
    -Real.log (100000000000 / 184681679177) ≤ (38341469 / 62500000) := by
  have h := checkLog_sound (w := (84681679177 / 284681679177)) (n := 12)
    (lo := (613463503 / 1000000000)) (hi := (38341469 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184681679177 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184681679177 / 100000000000) = 1/(100000000000 / 184681679177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (613463503 / 1000000000) (38341469 / 62500000) (Real.log (184681679177 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (184681679177 / 100000000000) = -Real.log (100000000000 / 184681679177) := by
    rw [show ((184681679177 / 100000000000) : ℝ) = ((100000000000 / 184681679177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (614749381 / 1000000000) ≤ -Real.log (250000000000 / 462298274903) ∧
    -Real.log (250000000000 / 462298274903) ≤ (307374691 / 500000000) := by
  have h := checkLog_sound (w := (212298274903 / 712298274903)) (n := 12)
    (lo := (614749381 / 1000000000)) (hi := (307374691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462298274903 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(462298274903 / 250000000000) = 1/(250000000000 / 462298274903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (614749381 / 1000000000) (307374691 / 500000000) (Real.log (462298274903 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (462298274903 / 250000000000) = -Real.log (250000000000 / 462298274903) := by
    rw [show ((462298274903 / 250000000000) : ℝ) = ((250000000000 / 462298274903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (428730571 / 1000000000) ≤ -Real.log (500000000000 / 767653661807) ∧
    -Real.log (500000000000 / 767653661807) ≤ (107182643 / 250000000) := by
  have h := checkLog_sound (w := (267653661807 / 1267653661807)) (n := 12)
    (lo := (428730571 / 1000000000)) (hi := (107182643 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767653661807 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767653661807 / 500000000000) = 1/(500000000000 / 767653661807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (428730571 / 1000000000) (107182643 / 250000000) (Real.log (767653661807 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (767653661807 / 500000000000) = -Real.log (500000000000 / 767653661807) := by
    rw [show ((767653661807 / 500000000000) : ℝ) = ((500000000000 / 767653661807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (214805971 / 500000000) ≤ -Real.log (250000000000 / 384165273617) ∧
    -Real.log (250000000000 / 384165273617) ≤ (429611943 / 1000000000) := by
  have h := checkLog_sound (w := (134165273617 / 634165273617)) (n := 12)
    (lo := (214805971 / 500000000)) (hi := (429611943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384165273617 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384165273617 / 250000000000) = 1/(250000000000 / 384165273617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (214805971 / 500000000) (429611943 / 1000000000) (Real.log (384165273617 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (384165273617 / 250000000000) = -Real.log (250000000000 / 384165273617) := by
    rw [show ((384165273617 / 250000000000) : ℝ) = ((250000000000 / 384165273617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (9520907 / 31250000) ≤ -Real.log (250000000000 / 339044016903) ∧
    -Real.log (250000000000 / 339044016903) ≤ (12186761 / 40000000) := by
  have h := checkLog_sound (w := (89044016903 / 589044016903)) (n := 12)
    (lo := (9520907 / 31250000)) (hi := (12186761 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339044016903 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339044016903 / 250000000000) = 1/(250000000000 / 339044016903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9520907 / 31250000) (12186761 / 40000000) (Real.log (339044016903 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (339044016903 / 250000000000) = -Real.log (250000000000 / 339044016903) := by
    rw [show ((339044016903 / 250000000000) : ℝ) = ((250000000000 / 339044016903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (305301507 / 1000000000) ≤ -Real.log (125000000000 / 169629262107) ∧
    -Real.log (125000000000 / 169629262107) ≤ (76325377 / 250000000) := by
  have h := checkLog_sound (w := (44629262107 / 294629262107)) (n := 12)
    (lo := (305301507 / 1000000000)) (hi := (76325377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169629262107 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169629262107 / 125000000000) = 1/(125000000000 / 169629262107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (305301507 / 1000000000) (76325377 / 250000000) (Real.log (169629262107 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (169629262107 / 125000000000) = -Real.log (125000000000 / 169629262107) := by
    rw [show ((169629262107 / 125000000000) : ℝ) = ((125000000000 / 169629262107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (23212311 / 1000000000) ≤ -Real.log (61065938839 / 62500000000) ∧
    -Real.log (61065938839 / 62500000000) ≤ (2901539 / 125000000) := by
  have h := checkLog_sound (w := (1434061161 / 123565938839)) (n := 12)
    (lo := (23212311 / 1000000000)) (hi := (2901539 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61065938839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61065938839) = 1/(61065938839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2901539 / 125000000) (-23212311 / 1000000000) (Real.log (61065938839 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (23116603 / 1000000000) ≤ -Real.log (977148538111 / 1000000000000) ∧
    -Real.log (977148538111 / 1000000000000) ≤ (5779151 / 250000000) := by
  have h := checkLog_sound (w := (22851461889 / 1977148538111)) (n := 12)
    (lo := (23116603 / 1000000000)) (hi := (5779151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977148538111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977148538111) = 1/(977148538111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5779151 / 250000000) (-23116603 / 1000000000) (Real.log (977148538111 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell081

end


