-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0103Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0103Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:58:47.31917+00:00
-- url     : https://prove2.me/theorems/be74e503-8d26-4822-b8fb-97c584245646
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0103Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0104Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0103Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0104Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0105Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0106Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0103Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0104Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0105Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0106Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0103Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0104Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0105Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0106Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0103Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0104Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0105Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0106Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0103Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0103
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (33541983 / 50000000) ≤ -Real.log (51200 / 100141) ∧
    -Real.log (51200 / 100141) ≤ (670839661 / 1000000000) := by
  have h := checkLog_sound (w := (48941 / 151341)) (n := 12)
    (lo := (33541983 / 50000000)) (hi := (670839661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100141 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100141 / 51200) = 1/(51200 / 100141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33541983 / 50000000) (670839661 / 1000000000) (Real.log (100141 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100141 / 51200) = -Real.log (51200 / 100141) := by
    rw [show ((100141 / 51200) : ℝ) = ((51200 / 100141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (780204323 / 250000000) ≤ -Real.log (2259 / 51200) ∧
    -Real.log (2259 / 51200) ≤ (3120817297 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 5459)) (n := 12)
    (lo := (87057143 / 250000000)) (hi := (348228573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2259) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2259) = 1/(2259 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3120817297 / 1000000000) (-780204323 / 250000000) (Real.log (2259 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67064991 / 100000000) ≤ -Real.log (25600 / 50061) ∧
    -Real.log (25600 / 50061) ≤ (670649911 / 1000000000) := by
  have h := checkLog_sound (w := (24461 / 75661)) (n := 12)
    (lo := (67064991 / 100000000)) (hi := (670649911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50061 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50061 / 25600) = 1/(25600 / 50061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67064991 / 100000000) (670649911 / 1000000000) (Real.log (50061 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50061 / 25600) = -Real.log (25600 / 50061) := by
    rw [show ((50061 / 25600) : ℝ) = ((25600 / 50061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (48631901 / 15625000) ≤ -Real.log (1139 / 25600) ∧
    -Real.log (1139 / 25600) ≤ (3112441669 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 2739)) (n := 12)
    (lo := (21240809 / 62500000)) (hi := (67970589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1139) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1139) = 1/(1139 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3112441669 / 1000000000) (-48631901 / 15625000) (Real.log (1139 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (648023139 / 1000000000) ≤ -Real.log (25600 / 48941) ∧
    -Real.log (25600 / 48941) ≤ (32401157 / 50000000) := by
  have h := checkLog_sound (w := (23341 / 74541)) (n := 12)
    (lo := (648023139 / 1000000000)) (hi := (32401157 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48941 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48941 / 25600) = 1/(25600 / 48941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (648023139 / 1000000000) (32401157 / 50000000) (Real.log (48941 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48941 / 25600) = -Real.log (25600 / 48941) := by
    rw [show ((48941 / 25600) : ℝ) = ((25600 / 48941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (75864691 / 31250000) ≤ -Real.log (2259 / 25600) ∧
    -Real.log (2259 / 25600) ≤ (606917529 / 250000000) := by
  have h := checkLog_sound (w := (941 / 5459)) (n := 12)
    (lo := (87057143 / 250000000)) (hi := (348228573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2259) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2259) = 1/(2259 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-606917529 / 250000000) (-75864691 / 31250000) (Real.log (2259 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (647634841 / 1000000000) ≤ -Real.log (12800 / 24461) ∧
    -Real.log (12800 / 24461) ≤ (323817421 / 500000000) := by
  have h := checkLog_sound (w := (11661 / 37261)) (n := 12)
    (lo := (647634841 / 1000000000)) (hi := (323817421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24461 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24461 / 12800) = 1/(12800 / 24461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (647634841 / 1000000000) (323817421 / 500000000) (Real.log (24461 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24461 / 12800) = -Real.log (12800 / 24461) := by
    rw [show ((24461 / 12800) : ℝ) = ((12800 / 24461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (604823621 / 250000000) ≤ -Real.log (1139 / 12800) ∧
    -Real.log (1139 / 12800) ≤ (302411811 / 125000000) := by
  have h := checkLog_sound (w := (461 / 2739)) (n := 12)
    (lo := (21240809 / 62500000)) (hi := (67970589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1139) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1139) = 1/(1139 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-302411811 / 125000000) (-604823621 / 250000000) (Real.log (1139 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (168692589 / 250000000) ≤ -Real.log (500000 / 981791) ∧
    -Real.log (500000 / 981791) ≤ (674770357 / 1000000000) := by
  have h := checkLog_sound (w := (481791 / 1481791)) (n := 12)
    (lo := (168692589 / 250000000)) (hi := (674770357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981791 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981791 / 500000) = 1/(500000 / 981791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (168692589 / 250000000) (674770357 / 1000000000) (Real.log (981791 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (981791 / 500000) = -Real.log (500000 / 981791) := by
    rw [show ((981791 / 500000) : ℝ) = ((500000 / 981791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1656346059 / 500000000) ≤ -Real.log (18209 / 500000) ∧
    -Real.log (18209 / 500000) ≤ (3312692123 / 1000000000) := by
  have h := checkLog_sound (w := (13041 / 49459)) (n := 12)
    (lo := (270051699 / 500000000)) (hi := (540103399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18209) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18209) = 1/(18209 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3312692123 / 1000000000) (-1656346059 / 500000000) (Real.log (18209 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (674916507 / 1000000000) ≤ -Real.log (1000000 / 1963869) ∧
    -Real.log (1000000 / 1963869) ≤ (168729127 / 250000000) := by
  have h := checkLog_sound (w := (963869 / 2963869)) (n := 12)
    (lo := (674916507 / 1000000000)) (hi := (168729127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963869 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963869 / 1000000) = 1/(1000000 / 1963869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (674916507 / 1000000000) (168729127 / 250000000) (Real.log (1963869 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1963869 / 1000000) = -Real.log (1000000 / 1963869) := by
    rw [show ((1963869 / 1000000) : ℝ) = ((1000000 / 1963869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1660302027 / 500000000) ≤ -Real.log (36131 / 1000000) ∧
    -Real.log (36131 / 1000000) ≤ (3320604059 / 1000000000) := by
  have h := checkLog_sound (w := (26369 / 98631)) (n := 12)
    (lo := (274007667 / 500000000)) (hi := (109603067 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36131) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36131) = 1/(36131 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3320604059 / 1000000000) (-1660302027 / 500000000) (Real.log (36131 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (337291463 / 500000000) ≤ -Real.log (500000 / 981607) ∧
    -Real.log (500000 / 981607) ≤ (674582927 / 1000000000) := by
  have h := checkLog_sound (w := (481607 / 1481607)) (n := 12)
    (lo := (337291463 / 500000000)) (hi := (674582927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981607 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981607 / 500000) = 1/(500000 / 981607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (337291463 / 500000000) (674582927 / 1000000000) (Real.log (981607 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (981607 / 500000) = -Real.log (500000 / 981607) := by
    rw [show ((981607 / 500000) : ℝ) = ((500000 / 981607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1651318969 / 500000000) ≤ -Real.log (18393 / 500000) ∧
    -Real.log (18393 / 500000) ≤ (3302637943 / 1000000000) := by
  have h := checkLog_sound (w := (12857 / 49643)) (n := 12)
    (lo := (265024609 / 500000000)) (hi := (530049219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18393) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18393) = 1/(18393 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3302637943 / 1000000000) (-1651318969 / 500000000) (Real.log (18393 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1054269 / 1562500) ≤ -Real.log (1000000 / 1963507) ∧
    -Real.log (1000000 / 1963507) ≤ (674732161 / 1000000000) := by
  have h := checkLog_sound (w := (963507 / 2963507)) (n := 12)
    (lo := (1054269 / 1562500)) (hi := (674732161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963507 / 1000000) = 1/(1000000 / 1963507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1054269 / 1562500) (674732161 / 1000000000) (Real.log (1963507 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1963507 / 1000000) = -Real.log (1000000 / 1963507) := by
    rw [show ((1963507 / 1000000) : ℝ) = ((1000000 / 1963507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (662126963 / 200000000) ≤ -Real.log (36493 / 1000000) ∧
    -Real.log (36493 / 1000000) ≤ (165531741 / 50000000) := by
  have h := checkLog_sound (w := (26007 / 98993)) (n := 12)
    (lo := (107609219 / 200000000)) (hi := (33627881 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36493) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36493) = 1/(36493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-165531741 / 50000000) (-662126963 / 200000000) (Real.log (36493 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1993731237 / 500000000) ≤ -Real.log (500000000000 / 26958948871437) ∧
    -Real.log (500000000000 / 26958948871437) ≤ (49843281 / 12500000) := by
  have h := checkLog_sound (w := (10958948871437 / 42958948871437)) (n := 12)
    (lo := (260863287 / 500000000)) (hi := (20869063 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26958948871437 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26958948871437 / 16000000000000) = 1/(500000000000 / 26958948871437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1993731237 / 500000000) (49843281 / 12500000) (Real.log (26958948871437 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (26958948871437 / 500000000000) = -Real.log (500000000000 / 26958948871437) := by
    rw [show ((26958948871437 / 500000000000) : ℝ) = ((500000000000 / 26958948871437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (49944007 / 12500000) ≤ -Real.log (10000000000 / 543541280341) ∧
    -Real.log (10000000000 / 543541280341) ≤ (1997760283 / 500000000) := by
  have h := checkLog_sound (w := (223541280341 / 863541280341)) (n := 12)
    (lo := (26489233 / 50000000)) (hi := (529784661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543541280341 / 320000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(543541280341 / 320000000000) = 1/(10000000000 / 543541280341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (49944007 / 12500000) (1997760283 / 500000000) (Real.log (543541280341 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (543541280341 / 10000000000) = -Real.log (10000000000 / 543541280341) := by
    rw [show ((543541280341 / 10000000000) : ℝ) = ((10000000000 / 543541280341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15536019 / 3906250) ≤ -Real.log (500000000000 / 26684254879573) ∧
    -Real.log (500000000000 / 26684254879573) ≤ (397722087 / 100000000) := by
  have h := checkLog_sound (w := (10684254879573 / 42684254879573)) (n := 12)
    (lo := (127871241 / 250000000)) (hi := (102296993 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26684254879573 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26684254879573 / 16000000000000) = 1/(500000000000 / 26684254879573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (15536019 / 3906250) (397722087 / 100000000) (Real.log (26684254879573 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (26684254879573 / 500000000000) = -Real.log (500000000000 / 26684254879573) := by
    rw [show ((26684254879573 / 500000000000) : ℝ) = ((500000000000 / 26684254879573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1992683487 / 500000000) ≤ -Real.log (31250000000 / 1681407221933) ∧
    -Real.log (31250000000 / 1681407221933) ≤ (199268349 / 50000000) := by
  have h := checkLog_sound (w := (681407221933 / 2681407221933)) (n := 12)
    (lo := (259815537 / 500000000)) (hi := (20785243 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1681407221933 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1681407221933 / 1000000000000) = 1/(31250000000 / 1681407221933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1992683487 / 500000000) (199268349 / 50000000) (Real.log (1681407221933 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1681407221933 / 31250000000) = -Real.log (31250000000 / 1681407221933) := by
    rw [show ((1681407221933 / 31250000000) : ℝ) = ((31250000000 / 1681407221933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0103

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0104Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0104
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (67064991 / 100000000) ≤ -Real.log (25600 / 50061) ∧
    -Real.log (25600 / 50061) ≤ (670649911 / 1000000000) := by
  have h := checkLog_sound (w := (24461 / 75661)) (n := 12)
    (lo := (67064991 / 100000000)) (hi := (670649911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50061 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50061 / 25600) = 1/(25600 / 50061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67064991 / 100000000) (670649911 / 1000000000) (Real.log (50061 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50061 / 25600) = -Real.log (25600 / 50061) := by
    rw [show ((50061 / 25600) : ℝ) = ((25600 / 50061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (48631901 / 15625000) ≤ -Real.log (1139 / 25600) ∧
    -Real.log (1139 / 25600) ≤ (3112441669 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 2739)) (n := 12)
    (lo := (21240809 / 62500000)) (hi := (67970589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1139) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1139) = 1/(1139 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3112441669 / 1000000000) (-48631901 / 15625000) (Real.log (1139 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (670460123 / 1000000000) ≤ -Real.log (51200 / 100103) ∧
    -Real.log (51200 / 100103) ≤ (167615031 / 250000000) := by
  have h := checkLog_sound (w := (48903 / 151303)) (n := 12)
    (lo := (670460123 / 1000000000)) (hi := (167615031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100103 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100103 / 51200) = 1/(51200 / 100103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (670460123 / 1000000000) (167615031 / 250000000) (Real.log (100103 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100103 / 51200) = -Real.log (51200 / 100103) := by
    rw [show ((100103 / 51200) : ℝ) = ((51200 / 100103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1552067803 / 500000000) ≤ -Real.log (2297 / 51200) ∧
    -Real.log (2297 / 51200) ≤ (3104135611 / 1000000000) := by
  have h := checkLog_sound (w := (903 / 5497)) (n := 12)
    (lo := (165773443 / 500000000)) (hi := (331546887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2297) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2297) = 1/(2297 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3104135611 / 1000000000) (-1552067803 / 500000000) (Real.log (2297 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (647634841 / 1000000000) ≤ -Real.log (12800 / 24461) ∧
    -Real.log (12800 / 24461) ≤ (323817421 / 500000000) := by
  have h := checkLog_sound (w := (11661 / 37261)) (n := 12)
    (lo := (647634841 / 1000000000)) (hi := (323817421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24461 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24461 / 12800) = 1/(12800 / 24461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (647634841 / 1000000000) (323817421 / 500000000) (Real.log (24461 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24461 / 12800) = -Real.log (12800 / 24461) := by
    rw [show ((24461 / 12800) : ℝ) = ((12800 / 24461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (604823621 / 250000000) ≤ -Real.log (1139 / 12800) ∧
    -Real.log (1139 / 12800) ≤ (302411811 / 125000000) := by
  have h := checkLog_sound (w := (461 / 2739)) (n := 12)
    (lo := (21240809 / 62500000)) (hi := (67970589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1139) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1139) = 1/(1139 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-302411811 / 125000000) (-604823621 / 250000000) (Real.log (1139 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (80905799 / 125000000) ≤ -Real.log (25600 / 48903) ∧
    -Real.log (25600 / 48903) ≤ (647246393 / 1000000000) := by
  have h := checkLog_sound (w := (23303 / 74503)) (n := 12)
    (lo := (80905799 / 125000000)) (hi := (647246393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48903 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48903 / 25600) = 1/(25600 / 48903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (80905799 / 125000000) (647246393 / 1000000000) (Real.log (48903 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48903 / 25600) = -Real.log (25600 / 48903) := by
    rw [show ((48903 / 25600) : ℝ) = ((25600 / 48903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1205494213 / 500000000) ≤ -Real.log (2297 / 25600) ∧
    -Real.log (2297 / 25600) ≤ (241098843 / 100000000) := by
  have h := checkLog_sound (w := (903 / 5497)) (n := 12)
    (lo := (165773443 / 500000000)) (hi := (331546887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2297) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2297) = 1/(2297 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-241098843 / 100000000) (-1205494213 / 500000000) (Real.log (2297 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (337312601 / 500000000) ≤ -Real.log (1000000 / 1963297) ∧
    -Real.log (1000000 / 1963297) ≤ (674625203 / 1000000000) := by
  have h := checkLog_sound (w := (963297 / 2963297)) (n := 12)
    (lo := (337312601 / 500000000)) (hi := (674625203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963297 / 1000000) = 1/(1000000 / 1963297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (337312601 / 500000000) (674625203 / 1000000000) (Real.log (1963297 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1963297 / 1000000) = -Real.log (1000000 / 1963297) := by
    rw [show ((1963297 / 1000000) : ℝ) = ((1000000 / 1963297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3304896781 / 1000000000) ≤ -Real.log (36703 / 1000000) ∧
    -Real.log (36703 / 1000000) ≤ (1652448393 / 500000000) := by
  have h := checkLog_sound (w := (25797 / 99203)) (n := 12)
    (lo := (532308061 / 1000000000)) (hi := (266154031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36703) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36703) = 1/(36703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1652448393 / 500000000) (-3304896781 / 1000000000) (Real.log (36703 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (134954173 / 200000000) ≤ -Real.log (1000000 / 1963583) ∧
    -Real.log (1000000 / 1963583) ≤ (337385433 / 500000000) := by
  have h := checkLog_sound (w := (963583 / 2963583)) (n := 12)
    (lo := (134954173 / 200000000)) (hi := (337385433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963583 / 1000000) = 1/(1000000 / 1963583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (134954173 / 200000000) (337385433 / 500000000) (Real.log (1963583 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1963583 / 1000000) = -Real.log (1000000 / 1963583) := by
    rw [show ((1963583 / 1000000) : ℝ) = ((1000000 / 1963583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1656359789 / 500000000) ≤ -Real.log (36417 / 1000000) ∧
    -Real.log (36417 / 1000000) ≤ (3312719583 / 1000000000) := by
  have h := checkLog_sound (w := (26083 / 98917)) (n := 12)
    (lo := (270065429 / 500000000)) (hi := (540130859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36417) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36417) = 1/(36417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3312719583 / 1000000000) (-1656359789 / 500000000) (Real.log (36417 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (674433669 / 1000000000) ≤ -Real.log (1000000 / 1962921) ∧
    -Real.log (1000000 / 1962921) ≤ (67443367 / 100000000) := by
  have h := checkLog_sound (w := (962921 / 2962921)) (n := 12)
    (lo := (674433669 / 1000000000)) (hi := (67443367 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962921 / 1000000) = 1/(1000000 / 1962921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (674433669 / 1000000000) (67443367 / 100000000) (Real.log (1962921 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1962921 / 1000000) = -Real.log (1000000 / 1962921) := by
    rw [show ((1962921 / 1000000) : ℝ) = ((1000000 / 1962921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (658940901 / 200000000) ≤ -Real.log (37079 / 1000000) ∧
    -Real.log (37079 / 1000000) ≤ (329470451 / 100000000) := by
  have h := checkLog_sound (w := (25421 / 99579)) (n := 12)
    (lo := (104423157 / 200000000)) (hi := (261057893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37079) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37079) = 1/(37079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-329470451 / 100000000) (-658940901 / 200000000) (Real.log (37079 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (134916687 / 200000000) ≤ -Real.log (200000 / 392643) ∧
    -Real.log (200000 / 392643) ≤ (168645859 / 250000000) := by
  have h := checkLog_sound (w := (192643 / 592643)) (n := 12)
    (lo := (134916687 / 200000000)) (hi := (168645859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392643 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392643 / 200000) = 1/(200000 / 392643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (134916687 / 200000000) (168645859 / 250000000) (Real.log (392643 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (392643 / 200000) = -Real.log (200000 / 392643) := by
    rw [show ((392643 / 200000) : ℝ) = ((200000 / 392643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3302665123 / 1000000000) ≤ -Real.log (7357 / 200000) ∧
    -Real.log (7357 / 200000) ≤ (412833141 / 125000000) := by
  have h := checkLog_sound (w := (5143 / 19857)) (n := 12)
    (lo := (530076403 / 1000000000)) (hi := (132519101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7357) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 7357) = 1/(7357 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-412833141 / 125000000) (-3302665123 / 1000000000) (Real.log (7357 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3979521983 / 1000000000) ≤ -Real.log (250000000000 / 13372864615971) ∧
    -Real.log (250000000000 / 13372864615971) ≤ (3979521989 / 1000000000) := by
  have h := checkLog_sound (w := (5372864615971 / 21372864615971)) (n := 12)
    (lo := (513786083 / 1000000000)) (hi := (128446521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13372864615971 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13372864615971 / 8000000000000) = 1/(250000000000 / 13372864615971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3979521983 / 1000000000) (3979521989 / 1000000000) (Real.log (13372864615971 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (13372864615971 / 250000000000) = -Real.log (250000000000 / 13372864615971) := by
    rw [show ((13372864615971 / 250000000000) : ℝ) = ((250000000000 / 13372864615971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3987490443 / 1000000000) ≤ -Real.log (100000000000 / 5391940577203) ∧
    -Real.log (100000000000 / 5391940577203) ≤ (3987490449 / 1000000000) := by
  have h := checkLog_sound (w := (2191940577203 / 8591940577203)) (n := 12)
    (lo := (521754543 / 1000000000)) (hi := (32609659 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5391940577203 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5391940577203 / 3200000000000) = 1/(100000000000 / 5391940577203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3987490443 / 1000000000) (3987490449 / 1000000000) (Real.log (5391940577203 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5391940577203 / 100000000000) = -Real.log (100000000000 / 5391940577203) := by
    rw [show ((5391940577203 / 100000000000) : ℝ) = ((100000000000 / 5391940577203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1984569087 / 500000000) ≤ -Real.log (250000000000 / 13234721810189) ∧
    -Real.log (250000000000 / 13234721810189) ≤ (198456909 / 50000000) := by
  have h := checkLog_sound (w := (5234721810189 / 21234721810189)) (n := 12)
    (lo := (251701137 / 500000000)) (hi := (20136091 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13234721810189 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13234721810189 / 8000000000000) = 1/(250000000000 / 13234721810189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1984569087 / 500000000) (198456909 / 50000000) (Real.log (13234721810189 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13234721810189 / 250000000000) = -Real.log (250000000000 / 13234721810189) := by
    rw [show ((13234721810189 / 250000000000) : ℝ) = ((250000000000 / 13234721810189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1988624279 / 500000000) ≤ -Real.log (500000000000 / 26684993883377) ∧
    -Real.log (500000000000 / 26684993883377) ≤ (994312141 / 250000000) := by
  have h := checkLog_sound (w := (10684993883377 / 42684993883377)) (n := 12)
    (lo := (255756329 / 500000000)) (hi := (511512659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26684993883377 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26684993883377 / 16000000000000) = 1/(500000000000 / 26684993883377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1988624279 / 500000000) (994312141 / 250000000) (Real.log (26684993883377 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (26684993883377 / 500000000000) = -Real.log (500000000000 / 26684993883377) := by
    rw [show ((26684993883377 / 500000000000) : ℝ) = ((500000000000 / 26684993883377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0104

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0105Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0105
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (670460123 / 1000000000) ≤ -Real.log (51200 / 100103) ∧
    -Real.log (51200 / 100103) ≤ (167615031 / 250000000) := by
  have h := checkLog_sound (w := (48903 / 151303)) (n := 12)
    (lo := (670460123 / 1000000000)) (hi := (167615031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100103 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100103 / 51200) = 1/(51200 / 100103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (670460123 / 1000000000) (167615031 / 250000000) (Real.log (100103 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100103 / 51200) = -Real.log (51200 / 100103) := by
    rw [show ((100103 / 51200) : ℝ) = ((51200 / 100103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1552067803 / 500000000) ≤ -Real.log (2297 / 51200) ∧
    -Real.log (2297 / 51200) ≤ (3104135611 / 1000000000) := by
  have h := checkLog_sound (w := (903 / 5497)) (n := 12)
    (lo := (165773443 / 500000000)) (hi := (331546887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2297) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2297) = 1/(2297 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3104135611 / 1000000000) (-1552067803 / 500000000) (Real.log (2297 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (670270301 / 1000000000) ≤ -Real.log (12800 / 25021) ∧
    -Real.log (12800 / 25021) ≤ (335135151 / 500000000) := by
  have h := checkLog_sound (w := (12221 / 37821)) (n := 12)
    (lo := (670270301 / 1000000000)) (hi := (335135151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25021 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25021 / 12800) = 1/(12800 / 25021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (670270301 / 1000000000) (335135151 / 500000000) (Real.log (25021 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25021 / 12800) = -Real.log (12800 / 25021) := by
    rw [show ((25021 / 12800) : ℝ) = ((12800 / 25021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (309589797 / 100000000) ≤ -Real.log (579 / 12800) ∧
    -Real.log (579 / 12800) ≤ (123835919 / 40000000) := by
  have h := checkLog_sound (w := (221 / 1379)) (n := 12)
    (lo := (1293237 / 4000000)) (hi := (323309251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 579) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 579) = 1/(579 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-123835919 / 40000000) (-309589797 / 100000000) (Real.log (579 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (80905799 / 125000000) ≤ -Real.log (25600 / 48903) ∧
    -Real.log (25600 / 48903) ≤ (647246393 / 1000000000) := by
  have h := checkLog_sound (w := (23303 / 74503)) (n := 12)
    (lo := (80905799 / 125000000)) (hi := (647246393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48903 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48903 / 25600) = 1/(25600 / 48903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (80905799 / 125000000) (647246393 / 1000000000) (Real.log (48903 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48903 / 25600) = -Real.log (25600 / 48903) := by
    rw [show ((48903 / 25600) : ℝ) = ((25600 / 48903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1205494213 / 500000000) ≤ -Real.log (2297 / 25600) ∧
    -Real.log (2297 / 25600) ≤ (241098843 / 100000000) := by
  have h := checkLog_sound (w := (903 / 5497)) (n := 12)
    (lo := (165773443 / 500000000)) (hi := (331546887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2297) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2297) = 1/(2297 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-241098843 / 100000000) (-1205494213 / 500000000) (Real.log (2297 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (646857793 / 1000000000) ≤ -Real.log (6400 / 12221) ∧
    -Real.log (6400 / 12221) ≤ (323428897 / 500000000) := by
  have h := checkLog_sound (w := (5821 / 18621)) (n := 12)
    (lo := (646857793 / 1000000000)) (hi := (323428897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12221 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12221 / 6400) = 1/(6400 / 12221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (646857793 / 1000000000) (323428897 / 500000000) (Real.log (12221 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12221 / 6400) = -Real.log (6400 / 12221) := by
    rw [show ((12221 / 6400) : ℝ) = ((6400 / 12221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (240275079 / 100000000) ≤ -Real.log (579 / 6400) ∧
    -Real.log (579 / 6400) ≤ (1201375397 / 500000000) := by
  have h := checkLog_sound (w := (221 / 1379)) (n := 12)
    (lo := (1293237 / 4000000)) (hi := (323309251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 579) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 579) = 1/(579 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1201375397 / 500000000) (-240275079 / 100000000) (Real.log (579 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (168620007 / 250000000) ≤ -Real.log (250000 / 490753) ∧
    -Real.log (250000 / 490753) ≤ (674480029 / 1000000000) := by
  have h := checkLog_sound (w := (240753 / 740753)) (n := 12)
    (lo := (168620007 / 250000000)) (hi := (674480029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490753 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490753 / 250000) = 1/(250000 / 490753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (168620007 / 250000000) (674480029 / 1000000000) (Real.log (490753 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (490753 / 250000) = -Real.log (250000 / 490753) := by
    rw [show ((490753 / 250000) : ℝ) = ((250000 / 490753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3297161741 / 1000000000) ≤ -Real.log (9247 / 250000) ∧
    -Real.log (9247 / 250000) ≤ (1648580873 / 500000000) := by
  have h := checkLog_sound (w := (3189 / 12436)) (n := 12)
    (lo := (524573021 / 1000000000)) (hi := (262286511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9247) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 9247) = 1/(9247 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1648580873 / 500000000) (-3297161741 / 1000000000) (Real.log (9247 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42164107 / 62500000) ≤ -Real.log (500000 / 981649) ∧
    -Real.log (500000 / 981649) ≤ (674625713 / 1000000000) := by
  have h := checkLog_sound (w := (481649 / 1481649)) (n := 12)
    (lo := (42164107 / 62500000)) (hi := (674625713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981649 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981649 / 500000) = 1/(500000 / 981649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42164107 / 62500000) (674625713 / 1000000000) (Real.log (981649 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (981649 / 500000) = -Real.log (500000 / 981649) := by
    rw [show ((981649 / 500000) : ℝ) = ((500000 / 981649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3304924027 / 1000000000) ≤ -Real.log (18351 / 500000) ∧
    -Real.log (18351 / 500000) ≤ (25819719 / 7812500) := by
  have h := checkLog_sound (w := (12899 / 49601)) (n := 12)
    (lo := (532335307 / 1000000000)) (hi := (133083827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18351) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18351) = 1/(18351 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-25819719 / 7812500) (-3304924027 / 1000000000) (Real.log (18351 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6742849 / 10000000) ≤ -Real.log (1000000 / 1962629) ∧
    -Real.log (1000000 / 1962629) ≤ (674284901 / 1000000000) := by
  have h := checkLog_sound (w := (962629 / 2962629)) (n := 12)
    (lo := (6742849 / 10000000)) (hi := (674284901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962629 / 1000000) = 1/(1000000 / 1962629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6742849 / 10000000) (674284901 / 1000000000) (Real.log (1962629 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1962629 / 1000000) = -Real.log (1000000 / 1962629) := by
    rw [show ((1962629 / 1000000) : ℝ) = ((1000000 / 1962629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1643430137 / 500000000) ≤ -Real.log (37371 / 1000000) ∧
    -Real.log (37371 / 1000000) ≤ (3286860279 / 1000000000) := by
  have h := checkLog_sound (w := (25129 / 99871)) (n := 12)
    (lo := (257135777 / 500000000)) (hi := (102854311 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37371) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37371) = 1/(37371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3286860279 / 1000000000) (-1643430137 / 500000000) (Real.log (37371 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (674434179 / 1000000000) ≤ -Real.log (500000 / 981461) ∧
    -Real.log (500000 / 981461) ≤ (33721709 / 50000000) := by
  have h := checkLog_sound (w := (481461 / 1481461)) (n := 12)
    (lo := (674434179 / 1000000000)) (hi := (33721709 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981461 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981461 / 500000) = 1/(500000 / 981461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (674434179 / 1000000000) (33721709 / 50000000) (Real.log (981461 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (981461 / 500000) = -Real.log (500000 / 981461) := by
    rw [show ((981461 / 500000) : ℝ) = ((500000 / 981461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1647365737 / 500000000) ≤ -Real.log (18539 / 500000) ∧
    -Real.log (18539 / 500000) ≤ (3294731479 / 1000000000) := by
  have h := checkLog_sound (w := (12711 / 49789)) (n := 12)
    (lo := (261071377 / 500000000)) (hi := (104428551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18539) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18539) = 1/(18539 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3294731479 / 1000000000) (-1647365737 / 500000000) (Real.log (18539 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (496455221 / 125000000) ≤ -Real.log (5000000000 / 265357953931) ∧
    -Real.log (5000000000 / 265357953931) ≤ (1985820887 / 500000000) := by
  have h := checkLog_sound (w := (105357953931 / 425357953931)) (n := 12)
    (lo := (126476467 / 250000000)) (hi := (505905869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265357953931 / 160000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(265357953931 / 160000000000) = 1/(5000000000 / 265357953931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (496455221 / 125000000) (1985820887 / 500000000) (Real.log (265357953931 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (265357953931 / 5000000000) = -Real.log (5000000000 / 265357953931) := by
    rw [show ((265357953931 / 5000000000) : ℝ) = ((5000000000 / 265357953931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1989774869 / 500000000) ≤ -Real.log (500000000000 / 26746471581931) ∧
    -Real.log (500000000000 / 26746471581931) ≤ (248721859 / 62500000) := by
  have h := checkLog_sound (w := (10746471581931 / 42746471581931)) (n := 12)
    (lo := (256906919 / 500000000)) (hi := (513813839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26746471581931 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26746471581931 / 16000000000000) = 1/(500000000000 / 26746471581931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1989774869 / 500000000) (248721859 / 62500000) (Real.log (26746471581931 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (26746471581931 / 500000000000) = -Real.log (500000000000 / 26746471581931) := by
    rw [show ((26746471581931 / 500000000000) : ℝ) = ((500000000000 / 26746471581931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1980572587 / 500000000) ≤ -Real.log (500000000000 / 26258716651949) ∧
    -Real.log (500000000000 / 26258716651949) ≤ (198057259 / 50000000) := by
  have h := checkLog_sound (w := (10258716651949 / 42258716651949)) (n := 12)
    (lo := (247704637 / 500000000)) (hi := (19816371 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26258716651949 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26258716651949 / 16000000000000) = 1/(500000000000 / 26258716651949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1980572587 / 500000000) (198057259 / 50000000) (Real.log (26258716651949 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (26258716651949 / 500000000000) = -Real.log (500000000000 / 26258716651949) := by
    rw [show ((26258716651949 / 500000000000) : ℝ) = ((500000000000 / 26258716651949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3969165653 / 1000000000) ≤ -Real.log (100000000000 / 5294034198177) ∧
    -Real.log (100000000000 / 5294034198177) ≤ (3969165659 / 1000000000) := by
  have h := checkLog_sound (w := (2094034198177 / 8494034198177)) (n := 12)
    (lo := (503429753 / 1000000000)) (hi := (251714877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5294034198177 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5294034198177 / 3200000000000) = 1/(100000000000 / 5294034198177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3969165653 / 1000000000) (3969165659 / 1000000000) (Real.log (5294034198177 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5294034198177 / 100000000000) = -Real.log (100000000000 / 5294034198177) := by
    rw [show ((5294034198177 / 100000000000) : ℝ) = ((100000000000 / 5294034198177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0105

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0106Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0106
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (670270301 / 1000000000) ≤ -Real.log (12800 / 25021) ∧
    -Real.log (12800 / 25021) ≤ (335135151 / 500000000) := by
  have h := checkLog_sound (w := (12221 / 37821)) (n := 12)
    (lo := (670270301 / 1000000000)) (hi := (335135151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25021 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25021 / 12800) = 1/(12800 / 25021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (670270301 / 1000000000) (335135151 / 500000000) (Real.log (25021 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25021 / 12800) = -Real.log (12800 / 25021) := by
    rw [show ((25021 / 12800) : ℝ) = ((12800 / 25021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (309589797 / 100000000) ≤ -Real.log (579 / 12800) ∧
    -Real.log (579 / 12800) ≤ (123835919 / 40000000) := by
  have h := checkLog_sound (w := (221 / 1379)) (n := 12)
    (lo := (1293237 / 4000000)) (hi := (323309251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 579) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 579) = 1/(579 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-123835919 / 40000000) (-309589797 / 100000000) (Real.log (579 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (335040221 / 500000000) ≤ -Real.log (10240 / 20013) ∧
    -Real.log (10240 / 20013) ≤ (670080443 / 1000000000) := by
  have h := checkLog_sound (w := (9773 / 30253)) (n := 12)
    (lo := (335040221 / 500000000)) (hi := (670080443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20013 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20013 / 10240) = 1/(10240 / 20013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (335040221 / 500000000) (670080443 / 1000000000) (Real.log (20013 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20013 / 10240) = -Real.log (10240 / 20013) := by
    rw [show ((20013 / 10240) : ℝ) = ((10240 / 20013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1543863819 / 500000000) ≤ -Real.log (467 / 10240) ∧
    -Real.log (467 / 10240) ≤ (3087727643 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 467) = 1/(467 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3087727643 / 1000000000) (-1543863819 / 500000000) (Real.log (467 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (646857793 / 1000000000) ≤ -Real.log (6400 / 12221) ∧
    -Real.log (6400 / 12221) ≤ (323428897 / 500000000) := by
  have h := checkLog_sound (w := (5821 / 18621)) (n := 12)
    (lo := (646857793 / 1000000000)) (hi := (323428897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12221 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12221 / 6400) = 1/(6400 / 12221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (646857793 / 1000000000) (323428897 / 500000000) (Real.log (12221 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12221 / 6400) = -Real.log (6400 / 12221) := by
    rw [show ((12221 / 6400) : ℝ) = ((6400 / 12221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (240275079 / 100000000) ≤ -Real.log (579 / 6400) ∧
    -Real.log (579 / 6400) ≤ (1201375397 / 500000000) := by
  have h := checkLog_sound (w := (221 / 1379)) (n := 12)
    (lo := (1293237 / 4000000)) (hi := (323309251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 579) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 579) = 1/(579 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1201375397 / 500000000) (-240275079 / 100000000) (Real.log (579 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (323234521 / 500000000) ≤ -Real.log (5120 / 9773) ∧
    -Real.log (5120 / 9773) ≤ (646469043 / 1000000000) := by
  have h := checkLog_sound (w := (4653 / 14893)) (n := 12)
    (lo := (323234521 / 500000000)) (hi := (646469043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9773 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9773 / 5120) = 1/(5120 / 9773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (323234521 / 500000000) (646469043 / 1000000000) (Real.log (9773 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9773 / 5120) = -Real.log (5120 / 9773) := by
    rw [show ((9773 / 5120) : ℝ) = ((5120 / 9773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1197290229 / 500000000) ≤ -Real.log (467 / 5120) ∧
    -Real.log (467 / 5120) ≤ (1197290231 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 467) = 1/(467 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1197290231 / 500000000) (-1197290229 / 500000000) (Real.log (467 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42145927 / 62500000) ≤ -Real.log (1000000 / 1962727) ∧
    -Real.log (1000000 / 1962727) ≤ (674334833 / 1000000000) := by
  have h := checkLog_sound (w := (962727 / 2962727)) (n := 12)
    (lo := (42145927 / 62500000)) (hi := (674334833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962727 / 1000000) = 1/(1000000 / 1962727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42145927 / 62500000) (674334833 / 1000000000) (Real.log (1962727 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1962727 / 1000000) = -Real.log (1000000 / 1962727) := by
    rw [show ((1962727 / 1000000) : ℝ) = ((1000000 / 1962727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (411185759 / 125000000) ≤ -Real.log (37273 / 1000000) ∧
    -Real.log (37273 / 1000000) ≤ (3289486077 / 1000000000) := by
  have h := checkLog_sound (w := (25227 / 99773)) (n := 12)
    (lo := (64612169 / 125000000)) (hi := (516897353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37273) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37273) = 1/(37273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3289486077 / 1000000000) (-411185759 / 125000000) (Real.log (37273 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (674480537 / 1000000000) ≤ -Real.log (1000000 / 1963013) ∧
    -Real.log (1000000 / 1963013) ≤ (337240269 / 500000000) := by
  have h := checkLog_sound (w := (963013 / 2963013)) (n := 12)
    (lo := (674480537 / 1000000000)) (hi := (337240269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963013 / 1000000) = 1/(1000000 / 1963013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (674480537 / 1000000000) (337240269 / 500000000) (Real.log (1963013 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1963013 / 1000000) = -Real.log (1000000 / 1963013) := by
    rw [show ((1963013 / 1000000) : ℝ) = ((1000000 / 1963013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3297188777 / 1000000000) ≤ -Real.log (36987 / 1000000) ∧
    -Real.log (36987 / 1000000) ≤ (1648594391 / 500000000) := by
  have h := checkLog_sound (w := (25513 / 99487)) (n := 12)
    (lo := (524600057 / 1000000000)) (hi := (262300029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36987) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36987) = 1/(36987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1648594391 / 500000000) (-3297188777 / 1000000000) (Real.log (36987 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (674136109 / 1000000000) ≤ -Real.log (1000000 / 1962337) ∧
    -Real.log (1000000 / 1962337) ≤ (67413611 / 100000000) := by
  have h := checkLog_sound (w := (962337 / 2962337)) (n := 12)
    (lo := (674136109 / 1000000000)) (hi := (67413611 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962337 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962337 / 1000000) = 1/(1000000 / 1962337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (674136109 / 1000000000) (67413611 / 100000000) (Real.log (1962337 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1962337 / 1000000) = -Real.log (1000000 / 1962337) := by
    rw [show ((1962337 / 1000000) : ℝ) = ((1000000 / 1962337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (409884637 / 125000000) ≤ -Real.log (37663 / 1000000) ∧
    -Real.log (37663 / 1000000) ≤ (3279077101 / 1000000000) := by
  have h := checkLog_sound (w := (24837 / 100163)) (n := 12)
    (lo := (63311047 / 125000000)) (hi := (506488377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37663) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37663) = 1/(37663 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3279077101 / 1000000000) (-409884637 / 125000000) (Real.log (37663 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (67428541 / 100000000) ≤ -Real.log (100000 / 196263) ∧
    -Real.log (100000 / 196263) ≤ (674285411 / 1000000000) := by
  have h := checkLog_sound (w := (96263 / 296263)) (n := 12)
    (lo := (67428541 / 100000000)) (hi := (674285411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196263 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196263 / 100000) = 1/(100000 / 196263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (67428541 / 100000000) (674285411 / 1000000000) (Real.log (196263 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (196263 / 100000) = -Real.log (100000 / 196263) := by
    rw [show ((196263 / 100000) : ℝ) = ((100000 / 196263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3286887033 / 1000000000) ≤ -Real.log (3737 / 100000) ∧
    -Real.log (3737 / 100000) ≤ (1643443519 / 500000000) := by
  have h := checkLog_sound (w := (2513 / 9987)) (n := 12)
    (lo := (514298313 / 1000000000)) (hi := (257149157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3737) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 3737) = 1/(3737 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1643443519 / 500000000) (-3286887033 / 1000000000) (Real.log (3737 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (792764181 / 200000000) ≤ -Real.log (312500000 / 16455669989) ∧
    -Real.log (312500000 / 16455669989) ≤ (3963820911 / 1000000000) := by
  have h := checkLog_sound (w := (6455669989 / 26455669989)) (n := 12)
    (lo := (99617001 / 200000000)) (hi := (249042503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16455669989 / 10000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16455669989 / 10000000000) = 1/(312500000 / 16455669989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (792764181 / 200000000) (3963820911 / 1000000000) (Real.log (16455669989 / 312500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (16455669989 / 312500000) = -Real.log (312500000 / 16455669989) := by
    rw [show ((16455669989 / 312500000) : ℝ) = ((312500000 / 16455669989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1985834657 / 500000000) ≤ -Real.log (100000000000 / 5307305269419) ∧
    -Real.log (100000000000 / 5307305269419) ≤ (99291733 / 25000000) := by
  have h := checkLog_sound (w := (2107305269419 / 8507305269419)) (n := 12)
    (lo := (252966707 / 500000000)) (hi := (101186683 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5307305269419 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5307305269419 / 3200000000000) = 1/(100000000000 / 5307305269419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1985834657 / 500000000) (99291733 / 25000000) (Real.log (5307305269419 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5307305269419 / 100000000000) = -Real.log (100000000000 / 5307305269419) := by
    rw [show ((5307305269419 / 100000000000) : ℝ) = ((100000000000 / 5307305269419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (790642641 / 200000000) ≤ -Real.log (125000000000 / 6512814300507) ∧
    -Real.log (125000000000 / 6512814300507) ≤ (3953213211 / 1000000000) := by
  have h := checkLog_sound (w := (2512814300507 / 10512814300507)) (n := 12)
    (lo := (97495461 / 200000000)) (hi := (243738653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6512814300507 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6512814300507 / 4000000000000) = 1/(125000000000 / 6512814300507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (790642641 / 200000000) (3953213211 / 1000000000) (Real.log (6512814300507 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6512814300507 / 125000000000) = -Real.log (125000000000 / 6512814300507) := by
    rw [show ((6512814300507 / 125000000000) : ℝ) = ((125000000000 / 6512814300507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3961172443 / 1000000000) ≤ -Real.log (500000000000 / 26259432700027) ∧
    -Real.log (500000000000 / 26259432700027) ≤ (3961172449 / 1000000000) := by
  have h := checkLog_sound (w := (10259432700027 / 42259432700027)) (n := 12)
    (lo := (495436543 / 1000000000)) (hi := (1935299 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26259432700027 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26259432700027 / 16000000000000) = 1/(500000000000 / 26259432700027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3961172443 / 1000000000) (3961172449 / 1000000000) (Real.log (26259432700027 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (26259432700027 / 500000000000) = -Real.log (500000000000 / 26259432700027) := by
    rw [show ((26259432700027 / 500000000000) : ℝ) = ((500000000000 / 26259432700027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0106

end


