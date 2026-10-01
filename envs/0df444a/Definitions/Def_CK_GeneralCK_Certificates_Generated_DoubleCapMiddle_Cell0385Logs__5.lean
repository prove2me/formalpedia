-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0385Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0385Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:33:09.466811+00:00
-- url     : https://prove2.me/theorems/9d749c2f-c7e7-4260-9eb4-f69f53d007a7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0385Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0386Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0385Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0386Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0387Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0388Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0389Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0385Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0386Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0387Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0388Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0389Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0385Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0386Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0387Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0388Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0389Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0385Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0386Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0387Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0388Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0389Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0385Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0385
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

theorem reflection_log_1_neg : (50954343 / 250000000) ≤ -Real.log (2048 / 2511) ∧
    -Real.log (2048 / 2511) ≤ (203817373 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 4559)) (n := 12)
    (lo := (50954343 / 250000000)) (hi := (203817373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2511 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2511 / 2048) = 1/(2048 / 2511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50954343 / 250000000) (203817373 / 1000000000) (Real.log (2511 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2511 / 2048) = -Real.log (2048 / 2511) := by
    rw [show ((2511 / 2048) : ℝ) = ((2048 / 2511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (256279299 / 1000000000) ≤ -Real.log (1585 / 2048) ∧
    -Real.log (1585 / 2048) ≤ (2562793 / 10000000) := by
  have h := checkLog_sound (w := (463 / 3633)) (n := 12)
    (lo := (256279299 / 1000000000)) (hi := (2562793 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1585) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1585) = 1/(1585 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2562793 / 10000000) (-256279299 / 1000000000) (Real.log (1585 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (40715679 / 200000000) ≤ -Real.log (1280 / 1569) ∧
    -Real.log (1280 / 1569) ≤ (50894599 / 250000000) := by
  have h := checkLog_sound (w := (289 / 2849)) (n := 12)
    (lo := (40715679 / 200000000)) (hi := (50894599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1569 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1569 / 1280) = 1/(1280 / 1569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (40715679 / 200000000) (50894599 / 250000000) (Real.log (1569 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1569 / 1280) = -Real.log (1280 / 1569) := by
    rw [show ((1569 / 1280) : ℝ) = ((1280 / 1569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (127950411 / 500000000) ≤ -Real.log (991 / 1280) ∧
    -Real.log (991 / 1280) ≤ (255900823 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 2271)) (n := 12)
    (lo := (127950411 / 500000000)) (hi := (255900823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 991) = 1/(991 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-255900823 / 1000000000) (-127950411 / 500000000) (Real.log (991 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18652207 / 50000000) ≤ -Real.log (1024 / 1487) ∧
    -Real.log (1024 / 1487) ≤ (373044141 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2511)) (n := 12)
    (lo := (18652207 / 50000000)) (hi := (373044141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1487 / 1024) = 1/(1024 / 1487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18652207 / 50000000) (373044141 / 1000000000) (Real.log (1487 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1487 / 1024) = -Real.log (1024 / 1487) := by
    rw [show ((1487 / 1024) : ℝ) = ((1024 / 1487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6017509 / 10000000) ≤ -Real.log (561 / 1024) ∧
    -Real.log (561 / 1024) ≤ (601750901 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 1585)) (n := 12)
    (lo := (6017509 / 10000000)) (hi := (601750901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 561) = 1/(561 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-601750901 / 1000000000) (-6017509 / 10000000) (Real.log (561 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (186320281 / 500000000) ≤ -Real.log (640 / 929) ∧
    -Real.log (640 / 929) ≤ (372640563 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 1569)) (n := 12)
    (lo := (186320281 / 500000000)) (hi := (372640563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929 / 640) = 1/(640 / 929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (186320281 / 500000000) (372640563 / 1000000000) (Real.log (929 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (929 / 640) = -Real.log (640 / 929) := by
    rw [show ((929 / 640) : ℝ) = ((640 / 929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (18771311 / 31250000) ≤ -Real.log (351 / 640) ∧
    -Real.log (351 / 640) ≤ (600681953 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 991)) (n := 12)
    (lo := (18771311 / 31250000)) (hi := (600681953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 351) = 1/(351 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-600681953 / 1000000000) (-18771311 / 31250000) (Real.log (351 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (11174089 / 40000000) ≤ -Real.log (1000000 / 1322273) ∧
    -Real.log (1000000 / 1322273) ≤ (139676113 / 500000000) := by
  have h := checkLog_sound (w := (322273 / 2322273)) (n := 12)
    (lo := (11174089 / 40000000)) (hi := (139676113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1322273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1322273 / 1000000) = 1/(1000000 / 1322273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (11174089 / 40000000) (139676113 / 500000000) (Real.log (1322273 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1322273 / 1000000) = -Real.log (1000000 / 1322273) := by
    rw [show ((1322273 / 1000000) : ℝ) = ((1000000 / 1322273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (194505363 / 500000000) ≤ -Real.log (677727 / 1000000) ∧
    -Real.log (677727 / 1000000) ≤ (389010727 / 1000000000) := by
  have h := checkLog_sound (w := (322273 / 1677727)) (n := 12)
    (lo := (194505363 / 500000000)) (hi := (389010727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 677727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 677727) = 1/(677727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-389010727 / 1000000000) (-194505363 / 500000000) (Real.log (677727 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (139837929 / 500000000) ≤ -Real.log (1000000 / 1322701) ∧
    -Real.log (1000000 / 1322701) ≤ (279675859 / 1000000000) := by
  have h := checkLog_sound (w := (322701 / 2322701)) (n := 12)
    (lo := (139837929 / 500000000)) (hi := (279675859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1322701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1322701 / 1000000) = 1/(1000000 / 1322701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (139837929 / 500000000) (279675859 / 1000000000) (Real.log (1322701 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1322701 / 1000000) = -Real.log (1000000 / 1322701) := by
    rw [show ((1322701 / 1000000) : ℝ) = ((1000000 / 1322701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (389642449 / 1000000000) ≤ -Real.log (677299 / 1000000) ∧
    -Real.log (677299 / 1000000) ≤ (7792849 / 20000000) := by
  have h := checkLog_sound (w := (322701 / 1677299)) (n := 12)
    (lo := (389642449 / 1000000000)) (hi := (7792849 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 677299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 677299) = 1/(677299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-7792849 / 20000000) (-389642449 / 1000000000) (Real.log (677299 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2107689 / 10000000) ≤ -Real.log (1000000 / 1234627) ∧
    -Real.log (1000000 / 1234627) ≤ (210768901 / 1000000000) := by
  have h := checkLog_sound (w := (234627 / 2234627)) (n := 12)
    (lo := (2107689 / 10000000)) (hi := (210768901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1234627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1234627 / 1000000) = 1/(1000000 / 1234627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2107689 / 10000000) (210768901 / 1000000000) (Real.log (1234627 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1234627 / 1000000) = -Real.log (1000000 / 1234627) := by
    rw [show ((1234627 / 1000000) : ℝ) = ((1000000 / 1234627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (133695991 / 500000000) ≤ -Real.log (765373 / 1000000) ∧
    -Real.log (765373 / 1000000) ≤ (267391983 / 1000000000) := by
  have h := checkLog_sound (w := (234627 / 1765373)) (n := 12)
    (lo := (133695991 / 500000000)) (hi := (267391983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 765373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 765373) = 1/(765373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-267391983 / 1000000000) (-133695991 / 500000000) (Real.log (765373 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (211036151 / 1000000000) ≤ -Real.log (1000000 / 1234957) ∧
    -Real.log (1000000 / 1234957) ≤ (26379519 / 125000000) := by
  have h := checkLog_sound (w := (234957 / 2234957)) (n := 12)
    (lo := (211036151 / 1000000000)) (hi := (26379519 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1234957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1234957 / 1000000) = 1/(1000000 / 1234957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (211036151 / 1000000000) (26379519 / 125000000) (Real.log (1234957 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1234957 / 1000000) = -Real.log (1000000 / 1234957) := by
    rw [show ((1234957 / 1000000) : ℝ) = ((1000000 / 1234957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (267823237 / 1000000000) ≤ -Real.log (765043 / 1000000) ∧
    -Real.log (765043 / 1000000) ≤ (133911619 / 500000000) := by
  have h := checkLog_sound (w := (234957 / 1765043)) (n := 12)
    (lo := (267823237 / 1000000000)) (hi := (133911619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 765043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 765043) = 1/(765043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-133911619 / 500000000) (-267823237 / 1000000000) (Real.log (765043 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (83545369 / 125000000) ≤ -Real.log (500000000000 / 975520379149) ∧
    -Real.log (500000000000 / 975520379149) ≤ (668362953 / 1000000000) := by
  have h := checkLog_sound (w := (475520379149 / 1475520379149)) (n := 12)
    (lo := (83545369 / 125000000)) (hi := (668362953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((975520379149 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(975520379149 / 500000000000) = 1/(500000000000 / 975520379149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (83545369 / 125000000) (668362953 / 1000000000) (Real.log (975520379149 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (975520379149 / 500000000000) = -Real.log (500000000000 / 975520379149) := by
    rw [show ((975520379149 / 500000000000) : ℝ) = ((500000000000 / 975520379149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (669318307 / 1000000000) ≤ -Real.log (500000000000 / 976452792637) ∧
    -Real.log (500000000000 / 976452792637) ≤ (167329577 / 250000000) := by
  have h := checkLog_sound (w := (476452792637 / 1476452792637)) (n := 12)
    (lo := (669318307 / 1000000000)) (hi := (167329577 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976452792637 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976452792637 / 500000000000) = 1/(500000000000 / 976452792637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (669318307 / 1000000000) (167329577 / 250000000) (Real.log (976452792637 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (976452792637 / 500000000000) = -Real.log (500000000000 / 976452792637) := by
    rw [show ((976452792637 / 500000000000) : ℝ) = ((500000000000 / 976452792637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (239080441 / 500000000) ≤ -Real.log (500000000000 / 806552491399) ∧
    -Real.log (500000000000 / 806552491399) ≤ (478160883 / 1000000000) := by
  have h := checkLog_sound (w := (306552491399 / 1306552491399)) (n := 12)
    (lo := (239080441 / 500000000)) (hi := (478160883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((806552491399 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(806552491399 / 500000000000) = 1/(500000000000 / 806552491399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (239080441 / 500000000) (478160883 / 1000000000) (Real.log (806552491399 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (806552491399 / 500000000000) = -Real.log (500000000000 / 806552491399) := by
    rw [show ((806552491399 / 500000000000) : ℝ) = ((500000000000 / 806552491399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (478859389 / 1000000000) ≤ -Real.log (2500000000 / 4035580353) ∧
    -Real.log (2500000000 / 4035580353) ≤ (47885939 / 100000000) := by
  have h := checkLog_sound (w := (1535580353 / 6535580353)) (n := 12)
    (lo := (478859389 / 1000000000)) (hi := (47885939 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4035580353 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4035580353 / 2500000000) = 1/(2500000000 / 4035580353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (478859389 / 1000000000) (47885939 / 100000000) (Real.log (4035580353 / 2500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4035580353 / 2500000000) = -Real.log (2500000000 / 4035580353) := by
    rw [show ((4035580353 / 2500000000) : ℝ) = ((2500000000 / 4035580353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0385

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0386Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0386
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

theorem reflection_log_1_neg : (40715679 / 200000000) ≤ -Real.log (1280 / 1569) ∧
    -Real.log (1280 / 1569) ≤ (50894599 / 250000000) := by
  have h := checkLog_sound (w := (289 / 2849)) (n := 12)
    (lo := (40715679 / 200000000)) (hi := (50894599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1569 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1569 / 1280) = 1/(1280 / 1569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (40715679 / 200000000) (50894599 / 250000000) (Real.log (1569 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1569 / 1280) = -Real.log (1280 / 1569) := by
    rw [show ((1569 / 1280) : ℝ) = ((1280 / 1569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (127950411 / 500000000) ≤ -Real.log (991 / 1280) ∧
    -Real.log (991 / 1280) ≤ (255900823 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 2271)) (n := 12)
    (lo := (127950411 / 500000000)) (hi := (255900823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 991) = 1/(991 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-255900823 / 1000000000) (-127950411 / 500000000) (Real.log (991 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (203339361 / 1000000000) ≤ -Real.log (10240 / 12549) ∧
    -Real.log (10240 / 12549) ≤ (101669681 / 500000000) := by
  have h := checkLog_sound (w := (2309 / 22789)) (n := 12)
    (lo := (203339361 / 1000000000)) (hi := (101669681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12549 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12549 / 10240) = 1/(10240 / 12549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (203339361 / 1000000000) (101669681 / 500000000) (Real.log (12549 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12549 / 10240) = -Real.log (10240 / 12549) := by
    rw [show ((12549 / 10240) : ℝ) = ((10240 / 12549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (31940311 / 125000000) ≤ -Real.log (7931 / 10240) ∧
    -Real.log (7931 / 10240) ≤ (255522489 / 1000000000) := by
  have h := checkLog_sound (w := (2309 / 18171)) (n := 12)
    (lo := (31940311 / 125000000)) (hi := (255522489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7931) = 1/(7931 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-255522489 / 1000000000) (-31940311 / 125000000) (Real.log (7931 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (186320281 / 500000000) ≤ -Real.log (640 / 929) ∧
    -Real.log (640 / 929) ≤ (372640563 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 1569)) (n := 12)
    (lo := (186320281 / 500000000)) (hi := (372640563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929 / 640) = 1/(640 / 929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (186320281 / 500000000) (372640563 / 1000000000) (Real.log (929 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (929 / 640) = -Real.log (640 / 929) := by
    rw [show ((929 / 640) : ℝ) = ((640 / 929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (18771311 / 31250000) ≤ -Real.log (351 / 640) ∧
    -Real.log (351 / 640) ≤ (600681953 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 991)) (n := 12)
    (lo := (18771311 / 31250000)) (hi := (600681953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 351) = 1/(351 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-600681953 / 1000000000) (-18771311 / 31250000) (Real.log (351 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (372236821 / 1000000000) ≤ -Real.log (5120 / 7429) ∧
    -Real.log (5120 / 7429) ≤ (186118411 / 500000000) := by
  have h := checkLog_sound (w := (2309 / 12549)) (n := 12)
    (lo := (372236821 / 1000000000)) (hi := (186118411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7429 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7429 / 5120) = 1/(5120 / 7429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (372236821 / 1000000000) (186118411 / 500000000) (Real.log (7429 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7429 / 5120) = -Real.log (5120 / 7429) := by
    rw [show ((7429 / 5120) : ℝ) = ((5120 / 7429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (599614147 / 1000000000) ≤ -Real.log (2811 / 5120) ∧
    -Real.log (2811 / 5120) ≤ (149903537 / 250000000) := by
  have h := checkLog_sound (w := (2309 / 7931)) (n := 12)
    (lo := (599614147 / 1000000000)) (hi := (149903537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2811) = 1/(2811 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-149903537 / 250000000) (-599614147 / 1000000000) (Real.log (2811 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27903 / 100000) ≤ -Real.log (1000000 / 1321847) ∧
    -Real.log (1000000 / 1321847) ≤ (279030001 / 1000000000) := by
  have h := checkLog_sound (w := (321847 / 2321847)) (n := 12)
    (lo := (27903 / 100000)) (hi := (279030001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321847 / 1000000) = 1/(1000000 / 1321847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27903 / 100000) (279030001 / 1000000000) (Real.log (1321847 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1321847 / 1000000) = -Real.log (1000000 / 1321847) := by
    rw [show ((1321847 / 1000000) : ℝ) = ((1000000 / 1321847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (24273897 / 62500000) ≤ -Real.log (678153 / 1000000) ∧
    -Real.log (678153 / 1000000) ≤ (388382353 / 1000000000) := by
  have h := checkLog_sound (w := (321847 / 1678153)) (n := 12)
    (lo := (24273897 / 62500000)) (hi := (388382353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 678153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 678153) = 1/(678153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-388382353 / 1000000000) (-24273897 / 62500000) (Real.log (678153 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (279352981 / 1000000000) ≤ -Real.log (500000 / 661137) ∧
    -Real.log (500000 / 661137) ≤ (139676491 / 500000000) := by
  have h := checkLog_sound (w := (161137 / 1161137)) (n := 12)
    (lo := (279352981 / 1000000000)) (hi := (139676491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661137 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661137 / 500000) = 1/(500000 / 661137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (279352981 / 1000000000) (139676491 / 500000000) (Real.log (661137 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (661137 / 500000) = -Real.log (500000 / 661137) := by
    rw [show ((661137 / 500000) : ℝ) = ((500000 / 661137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (194506101 / 500000000) ≤ -Real.log (338863 / 500000) ∧
    -Real.log (338863 / 500000) ≤ (389012203 / 1000000000) := by
  have h := checkLog_sound (w := (161137 / 838863)) (n := 12)
    (lo := (194506101 / 500000000)) (hi := (389012203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 338863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 338863) = 1/(338863 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-389012203 / 1000000000) (-194506101 / 500000000) (Real.log (338863 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (210502387 / 1000000000) ≤ -Real.log (500000 / 617149) ∧
    -Real.log (500000 / 617149) ≤ (52625597 / 250000000) := by
  have h := checkLog_sound (w := (117149 / 1117149)) (n := 12)
    (lo := (210502387 / 1000000000)) (hi := (52625597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(617149 / 500000) = 1/(500000 / 617149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (210502387 / 1000000000) (52625597 / 250000000) (Real.log (617149 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (617149 / 500000) = -Real.log (500000 / 617149) := by
    rw [show ((617149 / 500000) : ℝ) = ((500000 / 617149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (133481109 / 500000000) ≤ -Real.log (382851 / 500000) ∧
    -Real.log (382851 / 500000) ≤ (266962219 / 1000000000) := by
  have h := checkLog_sound (w := (117149 / 882851)) (n := 12)
    (lo := (133481109 / 500000000)) (hi := (266962219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 382851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 382851) = 1/(382851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-266962219 / 1000000000) (-133481109 / 500000000) (Real.log (382851 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21076971 / 100000000) ≤ -Real.log (250000 / 308657) ∧
    -Real.log (250000 / 308657) ≤ (210769711 / 1000000000) := by
  have h := checkLog_sound (w := (58657 / 558657)) (n := 12)
    (lo := (21076971 / 100000000)) (hi := (210769711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308657 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308657 / 250000) = 1/(250000 / 308657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21076971 / 100000000) (210769711 / 1000000000) (Real.log (308657 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (308657 / 250000) = -Real.log (250000 / 308657) := by
    rw [show ((308657 / 250000) : ℝ) = ((250000 / 308657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (33424161 / 125000000) ≤ -Real.log (191343 / 250000) ∧
    -Real.log (191343 / 250000) ≤ (267393289 / 1000000000) := by
  have h := checkLog_sound (w := (58657 / 441343)) (n := 12)
    (lo := (33424161 / 125000000)) (hi := (267393289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191343) = 1/(191343 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-267393289 / 1000000000) (-33424161 / 125000000) (Real.log (191343 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (667412353 / 1000000000) ≤ -Real.log (500000000000 / 974593491439) ∧
    -Real.log (500000000000 / 974593491439) ≤ (333706177 / 500000000) := by
  have h := checkLog_sound (w := (474593491439 / 1474593491439)) (n := 12)
    (lo := (667412353 / 1000000000)) (hi := (333706177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974593491439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974593491439 / 500000000000) = 1/(500000000000 / 974593491439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (667412353 / 1000000000) (333706177 / 500000000) (Real.log (974593491439 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (974593491439 / 500000000000) = -Real.log (500000000000 / 974593491439) := by
    rw [show ((974593491439 / 500000000000) : ℝ) = ((500000000000 / 974593491439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (5221603 / 7812500) ≤ -Real.log (250000000000 / 487761278157) ∧
    -Real.log (250000000000 / 487761278157) ≤ (133673037 / 200000000) := by
  have h := checkLog_sound (w := (237761278157 / 737761278157)) (n := 12)
    (lo := (5221603 / 7812500)) (hi := (133673037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487761278157 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487761278157 / 250000000000) = 1/(250000000000 / 487761278157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (5221603 / 7812500) (133673037 / 200000000) (Real.log (487761278157 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (487761278157 / 250000000000) = -Real.log (250000000000 / 487761278157) := by
    rw [show ((487761278157 / 250000000000) : ℝ) = ((250000000000 / 487761278157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (238732303 / 500000000) ≤ -Real.log (125000000000 / 201497775897) ∧
    -Real.log (125000000000 / 201497775897) ≤ (477464607 / 1000000000) := by
  have h := checkLog_sound (w := (76497775897 / 326497775897)) (n := 12)
    (lo := (238732303 / 500000000)) (hi := (477464607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201497775897 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201497775897 / 125000000000) = 1/(125000000000 / 201497775897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (238732303 / 500000000) (477464607 / 1000000000) (Real.log (201497775897 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (201497775897 / 125000000000) = -Real.log (125000000000 / 201497775897) := by
    rw [show ((201497775897 / 125000000000) : ℝ) = ((125000000000 / 201497775897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (239081499 / 500000000) ≤ -Real.log (250000000000 / 403277099241) ∧
    -Real.log (250000000000 / 403277099241) ≤ (478162999 / 1000000000) := by
  have h := checkLog_sound (w := (153277099241 / 653277099241)) (n := 12)
    (lo := (239081499 / 500000000)) (hi := (478162999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403277099241 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403277099241 / 250000000000) = 1/(250000000000 / 403277099241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (239081499 / 500000000) (478162999 / 1000000000) (Real.log (403277099241 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (403277099241 / 250000000000) = -Real.log (250000000000 / 403277099241) := by
    rw [show ((403277099241 / 250000000000) : ℝ) = ((250000000000 / 403277099241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0386

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0387Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0387
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

theorem reflection_log_1_neg : (203339361 / 1000000000) ≤ -Real.log (10240 / 12549) ∧
    -Real.log (10240 / 12549) ≤ (101669681 / 500000000) := by
  have h := checkLog_sound (w := (2309 / 22789)) (n := 12)
    (lo := (203339361 / 1000000000)) (hi := (101669681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12549 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12549 / 10240) = 1/(10240 / 12549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (203339361 / 1000000000) (101669681 / 500000000) (Real.log (12549 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12549 / 10240) = -Real.log (10240 / 12549) := by
    rw [show ((12549 / 10240) : ℝ) = ((10240 / 12549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (31940311 / 125000000) ≤ -Real.log (7931 / 10240) ∧
    -Real.log (7931 / 10240) ≤ (255522489 / 1000000000) := by
  have h := checkLog_sound (w := (2309 / 18171)) (n := 12)
    (lo := (31940311 / 125000000)) (hi := (255522489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7931) = 1/(7931 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-255522489 / 1000000000) (-31940311 / 125000000) (Real.log (7931 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20310027 / 100000000) ≤ -Real.log (5120 / 6273) ∧
    -Real.log (5120 / 6273) ≤ (203100271 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 11393)) (n := 12)
    (lo := (20310027 / 100000000)) (hi := (203100271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6273 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6273 / 5120) = 1/(5120 / 6273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20310027 / 100000000) (203100271 / 1000000000) (Real.log (6273 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6273 / 5120) = -Real.log (5120 / 6273) := by
    rw [show ((6273 / 5120) : ℝ) = ((5120 / 6273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (255144297 / 1000000000) ≤ -Real.log (3967 / 5120) ∧
    -Real.log (3967 / 5120) ≤ (127572149 / 500000000) := by
  have h := checkLog_sound (w := (1153 / 9087)) (n := 12)
    (lo := (255144297 / 1000000000)) (hi := (127572149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3967) = 1/(3967 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-127572149 / 500000000) (-255144297 / 1000000000) (Real.log (3967 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (372236821 / 1000000000) ≤ -Real.log (5120 / 7429) ∧
    -Real.log (5120 / 7429) ≤ (186118411 / 500000000) := by
  have h := checkLog_sound (w := (2309 / 12549)) (n := 12)
    (lo := (372236821 / 1000000000)) (hi := (186118411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7429 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7429 / 5120) = 1/(5120 / 7429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (372236821 / 1000000000) (186118411 / 500000000) (Real.log (7429 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7429 / 5120) = -Real.log (5120 / 7429) := by
    rw [show ((7429 / 5120) : ℝ) = ((5120 / 7429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (599614147 / 1000000000) ≤ -Real.log (2811 / 5120) ∧
    -Real.log (2811 / 5120) ≤ (149903537 / 250000000) := by
  have h := checkLog_sound (w := (2309 / 7931)) (n := 12)
    (lo := (599614147 / 1000000000)) (hi := (149903537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2811) = 1/(2811 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-149903537 / 250000000) (-599614147 / 1000000000) (Real.log (2811 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (92958229 / 250000000) ≤ -Real.log (2560 / 3713) ∧
    -Real.log (2560 / 3713) ≤ (371832917 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 6273)) (n := 12)
    (lo := (92958229 / 250000000)) (hi := (371832917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3713 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3713 / 2560) = 1/(2560 / 3713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (92958229 / 250000000) (371832917 / 1000000000) (Real.log (3713 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3713 / 2560) = -Real.log (2560 / 3713) := by
    rw [show ((3713 / 2560) : ℝ) = ((2560 / 3713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (14963687 / 25000000) ≤ -Real.log (1407 / 2560) ∧
    -Real.log (1407 / 2560) ≤ (598547481 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 3967)) (n := 12)
    (lo := (14963687 / 25000000)) (hi := (598547481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1407) = 1/(1407 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-598547481 / 1000000000) (-14963687 / 25000000) (Real.log (1407 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (55741383 / 200000000) ≤ -Real.log (50000 / 66071) ∧
    -Real.log (50000 / 66071) ≤ (69676729 / 250000000) := by
  have h := checkLog_sound (w := (16071 / 116071)) (n := 12)
    (lo := (55741383 / 200000000)) (hi := (69676729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66071 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66071 / 50000) = 1/(50000 / 66071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (55741383 / 200000000) (69676729 / 250000000) (Real.log (66071 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (66071 / 50000) = -Real.log (50000 / 66071) := by
    rw [show ((66071 / 50000) : ℝ) = ((50000 / 66071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (387752899 / 1000000000) ≤ -Real.log (33929 / 50000) ∧
    -Real.log (33929 / 50000) ≤ (3877529 / 10000000) := by
  have h := checkLog_sound (w := (16071 / 83929)) (n := 12)
    (lo := (387752899 / 1000000000)) (hi := (3877529 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33929) = 1/(33929 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3877529 / 10000000) (-387752899 / 1000000000) (Real.log (33929 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (279030757 / 1000000000) ≤ -Real.log (125000 / 165231) ∧
    -Real.log (125000 / 165231) ≤ (139515379 / 500000000) := by
  have h := checkLog_sound (w := (40231 / 290231)) (n := 12)
    (lo := (279030757 / 1000000000)) (hi := (139515379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165231 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165231 / 125000) = 1/(125000 / 165231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (279030757 / 1000000000) (139515379 / 500000000) (Real.log (165231 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (165231 / 125000) = -Real.log (125000 / 165231) := by
    rw [show ((165231 / 125000) : ℝ) = ((125000 / 165231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (388383827 / 1000000000) ≤ -Real.log (84769 / 125000) ∧
    -Real.log (84769 / 125000) ≤ (97095957 / 250000000) := by
  have h := checkLog_sound (w := (40231 / 209769)) (n := 12)
    (lo := (388383827 / 1000000000)) (hi := (97095957 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84769) = 1/(84769 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-97095957 / 250000000) (-388383827 / 1000000000) (Real.log (84769 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (210235803 / 1000000000) ≤ -Real.log (1000000 / 1233969) ∧
    -Real.log (1000000 / 1233969) ≤ (52558951 / 250000000) := by
  have h := checkLog_sound (w := (233969 / 2233969)) (n := 12)
    (lo := (210235803 / 1000000000)) (hi := (52558951 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233969 / 1000000) = 1/(1000000 / 1233969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (210235803 / 1000000000) (52558951 / 250000000) (Real.log (1233969 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1233969 / 1000000) = -Real.log (1000000 / 1233969) := by
    rw [show ((1233969 / 1000000) : ℝ) = ((1000000 / 1233969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1665829 / 6250000) ≤ -Real.log (766031 / 1000000) ∧
    -Real.log (766031 / 1000000) ≤ (266532641 / 1000000000) := by
  have h := checkLog_sound (w := (233969 / 1766031)) (n := 12)
    (lo := (1665829 / 6250000)) (hi := (266532641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766031) = 1/(766031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-266532641 / 1000000000) (-1665829 / 6250000) (Real.log (766031 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (210503197 / 1000000000) ≤ -Real.log (1000000 / 1234299) ∧
    -Real.log (1000000 / 1234299) ≤ (105251599 / 500000000) := by
  have h := checkLog_sound (w := (234299 / 2234299)) (n := 12)
    (lo := (210503197 / 1000000000)) (hi := (105251599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1234299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1234299 / 1000000) = 1/(1000000 / 1234299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (210503197 / 1000000000) (105251599 / 500000000) (Real.log (1234299 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1234299 / 1000000) = -Real.log (1000000 / 1234299) := by
    rw [show ((1234299 / 1000000) : ℝ) = ((1000000 / 1234299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (66740881 / 250000000) ≤ -Real.log (765701 / 1000000) ∧
    -Real.log (765701 / 1000000) ≤ (10678541 / 40000000) := by
  have h := checkLog_sound (w := (234299 / 1765701)) (n := 12)
    (lo := (66740881 / 250000000)) (hi := (10678541 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 765701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 765701) = 1/(765701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-10678541 / 40000000) (-66740881 / 250000000) (Real.log (765701 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (133291963 / 200000000) ≤ -Real.log (500000000000 / 973665595803) ∧
    -Real.log (500000000000 / 973665595803) ≤ (83307477 / 125000000) := by
  have h := checkLog_sound (w := (473665595803 / 1473665595803)) (n := 12)
    (lo := (133291963 / 200000000)) (hi := (83307477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973665595803 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973665595803 / 500000000000) = 1/(500000000000 / 973665595803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (133291963 / 200000000) (83307477 / 125000000) (Real.log (973665595803 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (973665595803 / 500000000000) = -Real.log (500000000000 / 973665595803) := by
    rw [show ((973665595803 / 500000000000) : ℝ) = ((500000000000 / 973665595803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (83426823 / 125000000) ≤ -Real.log (500000000000 / 974595665869) ∧
    -Real.log (500000000000 / 974595665869) ≤ (133482917 / 200000000) := by
  have h := checkLog_sound (w := (474595665869 / 1474595665869)) (n := 12)
    (lo := (83426823 / 125000000)) (hi := (133482917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974595665869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974595665869 / 500000000000) = 1/(500000000000 / 974595665869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (83426823 / 125000000) (133482917 / 200000000) (Real.log (974595665869 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (974595665869 / 500000000000) = -Real.log (500000000000 / 974595665869) := by
    rw [show ((974595665869 / 500000000000) : ℝ) = ((500000000000 / 974595665869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (476768443 / 1000000000) ≤ -Real.log (250000000000 / 402715098997) ∧
    -Real.log (250000000000 / 402715098997) ≤ (119192111 / 250000000) := by
  have h := checkLog_sound (w := (152715098997 / 652715098997)) (n := 12)
    (lo := (476768443 / 1000000000)) (hi := (119192111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((402715098997 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(402715098997 / 250000000000) = 1/(250000000000 / 402715098997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (476768443 / 1000000000) (119192111 / 250000000) (Real.log (402715098997 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (402715098997 / 250000000000) = -Real.log (250000000000 / 402715098997) := by
    rw [show ((402715098997 / 250000000000) : ℝ) = ((250000000000 / 402715098997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (238733361 / 500000000) ≤ -Real.log (125000000000 / 201498202301) ∧
    -Real.log (125000000000 / 201498202301) ≤ (477466723 / 1000000000) := by
  have h := checkLog_sound (w := (76498202301 / 326498202301)) (n := 12)
    (lo := (238733361 / 500000000)) (hi := (477466723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201498202301 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201498202301 / 125000000000) = 1/(125000000000 / 201498202301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (238733361 / 500000000) (477466723 / 1000000000) (Real.log (201498202301 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (201498202301 / 125000000000) = -Real.log (125000000000 / 201498202301) := by
    rw [show ((201498202301 / 125000000000) : ℝ) = ((125000000000 / 201498202301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0387

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0388Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0388
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

theorem reflection_log_1_neg : (20310027 / 100000000) ≤ -Real.log (5120 / 6273) ∧
    -Real.log (5120 / 6273) ≤ (203100271 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 11393)) (n := 12)
    (lo := (20310027 / 100000000)) (hi := (203100271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6273 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6273 / 5120) = 1/(5120 / 6273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20310027 / 100000000) (203100271 / 1000000000) (Real.log (6273 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6273 / 5120) = -Real.log (5120 / 6273) := by
    rw [show ((6273 / 5120) : ℝ) = ((5120 / 6273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (255144297 / 1000000000) ≤ -Real.log (3967 / 5120) ∧
    -Real.log (3967 / 5120) ≤ (127572149 / 500000000) := by
  have h := checkLog_sound (w := (1153 / 9087)) (n := 12)
    (lo := (255144297 / 1000000000)) (hi := (127572149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3967) = 1/(3967 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-127572149 / 500000000) (-255144297 / 1000000000) (Real.log (3967 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (202861121 / 1000000000) ≤ -Real.log (10240 / 12543) ∧
    -Real.log (10240 / 12543) ≤ (101430561 / 500000000) := by
  have h := checkLog_sound (w := (2303 / 22783)) (n := 12)
    (lo := (202861121 / 1000000000)) (hi := (101430561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12543 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12543 / 10240) = 1/(10240 / 12543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (202861121 / 1000000000) (101430561 / 500000000) (Real.log (12543 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12543 / 10240) = -Real.log (10240 / 12543) := by
    rw [show ((12543 / 10240) : ℝ) = ((10240 / 12543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (254766249 / 1000000000) ≤ -Real.log (7937 / 10240) ∧
    -Real.log (7937 / 10240) ≤ (203813 / 800000) := by
  have h := checkLog_sound (w := (2303 / 18177)) (n := 12)
    (lo := (254766249 / 1000000000)) (hi := (203813 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7937) = 1/(7937 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-203813 / 800000) (-254766249 / 1000000000) (Real.log (7937 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (92958229 / 250000000) ≤ -Real.log (2560 / 3713) ∧
    -Real.log (2560 / 3713) ≤ (371832917 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 6273)) (n := 12)
    (lo := (92958229 / 250000000)) (hi := (371832917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3713 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3713 / 2560) = 1/(2560 / 3713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (92958229 / 250000000) (371832917 / 1000000000) (Real.log (3713 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3713 / 2560) = -Real.log (2560 / 3713) := by
    rw [show ((3713 / 2560) : ℝ) = ((2560 / 3713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (14963687 / 25000000) ≤ -Real.log (1407 / 2560) ∧
    -Real.log (1407 / 2560) ≤ (598547481 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 3967)) (n := 12)
    (lo := (14963687 / 25000000)) (hi := (598547481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1407) = 1/(1407 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-598547481 / 1000000000) (-14963687 / 25000000) (Real.log (1407 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (371428849 / 1000000000) ≤ -Real.log (5120 / 7423) ∧
    -Real.log (5120 / 7423) ≤ (7428577 / 20000000) := by
  have h := checkLog_sound (w := (2303 / 12543)) (n := 12)
    (lo := (371428849 / 1000000000)) (hi := (7428577 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7423 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7423 / 5120) = 1/(5120 / 7423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (371428849 / 1000000000) (7428577 / 20000000) (Real.log (7423 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7423 / 5120) = -Real.log (5120 / 7423) := by
    rw [show ((7423 / 5120) : ℝ) = ((5120 / 7423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (11949639 / 20000000) ≤ -Real.log (2817 / 5120) ∧
    -Real.log (2817 / 5120) ≤ (597481951 / 1000000000) := by
  have h := checkLog_sound (w := (2303 / 7937)) (n := 12)
    (lo := (11949639 / 20000000)) (hi := (597481951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2817) = 1/(2817 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-597481951 / 1000000000) (-11949639 / 20000000) (Real.log (2817 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139191863 / 500000000) ≤ -Real.log (1000000 / 1320993) ∧
    -Real.log (1000000 / 1320993) ≤ (278383727 / 1000000000) := by
  have h := checkLog_sound (w := (320993 / 2320993)) (n := 12)
    (lo := (139191863 / 500000000)) (hi := (278383727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1320993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1320993 / 1000000) = 1/(1000000 / 1320993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139191863 / 500000000) (278383727 / 1000000000) (Real.log (1320993 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1320993 / 1000000) = -Real.log (1000000 / 1320993) := by
    rw [show ((1320993 / 1000000) : ℝ) = ((1000000 / 1320993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (193561921 / 500000000) ≤ -Real.log (679007 / 1000000) ∧
    -Real.log (679007 / 1000000) ≤ (387123843 / 1000000000) := by
  have h := checkLog_sound (w := (320993 / 1679007)) (n := 12)
    (lo := (193561921 / 500000000)) (hi := (387123843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 679007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 679007) = 1/(679007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-387123843 / 1000000000) (-193561921 / 500000000) (Real.log (679007 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34838459 / 125000000) ≤ -Real.log (1000000 / 1321421) ∧
    -Real.log (1000000 / 1321421) ≤ (278707673 / 1000000000) := by
  have h := checkLog_sound (w := (321421 / 2321421)) (n := 12)
    (lo := (34838459 / 125000000)) (hi := (278707673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321421 / 1000000) = 1/(1000000 / 1321421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34838459 / 125000000) (278707673 / 1000000000) (Real.log (1321421 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1321421 / 1000000) = -Real.log (1000000 / 1321421) := by
    rw [show ((1321421 / 1000000) : ℝ) = ((1000000 / 1321421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (387754373 / 1000000000) ≤ -Real.log (678579 / 1000000) ∧
    -Real.log (678579 / 1000000) ≤ (193877187 / 500000000) := by
  have h := checkLog_sound (w := (321421 / 1678579)) (n := 12)
    (lo := (387754373 / 1000000000)) (hi := (193877187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 678579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 678579) = 1/(678579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-193877187 / 500000000) (-387754373 / 1000000000) (Real.log (678579 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (52492287 / 250000000) ≤ -Real.log (25000 / 30841) ∧
    -Real.log (25000 / 30841) ≤ (209969149 / 1000000000) := by
  have h := checkLog_sound (w := (5841 / 55841)) (n := 12)
    (lo := (52492287 / 250000000)) (hi := (209969149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30841 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30841 / 25000) = 1/(25000 / 30841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (52492287 / 250000000) (209969149 / 1000000000) (Real.log (30841 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (30841 / 25000) = -Real.log (25000 / 30841) := by
    rw [show ((30841 / 25000) : ℝ) = ((25000 / 30841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (53220649 / 200000000) ≤ -Real.log (19159 / 25000) ∧
    -Real.log (19159 / 25000) ≤ (133051623 / 500000000) := by
  have h := checkLog_sound (w := (5841 / 44159)) (n := 12)
    (lo := (53220649 / 200000000)) (hi := (133051623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19159) = 1/(19159 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-133051623 / 500000000) (-53220649 / 200000000) (Real.log (19159 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (105118307 / 500000000) ≤ -Real.log (100000 / 123397) ∧
    -Real.log (100000 / 123397) ≤ (42047323 / 200000000) := by
  have h := checkLog_sound (w := (23397 / 223397)) (n := 12)
    (lo := (105118307 / 500000000)) (hi := (42047323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123397 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123397 / 100000) = 1/(100000 / 123397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (105118307 / 500000000) (42047323 / 200000000) (Real.log (123397 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (123397 / 100000) = -Real.log (100000 / 123397) := by
    rw [show ((123397 / 100000) : ℝ) = ((100000 / 123397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53306789 / 200000000) ≤ -Real.log (76603 / 100000) ∧
    -Real.log (76603 / 100000) ≤ (133266973 / 500000000) := by
  have h := checkLog_sound (w := (23397 / 176603)) (n := 12)
    (lo := (53306789 / 200000000)) (hi := (133266973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76603) = 1/(76603 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-133266973 / 500000000) (-53306789 / 200000000) (Real.log (76603 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (41594223 / 62500000) ≤ -Real.log (250000000000 / 486369433599) ∧
    -Real.log (250000000000 / 486369433599) ≤ (665507569 / 1000000000) := by
  have h := checkLog_sound (w := (236369433599 / 736369433599)) (n := 12)
    (lo := (41594223 / 62500000)) (hi := (665507569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486369433599 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486369433599 / 250000000000) = 1/(250000000000 / 486369433599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (41594223 / 62500000) (665507569 / 1000000000) (Real.log (486369433599 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (486369433599 / 250000000000) = -Real.log (250000000000 / 486369433599) := by
    rw [show ((486369433599 / 250000000000) : ℝ) = ((250000000000 / 486369433599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (133292409 / 200000000) ≤ -Real.log (500000000000 / 973667767497) ∧
    -Real.log (500000000000 / 973667767497) ≤ (333231023 / 500000000) := by
  have h := checkLog_sound (w := (473667767497 / 1473667767497)) (n := 12)
    (lo := (133292409 / 200000000)) (hi := (333231023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973667767497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973667767497 / 500000000000) = 1/(500000000000 / 973667767497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (133292409 / 200000000) (333231023 / 500000000) (Real.log (973667767497 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (973667767497 / 500000000000) = -Real.log (500000000000 / 973667767497) := by
    rw [show ((973667767497 / 500000000000) : ℝ) = ((500000000000 / 973667767497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (238036197 / 500000000) ≤ -Real.log (125000000000 / 201217443499) ∧
    -Real.log (125000000000 / 201217443499) ≤ (95214479 / 200000000) := by
  have h := checkLog_sound (w := (76217443499 / 326217443499)) (n := 12)
    (lo := (238036197 / 500000000)) (hi := (95214479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201217443499 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201217443499 / 125000000000) = 1/(125000000000 / 201217443499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (238036197 / 500000000) (95214479 / 200000000) (Real.log (201217443499 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (201217443499 / 125000000000) = -Real.log (125000000000 / 201217443499) := by
    rw [show ((201217443499 / 125000000000) : ℝ) = ((125000000000 / 201217443499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (476770559 / 1000000000) ≤ -Real.log (100000000000 / 161086380429) ∧
    -Real.log (100000000000 / 161086380429) ≤ (372477 / 781250) := by
  have h := checkLog_sound (w := (61086380429 / 261086380429)) (n := 12)
    (lo := (476770559 / 1000000000)) (hi := (372477 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161086380429 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161086380429 / 100000000000) = 1/(100000000000 / 161086380429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (476770559 / 1000000000) (372477 / 781250) (Real.log (161086380429 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (161086380429 / 100000000000) = -Real.log (100000000000 / 161086380429) := by
    rw [show ((161086380429 / 100000000000) : ℝ) = ((100000000000 / 161086380429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0388

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0389Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0389
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

theorem reflection_log_1_neg : (202861121 / 1000000000) ≤ -Real.log (10240 / 12543) ∧
    -Real.log (10240 / 12543) ≤ (101430561 / 500000000) := by
  have h := checkLog_sound (w := (2303 / 22783)) (n := 12)
    (lo := (202861121 / 1000000000)) (hi := (101430561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12543 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12543 / 10240) = 1/(10240 / 12543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (202861121 / 1000000000) (101430561 / 500000000) (Real.log (12543 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12543 / 10240) = -Real.log (10240 / 12543) := by
    rw [show ((12543 / 10240) : ℝ) = ((10240 / 12543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (254766249 / 1000000000) ≤ -Real.log (7937 / 10240) ∧
    -Real.log (7937 / 10240) ≤ (203813 / 800000) := by
  have h := checkLog_sound (w := (2303 / 18177)) (n := 12)
    (lo := (254766249 / 1000000000)) (hi := (203813 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7937) = 1/(7937 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-203813 / 800000) (-254766249 / 1000000000) (Real.log (7937 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (40524383 / 200000000) ≤ -Real.log (512 / 627) ∧
    -Real.log (512 / 627) ≤ (50655479 / 250000000) := by
  have h := checkLog_sound (w := (115 / 1139)) (n := 12)
    (lo := (40524383 / 200000000)) (hi := (50655479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627 / 512) = 1/(512 / 627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (40524383 / 200000000) (50655479 / 250000000) (Real.log (627 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (627 / 512) = -Real.log (512 / 627) := by
    rw [show ((627 / 512) : ℝ) = ((512 / 627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (31798543 / 125000000) ≤ -Real.log (397 / 512) ∧
    -Real.log (397 / 512) ≤ (50877669 / 200000000) := by
  have h := checkLog_sound (w := (115 / 909)) (n := 12)
    (lo := (31798543 / 125000000)) (hi := (50877669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 397) = 1/(397 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-50877669 / 200000000) (-31798543 / 125000000) (Real.log (397 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (371428849 / 1000000000) ≤ -Real.log (5120 / 7423) ∧
    -Real.log (5120 / 7423) ≤ (7428577 / 20000000) := by
  have h := checkLog_sound (w := (2303 / 12543)) (n := 12)
    (lo := (371428849 / 1000000000)) (hi := (7428577 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7423 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7423 / 5120) = 1/(5120 / 7423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (371428849 / 1000000000) (7428577 / 20000000) (Real.log (7423 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7423 / 5120) = -Real.log (5120 / 7423) := by
    rw [show ((7423 / 5120) : ℝ) = ((5120 / 7423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (11949639 / 20000000) ≤ -Real.log (2817 / 5120) ∧
    -Real.log (2817 / 5120) ≤ (597481951 / 1000000000) := by
  have h := checkLog_sound (w := (2303 / 7937)) (n := 12)
    (lo := (11949639 / 20000000)) (hi := (597481951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2817) = 1/(2817 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-597481951 / 1000000000) (-11949639 / 20000000) (Real.log (2817 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (185512309 / 500000000) ≤ -Real.log (256 / 371) ∧
    -Real.log (256 / 371) ≤ (371024619 / 1000000000) := by
  have h := checkLog_sound (w := (115 / 627)) (n := 12)
    (lo := (185512309 / 500000000)) (hi := (371024619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371 / 256) = 1/(256 / 371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (185512309 / 500000000) (371024619 / 1000000000) (Real.log (371 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (371 / 256) = -Real.log (256 / 371) := by
    rw [show ((371 / 256) : ℝ) = ((256 / 371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (298208777 / 500000000) ≤ -Real.log (141 / 256) ∧
    -Real.log (141 / 256) ≤ (119283511 / 200000000) := by
  have h := checkLog_sound (w := (115 / 397)) (n := 12)
    (lo := (298208777 / 500000000)) (hi := (119283511 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 141) = 1/(141 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-119283511 / 200000000) (-298208777 / 500000000) (Real.log (141 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (278061189 / 1000000000) ≤ -Real.log (1000000 / 1320567) ∧
    -Real.log (1000000 / 1320567) ≤ (27806119 / 100000000) := by
  have h := checkLog_sound (w := (320567 / 2320567)) (n := 12)
    (lo := (278061189 / 1000000000)) (hi := (27806119 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1320567 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1320567 / 1000000) = 1/(1000000 / 1320567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (278061189 / 1000000000) (27806119 / 100000000) (Real.log (1320567 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1320567 / 1000000) = -Real.log (1000000 / 1320567) := by
    rw [show ((1320567 / 1000000) : ℝ) = ((1000000 / 1320567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (96624163 / 250000000) ≤ -Real.log (679433 / 1000000) ∧
    -Real.log (679433 / 1000000) ≤ (386496653 / 1000000000) := by
  have h := checkLog_sound (w := (320567 / 1679433)) (n := 12)
    (lo := (96624163 / 250000000)) (hi := (386496653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 679433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 679433) = 1/(679433 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-386496653 / 1000000000) (-96624163 / 250000000) (Real.log (679433 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (278384483 / 1000000000) ≤ -Real.log (500000 / 660497) ∧
    -Real.log (500000 / 660497) ≤ (69596121 / 250000000) := by
  have h := checkLog_sound (w := (160497 / 1160497)) (n := 12)
    (lo := (278384483 / 1000000000)) (hi := (69596121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660497 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660497 / 500000) = 1/(500000 / 660497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (278384483 / 1000000000) (69596121 / 250000000) (Real.log (660497 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (660497 / 500000) = -Real.log (500000 / 660497) := by
    rw [show ((660497 / 500000) : ℝ) = ((500000 / 660497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (193562657 / 500000000) ≤ -Real.log (339503 / 500000) ∧
    -Real.log (339503 / 500000) ≤ (77425063 / 200000000) := by
  have h := checkLog_sound (w := (160497 / 839503)) (n := 12)
    (lo := (193562657 / 500000000)) (hi := (77425063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 339503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 339503) = 1/(339503 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-77425063 / 200000000) (-193562657 / 500000000) (Real.log (339503 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (209703233 / 1000000000) ≤ -Real.log (31250 / 38541) ∧
    -Real.log (31250 / 38541) ≤ (104851617 / 500000000) := by
  have h := checkLog_sound (w := (7291 / 69791)) (n := 12)
    (lo := (209703233 / 1000000000)) (hi := (104851617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38541 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38541 / 31250) = 1/(31250 / 38541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (209703233 / 1000000000) (104851617 / 500000000) (Real.log (38541 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (38541 / 31250) = -Real.log (31250 / 38541) := by
    rw [show ((38541 / 31250) : ℝ) = ((31250 / 38541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (13283767 / 50000000) ≤ -Real.log (23959 / 31250) ∧
    -Real.log (23959 / 31250) ≤ (265675341 / 1000000000) := by
  have h := checkLog_sound (w := (7291 / 55209)) (n := 12)
    (lo := (13283767 / 50000000)) (hi := (265675341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23959) = 1/(23959 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-265675341 / 1000000000) (-13283767 / 50000000) (Real.log (23959 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (209969959 / 1000000000) ≤ -Real.log (1000000 / 1233641) ∧
    -Real.log (1000000 / 1233641) ≤ (5249249 / 25000000) := by
  have h := checkLog_sound (w := (233641 / 2233641)) (n := 12)
    (lo := (209969959 / 1000000000)) (hi := (5249249 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233641 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233641 / 1000000) = 1/(1000000 / 1233641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (209969959 / 1000000000) (5249249 / 25000000) (Real.log (1233641 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1233641 / 1000000) = -Real.log (1000000 / 1233641) := by
    rw [show ((1233641 / 1000000) : ℝ) = ((1000000 / 1233641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (5322091 / 20000000) ≤ -Real.log (766359 / 1000000) ∧
    -Real.log (766359 / 1000000) ≤ (266104551 / 1000000000) := by
  have h := checkLog_sound (w := (233641 / 1766359)) (n := 12)
    (lo := (5322091 / 20000000)) (hi := (266104551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766359) = 1/(766359 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-266104551 / 1000000000) (-5322091 / 20000000) (Real.log (766359 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (664557841 / 1000000000) ≤ -Real.log (500000000000 / 971815469663) ∧
    -Real.log (500000000000 / 971815469663) ≤ (332278921 / 500000000) := by
  have h := checkLog_sound (w := (471815469663 / 1471815469663)) (n := 12)
    (lo := (664557841 / 1000000000)) (hi := (332278921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971815469663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971815469663 / 500000000000) = 1/(500000000000 / 971815469663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (664557841 / 1000000000) (332278921 / 500000000) (Real.log (971815469663 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (971815469663 / 500000000000) = -Real.log (500000000000 / 971815469663) := by
    rw [show ((971815469663 / 500000000000) : ℝ) = ((500000000000 / 971815469663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (332754899 / 500000000) ≤ -Real.log (250000000000 / 486370518081) ∧
    -Real.log (250000000000 / 486370518081) ≤ (665509799 / 1000000000) := by
  have h := checkLog_sound (w := (236370518081 / 736370518081)) (n := 12)
    (lo := (332754899 / 500000000)) (hi := (665509799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486370518081 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486370518081 / 250000000000) = 1/(250000000000 / 486370518081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (332754899 / 500000000) (665509799 / 1000000000) (Real.log (486370518081 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (486370518081 / 250000000000) = -Real.log (250000000000 / 486370518081) := by
    rw [show ((486370518081 / 250000000000) : ℝ) = ((250000000000 / 486370518081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (475378573 / 1000000000) ≤ -Real.log (2500000000 / 4021557661) ∧
    -Real.log (2500000000 / 4021557661) ≤ (237689287 / 500000000) := by
  have h := checkLog_sound (w := (1521557661 / 6521557661)) (n := 12)
    (lo := (475378573 / 1000000000)) (hi := (237689287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4021557661 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4021557661 / 2500000000) = 1/(2500000000 / 4021557661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (475378573 / 1000000000) (237689287 / 500000000) (Real.log (4021557661 / 2500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4021557661 / 2500000000) = -Real.log (2500000000 / 4021557661) := by
    rw [show ((4021557661 / 2500000000) : ℝ) = ((2500000000 / 4021557661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (476074509 / 1000000000) ≤ -Real.log (125000000000 / 201217869171) ∧
    -Real.log (125000000000 / 201217869171) ≤ (47607451 / 100000000) := by
  have h := checkLog_sound (w := (76217869171 / 326217869171)) (n := 12)
    (lo := (476074509 / 1000000000)) (hi := (47607451 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201217869171 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201217869171 / 125000000000) = 1/(125000000000 / 201217869171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (476074509 / 1000000000) (47607451 / 100000000) (Real.log (201217869171 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (201217869171 / 125000000000) = -Real.log (125000000000 / 201217869171) := by
    rw [show ((201217869171 / 125000000000) : ℝ) = ((125000000000 / 201217869171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0389

end


