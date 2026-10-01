-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0175Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0175Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:42:03.794979+00:00
-- url     : https://prove2.me/theorems/f0e50e24-2c6d-4665-9e1a-7b2efe7c3fea
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0175Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0176Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0175Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0176Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0177Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0178Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0179Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0175Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0176Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0177Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0178Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0179Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0175Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0176Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0177Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0178Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0179Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0175Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0176Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0177Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0178Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0179Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0175Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0175
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

theorem reflection_log_1_neg : (31696391 / 50000000) ≤ -Real.log (200 / 377) ∧
    -Real.log (200 / 377) ≤ (633927821 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 577)) (n := 12)
    (lo := (31696391 / 50000000)) (hi := (633927821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377 / 200) = 1/(200 / 377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (31696391 / 50000000) (633927821 / 1000000000) (Real.log (377 / 200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (377 / 200) = -Real.log (200 / 377) := by
    rw [show ((377 / 200) : ℝ) = ((200 / 377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (540705787 / 250000000) ≤ -Real.log (23 / 200) ∧
    -Real.log (23 / 200) ≤ (135176447 / 62500000) := by
  have h := checkLog_sound (w := (1 / 24)) (n := 12)
    (lo := (10422701 / 125000000)) (hi := (83381609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 23) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 23) = 1/(23 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-135176447 / 62500000) (-540705787 / 250000000) (Real.log (23 / 200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (126470329 / 200000000) ≤ -Real.log (1280 / 2409) ∧
    -Real.log (1280 / 2409) ≤ (316175823 / 500000000) := by
  have h := checkLog_sound (w := (1129 / 3689)) (n := 12)
    (lo := (126470329 / 200000000)) (hi := (316175823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2409 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2409 / 1280) = 1/(1280 / 2409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (126470329 / 200000000) (316175823 / 500000000) (Real.log (2409 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2409 / 1280) = -Real.log (1280 / 2409) := by
    rw [show ((2409 / 1280) : ℝ) = ((1280 / 2409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1068667759 / 500000000) ≤ -Real.log (151 / 1280) ∧
    -Real.log (151 / 1280) ≤ (1068667761 / 500000000) := by
  have h := checkLog_sound (w := (9 / 311)) (n := 12)
    (lo := (28946989 / 500000000)) (hi := (57893979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 151) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 151) = 1/(151 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1068667761 / 500000000) (-1068667759 / 500000000) (Real.log (151 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (285489773 / 500000000) ≤ -Real.log (100 / 177) ∧
    -Real.log (100 / 177) ≤ (570979547 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 277)) (n := 12)
    (lo := (285489773 / 500000000)) (hi := (570979547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 100) = 1/(100 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (285489773 / 500000000) (570979547 / 1000000000) (Real.log (177 / 100)) := by
  have h := reflection_log_5_neg
  have he : Real.log (177 / 100) = -Real.log (100 / 177) := by
    rw [show ((177 / 100) : ℝ) = ((100 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (22963687 / 15625000) ≤ -Real.log (23 / 100) ∧
    -Real.log (23 / 100) ≤ (1469675971 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 24)) (n := 12)
    (lo := (10422701 / 125000000)) (hi := (83381609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 23) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 23) = 1/(23 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1469675971 / 1000000000) (-22963687 / 15625000) (Real.log (23 / 100)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (567619387 / 1000000000) ≤ -Real.log (640 / 1129) ∧
    -Real.log (640 / 1129) ≤ (141904847 / 250000000) := by
  have h := checkLog_sound (w := (489 / 1769)) (n := 12)
    (lo := (567619387 / 1000000000)) (hi := (141904847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129 / 640) = 1/(640 / 1129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (567619387 / 1000000000) (141904847 / 250000000) (Real.log (1129 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1129 / 640) = -Real.log (640 / 1129) := by
    rw [show ((1129 / 640) : ℝ) = ((640 / 1129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (722094169 / 500000000) ≤ -Real.log (151 / 640) ∧
    -Real.log (151 / 640) ≤ (1444188341 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 311)) (n := 12)
    (lo := (28946989 / 500000000)) (hi := (57893979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 151) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 151) = 1/(151 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1444188341 / 1000000000) (-722094169 / 500000000) (Real.log (151 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (323908823 / 500000000) ≤ -Real.log (200000 / 382273) ∧
    -Real.log (200000 / 382273) ≤ (647817647 / 1000000000) := by
  have h := checkLog_sound (w := (182273 / 582273)) (n := 12)
    (lo := (323908823 / 500000000)) (hi := (647817647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382273 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382273 / 200000) = 1/(200000 / 382273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (323908823 / 500000000) (647817647 / 1000000000) (Real.log (382273 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (382273 / 200000) = -Real.log (200000 / 382273) := by
    rw [show ((382273 / 200000) : ℝ) = ((200000 / 382273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2423228463 / 1000000000) ≤ -Real.log (17727 / 200000) ∧
    -Real.log (17727 / 200000) ≤ (2423228467 / 1000000000) := by
  have h := checkLog_sound (w := (7273 / 42727)) (n := 12)
    (lo := (343786923 / 1000000000)) (hi := (85946731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17727) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 17727) = 1/(17727 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2423228467 / 1000000000) (-2423228463 / 1000000000) (Real.log (17727 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (648838907 / 1000000000) ≤ -Real.log (500000 / 956659) ∧
    -Real.log (500000 / 956659) ≤ (162209727 / 250000000) := by
  have h := checkLog_sound (w := (456659 / 1456659)) (n := 12)
    (lo := (648838907 / 1000000000)) (hi := (162209727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956659 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956659 / 500000) = 1/(500000 / 956659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (648838907 / 1000000000) (162209727 / 250000000) (Real.log (956659 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (956659 / 500000) = -Real.log (500000 / 956659) := by
    rw [show ((956659 / 500000) : ℝ) = ((500000 / 956659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2445509027 / 1000000000) ≤ -Real.log (43341 / 500000) ∧
    -Real.log (43341 / 500000) ≤ (2445509031 / 1000000000) := by
  have h := checkLog_sound (w := (19159 / 105841)) (n := 12)
    (lo := (366067487 / 1000000000)) (hi := (11439609 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43341) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 43341) = 1/(43341 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2445509031 / 1000000000) (-2445509027 / 1000000000) (Real.log (43341 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (645992677 / 1000000000) ≤ -Real.log (25000 / 47697) ∧
    -Real.log (25000 / 47697) ≤ (322996339 / 500000000) := by
  have h := checkLog_sound (w := (22697 / 72697)) (n := 12)
    (lo := (645992677 / 1000000000)) (hi := (322996339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47697 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47697 / 25000) = 1/(25000 / 47697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (645992677 / 1000000000) (322996339 / 500000000) (Real.log (47697 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (47697 / 25000) = -Real.log (25000 / 47697) := by
    rw [show ((47697 / 25000) : ℝ) = ((25000 / 47697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1192331601 / 500000000) ≤ -Real.log (2303 / 25000) ∧
    -Real.log (2303 / 25000) ≤ (1192331603 / 500000000) := by
  have h := checkLog_sound (w := (411 / 2714)) (n := 12)
    (lo := (152610831 / 500000000)) (hi := (305221663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2303) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 2303) = 1/(2303 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1192331603 / 500000000) (-1192331601 / 500000000) (Real.log (2303 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (323560783 / 500000000) ≤ -Real.log (200000 / 382007) ∧
    -Real.log (200000 / 382007) ≤ (647121567 / 1000000000) := by
  have h := checkLog_sound (w := (182007 / 582007)) (n := 12)
    (lo := (323560783 / 500000000)) (hi := (647121567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382007 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382007 / 200000) = 1/(200000 / 382007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (323560783 / 500000000) (647121567 / 1000000000) (Real.log (382007 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (382007 / 200000) = -Real.log (200000 / 382007) := by
    rw [show ((382007 / 200000) : ℝ) = ((200000 / 382007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2408334571 / 1000000000) ≤ -Real.log (17993 / 200000) ∧
    -Real.log (17993 / 200000) ≤ (96333383 / 40000000) := by
  have h := checkLog_sound (w := (7007 / 42993)) (n := 12)
    (lo := (328893031 / 1000000000)) (hi := (41111629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17993) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 17993) = 1/(17993 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-96333383 / 40000000) (-2408334571 / 1000000000) (Real.log (17993 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3071046109 / 1000000000) ≤ -Real.log (500000000000 / 10782224854741) ∧
    -Real.log (500000000000 / 10782224854741) ≤ (1535523057 / 500000000) := by
  have h := checkLog_sound (w := (2782224854741 / 18782224854741)) (n := 12)
    (lo := (298457389 / 1000000000)) (hi := (29845739 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10782224854741 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10782224854741 / 8000000000000) = 1/(500000000000 / 10782224854741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3071046109 / 1000000000) (1535523057 / 500000000) (Real.log (10782224854741 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10782224854741 / 500000000000) = -Real.log (500000000000 / 10782224854741) := by
    rw [show ((10782224854741 / 500000000000) : ℝ) = ((500000000000 / 10782224854741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1547173967 / 500000000) ≤ -Real.log (250000000000 / 5518210239727) ∧
    -Real.log (250000000000 / 5518210239727) ≤ (3094347939 / 1000000000) := by
  have h := checkLog_sound (w := (1518210239727 / 9518210239727)) (n := 12)
    (lo := (160879607 / 500000000)) (hi := (64351843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5518210239727 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5518210239727 / 4000000000000) = 1/(250000000000 / 5518210239727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1547173967 / 500000000) (3094347939 / 1000000000) (Real.log (5518210239727 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5518210239727 / 250000000000) = -Real.log (250000000000 / 5518210239727) := by
    rw [show ((5518210239727 / 250000000000) : ℝ) = ((250000000000 / 5518210239727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3030655879 / 1000000000) ≤ -Real.log (62500000000 / 1294425749023) ∧
    -Real.log (62500000000 / 1294425749023) ≤ (757663971 / 250000000) := by
  have h := checkLog_sound (w := (294425749023 / 2294425749023)) (n := 12)
    (lo := (258067159 / 1000000000)) (hi := (6451679 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1294425749023 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1294425749023 / 1000000000000) = 1/(62500000000 / 1294425749023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3030655879 / 1000000000) (757663971 / 250000000) (Real.log (1294425749023 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1294425749023 / 62500000000) = -Real.log (62500000000 / 1294425749023) := by
    rw [show ((1294425749023 / 62500000000) : ℝ) = ((62500000000 / 1294425749023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3055456137 / 1000000000) ≤ -Real.log (125000000000 / 2653858444951) ∧
    -Real.log (125000000000 / 2653858444951) ≤ (1527728071 / 500000000) := by
  have h := checkLog_sound (w := (653858444951 / 4653858444951)) (n := 12)
    (lo := (282867417 / 1000000000)) (hi := (141433709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2653858444951 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2653858444951 / 2000000000000) = 1/(125000000000 / 2653858444951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3055456137 / 1000000000) (1527728071 / 500000000) (Real.log (2653858444951 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2653858444951 / 125000000000) = -Real.log (125000000000 / 2653858444951) := by
    rw [show ((2653858444951 / 125000000000) : ℝ) = ((125000000000 / 2653858444951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0175

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0176Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0176
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

theorem reflection_log_1_neg : (126470329 / 200000000) ≤ -Real.log (1280 / 2409) ∧
    -Real.log (1280 / 2409) ≤ (316175823 / 500000000) := by
  have h := checkLog_sound (w := (1129 / 3689)) (n := 12)
    (lo := (126470329 / 200000000)) (hi := (316175823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2409 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2409 / 1280) = 1/(1280 / 2409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (126470329 / 200000000) (316175823 / 500000000) (Real.log (2409 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2409 / 1280) = -Real.log (1280 / 2409) := by
    rw [show ((2409 / 1280) : ℝ) = ((1280 / 2409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1068667759 / 500000000) ≤ -Real.log (151 / 1280) ∧
    -Real.log (151 / 1280) ≤ (1068667761 / 500000000) := by
  have h := checkLog_sound (w := (9 / 311)) (n := 12)
    (lo := (28946989 / 500000000)) (hi := (57893979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 151) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 151) = 1/(151 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1068667761 / 500000000) (-1068667759 / 500000000) (Real.log (151 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (315386491 / 500000000) ≤ -Real.log (3200 / 6013) ∧
    -Real.log (3200 / 6013) ≤ (630772983 / 1000000000) := by
  have h := checkLog_sound (w := (2813 / 9213)) (n := 12)
    (lo := (315386491 / 500000000)) (hi := (630772983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6013 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6013 / 3200) = 1/(3200 / 6013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (315386491 / 500000000) (630772983 / 1000000000) (Real.log (6013 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6013 / 3200) = -Real.log (3200 / 6013) := by
    rw [show ((6013 / 3200) : ℝ) = ((3200 / 6013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1056240697 / 500000000) ≤ -Real.log (387 / 3200) ∧
    -Real.log (387 / 3200) ≤ (1056240699 / 500000000) := by
  have h := checkLog_sound (w := (13 / 787)) (n := 12)
    (lo := (16519927 / 500000000)) (hi := (6607971 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 387) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 387) = 1/(387 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1056240699 / 500000000) (-1056240697 / 500000000) (Real.log (387 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (567619387 / 1000000000) ≤ -Real.log (640 / 1129) ∧
    -Real.log (640 / 1129) ≤ (141904847 / 250000000) := by
  have h := checkLog_sound (w := (489 / 1769)) (n := 12)
    (lo := (567619387 / 1000000000)) (hi := (141904847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129 / 640) = 1/(640 / 1129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (567619387 / 1000000000) (141904847 / 250000000) (Real.log (1129 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1129 / 640) = -Real.log (640 / 1129) := by
    rw [show ((1129 / 640) : ℝ) = ((640 / 1129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (722094169 / 500000000) ≤ -Real.log (151 / 640) ∧
    -Real.log (151 / 640) ≤ (1444188341 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 311)) (n := 12)
    (lo := (28946989 / 500000000)) (hi := (57893979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 151) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 151) = 1/(151 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1444188341 / 1000000000) (-722094169 / 500000000) (Real.log (151 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (5642479 / 10000000) ≤ -Real.log (1600 / 2813) ∧
    -Real.log (1600 / 2813) ≤ (564247901 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 4413)) (n := 12)
    (lo := (5642479 / 10000000)) (hi := (564247901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2813 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2813 / 1600) = 1/(1600 / 2813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (5642479 / 10000000) (564247901 / 1000000000) (Real.log (2813 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2813 / 1600) = -Real.log (1600 / 2813) := by
    rw [show ((2813 / 1600) : ℝ) = ((1600 / 2813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (709667107 / 500000000) ≤ -Real.log (387 / 1600) ∧
    -Real.log (387 / 1600) ≤ (1419334217 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 787)) (n := 12)
    (lo := (16519927 / 500000000)) (hi := (6607971 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 387) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 387) = 1/(387 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1419334217 / 1000000000) (-709667107 / 500000000) (Real.log (387 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (646803197 / 1000000000) ≤ -Real.log (1000000 / 1909427) ∧
    -Real.log (1000000 / 1909427) ≤ (323401599 / 500000000) := by
  have h := checkLog_sound (w := (909427 / 2909427)) (n := 12)
    (lo := (646803197 / 1000000000)) (hi := (323401599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1909427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1909427 / 1000000) = 1/(1000000 / 1909427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (646803197 / 1000000000) (323401599 / 500000000) (Real.log (1909427 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1909427 / 1000000) = -Real.log (1000000 / 1909427) := by
    rw [show ((1909427 / 1000000) : ℝ) = ((1000000 / 1909427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2401599121 / 1000000000) ≤ -Real.log (90573 / 1000000) ∧
    -Real.log (90573 / 1000000) ≤ (19212793 / 8000000) := by
  have h := checkLog_sound (w := (34427 / 215573)) (n := 12)
    (lo := (322157581 / 1000000000)) (hi := (161078791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90573) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 90573) = 1/(90573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-19212793 / 8000000) (-2401599121 / 1000000000) (Real.log (90573 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (647818169 / 1000000000) ≤ -Real.log (500000 / 955683) ∧
    -Real.log (500000 / 955683) ≤ (64781817 / 100000000) := by
  have h := checkLog_sound (w := (455683 / 1455683)) (n := 12)
    (lo := (647818169 / 1000000000)) (hi := (64781817 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955683 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955683 / 500000) = 1/(500000 / 955683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (647818169 / 1000000000) (64781817 / 100000000) (Real.log (955683 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (955683 / 500000) = -Real.log (500000 / 955683) := by
    rw [show ((955683 / 500000) : ℝ) = ((500000 / 955683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1211619873 / 500000000) ≤ -Real.log (44317 / 500000) ∧
    -Real.log (44317 / 500000) ≤ (9692959 / 4000000) := by
  have h := checkLog_sound (w := (18183 / 106817)) (n := 12)
    (lo := (171899103 / 500000000)) (hi := (343798207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44317) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 44317) = 1/(44317 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-9692959 / 4000000) (-1211619873 / 500000000) (Real.log (44317 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (322432831 / 500000000) ≤ -Real.log (1000000 / 1905731) ∧
    -Real.log (1000000 / 1905731) ≤ (644865663 / 1000000000) := by
  have h := checkLog_sound (w := (905731 / 2905731)) (n := 12)
    (lo := (322432831 / 500000000)) (hi := (644865663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1905731 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1905731 / 1000000) = 1/(1000000 / 1905731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (322432831 / 500000000) (644865663 / 1000000000) (Real.log (1905731 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1905731 / 1000000) = -Real.log (1000000 / 1905731) := by
    rw [show ((1905731 / 1000000) : ℝ) = ((1000000 / 1905731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2361602879 / 1000000000) ≤ -Real.log (94269 / 1000000) ∧
    -Real.log (94269 / 1000000) ≤ (2361602883 / 1000000000) := by
  have h := checkLog_sound (w := (30731 / 219269)) (n := 12)
    (lo := (282161339 / 1000000000)) (hi := (14108067 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94269) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 94269) = 1/(94269 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2361602883 / 1000000000) (-2361602879 / 1000000000) (Real.log (94269 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (322996601 / 500000000) ≤ -Real.log (1000000 / 1907881) ∧
    -Real.log (1000000 / 1907881) ≤ (645993203 / 1000000000) := by
  have h := checkLog_sound (w := (907881 / 2907881)) (n := 12)
    (lo := (322996601 / 500000000)) (hi := (645993203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1907881 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1907881 / 1000000) = 1/(1000000 / 1907881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (322996601 / 500000000) (645993203 / 1000000000) (Real.log (1907881 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1907881 / 1000000) = -Real.log (1000000 / 1907881) := by
    rw [show ((1907881 / 1000000) : ℝ) = ((1000000 / 1907881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2384674057 / 1000000000) ≤ -Real.log (92119 / 1000000) ∧
    -Real.log (92119 / 1000000) ≤ (2384674061 / 1000000000) := by
  have h := checkLog_sound (w := (32881 / 217119)) (n := 12)
    (lo := (305232517 / 1000000000)) (hi := (152616259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92119) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 92119) = 1/(92119 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2384674061 / 1000000000) (-2384674057 / 1000000000) (Real.log (92119 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1524201159 / 500000000) ≤ -Real.log (50000000000 / 1054081790379) ∧
    -Real.log (50000000000 / 1054081790379) ≤ (3048402323 / 1000000000) := by
  have h := checkLog_sound (w := (254081790379 / 1854081790379)) (n := 12)
    (lo := (137906799 / 500000000)) (hi := (275813599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1054081790379 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1054081790379 / 800000000000) = 1/(50000000000 / 1054081790379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1524201159 / 500000000) (3048402323 / 1000000000) (Real.log (1054081790379 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1054081790379 / 50000000000) = -Real.log (50000000000 / 1054081790379) := by
    rw [show ((1054081790379 / 50000000000) : ℝ) = ((50000000000 / 1054081790379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (614211583 / 200000000) ≤ -Real.log (62500000000 / 1347794018097) ∧
    -Real.log (62500000000 / 1347794018097) ≤ (1199632 / 390625) := by
  have h := checkLog_sound (w := (347794018097 / 2347794018097)) (n := 12)
    (lo := (59693839 / 200000000)) (hi := (74617299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347794018097 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1347794018097 / 1000000000000) = 1/(62500000000 / 1347794018097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (614211583 / 200000000) (1199632 / 390625) (Real.log (1347794018097 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1347794018097 / 62500000000) = -Real.log (62500000000 / 1347794018097) := by
    rw [show ((1347794018097 / 62500000000) : ℝ) = ((62500000000 / 1347794018097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3006468541 / 1000000000) ≤ -Real.log (50000000000 / 1010794110471) ∧
    -Real.log (50000000000 / 1010794110471) ≤ (1503234273 / 500000000) := by
  have h := checkLog_sound (w := (210794110471 / 1810794110471)) (n := 12)
    (lo := (233879821 / 1000000000)) (hi := (116939911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1010794110471 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1010794110471 / 800000000000) = 1/(50000000000 / 1010794110471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3006468541 / 1000000000) (1503234273 / 500000000) (Real.log (1010794110471 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1010794110471 / 50000000000) = -Real.log (50000000000 / 1010794110471) := by
    rw [show ((1010794110471 / 50000000000) : ℝ) = ((50000000000 / 1010794110471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3030667259 / 1000000000) ≤ -Real.log (500000000000 / 10355523833303) ∧
    -Real.log (500000000000 / 10355523833303) ≤ (5919272 / 1953125) := by
  have h := checkLog_sound (w := (2355523833303 / 18355523833303)) (n := 12)
    (lo := (258078539 / 1000000000)) (hi := (12903927 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10355523833303 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10355523833303 / 8000000000000) = 1/(500000000000 / 10355523833303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3030667259 / 1000000000) (5919272 / 1953125) (Real.log (10355523833303 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10355523833303 / 500000000000) = -Real.log (500000000000 / 10355523833303) := by
    rw [show ((10355523833303 / 500000000000) : ℝ) = ((500000000000 / 10355523833303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0176

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0177Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0177
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

theorem reflection_log_1_neg : (315386491 / 500000000) ≤ -Real.log (3200 / 6013) ∧
    -Real.log (3200 / 6013) ≤ (630772983 / 1000000000) := by
  have h := checkLog_sound (w := (2813 / 9213)) (n := 12)
    (lo := (315386491 / 500000000)) (hi := (630772983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6013 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6013 / 3200) = 1/(3200 / 6013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (315386491 / 500000000) (630772983 / 1000000000) (Real.log (6013 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6013 / 3200) = -Real.log (3200 / 6013) := by
    rw [show ((6013 / 3200) : ℝ) = ((3200 / 6013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1056240697 / 500000000) ≤ -Real.log (387 / 3200) ∧
    -Real.log (387 / 3200) ≤ (1056240699 / 500000000) := by
  have h := checkLog_sound (w := (13 / 787)) (n := 12)
    (lo := (16519927 / 500000000)) (hi := (6607971 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 387) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 387) = 1/(387 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1056240699 / 500000000) (-1056240697 / 500000000) (Real.log (387 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (314595911 / 500000000) ≤ -Real.log (6400 / 12007) ∧
    -Real.log (6400 / 12007) ≤ (629191823 / 1000000000) := by
  have h := checkLog_sound (w := (5607 / 18407)) (n := 12)
    (lo := (314595911 / 500000000)) (hi := (629191823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12007 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12007 / 6400) = 1/(6400 / 12007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (314595911 / 500000000) (629191823 / 1000000000) (Real.log (12007 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12007 / 6400) = -Real.log (6400 / 12007) := by
    rw [show ((12007 / 6400) : ℝ) = ((6400 / 12007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1044115023 / 500000000) ≤ -Real.log (793 / 6400) ∧
    -Real.log (793 / 6400) ≤ (41764601 / 20000000) := by
  have h := checkLog_sound (w := (7 / 1593)) (n := 12)
    (lo := (4394253 / 500000000)) (hi := (8788507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 793) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 793) = 1/(793 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-41764601 / 20000000) (-1044115023 / 500000000) (Real.log (793 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (5642479 / 10000000) ≤ -Real.log (1600 / 2813) ∧
    -Real.log (1600 / 2813) ≤ (564247901 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 4413)) (n := 12)
    (lo := (5642479 / 10000000)) (hi := (564247901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2813 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2813 / 1600) = 1/(1600 / 2813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (5642479 / 10000000) (564247901 / 1000000000) (Real.log (2813 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2813 / 1600) = -Real.log (1600 / 2813) := by
    rw [show ((2813 / 1600) : ℝ) = ((1600 / 2813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (709667107 / 500000000) ≤ -Real.log (387 / 1600) ∧
    -Real.log (387 / 1600) ≤ (1419334217 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 787)) (n := 12)
    (lo := (16519927 / 500000000)) (hi := (6607971 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 387) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 387) = 1/(387 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1419334217 / 1000000000) (-709667107 / 500000000) (Real.log (387 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (560865007 / 1000000000) ≤ -Real.log (3200 / 5607) ∧
    -Real.log (3200 / 5607) ≤ (35054063 / 62500000) := by
  have h := checkLog_sound (w := (2407 / 8807)) (n := 12)
    (lo := (560865007 / 1000000000)) (hi := (35054063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5607 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5607 / 3200) = 1/(3200 / 5607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (560865007 / 1000000000) (35054063 / 62500000) (Real.log (5607 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5607 / 3200) = -Real.log (3200 / 5607) := by
    rw [show ((5607 / 3200) : ℝ) = ((3200 / 5607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (697541433 / 500000000) ≤ -Real.log (793 / 3200) ∧
    -Real.log (793 / 3200) ≤ (1395082869 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 1593)) (n := 12)
    (lo := (4394253 / 500000000)) (hi := (8788507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 793) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 793) = 1/(793 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1395082869 / 1000000000) (-697541433 / 500000000) (Real.log (793 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (161448633 / 250000000) ≤ -Real.log (500000 / 953751) ∧
    -Real.log (500000 / 953751) ≤ (645794533 / 1000000000) := by
  have h := checkLog_sound (w := (453751 / 1453751)) (n := 12)
    (lo := (161448633 / 250000000)) (hi := (645794533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953751 / 500000) = 1/(500000 / 953751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (161448633 / 250000000) (645794533 / 1000000000) (Real.log (953751 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (953751 / 500000) = -Real.log (500000 / 953751) := by
    rw [show ((953751 / 500000) : ℝ) = ((500000 / 953751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1190284127 / 500000000) ≤ -Real.log (46249 / 500000) ∧
    -Real.log (46249 / 500000) ≤ (1190284129 / 500000000) := by
  have h := checkLog_sound (w := (16251 / 108749)) (n := 12)
    (lo := (150563357 / 500000000)) (hi := (60225343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46249) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 46249) = 1/(46249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1190284129 / 500000000) (-1190284127 / 500000000) (Real.log (46249 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16170093 / 25000000) ≤ -Real.log (250000 / 477357) ∧
    -Real.log (250000 / 477357) ≤ (646803721 / 1000000000) := by
  have h := checkLog_sound (w := (227357 / 727357)) (n := 12)
    (lo := (16170093 / 25000000)) (hi := (646803721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477357 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477357 / 250000) = 1/(250000 / 477357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16170093 / 25000000) (646803721 / 1000000000) (Real.log (477357 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (477357 / 250000) = -Real.log (250000 / 477357) := by
    rw [show ((477357 / 250000) : ℝ) = ((250000 / 477357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1200805081 / 500000000) ≤ -Real.log (22643 / 250000) ∧
    -Real.log (22643 / 250000) ≤ (1200805083 / 500000000) := by
  have h := checkLog_sound (w := (8607 / 53893)) (n := 12)
    (lo := (161084311 / 500000000)) (hi := (322168623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22643) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 22643) = 1/(22643 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1200805083 / 500000000) (-1200805081 / 500000000) (Real.log (22643 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (643741051 / 1000000000) ≤ -Real.log (1000000 / 1903589) ∧
    -Real.log (1000000 / 1903589) ≤ (160935263 / 250000000) := by
  have h := checkLog_sound (w := (903589 / 2903589)) (n := 12)
    (lo := (643741051 / 1000000000)) (hi := (160935263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1903589 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1903589 / 1000000) = 1/(1000000 / 1903589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (643741051 / 1000000000) (160935263 / 250000000) (Real.log (1903589 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1903589 / 1000000) = -Real.log (1000000 / 1903589) := by
    rw [show ((1903589 / 1000000) : ℝ) = ((1000000 / 1903589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1169567487 / 500000000) ≤ -Real.log (96411 / 1000000) ∧
    -Real.log (96411 / 1000000) ≤ (1169567489 / 500000000) := by
  have h := checkLog_sound (w := (28589 / 221411)) (n := 12)
    (lo := (129846717 / 500000000)) (hi := (51938687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96411) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 96411) = 1/(96411 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1169567489 / 500000000) (-1169567487 / 500000000) (Real.log (96411 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (322433093 / 500000000) ≤ -Real.log (250000 / 476433) ∧
    -Real.log (250000 / 476433) ≤ (644866187 / 1000000000) := by
  have h := checkLog_sound (w := (226433 / 726433)) (n := 12)
    (lo := (322433093 / 500000000)) (hi := (644866187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((476433 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(476433 / 250000) = 1/(250000 / 476433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (322433093 / 500000000) (644866187 / 1000000000) (Real.log (476433 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (476433 / 250000) = -Real.log (250000 / 476433) := by
    rw [show ((476433 / 250000) : ℝ) = ((250000 / 476433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2361613487 / 1000000000) ≤ -Real.log (23567 / 250000) ∧
    -Real.log (23567 / 250000) ≤ (2361613491 / 1000000000) := by
  have h := checkLog_sound (w := (7683 / 54817)) (n := 12)
    (lo := (282171947 / 1000000000)) (hi := (70542987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23567) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 23567) = 1/(23567 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2361613491 / 1000000000) (-2361613487 / 1000000000) (Real.log (23567 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1513181393 / 500000000) ≤ -Real.log (800000000 / 16497671301) ∧
    -Real.log (800000000 / 16497671301) ≤ (3026362791 / 1000000000) := by
  have h := checkLog_sound (w := (3697671301 / 29297671301)) (n := 12)
    (lo := (126887033 / 500000000)) (hi := (253774067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16497671301 / 12800000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16497671301 / 12800000000) = 1/(800000000 / 16497671301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1513181393 / 500000000) (3026362791 / 1000000000) (Real.log (16497671301 / 800000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (16497671301 / 800000000) = -Real.log (800000000 / 16497671301) := by
    rw [show ((16497671301 / 800000000) : ℝ) = ((800000000 / 16497671301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1524206941 / 500000000) ≤ -Real.log (500000000000 / 10540939804797) ∧
    -Real.log (500000000000 / 10540939804797) ≤ (3048413887 / 1000000000) := by
  have h := checkLog_sound (w := (2540939804797 / 18540939804797)) (n := 12)
    (lo := (137912581 / 500000000)) (hi := (275825163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10540939804797 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10540939804797 / 8000000000000) = 1/(500000000000 / 10540939804797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1524206941 / 500000000) (3048413887 / 1000000000) (Real.log (10540939804797 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (10540939804797 / 500000000000) = -Real.log (500000000000 / 10540939804797) := by
    rw [show ((10540939804797 / 500000000000) : ℝ) = ((500000000000 / 10540939804797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (119315041 / 40000000) ≤ -Real.log (250000000000 / 4936130213357) ∧
    -Real.log (250000000000 / 4936130213357) ≤ (298287603 / 100000000) := by
  have h := checkLog_sound (w := (936130213357 / 8936130213357)) (n := 12)
    (lo := (42057461 / 200000000)) (hi := (105143653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4936130213357 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4936130213357 / 4000000000000) = 1/(250000000000 / 4936130213357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (119315041 / 40000000) (298287603 / 100000000) (Real.log (4936130213357 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4936130213357 / 250000000000) = -Real.log (250000000000 / 4936130213357) := by
    rw [show ((4936130213357 / 250000000000) : ℝ) = ((250000000000 / 4936130213357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3006479673 / 1000000000) ≤ -Real.log (6250000000 / 126350670429) ∧
    -Real.log (6250000000 / 126350670429) ≤ (1503239839 / 500000000) := by
  have h := checkLog_sound (w := (26350670429 / 226350670429)) (n := 12)
    (lo := (233890953 / 1000000000)) (hi := (116945477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126350670429 / 100000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(126350670429 / 100000000000) = 1/(6250000000 / 126350670429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3006479673 / 1000000000) (1503239839 / 500000000) (Real.log (126350670429 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (126350670429 / 6250000000) = -Real.log (6250000000 / 126350670429) := by
    rw [show ((126350670429 / 6250000000) : ℝ) = ((6250000000 / 126350670429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0177

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0178Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0178
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

theorem reflection_log_1_neg : (314595911 / 500000000) ≤ -Real.log (6400 / 12007) ∧
    -Real.log (6400 / 12007) ≤ (629191823 / 1000000000) := by
  have h := checkLog_sound (w := (5607 / 18407)) (n := 12)
    (lo := (314595911 / 500000000)) (hi := (629191823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12007 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12007 / 6400) = 1/(6400 / 12007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (314595911 / 500000000) (629191823 / 1000000000) (Real.log (12007 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12007 / 6400) = -Real.log (6400 / 12007) := by
    rw [show ((12007 / 6400) : ℝ) = ((6400 / 12007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1044115023 / 500000000) ≤ -Real.log (793 / 6400) ∧
    -Real.log (793 / 6400) ≤ (41764601 / 20000000) := by
  have h := checkLog_sound (w := (7 / 1593)) (n := 12)
    (lo := (4394253 / 500000000)) (hi := (8788507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 793) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 793) = 1/(793 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-41764601 / 20000000) (-1044115023 / 500000000) (Real.log (793 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (627608159 / 1000000000) ≤ -Real.log (1600 / 2997) ∧
    -Real.log (1600 / 2997) ≤ (3922551 / 6250000) := by
  have h := checkLog_sound (w := (1397 / 4597)) (n := 12)
    (lo := (627608159 / 1000000000)) (hi := (3922551 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2997 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2997 / 1600) = 1/(1600 / 2997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (627608159 / 1000000000) (3922551 / 6250000) (Real.log (2997 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2997 / 1600) = -Real.log (1600 / 2997) := by
    rw [show ((2997 / 1600) : ℝ) = ((1600 / 2997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (64517279 / 31250000) ≤ -Real.log (203 / 1600) ∧
    -Real.log (203 / 1600) ≤ (2064552931 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 603)) (n := 12)
    (lo := (84782321 / 125000000)) (hi := (678258569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 203) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 203) = 1/(203 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2064552931 / 1000000000) (-64517279 / 31250000) (Real.log (203 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (560865007 / 1000000000) ≤ -Real.log (3200 / 5607) ∧
    -Real.log (3200 / 5607) ≤ (35054063 / 62500000) := by
  have h := checkLog_sound (w := (2407 / 8807)) (n := 12)
    (lo := (560865007 / 1000000000)) (hi := (35054063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5607 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5607 / 3200) = 1/(3200 / 5607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (560865007 / 1000000000) (35054063 / 62500000) (Real.log (5607 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5607 / 3200) = -Real.log (3200 / 5607) := by
    rw [show ((5607 / 3200) : ℝ) = ((3200 / 5607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (697541433 / 500000000) ≤ -Real.log (793 / 3200) ∧
    -Real.log (793 / 3200) ≤ (1395082869 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 1593)) (n := 12)
    (lo := (4394253 / 500000000)) (hi := (8788507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 793) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 793) = 1/(793 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1395082869 / 1000000000) (-697541433 / 500000000) (Real.log (793 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (557470631 / 1000000000) ≤ -Real.log (800 / 1397) ∧
    -Real.log (800 / 1397) ≤ (69683829 / 125000000) := by
  have h := checkLog_sound (w := (597 / 2197)) (n := 12)
    (lo := (557470631 / 1000000000)) (hi := (69683829 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397 / 800) = 1/(800 / 1397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (557470631 / 1000000000) (69683829 / 125000000) (Real.log (1397 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1397 / 800) = -Real.log (800 / 1397) := by
    rw [show ((1397 / 800) : ℝ) = ((800 / 1397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (342851437 / 250000000) ≤ -Real.log (203 / 800) ∧
    -Real.log (203 / 800) ≤ (5485623 / 4000000) := by
  have h := checkLog_sound (w := (197 / 603)) (n := 12)
    (lo := (84782321 / 125000000)) (hi := (678258569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 203) = 1/(203 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5485623 / 4000000) (-342851437 / 250000000) (Real.log (203 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (644791671 / 1000000000) ≤ -Real.log (100000 / 190559) ∧
    -Real.log (100000 / 190559) ≤ (80598959 / 125000000) := by
  have h := checkLog_sound (w := (90559 / 290559)) (n := 12)
    (lo := (644791671 / 1000000000)) (hi := (80598959 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190559 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190559 / 100000) = 1/(100000 / 190559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (644791671 / 1000000000) (80598959 / 125000000) (Real.log (190559 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (190559 / 100000) = -Real.log (100000 / 190559) := by
    rw [show ((190559 / 100000) : ℝ) = ((100000 / 190559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2360108277 / 1000000000) ≤ -Real.log (9441 / 100000) ∧
    -Real.log (9441 / 100000) ≤ (2360108281 / 1000000000) := by
  have h := checkLog_sound (w := (3059 / 21941)) (n := 12)
    (lo := (280666737 / 1000000000)) (hi := (140333369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9441) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 9441) = 1/(9441 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2360108281 / 1000000000) (-2360108277 / 1000000000) (Real.log (9441 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (40362191 / 62500000) ≤ -Real.log (1000000 / 1907503) ∧
    -Real.log (1000000 / 1907503) ≤ (645795057 / 1000000000) := by
  have h := checkLog_sound (w := (907503 / 2907503)) (n := 12)
    (lo := (40362191 / 62500000)) (hi := (645795057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1907503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1907503 / 1000000) = 1/(1000000 / 1907503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (40362191 / 62500000) (645795057 / 1000000000) (Real.log (1907503 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1907503 / 1000000) = -Real.log (1000000 / 1907503) := by
    rw [show ((1907503 / 1000000) : ℝ) = ((1000000 / 1907503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (476115813 / 200000000) ≤ -Real.log (92497 / 1000000) ∧
    -Real.log (92497 / 1000000) ≤ (2380579069 / 1000000000) := by
  have h := checkLog_sound (w := (32503 / 217497)) (n := 12)
    (lo := (12045501 / 40000000)) (hi := (150568763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92497) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 92497) = 1/(92497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2380579069 / 1000000000) (-476115813 / 200000000) (Real.log (92497 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (321308639 / 500000000) ≤ -Real.log (1000000 / 1901451) ∧
    -Real.log (1000000 / 1901451) ≤ (642617279 / 1000000000) := by
  have h := checkLog_sound (w := (901451 / 2901451)) (n := 12)
    (lo := (321308639 / 500000000)) (hi := (642617279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1901451 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1901451 / 1000000) = 1/(1000000 / 1901451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (321308639 / 500000000) (642617279 / 1000000000) (Real.log (1901451 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1901451 / 1000000) = -Real.log (1000000 / 1901451) := by
    rw [show ((1901451 / 1000000) : ℝ) = ((1000000 / 1901451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (231720139 / 100000000) ≤ -Real.log (98549 / 1000000) ∧
    -Real.log (98549 / 1000000) ≤ (1158600697 / 500000000) := by
  have h := checkLog_sound (w := (26451 / 223549)) (n := 12)
    (lo := (4755197 / 20000000)) (hi := (237759851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98549) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 98549) = 1/(98549 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1158600697 / 500000000) (-231720139 / 100000000) (Real.log (98549 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (643741577 / 1000000000) ≤ -Real.log (100000 / 190359) ∧
    -Real.log (100000 / 190359) ≤ (321870789 / 500000000) := by
  have h := checkLog_sound (w := (90359 / 290359)) (n := 12)
    (lo := (643741577 / 1000000000)) (hi := (321870789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190359 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190359 / 100000) = 1/(100000 / 190359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (643741577 / 1000000000) (321870789 / 500000000) (Real.log (190359 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (190359 / 100000) = -Real.log (100000 / 190359) := by
    rw [show ((190359 / 100000) : ℝ) = ((100000 / 190359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1169572673 / 500000000) ≤ -Real.log (9641 / 100000) ∧
    -Real.log (9641 / 100000) ≤ (46782907 / 20000000) := by
  have h := checkLog_sound (w := (2859 / 22141)) (n := 12)
    (lo := (129851903 / 500000000)) (hi := (259703807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9641) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 9641) = 1/(9641 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-46782907 / 20000000) (-1169572673 / 500000000) (Real.log (9641 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (751224987 / 250000000) ≤ -Real.log (31250000000 / 630756143417) ∧
    -Real.log (31250000000 / 630756143417) ≤ (3004899953 / 1000000000) := by
  have h := checkLog_sound (w := (130756143417 / 1130756143417)) (n := 12)
    (lo := (58077807 / 250000000)) (hi := (232311229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630756143417 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(630756143417 / 500000000000) = 1/(31250000000 / 630756143417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (751224987 / 250000000) (3004899953 / 1000000000) (Real.log (630756143417 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (630756143417 / 31250000000) = -Real.log (31250000000 / 630756143417) := by
    rw [show ((630756143417 / 31250000000) : ℝ) = ((31250000000 / 630756143417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1513187061 / 500000000) ≤ -Real.log (250000000000 / 5155580721537) ∧
    -Real.log (250000000000 / 5155580721537) ≤ (3026374127 / 1000000000) := by
  have h := checkLog_sound (w := (1155580721537 / 9155580721537)) (n := 12)
    (lo := (126892701 / 500000000)) (hi := (253785403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5155580721537 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5155580721537 / 4000000000000) = 1/(250000000000 / 5155580721537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1513187061 / 500000000) (3026374127 / 1000000000) (Real.log (5155580721537 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5155580721537 / 250000000000) = -Real.log (250000000000 / 5155580721537) := by
    rw [show ((5155580721537 / 250000000000) : ℝ) = ((250000000000 / 5155580721537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2959818669 / 1000000000) ≤ -Real.log (250000000000 / 4823618200083) ∧
    -Real.log (250000000000 / 4823618200083) ≤ (1479909337 / 500000000) := by
  have h := checkLog_sound (w := (823618200083 / 8823618200083)) (n := 12)
    (lo := (187229949 / 1000000000)) (hi := (3744599 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4823618200083 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4823618200083 / 4000000000000) = 1/(250000000000 / 4823618200083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2959818669 / 1000000000) (1479909337 / 500000000) (Real.log (4823618200083 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4823618200083 / 250000000000) = -Real.log (250000000000 / 4823618200083) := by
    rw [show ((4823618200083 / 250000000000) : ℝ) = ((250000000000 / 4823618200083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2982886923 / 1000000000) ≤ -Real.log (250000000000 / 4936184005809) ∧
    -Real.log (250000000000 / 4936184005809) ≤ (186430433 / 62500000) := by
  have h := checkLog_sound (w := (936184005809 / 8936184005809)) (n := 12)
    (lo := (210298203 / 1000000000)) (hi := (52574551 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4936184005809 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4936184005809 / 4000000000000) = 1/(250000000000 / 4936184005809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2982886923 / 1000000000) (186430433 / 62500000) (Real.log (4936184005809 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4936184005809 / 250000000000) = -Real.log (250000000000 / 4936184005809) := by
    rw [show ((4936184005809 / 250000000000) : ℝ) = ((250000000000 / 4936184005809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0178

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0179Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0179
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

theorem reflection_log_1_neg : (627608159 / 1000000000) ≤ -Real.log (1600 / 2997) ∧
    -Real.log (1600 / 2997) ≤ (3922551 / 6250000) := by
  have h := checkLog_sound (w := (1397 / 4597)) (n := 12)
    (lo := (627608159 / 1000000000)) (hi := (3922551 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2997 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2997 / 1600) = 1/(1600 / 2997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (627608159 / 1000000000) (3922551 / 6250000) (Real.log (2997 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2997 / 1600) = -Real.log (1600 / 2997) := by
    rw [show ((2997 / 1600) : ℝ) = ((1600 / 2997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (64517279 / 31250000) ≤ -Real.log (203 / 1600) ∧
    -Real.log (203 / 1600) ≤ (2064552931 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 603)) (n := 12)
    (lo := (84782321 / 125000000)) (hi := (678258569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 203) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 203) = 1/(203 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2064552931 / 1000000000) (-64517279 / 31250000) (Real.log (203 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (626021983 / 1000000000) ≤ -Real.log (6400 / 11969) ∧
    -Real.log (6400 / 11969) ≤ (19563187 / 31250000) := by
  have h := checkLog_sound (w := (5569 / 18369)) (n := 12)
    (lo := (626021983 / 1000000000)) (hi := (19563187 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11969 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11969 / 6400) = 1/(6400 / 11969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (626021983 / 1000000000) (19563187 / 31250000) (Real.log (11969 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11969 / 6400) = -Real.log (6400 / 11969) := by
    rw [show ((11969 / 6400) : ℝ) = ((6400 / 11969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2041423473 / 1000000000) ≤ -Real.log (831 / 6400) ∧
    -Real.log (831 / 6400) ≤ (510355869 / 250000000) := by
  have h := checkLog_sound (w := (769 / 2431)) (n := 12)
    (lo := (655129113 / 1000000000)) (hi := (327564557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 831) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 831) = 1/(831 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-510355869 / 250000000) (-2041423473 / 1000000000) (Real.log (831 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (557470631 / 1000000000) ≤ -Real.log (800 / 1397) ∧
    -Real.log (800 / 1397) ≤ (69683829 / 125000000) := by
  have h := checkLog_sound (w := (597 / 2197)) (n := 12)
    (lo := (557470631 / 1000000000)) (hi := (69683829 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397 / 800) = 1/(800 / 1397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (557470631 / 1000000000) (69683829 / 125000000) (Real.log (1397 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1397 / 800) = -Real.log (800 / 1397) := by
    rw [show ((1397 / 800) : ℝ) = ((800 / 1397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (342851437 / 250000000) ≤ -Real.log (203 / 800) ∧
    -Real.log (203 / 800) ≤ (5485623 / 4000000) := by
  have h := checkLog_sound (w := (197 / 603)) (n := 12)
    (lo := (84782321 / 125000000)) (hi := (678258569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 203) = 1/(203 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5485623 / 4000000) (-342851437 / 250000000) (Real.log (203 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (277032347 / 500000000) ≤ -Real.log (3200 / 5569) ∧
    -Real.log (3200 / 5569) ≤ (110812939 / 200000000) := by
  have h := checkLog_sound (w := (2369 / 8769)) (n := 12)
    (lo := (277032347 / 500000000)) (hi := (110812939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5569 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5569 / 3200) = 1/(3200 / 5569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (277032347 / 500000000) (110812939 / 200000000) (Real.log (5569 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5569 / 3200) = -Real.log (3200 / 5569) := by
    rw [show ((5569 / 3200) : ℝ) = ((3200 / 5569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1348276293 / 1000000000) ≤ -Real.log (831 / 3200) ∧
    -Real.log (831 / 3200) ≤ (269655259 / 200000000) := by
  have h := checkLog_sound (w := (769 / 2431)) (n := 12)
    (lo := (655129113 / 1000000000)) (hi := (327564557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 831) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 831) = 1/(831 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-269655259 / 200000000) (-1348276293 / 1000000000) (Real.log (831 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (643794633 / 1000000000) ≤ -Real.log (1000000 / 1903691) ∧
    -Real.log (1000000 / 1903691) ≤ (321897317 / 500000000) := by
  have h := checkLog_sound (w := (903691 / 2903691)) (n := 12)
    (lo := (643794633 / 1000000000)) (hi := (321897317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1903691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1903691 / 1000000) = 1/(1000000 / 1903691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (643794633 / 1000000000) (321897317 / 500000000) (Real.log (1903691 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1903691 / 1000000) = -Real.log (1000000 / 1903691) := by
    rw [show ((1903691 / 1000000) : ℝ) = ((1000000 / 1903691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (73131047 / 31250000) ≤ -Real.log (96309 / 1000000) ∧
    -Real.log (96309 / 1000000) ≤ (585048377 / 250000000) := by
  have h := checkLog_sound (w := (28691 / 221309)) (n := 12)
    (lo := (65187991 / 250000000)) (hi := (52150393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96309) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 96309) = 1/(96309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-585048377 / 250000000) (-73131047 / 31250000) (Real.log (96309 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (161198049 / 250000000) ≤ -Real.log (1000000 / 1905591) ∧
    -Real.log (1000000 / 1905591) ≤ (644792197 / 1000000000) := by
  have h := checkLog_sound (w := (905591 / 2905591)) (n := 12)
    (lo := (161198049 / 250000000)) (hi := (644792197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1905591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1905591 / 1000000) = 1/(1000000 / 1905591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (161198049 / 250000000) (644792197 / 1000000000) (Real.log (1905591 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1905591 / 1000000) = -Real.log (1000000 / 1905591) := by
    rw [show ((1905591 / 1000000) : ℝ) = ((1000000 / 1905591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2360118869 / 1000000000) ≤ -Real.log (94409 / 1000000) ∧
    -Real.log (94409 / 1000000) ≤ (2360118873 / 1000000000) := by
  have h := checkLog_sound (w := (30591 / 219409)) (n := 12)
    (lo := (280677329 / 1000000000)) (hi := (28067733 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94409) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 94409) = 1/(94409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2360118873 / 1000000000) (-2360118869 / 1000000000) (Real.log (94409 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (641495927 / 1000000000) ≤ -Real.log (25000 / 47483) ∧
    -Real.log (25000 / 47483) ≤ (80186991 / 125000000) := by
  have h := checkLog_sound (w := (22483 / 72483)) (n := 12)
    (lo := (641495927 / 1000000000)) (hi := (80186991 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47483 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47483 / 25000) = 1/(25000 / 47483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (641495927 / 1000000000) (80186991 / 125000000) (Real.log (47483 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (47483 / 25000) = -Real.log (25000 / 47483) := by
    rw [show ((47483 / 25000) : ℝ) = ((25000 / 47483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2295808107 / 1000000000) ≤ -Real.log (2517 / 25000) ∧
    -Real.log (2517 / 25000) ≤ (2295808111 / 1000000000) := by
  have h := checkLog_sound (w := (304 / 2821)) (n := 12)
    (lo := (216366567 / 1000000000)) (hi := (27045821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2517) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 2517) = 1/(2517 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2295808111 / 1000000000) (-2295808107 / 1000000000) (Real.log (2517 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (160654451 / 250000000) ≤ -Real.log (250000 / 475363) ∧
    -Real.log (250000 / 475363) ≤ (128523561 / 200000000) := by
  have h := checkLog_sound (w := (225363 / 725363)) (n := 12)
    (lo := (160654451 / 250000000)) (hi := (128523561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((475363 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(475363 / 250000) = 1/(250000 / 475363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (160654451 / 250000000) (128523561 / 200000000) (Real.log (475363 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (475363 / 250000) = -Real.log (250000 / 475363) := by
    rw [show ((475363 / 250000) : ℝ) = ((250000 / 475363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1158605769 / 500000000) ≤ -Real.log (24637 / 250000) ∧
    -Real.log (24637 / 250000) ≤ (1158605771 / 500000000) := by
  have h := checkLog_sound (w := (6613 / 55887)) (n := 12)
    (lo := (118884999 / 500000000)) (hi := (237769999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24637) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 24637) = 1/(24637 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1158605771 / 500000000) (-1158605769 / 500000000) (Real.log (24637 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2983988137 / 1000000000) ≤ -Real.log (125000000000 / 2470811398727) ∧
    -Real.log (125000000000 / 2470811398727) ≤ (1491994071 / 500000000) := by
  have h := checkLog_sound (w := (470811398727 / 4470811398727)) (n := 12)
    (lo := (211399417 / 1000000000)) (hi := (105699709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2470811398727 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2470811398727 / 2000000000000) = 1/(125000000000 / 2470811398727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2983988137 / 1000000000) (1491994071 / 500000000) (Real.log (2470811398727 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2470811398727 / 125000000000) = -Real.log (125000000000 / 2470811398727) := by
    rw [show ((2470811398727 / 125000000000) : ℝ) = ((125000000000 / 2470811398727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (600982213 / 200000000) ≤ -Real.log (500000000000 / 10092210488407) ∧
    -Real.log (500000000000 / 10092210488407) ≤ (300491107 / 100000000) := by
  have h := checkLog_sound (w := (2092210488407 / 18092210488407)) (n := 12)
    (lo := (46464469 / 200000000)) (hi := (116161173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10092210488407 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10092210488407 / 8000000000000) = 1/(500000000000 / 10092210488407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (600982213 / 200000000) (300491107 / 100000000) (Real.log (10092210488407 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (10092210488407 / 500000000000) = -Real.log (500000000000 / 10092210488407) := by
    rw [show ((10092210488407 / 500000000000) : ℝ) = ((500000000000 / 10092210488407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2937304033 / 1000000000) ≤ -Real.log (125000000000 / 2358114819229) ∧
    -Real.log (125000000000 / 2358114819229) ≤ (1468652019 / 500000000) := by
  have h := checkLog_sound (w := (358114819229 / 4358114819229)) (n := 12)
    (lo := (164715313 / 1000000000)) (hi := (82357657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2358114819229 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2358114819229 / 2000000000000) = 1/(125000000000 / 2358114819229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2937304033 / 1000000000) (1468652019 / 500000000) (Real.log (2358114819229 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2358114819229 / 125000000000) = -Real.log (125000000000 / 2358114819229) := by
    rw [show ((2358114819229 / 125000000000) : ℝ) = ((125000000000 / 2358114819229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1479914671 / 500000000) ≤ -Real.log (250000000000 / 4823669683809) ∧
    -Real.log (250000000000 / 4823669683809) ≤ (2959829347 / 1000000000) := by
  have h := checkLog_sound (w := (823669683809 / 8823669683809)) (n := 12)
    (lo := (93620311 / 500000000)) (hi := (187240623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4823669683809 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4823669683809 / 4000000000000) = 1/(250000000000 / 4823669683809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1479914671 / 500000000) (2959829347 / 1000000000) (Real.log (4823669683809 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4823669683809 / 250000000000) = -Real.log (250000000000 / 4823669683809) := by
    rw [show ((4823669683809 / 250000000000) : ℝ) = ((250000000000 / 4823669683809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0179

end


