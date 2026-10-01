-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0069Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0069Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:57:11.759974+00:00
-- url     : https://prove2.me/theorems/5ab1f5dc-8cd8-47bd-a72f-0a022fcbe772
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0069Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0070Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0069Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0070Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0071Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0072Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0073Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0069Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0070Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0071Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0072Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0073Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0069Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0070Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0071Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0072Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0073Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0069Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0070Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0071Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0072Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0073Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0069Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0069
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

theorem reflection_log_1_neg : (677269847 / 1000000000) ≤ -Real.log (51200 / 100787) ∧
    -Real.log (51200 / 100787) ≤ (84658731 / 125000000) := by
  have h := checkLog_sound (w := (49587 / 151987)) (n := 12)
    (lo := (677269847 / 1000000000)) (hi := (84658731 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100787 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100787 / 51200) = 1/(51200 / 100787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (677269847 / 1000000000) (84658731 / 125000000) (Real.log (100787 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100787 / 51200) = -Real.log (51200 / 100787) := by
    rw [show ((100787 / 51200) : ℝ) = ((51200 / 100787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (345764373 / 100000000) ≤ -Real.log (1613 / 51200) ∧
    -Real.log (1613 / 51200) ≤ (691528747 / 200000000) := by
  have h := checkLog_sound (w := (1587 / 4813)) (n := 12)
    (lo := (68505501 / 100000000)) (hi := (685055011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1613) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1613) = 1/(1613 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-691528747 / 200000000) (-345764373 / 100000000) (Real.log (1613 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (21158791 / 31250000) ≤ -Real.log (1600 / 3149) ∧
    -Real.log (1600 / 3149) ≤ (677081313 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 4749)) (n := 12)
    (lo := (21158791 / 31250000)) (hi := (677081313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3149 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3149 / 1600) = 1/(1600 / 3149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (21158791 / 31250000) (677081313 / 1000000000) (Real.log (3149 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3149 / 1600) = -Real.log (1600 / 3149) := by
    rw [show ((3149 / 1600) : ℝ) = ((1600 / 3149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3445933273 / 1000000000) ≤ -Real.log (51 / 1600) ∧
    -Real.log (51 / 1600) ≤ (1722966639 / 500000000) := by
  have h := checkLog_sound (w := (49 / 151)) (n := 12)
    (lo := (673344553 / 1000000000)) (hi := (336672277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 51) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 51) = 1/(51 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1722966639 / 500000000) (-3445933273 / 1000000000) (Real.log (51 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (661136351 / 1000000000) ≤ -Real.log (25600 / 49587) ∧
    -Real.log (25600 / 49587) ≤ (20660511 / 31250000) := by
  have h := checkLog_sound (w := (23987 / 75187)) (n := 12)
    (lo := (661136351 / 1000000000)) (hi := (20660511 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49587 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49587 / 25600) = 1/(25600 / 49587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (661136351 / 1000000000) (20660511 / 31250000) (Real.log (49587 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49587 / 25600) = -Real.log (25600 / 49587) := by
    rw [show ((49587 / 25600) : ℝ) = ((25600 / 49587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (55289931 / 20000000) ≤ -Real.log (1613 / 25600) ∧
    -Real.log (1613 / 25600) ≤ (1382248277 / 500000000) := by
  have h := checkLog_sound (w := (1587 / 4813)) (n := 12)
    (lo := (68505501 / 100000000)) (hi := (685055011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1613) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1613) = 1/(1613 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1382248277 / 500000000) (-55289931 / 20000000) (Real.log (1613 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (82594139 / 125000000) ≤ -Real.log (800 / 1549) ∧
    -Real.log (800 / 1549) ≤ (660753113 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 2349)) (n := 12)
    (lo := (82594139 / 125000000)) (hi := (660753113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1549 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1549 / 800) = 1/(800 / 1549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (82594139 / 125000000) (660753113 / 1000000000) (Real.log (1549 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1549 / 800) = -Real.log (800 / 1549) := by
    rw [show ((1549 / 800) : ℝ) = ((800 / 1549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2752786093 / 1000000000) ≤ -Real.log (51 / 800) ∧
    -Real.log (51 / 800) ≤ (2752786097 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 151)) (n := 12)
    (lo := (673344553 / 1000000000)) (hi := (336672277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 51) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 51) = 1/(51 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2752786097 / 1000000000) (-2752786093 / 1000000000) (Real.log (51 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135954629 / 200000000) ≤ -Real.log (100000 / 197343) ∧
    -Real.log (100000 / 197343) ≤ (339886573 / 500000000) := by
  have h := checkLog_sound (w := (97343 / 297343)) (n := 12)
    (lo := (135954629 / 200000000)) (hi := (339886573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197343 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197343 / 100000) = 1/(100000 / 197343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135954629 / 200000000) (339886573 / 500000000) (Real.log (197343 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (197343 / 100000) = -Real.log (100000 / 197343) := by
    rw [show ((197343 / 100000) : ℝ) = ((100000 / 197343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (906993129 / 250000000) ≤ -Real.log (2657 / 100000) ∧
    -Real.log (2657 / 100000) ≤ (1813986261 / 500000000) := by
  have h := checkLog_sound (w := (234 / 2891)) (n := 12)
    (lo := (20279577 / 125000000)) (hi := (162236617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2657) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2657) = 1/(2657 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1813986261 / 500000000) (-906993129 / 250000000) (Real.log (2657 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339961563 / 500000000) ≤ -Real.log (500000 / 986863) ∧
    -Real.log (500000 / 986863) ≤ (679923127 / 1000000000) := by
  have h := checkLog_sound (w := (486863 / 1486863)) (n := 12)
    (lo := (339961563 / 500000000)) (hi := (679923127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986863 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986863 / 500000) = 1/(500000 / 986863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339961563 / 500000000) (679923127 / 1000000000) (Real.log (986863 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (986863 / 500000) = -Real.log (500000 / 986863) := by
    rw [show ((986863 / 500000) : ℝ) = ((500000 / 986863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3639175419 / 1000000000) ≤ -Real.log (13137 / 500000) ∧
    -Real.log (13137 / 500000) ≤ (145567017 / 40000000) := by
  have h := checkLog_sound (w := (1244 / 14381)) (n := 12)
    (lo := (173439519 / 1000000000)) (hi := (1083997 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13137) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13137) = 1/(13137 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-145567017 / 40000000) (-3639175419 / 1000000000) (Real.log (13137 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (679685477 / 1000000000) ≤ -Real.log (1000000 / 1973257) ∧
    -Real.log (1000000 / 1973257) ≤ (339842739 / 500000000) := by
  have h := checkLog_sound (w := (973257 / 2973257)) (n := 12)
    (lo := (679685477 / 1000000000)) (hi := (339842739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1973257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1973257 / 1000000) = 1/(1000000 / 1973257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (679685477 / 1000000000) (339842739 / 500000000) (Real.log (1973257 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1973257 / 1000000) = -Real.log (1000000 / 1973257) := by
    rw [show ((1973257 / 1000000) : ℝ) = ((1000000 / 1973257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3621482519 / 1000000000) ≤ -Real.log (26743 / 1000000) ∧
    -Real.log (26743 / 1000000) ≤ (144859301 / 40000000) := by
  have h := checkLog_sound (w := (4507 / 57993)) (n := 12)
    (lo := (155746619 / 1000000000)) (hi := (7787331 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26743) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 26743) = 1/(26743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-144859301 / 40000000) (-3621482519 / 1000000000) (Real.log (26743 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (679836991 / 1000000000) ≤ -Real.log (250000 / 493389) ∧
    -Real.log (250000 / 493389) ≤ (10622453 / 15625000) := by
  have h := checkLog_sound (w := (243389 / 743389)) (n := 12)
    (lo := (679836991 / 1000000000)) (hi := (10622453 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493389 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493389 / 250000) = 1/(250000 / 493389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (679836991 / 1000000000) (10622453 / 15625000) (Real.log (493389 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (493389 / 250000) = -Real.log (250000 / 493389) := by
    rw [show ((493389 / 250000) : ℝ) = ((250000 / 493389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1816362993 / 500000000) ≤ -Real.log (6611 / 250000) ∧
    -Real.log (6611 / 250000) ≤ (454090749 / 125000000) := by
  have h := checkLog_sound (w := (2403 / 28847)) (n := 12)
    (lo := (83495043 / 500000000)) (hi := (166990087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13222) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13222) = 1/(6611 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-454090749 / 125000000) (-1816362993 / 500000000) (Real.log (6611 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4307745661 / 1000000000) ≤ -Real.log (1562500000 / 116051350207) ∧
    -Real.log (1562500000 / 116051350207) ≤ (1076936417 / 250000000) := by
  have h := checkLog_sound (w := (16051350207 / 216051350207)) (n := 12)
    (lo := (148862581 / 1000000000)) (hi := (74431291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116051350207 / 100000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(116051350207 / 100000000000) = 1/(1562500000 / 116051350207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4307745661 / 1000000000) (1076936417 / 250000000) (Real.log (116051350207 / 1562500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (116051350207 / 1562500000) = -Real.log (1562500000 / 116051350207) := by
    rw [show ((116051350207 / 1562500000) : ℝ) = ((1562500000 / 116051350207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (863819709 / 200000000) ≤ -Real.log (500000000000 / 37560439978687) ∧
    -Real.log (500000000000 / 37560439978687) ≤ (539887319 / 125000000) := by
  have h := checkLog_sound (w := (5560439978687 / 69560439978687)) (n := 12)
    (lo := (32043093 / 200000000)) (hi := (80107733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37560439978687 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37560439978687 / 32000000000000) = 1/(500000000000 / 37560439978687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (863819709 / 200000000) (539887319 / 125000000) (Real.log (37560439978687 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (37560439978687 / 500000000000) = -Real.log (500000000000 / 37560439978687) := by
    rw [show ((37560439978687 / 500000000000) : ℝ) = ((500000000000 / 37560439978687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (860233599 / 200000000) ≤ -Real.log (50000000000 / 3689296264443) ∧
    -Real.log (50000000000 / 3689296264443) ≤ (2150584001 / 500000000) := by
  have h := checkLog_sound (w := (489296264443 / 6889296264443)) (n := 12)
    (lo := (28456983 / 200000000)) (hi := (35571229 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3689296264443 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3689296264443 / 3200000000000) = 1/(50000000000 / 3689296264443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (860233599 / 200000000) (2150584001 / 500000000) (Real.log (3689296264443 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3689296264443 / 50000000000) = -Real.log (50000000000 / 3689296264443) := by
    rw [show ((3689296264443 / 50000000000) : ℝ) = ((50000000000 / 3689296264443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4312562977 / 1000000000) ≤ -Real.log (500000000000 / 37315761609439) ∧
    -Real.log (500000000000 / 37315761609439) ≤ (539070373 / 125000000) := by
  have h := checkLog_sound (w := (5315761609439 / 69315761609439)) (n := 12)
    (lo := (153679897 / 1000000000)) (hi := (76839949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37315761609439 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37315761609439 / 32000000000000) = 1/(500000000000 / 37315761609439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4312562977 / 1000000000) (539070373 / 125000000) (Real.log (37315761609439 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (37315761609439 / 500000000000) = -Real.log (500000000000 / 37315761609439) := by
    rw [show ((37315761609439 / 500000000000) : ℝ) = ((500000000000 / 37315761609439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0069

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0070Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0070
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

theorem reflection_log_1_neg : (21158791 / 31250000) ≤ -Real.log (1600 / 3149) ∧
    -Real.log (1600 / 3149) ≤ (677081313 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 4749)) (n := 12)
    (lo := (21158791 / 31250000)) (hi := (677081313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3149 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3149 / 1600) = 1/(1600 / 3149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (21158791 / 31250000) (677081313 / 1000000000) (Real.log (3149 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3149 / 1600) = -Real.log (1600 / 3149) := by
    rw [show ((3149 / 1600) : ℝ) = ((1600 / 3149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3445933273 / 1000000000) ≤ -Real.log (51 / 1600) ∧
    -Real.log (51 / 1600) ≤ (1722966639 / 500000000) := by
  have h := checkLog_sound (w := (49 / 151)) (n := 12)
    (lo := (673344553 / 1000000000)) (hi := (336672277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 51) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 51) = 1/(51 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1722966639 / 500000000) (-3445933273 / 1000000000) (Real.log (51 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (676892743 / 1000000000) ≤ -Real.log (51200 / 100749) ∧
    -Real.log (51200 / 100749) ≤ (84611593 / 125000000) := by
  have h := checkLog_sound (w := (49549 / 151949)) (n := 12)
    (lo := (676892743 / 1000000000)) (hi := (84611593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100749 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100749 / 51200) = 1/(51200 / 100749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (676892743 / 1000000000) (84611593 / 125000000) (Real.log (100749 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100749 / 51200) = -Real.log (51200 / 100749) := by
    rw [show ((100749 / 51200) : ℝ) = ((51200 / 100749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (858589591 / 250000000) ≤ -Real.log (1651 / 51200) ∧
    -Real.log (1651 / 51200) ≤ (3434358369 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 4851)) (n := 12)
    (lo := (165442411 / 250000000)) (hi := (132353929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1651) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1651) = 1/(1651 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3434358369 / 1000000000) (-858589591 / 250000000) (Real.log (1651 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (82594139 / 125000000) ≤ -Real.log (800 / 1549) ∧
    -Real.log (800 / 1549) ≤ (660753113 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 2349)) (n := 12)
    (lo := (82594139 / 125000000)) (hi := (660753113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1549 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1549 / 800) = 1/(800 / 1549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (82594139 / 125000000) (660753113 / 1000000000) (Real.log (1549 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1549 / 800) = -Real.log (800 / 1549) := by
    rw [show ((1549 / 800) : ℝ) = ((800 / 1549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2752786093 / 1000000000) ≤ -Real.log (51 / 800) ∧
    -Real.log (51 / 800) ≤ (2752786097 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 151)) (n := 12)
    (lo := (673344553 / 1000000000)) (hi := (336672277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 51) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 51) = 1/(51 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2752786097 / 1000000000) (-2752786093 / 1000000000) (Real.log (51 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (660369727 / 1000000000) ≤ -Real.log (25600 / 49549) ∧
    -Real.log (25600 / 49549) ≤ (10318277 / 15625000) := by
  have h := checkLog_sound (w := (23949 / 75149)) (n := 12)
    (lo := (660369727 / 1000000000)) (hi := (10318277 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49549 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49549 / 25600) = 1/(25600 / 49549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (660369727 / 1000000000) (10318277 / 15625000) (Real.log (49549 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49549 / 25600) = -Real.log (25600 / 49549) := by
    rw [show ((49549 / 25600) : ℝ) = ((25600 / 49549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (171325699 / 62500000) ≤ -Real.log (1651 / 25600) ∧
    -Real.log (1651 / 25600) ≤ (685302797 / 250000000) := by
  have h := checkLog_sound (w := (1549 / 4851)) (n := 12)
    (lo := (165442411 / 250000000)) (hi := (132353929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1651) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1651) = 1/(1651 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-685302797 / 250000000) (-171325699 / 62500000) (Real.log (1651 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (339812331 / 500000000) ≤ -Real.log (1000000 / 1973137) ∧
    -Real.log (1000000 / 1973137) ≤ (679624663 / 1000000000) := by
  have h := checkLog_sound (w := (973137 / 2973137)) (n := 12)
    (lo := (339812331 / 500000000)) (hi := (679624663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1973137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1973137 / 1000000) = 1/(1000000 / 1973137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (339812331 / 500000000) (679624663 / 1000000000) (Real.log (1973137 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1973137 / 1000000) = -Real.log (1000000 / 1973137) := by
    rw [show ((1973137 / 1000000) : ℝ) = ((1000000 / 1973137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3617005401 / 1000000000) ≤ -Real.log (26863 / 1000000) ∧
    -Real.log (26863 / 1000000) ≤ (3617005407 / 1000000000) := by
  have h := checkLog_sound (w := (4387 / 58113)) (n := 12)
    (lo := (151269501 / 1000000000)) (hi := (75634751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26863) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 26863) = 1/(26863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3617005407 / 1000000000) (-3617005401 / 1000000000) (Real.log (26863 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169943413 / 250000000) ≤ -Real.log (1000000 / 1973431) ∧
    -Real.log (1000000 / 1973431) ≤ (679773653 / 1000000000) := by
  have h := checkLog_sound (w := (973431 / 2973431)) (n := 12)
    (lo := (169943413 / 250000000)) (hi := (679773653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1973431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1973431 / 1000000) = 1/(1000000 / 1973431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169943413 / 250000000) (679773653 / 1000000000) (Real.log (1973431 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1973431 / 1000000) = -Real.log (1000000 / 1973431) := by
    rw [show ((1973431 / 1000000) : ℝ) = ((1000000 / 1973431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3628010153 / 1000000000) ≤ -Real.log (26569 / 1000000) ∧
    -Real.log (26569 / 1000000) ≤ (3628010159 / 1000000000) := by
  have h := checkLog_sound (w := (4681 / 57819)) (n := 12)
    (lo := (162274253 / 1000000000)) (hi := (81137127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26569) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 26569) = 1/(26569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3628010159 / 1000000000) (-3628010153 / 1000000000) (Real.log (26569 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (679533939 / 1000000000) ≤ -Real.log (500000 / 986479) ∧
    -Real.log (500000 / 986479) ≤ (33976697 / 50000000) := by
  have h := checkLog_sound (w := (486479 / 1486479)) (n := 12)
    (lo := (679533939 / 1000000000)) (hi := (33976697 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986479 / 500000) = 1/(500000 / 986479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (679533939 / 1000000000) (33976697 / 50000000) (Real.log (986479 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (986479 / 500000) = -Real.log (500000 / 986479) := by
    rw [show ((986479 / 500000) : ℝ) = ((500000 / 986479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3610364063 / 1000000000) ≤ -Real.log (13521 / 500000) ∧
    -Real.log (13521 / 500000) ≤ (3610364069 / 1000000000) := by
  have h := checkLog_sound (w := (1052 / 14573)) (n := 12)
    (lo := (144628163 / 1000000000)) (hi := (36157041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13521) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13521) = 1/(13521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3610364069 / 1000000000) (-3610364063 / 1000000000) (Real.log (13521 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (679685983 / 1000000000) ≤ -Real.log (500000 / 986629) ∧
    -Real.log (500000 / 986629) ≤ (21240187 / 31250000) := by
  have h := checkLog_sound (w := (486629 / 1486629)) (n := 12)
    (lo := (679685983 / 1000000000)) (hi := (21240187 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986629 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986629 / 500000) = 1/(500000 / 986629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (679685983 / 1000000000) (21240187 / 31250000) (Real.log (986629 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (986629 / 500000) = -Real.log (500000 / 986629) := by
    rw [show ((986629 / 500000) : ℝ) = ((500000 / 986629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (452689989 / 125000000) ≤ -Real.log (13371 / 500000) ∧
    -Real.log (13371 / 500000) ≤ (1810759959 / 500000000) := by
  have h := checkLog_sound (w := (1127 / 14498)) (n := 12)
    (lo := (38946003 / 250000000)) (hi := (155784013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13371) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13371) = 1/(13371 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1810759959 / 500000000) (-452689989 / 125000000) (Real.log (13371 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2148315031 / 500000000) ≤ -Real.log (250000000000 / 18362962066783) ∧
    -Real.log (250000000000 / 18362962066783) ≤ (4296630069 / 1000000000) := by
  have h := checkLog_sound (w := (2362962066783 / 34362962066783)) (n := 12)
    (lo := (68873491 / 500000000)) (hi := (137746983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18362962066783 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18362962066783 / 16000000000000) = 1/(250000000000 / 18362962066783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2148315031 / 500000000) (4296630069 / 1000000000) (Real.log (18362962066783 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (18362962066783 / 250000000000) = -Real.log (250000000000 / 18362962066783) := by
    rw [show ((18362962066783 / 250000000000) : ℝ) = ((250000000000 / 18362962066783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (861556761 / 200000000) ≤ -Real.log (500000000000 / 37137848620573) ∧
    -Real.log (500000000000 / 37137848620573) ≤ (1076945953 / 250000000) := by
  have h := checkLog_sound (w := (5137848620573 / 69137848620573)) (n := 12)
    (lo := (5956029 / 40000000)) (hi := (74450363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37137848620573 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37137848620573 / 32000000000000) = 1/(500000000000 / 37137848620573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (861556761 / 200000000) (1076945953 / 250000000) (Real.log (37137848620573 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (37137848620573 / 500000000000) = -Real.log (500000000000 / 37137848620573) := by
    rw [show ((37137848620573 / 500000000000) : ℝ) = ((500000000000 / 37137848620573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2144949001 / 500000000) ≤ -Real.log (125000000000 / 9119878337401) ∧
    -Real.log (125000000000 / 9119878337401) ≤ (4289898009 / 1000000000) := by
  have h := checkLog_sound (w := (1119878337401 / 17119878337401)) (n := 12)
    (lo := (65507461 / 500000000)) (hi := (131014923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9119878337401 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9119878337401 / 8000000000000) = 1/(125000000000 / 9119878337401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2144949001 / 500000000) (4289898009 / 1000000000) (Real.log (9119878337401 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9119878337401 / 125000000000) = -Real.log (125000000000 / 9119878337401) := by
    rw [show ((9119878337401 / 125000000000) : ℝ) = ((125000000000 / 9119878337401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (537650737 / 125000000) ≤ -Real.log (125000000000 / 9223590232593) ∧
    -Real.log (125000000000 / 9223590232593) ≤ (4301205903 / 1000000000) := by
  have h := checkLog_sound (w := (1223590232593 / 17223590232593)) (n := 12)
    (lo := (1111897 / 7812500)) (hi := (142322817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9223590232593 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9223590232593 / 8000000000000) = 1/(125000000000 / 9223590232593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (537650737 / 125000000) (4301205903 / 1000000000) (Real.log (9223590232593 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9223590232593 / 125000000000) = -Real.log (125000000000 / 9223590232593) := by
    rw [show ((9223590232593 / 125000000000) : ℝ) = ((125000000000 / 9223590232593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0070

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0071Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0071
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

theorem reflection_log_1_neg : (676892743 / 1000000000) ≤ -Real.log (51200 / 100749) ∧
    -Real.log (51200 / 100749) ≤ (84611593 / 125000000) := by
  have h := checkLog_sound (w := (49549 / 151949)) (n := 12)
    (lo := (676892743 / 1000000000)) (hi := (84611593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100749 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100749 / 51200) = 1/(51200 / 100749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (676892743 / 1000000000) (84611593 / 125000000) (Real.log (100749 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100749 / 51200) = -Real.log (51200 / 100749) := by
    rw [show ((100749 / 51200) : ℝ) = ((51200 / 100749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (858589591 / 250000000) ≤ -Real.log (1651 / 51200) ∧
    -Real.log (1651 / 51200) ≤ (3434358369 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 4851)) (n := 12)
    (lo := (165442411 / 250000000)) (hi := (132353929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1651) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1651) = 1/(1651 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3434358369 / 1000000000) (-858589591 / 250000000) (Real.log (1651 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (676704137 / 1000000000) ≤ -Real.log (5120 / 10073) ∧
    -Real.log (5120 / 10073) ≤ (338352069 / 500000000) := by
  have h := checkLog_sound (w := (4953 / 15193)) (n := 12)
    (lo := (676704137 / 1000000000)) (hi := (338352069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10073 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10073 / 5120) = 1/(5120 / 10073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (676704137 / 1000000000) (338352069 / 500000000) (Real.log (10073 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (10073 / 5120) = -Real.log (5120 / 10073) := by
    rw [show ((10073 / 5120) : ℝ) = ((5120 / 10073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3422915903 / 1000000000) ≤ -Real.log (167 / 5120) ∧
    -Real.log (167 / 5120) ≤ (855728977 / 250000000) := by
  have h := checkLog_sound (w := (153 / 487)) (n := 12)
    (lo := (650327183 / 1000000000)) (hi := (40645449 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 167) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 167) = 1/(167 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-855728977 / 250000000) (-3422915903 / 1000000000) (Real.log (167 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (660369727 / 1000000000) ≤ -Real.log (25600 / 49549) ∧
    -Real.log (25600 / 49549) ≤ (10318277 / 15625000) := by
  have h := checkLog_sound (w := (23949 / 75149)) (n := 12)
    (lo := (660369727 / 1000000000)) (hi := (10318277 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49549 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49549 / 25600) = 1/(25600 / 49549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (660369727 / 1000000000) (10318277 / 15625000) (Real.log (49549 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49549 / 25600) = -Real.log (25600 / 49549) := by
    rw [show ((49549 / 25600) : ℝ) = ((25600 / 49549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (171325699 / 62500000) ≤ -Real.log (1651 / 25600) ∧
    -Real.log (1651 / 25600) ≤ (685302797 / 250000000) := by
  have h := checkLog_sound (w := (1549 / 4851)) (n := 12)
    (lo := (165442411 / 250000000)) (hi := (132353929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1651) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1651) = 1/(1651 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-685302797 / 250000000) (-171325699 / 62500000) (Real.log (1651 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (131997239 / 200000000) ≤ -Real.log (2560 / 4953) ∧
    -Real.log (2560 / 4953) ≤ (164996549 / 250000000) := by
  have h := checkLog_sound (w := (2393 / 7513)) (n := 12)
    (lo := (131997239 / 200000000)) (hi := (164996549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4953 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4953 / 2560) = 1/(2560 / 4953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (131997239 / 200000000) (164996549 / 250000000) (Real.log (4953 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4953 / 2560) = -Real.log (2560 / 4953) := by
    rw [show ((4953 / 2560) : ℝ) = ((2560 / 4953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2729768723 / 1000000000) ≤ -Real.log (167 / 2560) ∧
    -Real.log (167 / 2560) ≤ (2729768727 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 487)) (n := 12)
    (lo := (650327183 / 1000000000)) (hi := (40645449 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 167) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 167) = 1/(167 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2729768727 / 1000000000) (-2729768723 / 1000000000) (Real.log (167 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (679475649 / 1000000000) ≤ -Real.log (1000000 / 1972843) ∧
    -Real.log (1000000 / 1972843) ≤ (13589513 / 20000000) := by
  have h := checkLog_sound (w := (972843 / 2972843)) (n := 12)
    (lo := (679475649 / 1000000000)) (hi := (13589513 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972843 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972843 / 1000000) = 1/(1000000 / 1972843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (679475649 / 1000000000) (13589513 / 20000000) (Real.log (1972843 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1972843 / 1000000) = -Real.log (1000000 / 1972843) := by
    rw [show ((1972843 / 1000000) : ℝ) = ((1000000 / 1972843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (901530109 / 250000000) ≤ -Real.log (27157 / 1000000) ∧
    -Real.log (27157 / 1000000) ≤ (1803060221 / 500000000) := by
  have h := checkLog_sound (w := (4093 / 58407)) (n := 12)
    (lo := (17548067 / 125000000)) (hi := (140384537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27157) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27157) = 1/(27157 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1803060221 / 500000000) (-901530109 / 250000000) (Real.log (27157 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42476573 / 62500000) ≤ -Real.log (500000 / 986569) ∧
    -Real.log (500000 / 986569) ≤ (679625169 / 1000000000) := by
  have h := checkLog_sound (w := (486569 / 1486569)) (n := 12)
    (lo := (42476573 / 62500000)) (hi := (679625169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986569 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986569 / 500000) = 1/(500000 / 986569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42476573 / 62500000) (679625169 / 1000000000) (Real.log (986569 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (986569 / 500000) = -Real.log (500000 / 986569) := by
    rw [show ((986569 / 500000) : ℝ) = ((500000 / 986569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3617042627 / 1000000000) ≤ -Real.log (13431 / 500000) ∧
    -Real.log (13431 / 500000) ≤ (3617042633 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 14528)) (n := 12)
    (lo := (151306727 / 1000000000)) (hi := (18913341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13431) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13431) = 1/(13431 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3617042633 / 1000000000) (-3617042627 / 1000000000) (Real.log (13431 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (135876577 / 200000000) ≤ -Real.log (50000 / 98633) ∧
    -Real.log (50000 / 98633) ≤ (339691443 / 500000000) := by
  have h := checkLog_sound (w := (48633 / 148633)) (n := 12)
    (lo := (135876577 / 200000000)) (hi := (339691443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98633 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98633 / 50000) = 1/(50000 / 98633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (135876577 / 200000000) (339691443 / 500000000) (Real.log (98633 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (98633 / 50000) = -Real.log (50000 / 98633) := by
    rw [show ((98633 / 50000) : ℝ) = ((50000 / 98633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (899851111 / 250000000) ≤ -Real.log (1367 / 50000) ∧
    -Real.log (1367 / 50000) ≤ (71988089 / 20000000) := by
  have h := checkLog_sound (w := (391 / 5859)) (n := 12)
    (lo := (2088571 / 15625000)) (hi := (26733709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2734) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2734) = 1/(1367 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-71988089 / 20000000) (-899851111 / 250000000) (Real.log (1367 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (339767223 / 500000000) ≤ -Real.log (1000000 / 1972959) ∧
    -Real.log (1000000 / 1972959) ≤ (679534447 / 1000000000) := by
  have h := checkLog_sound (w := (972959 / 2972959)) (n := 12)
    (lo := (339767223 / 500000000)) (hi := (679534447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972959 / 1000000) = 1/(1000000 / 1972959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (339767223 / 500000000) (679534447 / 1000000000) (Real.log (1972959 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1972959 / 1000000) = -Real.log (1000000 / 1972959) := by
    rw [show ((1972959 / 1000000) : ℝ) = ((1000000 / 1972959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3610401043 / 1000000000) ≤ -Real.log (27041 / 1000000) ∧
    -Real.log (27041 / 1000000) ≤ (3610401049 / 1000000000) := by
  have h := checkLog_sound (w := (4209 / 58291)) (n := 12)
    (lo := (144665143 / 1000000000)) (hi := (18083143 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27041) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27041) = 1/(27041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3610401049 / 1000000000) (-3610401043 / 1000000000) (Real.log (27041 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (857119217 / 200000000) ≤ -Real.log (500000000000 / 36322918584527) ∧
    -Real.log (500000000000 / 36322918584527) ≤ (1071399023 / 250000000) := by
  have h := checkLog_sound (w := (4322918584527 / 68322918584527)) (n := 12)
    (lo := (25342601 / 200000000)) (hi := (63356503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36322918584527 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(36322918584527 / 32000000000000) = 1/(500000000000 / 36322918584527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (857119217 / 200000000) (1071399023 / 250000000) (Real.log (36322918584527 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (36322918584527 / 500000000000) = -Real.log (500000000000 / 36322918584527) := by
    rw [show ((36322918584527 / 500000000000) : ℝ) = ((500000000000 / 36322918584527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (859333559 / 200000000) ≤ -Real.log (500000000000 / 36727309954583) ∧
    -Real.log (500000000000 / 36727309954583) ≤ (2148333901 / 500000000) := by
  have h := checkLog_sound (w := (4727309954583 / 68727309954583)) (n := 12)
    (lo := (27556943 / 200000000)) (hi := (34446179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36727309954583 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(36727309954583 / 32000000000000) = 1/(500000000000 / 36727309954583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (859333559 / 200000000) (2148333901 / 500000000) (Real.log (36727309954583 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (36727309954583 / 500000000000) = -Real.log (500000000000 / 36727309954583) := by
    rw [show ((36727309954583 / 500000000000) : ℝ) = ((500000000000 / 36727309954583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (427878733 / 100000000) ≤ -Real.log (15625000000 / 1127388899049) ∧
    -Real.log (15625000000 / 1127388899049) ≤ (4278787337 / 1000000000) := by
  have h := checkLog_sound (w := (127388899049 / 2127388899049)) (n := 12)
    (lo := (479617 / 4000000)) (hi := (119904251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127388899049 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1127388899049 / 1000000000000) = 1/(15625000000 / 1127388899049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (427878733 / 100000000) (4278787337 / 1000000000) (Real.log (1127388899049 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1127388899049 / 15625000000) = -Real.log (15625000000 / 1127388899049) := by
    rw [show ((1127388899049 / 15625000000) : ℝ) = ((15625000000 / 1127388899049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4289935489 / 1000000000) ≤ -Real.log (500000000000 / 36480880884583) ∧
    -Real.log (500000000000 / 36480880884583) ≤ (536241937 / 125000000) := by
  have h := checkLog_sound (w := (4480880884583 / 68480880884583)) (n := 12)
    (lo := (131052409 / 1000000000)) (hi := (13105241 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36480880884583 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(36480880884583 / 32000000000000) = 1/(500000000000 / 36480880884583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4289935489 / 1000000000) (536241937 / 125000000) (Real.log (36480880884583 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (36480880884583 / 500000000000) = -Real.log (500000000000 / 36480880884583) := by
    rw [show ((36480880884583 / 500000000000) : ℝ) = ((500000000000 / 36480880884583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0071

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0072Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0072
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

theorem reflection_log_1_neg : (676704137 / 1000000000) ≤ -Real.log (5120 / 10073) ∧
    -Real.log (5120 / 10073) ≤ (338352069 / 500000000) := by
  have h := checkLog_sound (w := (4953 / 15193)) (n := 12)
    (lo := (676704137 / 1000000000)) (hi := (338352069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10073 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10073 / 5120) = 1/(5120 / 10073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (676704137 / 1000000000) (338352069 / 500000000) (Real.log (10073 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (10073 / 5120) = -Real.log (5120 / 10073) := by
    rw [show ((10073 / 5120) : ℝ) = ((5120 / 10073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3422915903 / 1000000000) ≤ -Real.log (167 / 5120) ∧
    -Real.log (167 / 5120) ≤ (855728977 / 250000000) := by
  have h := checkLog_sound (w := (153 / 487)) (n := 12)
    (lo := (650327183 / 1000000000)) (hi := (40645449 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 167) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 167) = 1/(167 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-855728977 / 250000000) (-3422915903 / 1000000000) (Real.log (167 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (676515497 / 1000000000) ≤ -Real.log (51200 / 100711) ∧
    -Real.log (51200 / 100711) ≤ (338257749 / 500000000) := by
  have h := checkLog_sound (w := (49511 / 151911)) (n := 12)
    (lo := (676515497 / 1000000000)) (hi := (338257749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100711 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100711 / 51200) = 1/(51200 / 100711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (676515497 / 1000000000) (338257749 / 500000000) (Real.log (100711 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100711 / 51200) = -Real.log (51200 / 100711) := by
    rw [show ((100711 / 51200) : ℝ) = ((51200 / 100711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3411602891 / 1000000000) ≤ -Real.log (1689 / 51200) ∧
    -Real.log (1689 / 51200) ≤ (213225181 / 62500000) := by
  have h := checkLog_sound (w := (1511 / 4889)) (n := 12)
    (lo := (639014171 / 1000000000)) (hi := (159753543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1689) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1689) = 1/(1689 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-213225181 / 62500000) (-3411602891 / 1000000000) (Real.log (1689 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (131997239 / 200000000) ≤ -Real.log (2560 / 4953) ∧
    -Real.log (2560 / 4953) ≤ (164996549 / 250000000) := by
  have h := checkLog_sound (w := (2393 / 7513)) (n := 12)
    (lo := (131997239 / 200000000)) (hi := (164996549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4953 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4953 / 2560) = 1/(2560 / 4953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (131997239 / 200000000) (164996549 / 250000000) (Real.log (4953 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4953 / 2560) = -Real.log (2560 / 4953) := by
    rw [show ((4953 / 2560) : ℝ) = ((2560 / 4953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2729768723 / 1000000000) ≤ -Real.log (167 / 2560) ∧
    -Real.log (167 / 2560) ≤ (2729768727 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 487)) (n := 12)
    (lo := (650327183 / 1000000000)) (hi := (40645449 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 167) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 167) = 1/(167 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2729768727 / 1000000000) (-2729768723 / 1000000000) (Real.log (167 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (131920503 / 200000000) ≤ -Real.log (25600 / 49511) ∧
    -Real.log (25600 / 49511) ≤ (164900629 / 250000000) := by
  have h := checkLog_sound (w := (23911 / 75111)) (n := 12)
    (lo := (131920503 / 200000000)) (hi := (164900629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49511 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49511 / 25600) = 1/(25600 / 49511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (131920503 / 200000000) (164900629 / 250000000) (Real.log (49511 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49511 / 25600) = -Real.log (25600 / 49511) := by
    rw [show ((49511 / 25600) : ℝ) = ((25600 / 49511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2718455711 / 1000000000) ≤ -Real.log (1689 / 25600) ∧
    -Real.log (1689 / 25600) ≤ (543691143 / 200000000) := by
  have h := checkLog_sound (w := (1511 / 4889)) (n := 12)
    (lo := (639014171 / 1000000000)) (hi := (159753543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1689) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1689) = 1/(1689 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-543691143 / 200000000) (-2718455711 / 1000000000) (Real.log (1689 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (679327121 / 1000000000) ≤ -Real.log (20000 / 39451) ∧
    -Real.log (20000 / 39451) ≤ (339663561 / 500000000) := by
  have h := checkLog_sound (w := (19451 / 59451)) (n := 12)
    (lo := (679327121 / 1000000000)) (hi := (339663561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39451 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39451 / 20000) = 1/(20000 / 39451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (679327121 / 1000000000) (339663561 / 500000000) (Real.log (39451 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (39451 / 20000) = -Real.log (20000 / 39451) := by
    rw [show ((39451 / 20000) : ℝ) = ((20000 / 39451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (898847277 / 250000000) ≤ -Real.log (549 / 20000) ∧
    -Real.log (549 / 20000) ≤ (1797694557 / 500000000) := by
  have h := checkLog_sound (w := (38 / 587)) (n := 12)
    (lo := (16206651 / 125000000)) (hi := (129653209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 549) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(625 / 549) = 1/(549 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1797694557 / 500000000) (-898847277 / 250000000) (Real.log (549 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169869039 / 250000000) ≤ -Real.log (250000 / 493211) ∧
    -Real.log (250000 / 493211) ≤ (679476157 / 1000000000) := by
  have h := checkLog_sound (w := (243211 / 743211)) (n := 12)
    (lo := (169869039 / 250000000)) (hi := (679476157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493211 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493211 / 250000) = 1/(250000 / 493211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169869039 / 250000000) (679476157 / 1000000000) (Real.log (493211 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (493211 / 250000) = -Real.log (250000 / 493211) := by
    rw [show ((493211 / 250000) : ℝ) = ((250000 / 493211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3606157259 / 1000000000) ≤ -Real.log (6789 / 250000) ∧
    -Real.log (6789 / 250000) ≤ (721231453 / 200000000) := by
  have h := checkLog_sound (w := (2047 / 29203)) (n := 12)
    (lo := (140421359 / 1000000000)) (hi := (1755267 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13578) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13578) = 1/(6789 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-721231453 / 200000000) (-3606157259 / 1000000000) (Real.log (6789 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (679231809 / 1000000000) ≤ -Real.log (500000 / 986181) ∧
    -Real.log (500000 / 986181) ≤ (67923181 / 100000000) := by
  have h := checkLog_sound (w := (486181 / 1486181)) (n := 12)
    (lo := (679231809 / 1000000000)) (hi := (67923181 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986181 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986181 / 500000) = 1/(500000 / 986181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (679231809 / 1000000000) (67923181 / 100000000) (Real.log (986181 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (986181 / 500000) = -Real.log (500000 / 986181) := by
    rw [show ((986181 / 500000) : ℝ) = ((500000 / 986181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1794281819 / 500000000) ≤ -Real.log (13819 / 500000) ∧
    -Real.log (13819 / 500000) ≤ (897140911 / 250000000) := by
  have h := checkLog_sound (w := (903 / 14722)) (n := 12)
    (lo := (61413869 / 500000000)) (hi := (122827739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13819) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13819) = 1/(13819 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-897140911 / 250000000) (-1794281819 / 500000000) (Real.log (13819 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21230731 / 31250000) ≤ -Real.log (1000000 / 1972661) ∧
    -Real.log (1000000 / 1972661) ≤ (679383393 / 1000000000) := by
  have h := checkLog_sound (w := (972661 / 2972661)) (n := 12)
    (lo := (21230731 / 31250000)) (hi := (679383393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972661 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972661 / 1000000) = 1/(1000000 / 1972661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21230731 / 31250000) (679383393 / 1000000000) (Real.log (1972661 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1972661 / 1000000) = -Real.log (1000000 / 1972661) := by
    rw [show ((1972661 / 1000000) : ℝ) = ((1000000 / 1972661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1799720511 / 500000000) ≤ -Real.log (27339 / 1000000) ∧
    -Real.log (27339 / 1000000) ≤ (899860257 / 250000000) := by
  have h := checkLog_sound (w := (3911 / 58589)) (n := 12)
    (lo := (66852561 / 500000000)) (hi := (133705123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27339) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27339) = 1/(27339 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-899860257 / 250000000) (-1799720511 / 500000000) (Real.log (27339 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4274716229 / 1000000000) ≤ -Real.log (250000000000 / 17964936247723) ∧
    -Real.log (250000000000 / 17964936247723) ≤ (1068679059 / 250000000) := by
  have h := checkLog_sound (w := (1964936247723 / 33964936247723)) (n := 12)
    (lo := (115833149 / 1000000000)) (hi := (2316663 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17964936247723 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17964936247723 / 16000000000000) = 1/(250000000000 / 17964936247723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4274716229 / 1000000000) (1068679059 / 250000000) (Real.log (17964936247723 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (17964936247723 / 250000000000) = -Real.log (250000000000 / 17964936247723) := by
    rw [show ((17964936247723 / 250000000000) : ℝ) = ((250000000000 / 17964936247723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (857126683 / 200000000) ≤ -Real.log (1953125000 / 141891697507) ∧
    -Real.log (1953125000 / 141891697507) ≤ (2142816711 / 500000000) := by
  have h := checkLog_sound (w := (16891697507 / 266891697507)) (n := 12)
    (lo := (25350067 / 200000000)) (hi := (990237 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141891697507 / 125000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(141891697507 / 125000000000) = 1/(1953125000 / 141891697507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (857126683 / 200000000) (2142816711 / 500000000) (Real.log (141891697507 / 1953125000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (141891697507 / 1953125000) = -Real.log (1953125000 / 141891697507) := by
    rw [show ((141891697507 / 1953125000) : ℝ) = ((1953125000 / 141891697507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4267795447 / 1000000000) ≤ -Real.log (62500000000 / 4460258520877) ∧
    -Real.log (62500000000 / 4460258520877) ≤ (2133897727 / 500000000) := by
  have h := checkLog_sound (w := (460258520877 / 8460258520877)) (n := 12)
    (lo := (108912367 / 1000000000)) (hi := (6807023 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4460258520877 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4460258520877 / 4000000000000) = 1/(62500000000 / 4460258520877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4267795447 / 1000000000) (2133897727 / 500000000) (Real.log (4460258520877 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4460258520877 / 62500000000) = -Real.log (62500000000 / 4460258520877) := by
    rw [show ((4460258520877 / 62500000000) : ℝ) = ((62500000000 / 4460258520877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2139412207 / 500000000) ≤ -Real.log (15625000000 / 1127430707963) ∧
    -Real.log (15625000000 / 1127430707963) ≤ (4278824421 / 1000000000) := by
  have h := checkLog_sound (w := (127430707963 / 2127430707963)) (n := 12)
    (lo := (59970667 / 500000000)) (hi := (23988267 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127430707963 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1127430707963 / 1000000000000) = 1/(15625000000 / 1127430707963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2139412207 / 500000000) (4278824421 / 1000000000) (Real.log (1127430707963 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1127430707963 / 15625000000) = -Real.log (15625000000 / 1127430707963) := by
    rw [show ((1127430707963 / 15625000000) : ℝ) = ((15625000000 / 1127430707963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0072

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0073Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0073
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

theorem reflection_log_1_neg : (676515497 / 1000000000) ≤ -Real.log (51200 / 100711) ∧
    -Real.log (51200 / 100711) ≤ (338257749 / 500000000) := by
  have h := checkLog_sound (w := (49511 / 151911)) (n := 12)
    (lo := (676515497 / 1000000000)) (hi := (338257749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100711 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100711 / 51200) = 1/(51200 / 100711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (676515497 / 1000000000) (338257749 / 500000000) (Real.log (100711 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100711 / 51200) = -Real.log (51200 / 100711) := by
    rw [show ((100711 / 51200) : ℝ) = ((51200 / 100711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3411602891 / 1000000000) ≤ -Real.log (1689 / 51200) ∧
    -Real.log (1689 / 51200) ≤ (213225181 / 62500000) := by
  have h := checkLog_sound (w := (1511 / 4889)) (n := 12)
    (lo := (639014171 / 1000000000)) (hi := (159753543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1689) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1689) = 1/(1689 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-213225181 / 62500000) (-3411602891 / 1000000000) (Real.log (1689 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33816341 / 50000000) ≤ -Real.log (12800 / 25173) ∧
    -Real.log (12800 / 25173) ≤ (676326821 / 1000000000) := by
  have h := checkLog_sound (w := (12373 / 37973)) (n := 12)
    (lo := (33816341 / 50000000)) (hi := (676326821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25173 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25173 / 12800) = 1/(12800 / 25173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33816341 / 50000000) (676326821 / 1000000000) (Real.log (25173 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25173 / 12800) = -Real.log (12800 / 25173) := by
    rw [show ((25173 / 12800) : ℝ) = ((12800 / 25173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1700208217 / 500000000) ≤ -Real.log (427 / 12800) ∧
    -Real.log (427 / 12800) ≤ (3400416439 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 1227)) (n := 12)
    (lo := (313913857 / 500000000)) (hi := (125565543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 427) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 427) = 1/(427 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3400416439 / 1000000000) (-1700208217 / 500000000) (Real.log (427 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (131920503 / 200000000) ≤ -Real.log (25600 / 49511) ∧
    -Real.log (25600 / 49511) ≤ (164900629 / 250000000) := by
  have h := checkLog_sound (w := (23911 / 75111)) (n := 12)
    (lo := (131920503 / 200000000)) (hi := (164900629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49511 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49511 / 25600) = 1/(25600 / 49511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (131920503 / 200000000) (164900629 / 250000000) (Real.log (49511 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49511 / 25600) = -Real.log (25600 / 49511) := by
    rw [show ((49511 / 25600) : ℝ) = ((25600 / 49511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2718455711 / 1000000000) ≤ -Real.log (1689 / 25600) ∧
    -Real.log (1689 / 25600) ≤ (543691143 / 200000000) := by
  have h := checkLog_sound (w := (1511 / 4889)) (n := 12)
    (lo := (639014171 / 1000000000)) (hi := (159753543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1689) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1689) = 1/(1689 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-543691143 / 200000000) (-2718455711 / 1000000000) (Real.log (1689 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2575073 / 3906250) ≤ -Real.log (6400 / 12373) ∧
    -Real.log (6400 / 12373) ≤ (659218689 / 1000000000) := by
  have h := checkLog_sound (w := (5973 / 18773)) (n := 12)
    (lo := (2575073 / 3906250)) (hi := (659218689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12373 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12373 / 6400) = 1/(6400 / 12373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2575073 / 3906250) (659218689 / 1000000000) (Real.log (12373 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12373 / 6400) = -Real.log (6400 / 12373) := by
    rw [show ((12373 / 6400) : ℝ) = ((6400 / 12373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1353634627 / 500000000) ≤ -Real.log (427 / 6400) ∧
    -Real.log (427 / 6400) ≤ (1353634629 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1227)) (n := 12)
    (lo := (313913857 / 500000000)) (hi := (125565543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 427) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 427) = 1/(427 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1353634629 / 500000000) (-1353634627 / 500000000) (Real.log (427 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135835613 / 200000000) ≤ -Real.log (31250 / 61633) ∧
    -Real.log (31250 / 61633) ≤ (339589033 / 500000000) := by
  have h := checkLog_sound (w := (30383 / 92883)) (n := 12)
    (lo := (135835613 / 200000000)) (hi := (339589033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61633 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61633 / 31250) = 1/(31250 / 61633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135835613 / 200000000) (339589033 / 500000000) (Real.log (61633 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (61633 / 31250) = -Real.log (31250 / 61633) := by
    rw [show ((61633 / 31250) : ℝ) = ((31250 / 61633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (143389427 / 40000000) ≤ -Real.log (867 / 31250) ∧
    -Real.log (867 / 31250) ≤ (3584735681 / 1000000000) := by
  have h := checkLog_sound (w := (1753 / 29497)) (n := 12)
    (lo := (4759991 / 40000000)) (hi := (3718743 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13872) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13872) = 1/(867 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3584735681 / 1000000000) (-143389427 / 40000000) (Real.log (867 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169831907 / 250000000) ≤ -Real.log (1000000 / 1972551) ∧
    -Real.log (1000000 / 1972551) ≤ (679327629 / 1000000000) := by
  have h := checkLog_sound (w := (972551 / 2972551)) (n := 12)
    (lo := (169831907 / 250000000)) (hi := (679327629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972551 / 1000000) = 1/(1000000 / 1972551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169831907 / 250000000) (679327629 / 1000000000) (Real.log (1972551 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1972551 / 1000000) = -Real.log (1000000 / 1972551) := by
    rw [show ((1972551 / 1000000) : ℝ) = ((1000000 / 1972551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1797712769 / 500000000) ≤ -Real.log (27449 / 1000000) ∧
    -Real.log (27449 / 1000000) ≤ (449428193 / 125000000) := by
  have h := checkLog_sound (w := (3801 / 58699)) (n := 12)
    (lo := (64844819 / 500000000)) (hi := (129689639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27449) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27449) = 1/(27449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-449428193 / 125000000) (-1797712769 / 500000000) (Real.log (27449 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67908071 / 100000000) ≤ -Real.log (31250 / 61627) ∧
    -Real.log (31250 / 61627) ≤ (679080711 / 1000000000) := by
  have h := checkLog_sound (w := (30377 / 92877)) (n := 12)
    (lo := (67908071 / 100000000)) (hi := (679080711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61627 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61627 / 31250) = 1/(31250 / 61627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67908071 / 100000000) (679080711 / 1000000000) (Real.log (61627 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61627 / 31250) = -Real.log (31250 / 61627) := by
    rw [show ((61627 / 31250) : ℝ) = ((31250 / 61627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (447229887 / 125000000) ≤ -Real.log (873 / 31250) ∧
    -Real.log (873 / 31250) ≤ (1788919551 / 500000000) := by
  have h := checkLog_sound (w := (1657 / 29593)) (n := 12)
    (lo := (28025799 / 250000000)) (hi := (112103197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13968) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13968) = 1/(873 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1788919551 / 500000000) (-447229887 / 125000000) (Real.log (873 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (169808079 / 250000000) ≤ -Real.log (1000000 / 1972363) ∧
    -Real.log (1000000 / 1972363) ≤ (679232317 / 1000000000) := by
  have h := checkLog_sound (w := (972363 / 2972363)) (n := 12)
    (lo := (169808079 / 250000000)) (hi := (679232317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972363 / 1000000) = 1/(1000000 / 1972363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (169808079 / 250000000) (679232317 / 1000000000) (Real.log (1972363 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1972363 / 1000000) = -Real.log (1000000 / 1972363) := by
    rw [show ((1972363 / 1000000) : ℝ) = ((1000000 / 1972363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3588599821 / 1000000000) ≤ -Real.log (27637 / 1000000) ∧
    -Real.log (27637 / 1000000) ≤ (3588599827 / 1000000000) := by
  have h := checkLog_sound (w := (3613 / 58887)) (n := 12)
    (lo := (122863921 / 1000000000)) (hi := (61431961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27637) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27637) = 1/(27637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3588599827 / 1000000000) (-3588599821 / 1000000000) (Real.log (27637 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (213195687 / 50000000) ≤ -Real.log (62500000000 / 4442978662053) ∧
    -Real.log (62500000000 / 4442978662053) ≤ (4263913747 / 1000000000) := by
  have h := checkLog_sound (w := (442978662053 / 8442978662053)) (n := 12)
    (lo := (5251533 / 50000000)) (hi := (105030661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4442978662053 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4442978662053 / 4000000000000) = 1/(62500000000 / 4442978662053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (213195687 / 50000000) (4263913747 / 1000000000) (Real.log (4442978662053 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4442978662053 / 62500000000) = -Real.log (62500000000 / 4442978662053) := by
    rw [show ((4442978662053 / 62500000000) : ℝ) = ((62500000000 / 4442978662053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4274753167 / 1000000000) ≤ -Real.log (250000000000 / 17965599839703) ∧
    -Real.log (250000000000 / 17965599839703) ≤ (2137376587 / 500000000) := by
  have h := checkLog_sound (w := (1965599839703 / 33965599839703)) (n := 12)
    (lo := (115870087 / 1000000000)) (hi := (14483761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17965599839703 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17965599839703 / 16000000000000) = 1/(250000000000 / 17965599839703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4274753167 / 1000000000) (2137376587 / 500000000) (Real.log (17965599839703 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (17965599839703 / 250000000000) = -Real.log (250000000000 / 17965599839703) := by
    rw [show ((17965599839703 / 250000000000) : ℝ) = ((250000000000 / 17965599839703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (851383961 / 200000000) ≤ -Real.log (250000000000 / 17648052691867) ∧
    -Real.log (250000000000 / 17648052691867) ≤ (1064229953 / 250000000) := by
  have h := checkLog_sound (w := (1648052691867 / 33648052691867)) (n := 12)
    (lo := (3921469 / 40000000)) (hi := (49018363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17648052691867 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17648052691867 / 16000000000000) = 1/(250000000000 / 17648052691867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (851383961 / 200000000) (1064229953 / 250000000) (Real.log (17648052691867 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (17648052691867 / 250000000000) = -Real.log (250000000000 / 17648052691867) := by
    rw [show ((17648052691867 / 250000000000) : ℝ) = ((250000000000 / 17648052691867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4267832137 / 1000000000) ≤ -Real.log (500000000000 / 35683377356443) ∧
    -Real.log (500000000000 / 35683377356443) ≤ (266739509 / 62500000) := by
  have h := checkLog_sound (w := (3683377356443 / 67683377356443)) (n := 12)
    (lo := (108949057 / 1000000000)) (hi := (54474529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35683377356443 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(35683377356443 / 32000000000000) = 1/(500000000000 / 35683377356443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4267832137 / 1000000000) (266739509 / 62500000) (Real.log (35683377356443 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (35683377356443 / 500000000000) = -Real.log (500000000000 / 35683377356443) := by
    rw [show ((35683377356443 / 500000000000) : ℝ) = ((500000000000 / 35683377356443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0073

end


