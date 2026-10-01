-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0079Logs__3
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0079Logs__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:00:31.382984+00:00
-- url     : https://prove2.me/theorems/56939350-3d45-4850-9943-253cb97b95c3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0079Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0080Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0079Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0080Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0081Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0079Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0080Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0081Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0079Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0080Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0081Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0079Logs (+2 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0080Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0081Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0079Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0079
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

theorem reflection_log_1_neg : (84422863 / 125000000) ≤ -Real.log (51200 / 100597) ∧
    -Real.log (51200 / 100597) ≤ (135076581 / 200000000) := by
  have h := checkLog_sound (w := (49397 / 151797)) (n := 12)
    (lo := (84422863 / 125000000)) (hi := (135076581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100597 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100597 / 51200) = 1/(51200 / 100597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (84422863 / 125000000) (135076581 / 200000000) (Real.log (100597 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100597 / 51200) = -Real.log (51200 / 100597) := by
    rw [show ((100597 / 51200) : ℝ) = ((51200 / 100597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (669257517 / 200000000) ≤ -Real.log (1803 / 51200) ∧
    -Real.log (1803 / 51200) ≤ (334628759 / 100000000) := by
  have h := checkLog_sound (w := (1397 / 5003)) (n := 12)
    (lo := (114739773 / 200000000)) (hi := (286849433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1803) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1803) = 1/(1803 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-334628759 / 100000000) (-669257517 / 200000000) (Real.log (1803 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (675194013 / 1000000000) ≤ -Real.log (25600 / 50289) ∧
    -Real.log (25600 / 50289) ≤ (337597007 / 500000000) := by
  have h := checkLog_sound (w := (24689 / 75889)) (n := 12)
    (lo := (675194013 / 1000000000)) (hi := (337597007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50289 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50289 / 25600) = 1/(25600 / 50289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (675194013 / 1000000000) (337597007 / 500000000) (Real.log (50289 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50289 / 25600) = -Real.log (25600 / 50289) := by
    rw [show ((50289 / 25600) : ℝ) = ((25600 / 50289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (333580473 / 100000000) ≤ -Real.log (911 / 25600) ∧
    -Real.log (911 / 25600) ≤ (667160947 / 200000000) := by
  have h := checkLog_sound (w := (689 / 2511)) (n := 12)
    (lo := (56321601 / 100000000)) (hi := (563216011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 911) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 911) = 1/(911 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-667160947 / 200000000) (-333580473 / 100000000) (Real.log (911 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (328648671 / 500000000) ≤ -Real.log (25600 / 49397) ∧
    -Real.log (25600 / 49397) ≤ (657297343 / 1000000000) := by
  have h := checkLog_sound (w := (23797 / 74997)) (n := 12)
    (lo := (328648671 / 500000000)) (hi := (657297343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49397 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49397 / 25600) = 1/(25600 / 49397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (328648671 / 500000000) (657297343 / 1000000000) (Real.log (49397 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49397 / 25600) = -Real.log (25600 / 49397) := by
    rw [show ((49397 / 25600) : ℝ) = ((25600 / 49397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (530628081 / 200000000) ≤ -Real.log (1803 / 25600) ∧
    -Real.log (1803 / 25600) ≤ (2653140409 / 1000000000) := by
  have h := checkLog_sound (w := (1397 / 5003)) (n := 12)
    (lo := (114739773 / 200000000)) (hi := (286849433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1803) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1803) = 1/(1803 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2653140409 / 1000000000) (-530628081 / 200000000) (Real.log (1803 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (656912629 / 1000000000) ≤ -Real.log (12800 / 24689) ∧
    -Real.log (12800 / 24689) ≤ (65691263 / 100000000) := by
  have h := checkLog_sound (w := (11889 / 37489)) (n := 12)
    (lo := (656912629 / 1000000000)) (hi := (65691263 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24689 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24689 / 12800) = 1/(12800 / 24689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (656912629 / 1000000000) (65691263 / 100000000) (Real.log (24689 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24689 / 12800) = -Real.log (12800 / 24689) := by
    rw [show ((24689 / 12800) : ℝ) = ((12800 / 24689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (52853151 / 20000000) ≤ -Real.log (911 / 12800) ∧
    -Real.log (911 / 12800) ≤ (1321328777 / 500000000) := by
  have h := checkLog_sound (w := (689 / 2511)) (n := 12)
    (lo := (56321601 / 100000000)) (hi := (563216011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 911) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 911) = 1/(911 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1321328777 / 500000000) (-52853151 / 20000000) (Real.log (911 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16957221 / 25000000) ≤ -Real.log (1000000 / 1970503) ∧
    -Real.log (1000000 / 1970503) ≤ (678288841 / 1000000000) := by
  have h := checkLog_sound (w := (970503 / 2970503)) (n := 12)
    (lo := (16957221 / 25000000)) (hi := (678288841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1970503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1970503 / 1000000) = 1/(1000000 / 1970503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16957221 / 25000000) (678288841 / 1000000000) (Real.log (1970503 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1970503 / 1000000) = -Real.log (1000000 / 1970503) := by
    rw [show ((1970503 / 1000000) : ℝ) = ((1000000 / 1970503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (440433339 / 125000000) ≤ -Real.log (29497 / 1000000) ∧
    -Real.log (29497 / 1000000) ≤ (1761733359 / 500000000) := by
  have h := checkLog_sound (w := (1753 / 60747)) (n := 12)
    (lo := (14432703 / 250000000)) (hi := (57730813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29497) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 29497) = 1/(29497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1761733359 / 500000000) (-440433339 / 125000000) (Real.log (29497 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339218761 / 500000000) ≤ -Real.log (250000 / 492699) ∧
    -Real.log (250000 / 492699) ≤ (678437523 / 1000000000) := by
  have h := checkLog_sound (w := (242699 / 742699)) (n := 12)
    (lo := (339218761 / 500000000)) (hi := (678437523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492699 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492699 / 250000) = 1/(250000 / 492699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339218761 / 500000000) (678437523 / 1000000000) (Real.log (492699 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (492699 / 250000) = -Real.log (250000 / 492699) := by
    rw [show ((492699 / 250000) : ℝ) = ((250000 / 492699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3533449589 / 1000000000) ≤ -Real.log (7301 / 250000) ∧
    -Real.log (7301 / 250000) ≤ (706689919 / 200000000) := by
  have h := checkLog_sound (w := (1023 / 30227)) (n := 12)
    (lo := (67713689 / 1000000000)) (hi := (6771369 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14602) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14602) = 1/(7301 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-706689919 / 200000000) (-3533449589 / 1000000000) (Real.log (7301 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (169544043 / 250000000) ≤ -Real.log (1000000 / 1970281) ∧
    -Real.log (1000000 / 1970281) ≤ (678176173 / 1000000000) := by
  have h := checkLog_sound (w := (970281 / 2970281)) (n := 12)
    (lo := (169544043 / 250000000)) (hi := (678176173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1970281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1970281 / 1000000) = 1/(1000000 / 1970281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (169544043 / 250000000) (678176173 / 1000000000) (Real.log (1970281 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1970281 / 1000000) = -Real.log (1000000 / 1970281) := by
    rw [show ((1970281 / 1000000) : ℝ) = ((1000000 / 1970281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (54937011 / 15625000) ≤ -Real.log (29719 / 1000000) ∧
    -Real.log (29719 / 1000000) ≤ (351596871 / 100000000) := by
  have h := checkLog_sound (w := (1531 / 60969)) (n := 12)
    (lo := (12558201 / 250000000)) (hi := (10046561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29719) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 29719) = 1/(29719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-351596871 / 100000000) (-54937011 / 15625000) (Real.log (29719 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (6783269 / 10000000) ≤ -Real.log (500000 / 985289) ∧
    -Real.log (500000 / 985289) ≤ (678326901 / 1000000000) := by
  have h := checkLog_sound (w := (485289 / 1485289)) (n := 12)
    (lo := (6783269 / 10000000)) (hi := (678326901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985289 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985289 / 500000) = 1/(500000 / 985289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6783269 / 10000000) (678326901 / 1000000000) (Real.log (985289 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (985289 / 500000) = -Real.log (500000 / 985289) := by
    rw [show ((985289 / 500000) : ℝ) = ((500000 / 985289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1763006291 / 500000000) ≤ -Real.log (14711 / 500000) ∧
    -Real.log (14711 / 500000) ≤ (881503147 / 250000000) := by
  have h := checkLog_sound (w := (457 / 15168)) (n := 12)
    (lo := (30138341 / 500000000)) (hi := (60276683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14711) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14711) = 1/(14711 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-881503147 / 250000000) (-1763006291 / 500000000) (Real.log (14711 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (131304861 / 31250000) ≤ -Real.log (100000000000 / 6680350544123) ∧
    -Real.log (100000000000 / 6680350544123) ≤ (4201755559 / 1000000000) := by
  have h := checkLog_sound (w := (280350544123 / 13080350544123)) (n := 12)
    (lo := (5359059 / 125000000)) (hi := (42872473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6680350544123 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6680350544123 / 6400000000000) = 1/(100000000000 / 6680350544123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (131304861 / 31250000) (4201755559 / 1000000000) (Real.log (6680350544123 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6680350544123 / 100000000000) = -Real.log (100000000000 / 6680350544123) := by
    rw [show ((6680350544123 / 100000000000) : ℝ) = ((100000000000 / 6680350544123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4211887111 / 1000000000) ≤ -Real.log (500000000000 / 33741884673333) ∧
    -Real.log (500000000000 / 33741884673333) ≤ (2105943559 / 500000000) := by
  have h := checkLog_sound (w := (1741884673333 / 65741884673333)) (n := 12)
    (lo := (53004031 / 1000000000)) (hi := (207047 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33741884673333 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33741884673333 / 32000000000000) = 1/(500000000000 / 33741884673333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4211887111 / 1000000000) (2105943559 / 500000000) (Real.log (33741884673333 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (33741884673333 / 500000000000) = -Real.log (500000000000 / 33741884673333) := by
    rw [show ((33741884673333 / 500000000000) : ℝ) = ((500000000000 / 33741884673333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33553159 / 8000000) ≤ -Real.log (125000000000 / 8287126922171) ∧
    -Real.log (125000000000 / 8287126922171) ≤ (2097072441 / 500000000) := by
  have h := checkLog_sound (w := (287126922171 / 16287126922171)) (n := 12)
    (lo := (7052359 / 200000000)) (hi := (8815449 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8287126922171 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8287126922171 / 8000000000000) = 1/(125000000000 / 8287126922171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (33553159 / 8000000) (2097072441 / 500000000) (Real.log (8287126922171 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8287126922171 / 125000000000) = -Real.log (125000000000 / 8287126922171) := by
    rw [show ((8287126922171 / 125000000000) : ℝ) = ((125000000000 / 8287126922171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2102169741 / 500000000) ≤ -Real.log (62500000000 / 4186021514513) ∧
    -Real.log (62500000000 / 4186021514513) ≤ (4204339489 / 1000000000) := by
  have h := checkLog_sound (w := (186021514513 / 8186021514513)) (n := 12)
    (lo := (22728201 / 500000000)) (hi := (45456403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4186021514513 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4186021514513 / 4000000000000) = 1/(62500000000 / 4186021514513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2102169741 / 500000000) (4204339489 / 1000000000) (Real.log (4186021514513 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4186021514513 / 62500000000) = -Real.log (62500000000 / 4186021514513) := by
    rw [show ((4186021514513 / 62500000000) : ℝ) = ((62500000000 / 4186021514513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0079

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0080Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0080
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

theorem reflection_log_1_neg : (675194013 / 1000000000) ≤ -Real.log (25600 / 50289) ∧
    -Real.log (25600 / 50289) ≤ (337597007 / 500000000) := by
  have h := checkLog_sound (w := (24689 / 75889)) (n := 12)
    (lo := (675194013 / 1000000000)) (hi := (337597007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50289 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50289 / 25600) = 1/(25600 / 50289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (675194013 / 1000000000) (337597007 / 500000000) (Real.log (50289 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50289 / 25600) = -Real.log (25600 / 50289) := by
    rw [show ((50289 / 25600) : ℝ) = ((25600 / 50289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (333580473 / 100000000) ≤ -Real.log (911 / 25600) ∧
    -Real.log (911 / 25600) ≤ (667160947 / 200000000) := by
  have h := checkLog_sound (w := (689 / 2511)) (n := 12)
    (lo := (56321601 / 100000000)) (hi := (563216011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 911) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 911) = 1/(911 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-667160947 / 200000000) (-333580473 / 100000000) (Real.log (911 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (675005087 / 1000000000) ≤ -Real.log (51200 / 100559) ∧
    -Real.log (51200 / 100559) ≤ (21093909 / 31250000) := by
  have h := checkLog_sound (w := (49359 / 151759)) (n := 12)
    (lo := (675005087 / 1000000000)) (hi := (21093909 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100559 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100559 / 51200) = 1/(51200 / 100559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (675005087 / 1000000000) (21093909 / 31250000) (Real.log (100559 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100559 / 51200) = -Real.log (51200 / 100559) := by
    rw [show ((100559 / 51200) : ℝ) = ((51200 / 100559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3325430627 / 1000000000) ≤ -Real.log (1841 / 51200) ∧
    -Real.log (1841 / 51200) ≤ (415678829 / 125000000) := by
  have h := checkLog_sound (w := (1359 / 5041)) (n := 12)
    (lo := (552841907 / 1000000000)) (hi := (138210477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1841) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1841) = 1/(1841 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-415678829 / 125000000) (-3325430627 / 1000000000) (Real.log (1841 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (656912629 / 1000000000) ≤ -Real.log (12800 / 24689) ∧
    -Real.log (12800 / 24689) ≤ (65691263 / 100000000) := by
  have h := checkLog_sound (w := (11889 / 37489)) (n := 12)
    (lo := (656912629 / 1000000000)) (hi := (65691263 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24689 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24689 / 12800) = 1/(12800 / 24689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (656912629 / 1000000000) (65691263 / 100000000) (Real.log (24689 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24689 / 12800) = -Real.log (12800 / 24689) := by
    rw [show ((24689 / 12800) : ℝ) = ((12800 / 24689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (52853151 / 20000000) ≤ -Real.log (911 / 12800) ∧
    -Real.log (911 / 12800) ≤ (1321328777 / 500000000) := by
  have h := checkLog_sound (w := (689 / 2511)) (n := 12)
    (lo := (56321601 / 100000000)) (hi := (563216011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 911) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 911) = 1/(911 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1321328777 / 500000000) (-52853151 / 20000000) (Real.log (911 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (82065971 / 125000000) ≤ -Real.log (25600 / 49359) ∧
    -Real.log (25600 / 49359) ≤ (656527769 / 1000000000) := by
  have h := checkLog_sound (w := (23759 / 74959)) (n := 12)
    (lo := (82065971 / 125000000)) (hi := (656527769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49359 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49359 / 25600) = 1/(25600 / 49359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (82065971 / 125000000) (656527769 / 1000000000) (Real.log (49359 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49359 / 25600) = -Real.log (25600 / 49359) := by
    rw [show ((49359 / 25600) : ℝ) = ((25600 / 49359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2632283447 / 1000000000) ≤ -Real.log (1841 / 25600) ∧
    -Real.log (1841 / 25600) ≤ (2632283451 / 1000000000) := by
  have h := checkLog_sound (w := (1359 / 5041)) (n := 12)
    (lo := (552841907 / 1000000000)) (hi := (138210477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1841) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1841) = 1/(1841 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2632283451 / 1000000000) (-2632283447 / 1000000000) (Real.log (1841 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (678141151 / 1000000000) ≤ -Real.log (250000 / 492553) ∧
    -Real.log (250000 / 492553) ≤ (21191911 / 31250000) := by
  have h := checkLog_sound (w := (242553 / 742553)) (n := 12)
    (lo := (678141151 / 1000000000)) (hi := (21191911 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492553 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492553 / 250000) = 1/(250000 / 492553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (678141151 / 1000000000) (21191911 / 31250000) (Real.log (492553 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (492553 / 250000) = -Real.log (250000 / 492553) := by
    rw [show ((492553 / 250000) : ℝ) = ((250000 / 492553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (219603103 / 62500000) ≤ -Real.log (7447 / 250000) ∧
    -Real.log (7447 / 250000) ≤ (1756824827 / 500000000) := by
  have h := checkLog_sound (w := (731 / 30519)) (n := 12)
    (lo := (11978437 / 250000000)) (hi := (47913749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14894) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14894) = 1/(7447 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1756824827 / 500000000) (-219603103 / 62500000) (Real.log (7447 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (678289347 / 1000000000) ≤ -Real.log (125000 / 246313) ∧
    -Real.log (125000 / 246313) ≤ (169572337 / 250000000) := by
  have h := checkLog_sound (w := (121313 / 371313)) (n := 12)
    (lo := (678289347 / 1000000000)) (hi := (169572337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246313 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246313 / 125000) = 1/(125000 / 246313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (678289347 / 1000000000) (169572337 / 250000000) (Real.log (246313 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (246313 / 125000) = -Real.log (125000 / 246313) := by
    rw [show ((246313 / 125000) : ℝ) = ((125000 / 246313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (704700123 / 200000000) ≤ -Real.log (3687 / 125000) ∧
    -Real.log (3687 / 125000) ≤ (3523500621 / 1000000000) := by
  have h := checkLog_sound (w := (877 / 30373)) (n := 12)
    (lo := (11552943 / 200000000)) (hi := (14441179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14748) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14748) = 1/(3687 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3523500621 / 1000000000) (-704700123 / 200000000) (Real.log (3687 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (33901271 / 50000000) ≤ -Real.log (15625 / 30781) ∧
    -Real.log (15625 / 30781) ≤ (678025421 / 1000000000) := by
  have h := checkLog_sound (w := (7578 / 23203)) (n := 12)
    (lo := (33901271 / 50000000)) (hi := (678025421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30781 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30781 / 15625) = 1/(15625 / 30781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (33901271 / 50000000) (678025421 / 1000000000) (Real.log (30781 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (30781 / 15625) = -Real.log (15625 / 30781) := by
    rw [show ((30781 / 15625) : ℝ) = ((15625 / 30781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3506024703 / 1000000000) ≤ -Real.log (469 / 15625) ∧
    -Real.log (469 / 15625) ≤ (3506024709 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 30633)) (n := 12)
    (lo := (40288803 / 1000000000)) (hi := (10072201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15008) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 15008) = 1/(469 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3506024709 / 1000000000) (-3506024703 / 1000000000) (Real.log (469 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (678176679 / 1000000000) ≤ -Real.log (500000 / 985141) ∧
    -Real.log (500000 / 985141) ≤ (16954417 / 25000000) := by
  have h := checkLog_sound (w := (485141 / 1485141)) (n := 12)
    (lo := (678176679 / 1000000000)) (hi := (16954417 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985141 / 500000) = 1/(500000 / 985141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (678176679 / 1000000000) (16954417 / 25000000) (Real.log (985141 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (985141 / 500000) = -Real.log (500000 / 985141) := by
    rw [show ((985141 / 500000) : ℝ) = ((500000 / 985141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3516002353 / 1000000000) ≤ -Real.log (14859 / 500000) ∧
    -Real.log (14859 / 500000) ≤ (3516002359 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 15242)) (n := 12)
    (lo := (50266453 / 1000000000)) (hi := (25133227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14859) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14859) = 1/(14859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3516002359 / 1000000000) (-3516002353 / 1000000000) (Real.log (14859 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2095895399 / 500000000) ≤ -Real.log (1562500000 / 103345516651) ∧
    -Real.log (1562500000 / 103345516651) ≤ (838358161 / 200000000) := by
  have h := checkLog_sound (w := (3345516651 / 203345516651)) (n := 12)
    (lo := (16453859 / 500000000)) (hi := (32907719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103345516651 / 100000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(103345516651 / 100000000000) = 1/(1562500000 / 103345516651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2095895399 / 500000000) (838358161 / 200000000) (Real.log (103345516651 / 1562500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (103345516651 / 1562500000) = -Real.log (1562500000 / 103345516651) := by
    rw [show ((103345516651 / 1562500000) : ℝ) = ((1562500000 / 103345516651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2100894981 / 500000000) ≤ -Real.log (500000000000 / 33402902088419) ∧
    -Real.log (500000000000 / 33402902088419) ≤ (4201789969 / 1000000000) := by
  have h := checkLog_sound (w := (1402902088419 / 65402902088419)) (n := 12)
    (lo := (21453441 / 500000000)) (hi := (42906883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33402902088419 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33402902088419 / 32000000000000) = 1/(500000000000 / 33402902088419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2100894981 / 500000000) (4201789969 / 1000000000) (Real.log (33402902088419 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (33402902088419 / 500000000000) = -Real.log (500000000000 / 33402902088419) := by
    rw [show ((33402902088419 / 500000000000) : ℝ) = ((500000000000 / 33402902088419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4184050123 / 1000000000) ≤ -Real.log (250000000000 / 16407782515991) ∧
    -Real.log (250000000000 / 16407782515991) ≤ (418405013 / 100000000) := by
  have h := checkLog_sound (w := (407782515991 / 32407782515991)) (n := 12)
    (lo := (25167043 / 1000000000)) (hi := (6291761 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16407782515991 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(16407782515991 / 16000000000000) = 1/(250000000000 / 16407782515991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4184050123 / 1000000000) (418405013 / 100000000) (Real.log (16407782515991 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (16407782515991 / 250000000000) = -Real.log (250000000000 / 16407782515991) := by
    rw [show ((16407782515991 / 250000000000) : ℝ) = ((250000000000 / 16407782515991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (524272379 / 125000000) ≤ -Real.log (500000000000 / 33149639948853) ∧
    -Real.log (500000000000 / 33149639948853) ≤ (4194179039 / 1000000000) := by
  have h := checkLog_sound (w := (1149639948853 / 65149639948853)) (n := 12)
    (lo := (2205997 / 62500000)) (hi := (35295953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33149639948853 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33149639948853 / 32000000000000) = 1/(500000000000 / 33149639948853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (524272379 / 125000000) (4194179039 / 1000000000) (Real.log (33149639948853 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (33149639948853 / 500000000000) = -Real.log (500000000000 / 33149639948853) := by
    rw [show ((33149639948853 / 500000000000) : ℝ) = ((500000000000 / 33149639948853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0080

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0081Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0081
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

theorem reflection_log_1_neg : (675005087 / 1000000000) ≤ -Real.log (51200 / 100559) ∧
    -Real.log (51200 / 100559) ≤ (21093909 / 31250000) := by
  have h := checkLog_sound (w := (49359 / 151759)) (n := 12)
    (lo := (675005087 / 1000000000)) (hi := (21093909 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100559 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100559 / 51200) = 1/(51200 / 100559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (675005087 / 1000000000) (21093909 / 31250000) (Real.log (100559 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100559 / 51200) = -Real.log (51200 / 100559) := by
    rw [show ((100559 / 51200) : ℝ) = ((51200 / 100559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3325430627 / 1000000000) ≤ -Real.log (1841 / 51200) ∧
    -Real.log (1841 / 51200) ≤ (415678829 / 125000000) := by
  have h := checkLog_sound (w := (1359 / 5041)) (n := 12)
    (lo := (552841907 / 1000000000)) (hi := (138210477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1841) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1841) = 1/(1841 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-415678829 / 125000000) (-3325430627 / 1000000000) (Real.log (1841 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (337408063 / 500000000) ≤ -Real.log (2560 / 5027) ∧
    -Real.log (2560 / 5027) ≤ (674816127 / 1000000000) := by
  have h := checkLog_sound (w := (2467 / 7587)) (n := 12)
    (lo := (337408063 / 500000000)) (hi := (674816127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5027 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5027 / 2560) = 1/(2560 / 5027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (337408063 / 500000000) (674816127 / 1000000000) (Real.log (5027 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5027 / 2560) = -Real.log (2560 / 5027) := by
    rw [show ((5027 / 2560) : ℝ) = ((2560 / 5027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1657581521 / 500000000) ≤ -Real.log (93 / 2560) ∧
    -Real.log (93 / 2560) ≤ (3315163047 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 93) = 1/(93 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3315163047 / 1000000000) (-1657581521 / 500000000) (Real.log (93 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (82065971 / 125000000) ≤ -Real.log (25600 / 49359) ∧
    -Real.log (25600 / 49359) ≤ (656527769 / 1000000000) := by
  have h := checkLog_sound (w := (23759 / 74959)) (n := 12)
    (lo := (82065971 / 125000000)) (hi := (656527769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49359 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49359 / 25600) = 1/(25600 / 49359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (82065971 / 125000000) (656527769 / 1000000000) (Real.log (49359 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49359 / 25600) = -Real.log (25600 / 49359) := by
    rw [show ((49359 / 25600) : ℝ) = ((25600 / 49359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2632283447 / 1000000000) ≤ -Real.log (1841 / 25600) ∧
    -Real.log (1841 / 25600) ≤ (2632283451 / 1000000000) := by
  have h := checkLog_sound (w := (1359 / 5041)) (n := 12)
    (lo := (552841907 / 1000000000)) (hi := (138210477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1841) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1841) = 1/(1841 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2632283451 / 1000000000) (-2632283447 / 1000000000) (Real.log (1841 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (656142759 / 1000000000) ≤ -Real.log (1280 / 2467) ∧
    -Real.log (1280 / 2467) ≤ (16403569 / 25000000) := by
  have h := checkLog_sound (w := (1187 / 3747)) (n := 12)
    (lo := (656142759 / 1000000000)) (hi := (16403569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2467 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2467 / 1280) = 1/(1280 / 2467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (656142759 / 1000000000) (16403569 / 25000000) (Real.log (2467 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2467 / 1280) = -Real.log (1280 / 2467) := by
    rw [show ((2467 / 1280) : ℝ) = ((1280 / 2467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1311007931 / 500000000) ≤ -Real.log (93 / 1280) ∧
    -Real.log (93 / 1280) ≤ (1311007933 / 500000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 93) = 1/(93 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1311007933 / 500000000) (-1311007931 / 500000000) (Real.log (93 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4237459 / 6250000) ≤ -Real.log (1000000 / 1969921) ∧
    -Real.log (1000000 / 1969921) ≤ (677993441 / 1000000000) := by
  have h := checkLog_sound (w := (969921 / 2969921)) (n := 12)
    (lo := (4237459 / 6250000)) (hi := (677993441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969921 / 1000000) = 1/(1000000 / 1969921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4237459 / 6250000) (677993441 / 1000000000) (Real.log (1969921 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1969921 / 1000000) = -Real.log (1000000 / 1969921) := by
    rw [show ((1969921 / 1000000) : ℝ) = ((1000000 / 1969921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1751964011 / 500000000) ≤ -Real.log (30079 / 1000000) ∧
    -Real.log (30079 / 1000000) ≤ (875982007 / 250000000) := by
  have h := checkLog_sound (w := (1171 / 61329)) (n := 12)
    (lo := (19096061 / 500000000)) (hi := (38192123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30079) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30079) = 1/(30079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-875982007 / 250000000) (-1751964011 / 500000000) (Real.log (30079 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339070829 / 500000000) ≤ -Real.log (1000000 / 1970213) ∧
    -Real.log (1000000 / 1970213) ≤ (678141659 / 1000000000) := by
  have h := checkLog_sound (w := (970213 / 2970213)) (n := 12)
    (lo := (339070829 / 500000000)) (hi := (678141659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1970213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1970213 / 1000000) = 1/(1000000 / 1970213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339070829 / 500000000) (678141659 / 1000000000) (Real.log (1970213 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1970213 / 1000000) = -Real.log (1000000 / 1970213) := by
    rw [show ((1970213 / 1000000) : ℝ) = ((1000000 / 1970213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3513683219 / 1000000000) ≤ -Real.log (29787 / 1000000) ∧
    -Real.log (29787 / 1000000) ≤ (140547329 / 40000000) := by
  have h := checkLog_sound (w := (1463 / 61037)) (n := 12)
    (lo := (47947319 / 1000000000)) (hi := (1198683 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29787) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 29787) = 1/(29787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-140547329 / 40000000) (-3513683219 / 1000000000) (Real.log (29787 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (338937577 / 500000000) ≤ -Real.log (125000 / 246211) ∧
    -Real.log (125000 / 246211) ≤ (135575031 / 200000000) := by
  have h := checkLog_sound (w := (121211 / 371211)) (n := 12)
    (lo := (338937577 / 500000000)) (hi := (135575031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246211 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246211 / 125000) = 1/(125000 / 246211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (338937577 / 500000000) (135575031 / 200000000) (Real.log (246211 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (246211 / 125000) = -Real.log (125000 / 246211) := by
    rw [show ((246211 / 125000) : ℝ) = ((125000 / 246211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1748105801 / 500000000) ≤ -Real.log (3789 / 125000) ∧
    -Real.log (3789 / 125000) ≤ (437026451 / 125000000) := by
  have h := checkLog_sound (w := (469 / 30781)) (n := 12)
    (lo := (15237851 / 500000000)) (hi := (30475703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15156) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 15156) = 1/(3789 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-437026451 / 125000000) (-1748105801 / 500000000) (Real.log (3789 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (84753241 / 125000000) ≤ -Real.log (200000 / 393997) ∧
    -Real.log (200000 / 393997) ≤ (678025929 / 1000000000) := by
  have h := checkLog_sound (w := (193997 / 593997)) (n := 12)
    (lo := (84753241 / 125000000)) (hi := (678025929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393997 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393997 / 200000) = 1/(200000 / 393997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (84753241 / 125000000) (678025929 / 1000000000) (Real.log (393997 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (393997 / 200000) = -Real.log (200000 / 393997) := by
    rw [show ((393997 / 200000) : ℝ) = ((200000 / 393997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3506058019 / 1000000000) ≤ -Real.log (6003 / 200000) ∧
    -Real.log (6003 / 200000) ≤ (140242321 / 40000000) := by
  have h := checkLog_sound (w := (247 / 12253)) (n := 12)
    (lo := (40322119 / 1000000000)) (hi := (1008053 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 6003) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 6003) = 1/(6003 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-140242321 / 40000000) (-3506058019 / 1000000000) (Real.log (6003 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2090960731 / 500000000) ≤ -Real.log (125000000000 / 8186446524153) ∧
    -Real.log (125000000000 / 8186446524153) ≤ (4181921469 / 1000000000) := by
  have h := checkLog_sound (w := (186446524153 / 16186446524153)) (n := 12)
    (lo := (11519191 / 500000000)) (hi := (23038383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8186446524153 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8186446524153 / 8000000000000) = 1/(125000000000 / 8186446524153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2090960731 / 500000000) (4181921469 / 1000000000) (Real.log (8186446524153 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8186446524153 / 125000000000) = -Real.log (125000000000 / 8186446524153) := by
    rw [show ((8186446524153 / 125000000000) : ℝ) = ((125000000000 / 8186446524153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4191824877 / 1000000000) ≤ -Real.log (125000000000 / 8267923087253) ∧
    -Real.log (125000000000 / 8267923087253) ≤ (1047956221 / 250000000) := by
  have h := checkLog_sound (w := (267923087253 / 16267923087253)) (n := 12)
    (lo := (32941797 / 1000000000)) (hi := (16470899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8267923087253 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8267923087253 / 8000000000000) = 1/(125000000000 / 8267923087253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4191824877 / 1000000000) (1047956221 / 250000000) (Real.log (8267923087253 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (8267923087253 / 125000000000) = -Real.log (125000000000 / 8267923087253) := by
    rw [show ((8267923087253 / 125000000000) : ℝ) = ((125000000000 / 8267923087253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1043521689 / 250000000) ≤ -Real.log (62500000000 / 4061279361309) ∧
    -Real.log (62500000000 / 4061279361309) ≤ (4174086763 / 1000000000) := by
  have h := checkLog_sound (w := (61279361309 / 8061279361309)) (n := 12)
    (lo := (3800919 / 250000000)) (hi := (15203677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4061279361309 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4061279361309 / 4000000000000) = 1/(62500000000 / 4061279361309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1043521689 / 250000000) (4174086763 / 1000000000) (Real.log (4061279361309 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4061279361309 / 62500000000) = -Real.log (62500000000 / 4061279361309) := by
    rw [show ((4061279361309 / 62500000000) : ℝ) = ((62500000000 / 4061279361309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4184083947 / 1000000000) ≤ -Real.log (125000000000 / 8204168748959) ∧
    -Real.log (125000000000 / 8204168748959) ≤ (2092041977 / 500000000) := by
  have h := checkLog_sound (w := (204168748959 / 16204168748959)) (n := 12)
    (lo := (25200867 / 1000000000)) (hi := (6300217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8204168748959 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8204168748959 / 8000000000000) = 1/(125000000000 / 8204168748959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4184083947 / 1000000000) (2092041977 / 500000000) (Real.log (8204168748959 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8204168748959 / 125000000000) = -Real.log (125000000000 / 8204168748959) := by
    rw [show ((8204168748959 / 125000000000) : ℝ) = ((125000000000 / 8204168748959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0081

end


