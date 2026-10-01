-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0156Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0156Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:47:28.248178+00:00
-- url     : https://prove2.me/theorems/2aa6b326-af00-49b7-9446-c25dc4d117de
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0156Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0157Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0156Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0157Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0158Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0159Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0160Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0161Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0156Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0157Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0158Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0159Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0160Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0161Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0156Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0157Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0158Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0159Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0160Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0161Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0156Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0157Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0158Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0159Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0160Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0161Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0156Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0156
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

theorem reflection_log_1_neg : (324389433 / 500000000) ≤ -Real.log (12800 / 24489) ∧
    -Real.log (12800 / 24489) ≤ (648778867 / 1000000000) := by
  have h := checkLog_sound (w := (11689 / 37289)) (n := 12)
    (lo := (324389433 / 500000000)) (hi := (648778867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24489 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24489 / 12800) = 1/(12800 / 24489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (324389433 / 500000000) (648778867 / 1000000000) (Real.log (24489 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24489 / 12800) = -Real.log (12800 / 24489) := by
    rw [show ((24489 / 12800) : ℝ) = ((12800 / 24489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1222092329 / 500000000) ≤ -Real.log (1111 / 12800) ∧
    -Real.log (1111 / 12800) ≤ (1222092331 / 500000000) := by
  have h := checkLog_sound (w := (489 / 2711)) (n := 12)
    (lo := (182371559 / 500000000)) (hi := (364743119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1111) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1111) = 1/(1111 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1222092331 / 500000000) (-1222092329 / 500000000) (Real.log (1111 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (324001353 / 500000000) ≤ -Real.log (1280 / 2447) ∧
    -Real.log (1280 / 2447) ≤ (648002707 / 1000000000) := by
  have h := checkLog_sound (w := (1167 / 3727)) (n := 12)
    (lo := (324001353 / 500000000)) (hi := (648002707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2447 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2447 / 1280) = 1/(1280 / 2447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (324001353 / 500000000) (648002707 / 1000000000) (Real.log (2447 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2447 / 1280) = -Real.log (1280 / 2447) := by
    rw [show ((2447 / 1280) : ℝ) = ((1280 / 2447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (151701721 / 62500000) ≤ -Real.log (113 / 1280) ∧
    -Real.log (113 / 1280) ≤ (121361377 / 50000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 113) = 1/(113 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-121361377 / 50000000) (-151701721 / 62500000) (Real.log (113 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (301175119 / 500000000) ≤ -Real.log (6400 / 11689) ∧
    -Real.log (6400 / 11689) ≤ (602350239 / 1000000000) := by
  have h := checkLog_sound (w := (5289 / 18089)) (n := 12)
    (lo := (301175119 / 500000000)) (hi := (602350239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11689 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11689 / 6400) = 1/(6400 / 11689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (301175119 / 500000000) (602350239 / 1000000000) (Real.log (11689 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11689 / 6400) = -Real.log (6400 / 11689) := by
    rw [show ((11689 / 6400) : ℝ) = ((6400 / 11689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (875518739 / 500000000) ≤ -Real.log (1111 / 6400) ∧
    -Real.log (1111 / 6400) ≤ (1751037481 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 2711)) (n := 12)
    (lo := (182371559 / 500000000)) (hi := (364743119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1111) = 1/(1111 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1751037481 / 1000000000) (-875518739 / 500000000) (Real.log (1111 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (120144691 / 200000000) ≤ -Real.log (640 / 1167) ∧
    -Real.log (640 / 1167) ≤ (1173288 / 1953125) := by
  have h := checkLog_sound (w := (527 / 1807)) (n := 12)
    (lo := (120144691 / 200000000)) (hi := (1173288 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167 / 640) = 1/(640 / 1167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (120144691 / 200000000) (1173288 / 1953125) (Real.log (1167 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1167 / 640) = -Real.log (640 / 1167) := by
    rw [show ((1167 / 640) : ℝ) = ((640 / 1167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (433520089 / 250000000) ≤ -Real.log (113 / 640) ∧
    -Real.log (113 / 640) ≤ (1734080359 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 113) = 1/(113 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1734080359 / 1000000000) (-433520089 / 250000000) (Real.log (113 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131656067 / 200000000) ≤ -Real.log (250000 / 482867) ∧
    -Real.log (250000 / 482867) ≤ (41142521 / 62500000) := by
  have h := checkLog_sound (w := (232867 / 732867)) (n := 12)
    (lo := (131656067 / 200000000)) (hi := (41142521 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((482867 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(482867 / 250000) = 1/(250000 / 482867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131656067 / 200000000) (41142521 / 62500000) (Real.log (482867 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (482867 / 250000) = -Real.log (250000 / 482867) := by
    rw [show ((482867 / 250000) : ℝ) = ((250000 / 482867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2680454487 / 1000000000) ≤ -Real.log (17133 / 250000) ∧
    -Real.log (17133 / 250000) ≤ (2680454491 / 1000000000) := by
  have h := checkLog_sound (w := (14117 / 48383)) (n := 12)
    (lo := (601012947 / 1000000000)) (hi := (150253237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17133) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 17133) = 1/(17133 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2680454491 / 1000000000) (-2680454487 / 1000000000) (Real.log (17133 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (658818641 / 1000000000) ≤ -Real.log (250000 / 483127) ∧
    -Real.log (250000 / 483127) ≤ (329409321 / 500000000) := by
  have h := checkLog_sound (w := (233127 / 733127)) (n := 12)
    (lo := (658818641 / 1000000000)) (hi := (329409321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483127 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483127 / 250000) = 1/(250000 / 483127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (658818641 / 1000000000) (329409321 / 500000000) (Real.log (483127 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (483127 / 250000) = -Real.log (250000 / 483127) := by
    rw [show ((483127 / 250000) : ℝ) = ((250000 / 483127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (673936551 / 250000000) ≤ -Real.log (16873 / 250000) ∧
    -Real.log (16873 / 250000) ≤ (84242069 / 31250000) := by
  have h := checkLog_sound (w := (14377 / 48123)) (n := 12)
    (lo := (77038083 / 125000000)) (hi := (123260933 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16873) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 16873) = 1/(16873 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-84242069 / 31250000) (-673936551 / 250000000) (Real.log (16873 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (131472599 / 200000000) ≤ -Real.log (1000000 / 1929697) ∧
    -Real.log (1000000 / 1929697) ≤ (164340749 / 250000000) := by
  have h := checkLog_sound (w := (929697 / 2929697)) (n := 12)
    (lo := (131472599 / 200000000)) (hi := (164340749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1929697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1929697 / 1000000) = 1/(1000000 / 1929697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (131472599 / 200000000) (164340749 / 250000000) (Real.log (1929697 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1929697 / 1000000) = -Real.log (1000000 / 1929697) := by
    rw [show ((1929697 / 1000000) : ℝ) = ((1000000 / 1929697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (530988161 / 200000000) ≤ -Real.log (70303 / 1000000) ∧
    -Real.log (70303 / 1000000) ≤ (2654940809 / 1000000000) := by
  have h := checkLog_sound (w := (54697 / 195303)) (n := 12)
    (lo := (115099853 / 200000000)) (hi := (287749633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 70303) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 70303) = 1/(70303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2654940809 / 1000000000) (-530988161 / 200000000) (Real.log (70303 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (164484383 / 250000000) ≤ -Real.log (500000 / 965403) ∧
    -Real.log (500000 / 965403) ≤ (657937533 / 1000000000) := by
  have h := checkLog_sound (w := (465403 / 1465403)) (n := 12)
    (lo := (164484383 / 250000000)) (hi := (657937533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((965403 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(965403 / 500000) = 1/(500000 / 965403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (164484383 / 250000000) (657937533 / 1000000000) (Real.log (965403 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (965403 / 500000) = -Real.log (500000 / 965403) := by
    rw [show ((965403 / 500000) : ℝ) = ((500000 / 965403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2670841123 / 1000000000) ≤ -Real.log (34597 / 500000) ∧
    -Real.log (34597 / 500000) ≤ (2670841127 / 1000000000) := by
  have h := checkLog_sound (w := (27903 / 97097)) (n := 12)
    (lo := (591399583 / 1000000000)) (hi := (18481237 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34597) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 34597) = 1/(34597 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2670841127 / 1000000000) (-2670841123 / 1000000000) (Real.log (34597 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1669367411 / 500000000) ≤ -Real.log (125000000000 / 3522930893597) ∧
    -Real.log (125000000000 / 3522930893597) ≤ (3338734827 / 1000000000) := by
  have h := checkLog_sound (w := (1522930893597 / 5522930893597)) (n := 12)
    (lo := (283073051 / 500000000)) (hi := (566146103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3522930893597 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3522930893597 / 2000000000000) = 1/(125000000000 / 3522930893597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1669367411 / 500000000) (3338734827 / 1000000000) (Real.log (3522930893597 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3522930893597 / 125000000000) = -Real.log (125000000000 / 3522930893597) := by
    rw [show ((3522930893597 / 125000000000) : ℝ) = ((125000000000 / 3522930893597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (670912969 / 200000000) ≤ -Real.log (250000000000 / 7158285426421) ∧
    -Real.log (250000000000 / 7158285426421) ≤ (67091297 / 20000000) := by
  have h := checkLog_sound (w := (3158285426421 / 11158285426421)) (n := 12)
    (lo := (4655809 / 8000000)) (hi := (290988063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7158285426421 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7158285426421 / 4000000000000) = 1/(250000000000 / 7158285426421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (670912969 / 200000000) (67091297 / 20000000) (Real.log (7158285426421 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7158285426421 / 250000000000) = -Real.log (250000000000 / 7158285426421) := by
    rw [show ((7158285426421 / 250000000000) : ℝ) = ((250000000000 / 7158285426421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16561519 / 5000000) ≤ -Real.log (500000000000 / 13724144062131) ∧
    -Real.log (500000000000 / 13724144062131) ≤ (662460761 / 200000000) := by
  have h := checkLog_sound (w := (5724144062131 / 21724144062131)) (n := 12)
    (lo := (13492877 / 25000000)) (hi := (539715081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13724144062131 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13724144062131 / 8000000000000) = 1/(500000000000 / 13724144062131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (16561519 / 5000000) (662460761 / 200000000) (Real.log (13724144062131 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13724144062131 / 500000000000) = -Real.log (500000000000 / 13724144062131) := by
    rw [show ((13724144062131 / 500000000000) : ℝ) = ((500000000000 / 13724144062131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (665755731 / 200000000) ≤ -Real.log (500000000000 / 13952120126023) ∧
    -Real.log (500000000000 / 13952120126023) ≤ (166438933 / 50000000) := by
  have h := checkLog_sound (w := (5952120126023 / 21952120126023)) (n := 12)
    (lo := (111237987 / 200000000)) (hi := (34761871 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13952120126023 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13952120126023 / 8000000000000) = 1/(500000000000 / 13952120126023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (665755731 / 200000000) (166438933 / 50000000) (Real.log (13952120126023 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13952120126023 / 500000000000) = -Real.log (500000000000 / 13952120126023) := by
    rw [show ((13952120126023 / 500000000000) : ℝ) = ((500000000000 / 13952120126023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0156

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0157Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0157
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

theorem reflection_log_1_neg : (324001353 / 500000000) ≤ -Real.log (1280 / 2447) ∧
    -Real.log (1280 / 2447) ≤ (648002707 / 1000000000) := by
  have h := checkLog_sound (w := (1167 / 3727)) (n := 12)
    (lo := (324001353 / 500000000)) (hi := (648002707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2447 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2447 / 1280) = 1/(1280 / 2447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (324001353 / 500000000) (648002707 / 1000000000) (Real.log (2447 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2447 / 1280) = -Real.log (1280 / 2447) := by
    rw [show ((2447 / 1280) : ℝ) = ((1280 / 2447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (151701721 / 62500000) ≤ -Real.log (113 / 1280) ∧
    -Real.log (113 / 1280) ≤ (121361377 / 50000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 113) = 1/(113 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-121361377 / 50000000) (-151701721 / 62500000) (Real.log (113 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (647225943 / 1000000000) ≤ -Real.log (12800 / 24451) ∧
    -Real.log (12800 / 24451) ≤ (80903243 / 125000000) := by
  have h := checkLog_sound (w := (11651 / 37251)) (n := 12)
    (lo := (647225943 / 1000000000)) (hi := (80903243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24451 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24451 / 12800) = 1/(12800 / 24451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (647225943 / 1000000000) (80903243 / 125000000) (Real.log (24451 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24451 / 12800) = -Real.log (12800 / 24451) := by
    rw [show ((24451 / 12800) : ℝ) = ((12800 / 24451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (241055317 / 100000000) ≤ -Real.log (1149 / 12800) ∧
    -Real.log (1149 / 12800) ≤ (1205276587 / 500000000) := by
  have h := checkLog_sound (w := (451 / 2749)) (n := 12)
    (lo := (33111163 / 100000000)) (hi := (331111631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1149) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1149) = 1/(1149 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1205276587 / 500000000) (-241055317 / 100000000) (Real.log (1149 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (120144691 / 200000000) ≤ -Real.log (640 / 1167) ∧
    -Real.log (640 / 1167) ≤ (1173288 / 1953125) := by
  have h := checkLog_sound (w := (527 / 1807)) (n := 12)
    (lo := (120144691 / 200000000)) (hi := (1173288 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167 / 640) = 1/(640 / 1167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (120144691 / 200000000) (1173288 / 1953125) (Real.log (1167 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1167 / 640) = -Real.log (640 / 1167) := by
    rw [show ((1167 / 640) : ℝ) = ((640 / 1167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (433520089 / 250000000) ≤ -Real.log (113 / 640) ∧
    -Real.log (113 / 640) ≤ (1734080359 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 113) = 1/(113 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1734080359 / 1000000000) (-433520089 / 250000000) (Real.log (113 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (299547011 / 500000000) ≤ -Real.log (6400 / 11651) ∧
    -Real.log (6400 / 11651) ≤ (599094023 / 1000000000) := by
  have h := checkLog_sound (w := (5251 / 18051)) (n := 12)
    (lo := (299547011 / 500000000)) (hi := (599094023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11651 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11651 / 6400) = 1/(6400 / 11651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (299547011 / 500000000) (599094023 / 1000000000) (Real.log (11651 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11651 / 6400) = -Real.log (6400 / 11651) := by
    rw [show ((11651 / 6400) : ℝ) = ((6400 / 11651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (171740599 / 100000000) ≤ -Real.log (1149 / 6400) ∧
    -Real.log (1149 / 6400) ≤ (1717405993 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 2749)) (n := 12)
    (lo := (33111163 / 100000000)) (hi := (331111631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1149) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1149) = 1/(1149 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1717405993 / 1000000000) (-171740599 / 100000000) (Real.log (1149 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (328871647 / 500000000) ≤ -Real.log (1000000 / 1930431) ∧
    -Real.log (1000000 / 1930431) ≤ (131548659 / 200000000) := by
  have h := checkLog_sound (w := (930431 / 2930431)) (n := 12)
    (lo := (328871647 / 500000000)) (hi := (131548659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1930431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1930431 / 1000000) = 1/(1000000 / 1930431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (328871647 / 500000000) (131548659 / 200000000) (Real.log (1930431 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1930431 / 1000000) = -Real.log (1000000 / 1930431) := by
    rw [show ((1930431 / 1000000) : ℝ) = ((1000000 / 1930431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2665436211 / 1000000000) ≤ -Real.log (69569 / 1000000) ∧
    -Real.log (69569 / 1000000) ≤ (533087243 / 200000000) := by
  have h := checkLog_sound (w := (55431 / 194569)) (n := 12)
    (lo := (585994671 / 1000000000)) (hi := (36624667 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 69569) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 69569) = 1/(69569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-533087243 / 200000000) (-2665436211 / 1000000000) (Real.log (69569 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (658280853 / 1000000000) ≤ -Real.log (1000000 / 1931469) ∧
    -Real.log (1000000 / 1931469) ≤ (329140427 / 500000000) := by
  have h := checkLog_sound (w := (931469 / 2931469)) (n := 12)
    (lo := (658280853 / 1000000000)) (hi := (329140427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1931469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1931469 / 1000000) = 1/(1000000 / 1931469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (658280853 / 1000000000) (329140427 / 500000000) (Real.log (1931469 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1931469 / 1000000) = -Real.log (1000000 / 1931469) := by
    rw [show ((1931469 / 1000000) : ℝ) = ((1000000 / 1931469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2680469079 / 1000000000) ≤ -Real.log (68531 / 1000000) ∧
    -Real.log (68531 / 1000000) ≤ (2680469083 / 1000000000) := by
  have h := checkLog_sound (w := (56469 / 193531)) (n := 12)
    (lo := (601027539 / 1000000000)) (hi := (30051377 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 68531) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 68531) = 1/(68531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2680469083 / 1000000000) (-2680469079 / 1000000000) (Real.log (68531 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (164197421 / 250000000) ≤ -Real.log (1000000 / 1928591) ∧
    -Real.log (1000000 / 1928591) ≤ (131357937 / 200000000) := by
  have h := checkLog_sound (w := (928591 / 2928591)) (n := 12)
    (lo := (164197421 / 250000000)) (hi := (131357937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1928591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1928591 / 1000000) = 1/(1000000 / 1928591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (164197421 / 250000000) (131357937 / 200000000) (Real.log (1928591 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1928591 / 1000000) = -Real.log (1000000 / 1928591) := by
    rw [show ((1928591 / 1000000) : ℝ) = ((1000000 / 1928591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (527866273 / 200000000) ≤ -Real.log (71409 / 1000000) ∧
    -Real.log (71409 / 1000000) ≤ (2639331369 / 1000000000) := by
  have h := checkLog_sound (w := (53591 / 196409)) (n := 12)
    (lo := (22395593 / 40000000)) (hi := (279944913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 71409) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 71409) = 1/(71409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2639331369 / 1000000000) (-527866273 / 200000000) (Real.log (71409 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (657363513 / 1000000000) ≤ -Real.log (500000 / 964849) ∧
    -Real.log (500000 / 964849) ≤ (328681757 / 500000000) := by
  have h := checkLog_sound (w := (464849 / 1464849)) (n := 12)
    (lo := (657363513 / 1000000000)) (hi := (328681757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((964849 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(964849 / 500000) = 1/(500000 / 964849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (657363513 / 1000000000) (328681757 / 500000000) (Real.log (964849 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (964849 / 500000) = -Real.log (500000 / 964849) := by
    rw [show ((964849 / 500000) : ℝ) = ((500000 / 964849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2654955029 / 1000000000) ≤ -Real.log (35151 / 500000) ∧
    -Real.log (35151 / 500000) ≤ (2654955033 / 1000000000) := by
  have h := checkLog_sound (w := (27349 / 97651)) (n := 12)
    (lo := (575513489 / 1000000000)) (hi := (57551349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35151) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 35151) = 1/(35151 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2654955033 / 1000000000) (-2654955029 / 1000000000) (Real.log (35151 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (207698719 / 62500000) ≤ -Real.log (250000000000 / 6937109200937) ∧
    -Real.log (250000000000 / 6937109200937) ≤ (3323179509 / 1000000000) := by
  have h := checkLog_sound (w := (2937109200937 / 10937109200937)) (n := 12)
    (lo := (8602981 / 15625000)) (hi := (110118157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6937109200937 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6937109200937 / 4000000000000) = 1/(250000000000 / 6937109200937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (207698719 / 62500000) (3323179509 / 1000000000) (Real.log (6937109200937 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6937109200937 / 250000000000) = -Real.log (250000000000 / 6937109200937) := by
    rw [show ((6937109200937 / 250000000000) : ℝ) = ((250000000000 / 6937109200937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (834687483 / 250000000) ≤ -Real.log (500000000000 / 14091936495893) ∧
    -Real.log (500000000000 / 14091936495893) ≤ (3338749937 / 1000000000) := by
  have h := checkLog_sound (w := (6091936495893 / 22091936495893)) (n := 12)
    (lo := (141540303 / 250000000)) (hi := (566161213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14091936495893 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14091936495893 / 8000000000000) = 1/(500000000000 / 14091936495893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (834687483 / 250000000) (3338749937 / 1000000000) (Real.log (14091936495893 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14091936495893 / 500000000000) = -Real.log (500000000000 / 14091936495893) := by
    rw [show ((14091936495893 / 500000000000) : ℝ) = ((500000000000 / 14091936495893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3296121049 / 1000000000) ≤ -Real.log (62500000000 / 1687979631419) ∧
    -Real.log (62500000000 / 1687979631419) ≤ (1648060527 / 500000000) := by
  have h := checkLog_sound (w := (687979631419 / 2687979631419)) (n := 12)
    (lo := (523532329 / 1000000000)) (hi := (52353233 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1687979631419 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1687979631419 / 1000000000000) = 1/(62500000000 / 1687979631419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3296121049 / 1000000000) (1648060527 / 500000000) (Real.log (1687979631419 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1687979631419 / 62500000000) = -Real.log (62500000000 / 1687979631419) := by
    rw [show ((1687979631419 / 62500000000) : ℝ) = ((62500000000 / 1687979631419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1656159271 / 500000000) ≤ -Real.log (125000000000 / 3431086597821) ∧
    -Real.log (125000000000 / 3431086597821) ≤ (3312318547 / 1000000000) := by
  have h := checkLog_sound (w := (1431086597821 / 5431086597821)) (n := 12)
    (lo := (269864911 / 500000000)) (hi := (539729823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3431086597821 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3431086597821 / 2000000000000) = 1/(125000000000 / 3431086597821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1656159271 / 500000000) (3312318547 / 1000000000) (Real.log (3431086597821 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3431086597821 / 125000000000) = -Real.log (125000000000 / 3431086597821) := by
    rw [show ((3431086597821 / 125000000000) : ℝ) = ((125000000000 / 3431086597821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0157

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0158Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0158
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

theorem reflection_log_1_neg : (647225943 / 1000000000) ≤ -Real.log (12800 / 24451) ∧
    -Real.log (12800 / 24451) ≤ (80903243 / 125000000) := by
  have h := checkLog_sound (w := (11651 / 37251)) (n := 12)
    (lo := (647225943 / 1000000000)) (hi := (80903243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24451 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24451 / 12800) = 1/(12800 / 24451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (647225943 / 1000000000) (80903243 / 125000000) (Real.log (24451 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24451 / 12800) = -Real.log (12800 / 24451) := by
    rw [show ((24451 / 12800) : ℝ) = ((12800 / 24451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (241055317 / 100000000) ≤ -Real.log (1149 / 12800) ∧
    -Real.log (1149 / 12800) ≤ (1205276587 / 500000000) := by
  have h := checkLog_sound (w := (451 / 2749)) (n := 12)
    (lo := (33111163 / 100000000)) (hi := (331111631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1149) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1149) = 1/(1149 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1205276587 / 500000000) (-241055317 / 100000000) (Real.log (1149 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (646448577 / 1000000000) ≤ -Real.log (800 / 1527) ∧
    -Real.log (800 / 1527) ≤ (323224289 / 500000000) := by
  have h := checkLog_sound (w := (727 / 2327)) (n := 12)
    (lo := (646448577 / 1000000000)) (hi := (323224289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1527 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1527 / 800) = 1/(800 / 1527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (646448577 / 1000000000) (323224289 / 500000000) (Real.log (1527 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1527 / 800) = -Real.log (800 / 1527) := by
    rw [show ((1527 / 800) : ℝ) = ((800 / 1527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (598538071 / 250000000) ≤ -Real.log (73 / 800) ∧
    -Real.log (73 / 800) ≤ (74817259 / 31250000) := by
  have h := checkLog_sound (w := (27 / 173)) (n := 12)
    (lo := (39338843 / 125000000)) (hi := (62942149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 73) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 73) = 1/(73 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-74817259 / 31250000) (-598538071 / 250000000) (Real.log (73 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (299547011 / 500000000) ≤ -Real.log (6400 / 11651) ∧
    -Real.log (6400 / 11651) ≤ (599094023 / 1000000000) := by
  have h := checkLog_sound (w := (5251 / 18051)) (n := 12)
    (lo := (299547011 / 500000000)) (hi := (599094023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11651 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11651 / 6400) = 1/(6400 / 11651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (299547011 / 500000000) (599094023 / 1000000000) (Real.log (11651 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11651 / 6400) = -Real.log (6400 / 11651) := by
    rw [show ((11651 / 6400) : ℝ) = ((6400 / 11651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (171740599 / 100000000) ≤ -Real.log (1149 / 6400) ∧
    -Real.log (1149 / 6400) ≤ (1717405993 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 2749)) (n := 12)
    (lo := (33111163 / 100000000)) (hi := (331111631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1149) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1149) = 1/(1149 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1717405993 / 1000000000) (-171740599 / 100000000) (Real.log (1149 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (59746193 / 100000000) ≤ -Real.log (400 / 727) ∧
    -Real.log (400 / 727) ≤ (597461931 / 1000000000) := by
  have h := checkLog_sound (w := (327 / 1127)) (n := 12)
    (lo := (59746193 / 100000000)) (hi := (597461931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727 / 400) = 1/(400 / 727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (59746193 / 100000000) (597461931 / 1000000000) (Real.log (727 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (727 / 400) = -Real.log (400 / 727) := by
    rw [show ((727 / 400) : ℝ) = ((400 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (106312819 / 62500000) ≤ -Real.log (73 / 400) ∧
    -Real.log (73 / 400) ≤ (1701005107 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 173)) (n := 12)
    (lo := (39338843 / 125000000)) (hi := (62942149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 73) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(100 / 73) = 1/(73 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1701005107 / 1000000000) (-106312819 / 62500000) (Real.log (73 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (657208037 / 1000000000) ≤ -Real.log (500000 / 964699) ∧
    -Real.log (500000 / 964699) ≤ (328604019 / 500000000) := by
  have h := checkLog_sound (w := (464699 / 1464699)) (n := 12)
    (lo := (657208037 / 1000000000)) (hi := (328604019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((964699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(964699 / 500000) = 1/(500000 / 964699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (657208037 / 1000000000) (328604019 / 500000000) (Real.log (964699 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (964699 / 500000) = -Real.log (500000 / 964699) := by
    rw [show ((964699 / 500000) : ℝ) = ((500000 / 964699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (662674201 / 250000000) ≤ -Real.log (35301 / 500000) ∧
    -Real.log (35301 / 500000) ≤ (331337101 / 125000000) := by
  have h := checkLog_sound (w := (27199 / 97801)) (n := 12)
    (lo := (17851727 / 31250000)) (hi := (114251053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35301) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 35301) = 1/(35301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-331337101 / 125000000) (-662674201 / 250000000) (Real.log (35301 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (164435953 / 250000000) ≤ -Real.log (15625 / 30163) ∧
    -Real.log (15625 / 30163) ≤ (657743813 / 1000000000) := by
  have h := checkLog_sound (w := (7269 / 22894)) (n := 12)
    (lo := (164435953 / 250000000)) (hi := (657743813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30163 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30163 / 15625) = 1/(15625 / 30163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (164435953 / 250000000) (657743813 / 1000000000) (Real.log (30163 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (30163 / 15625) = -Real.log (15625 / 30163) := by
    rw [show ((30163 / 15625) : ℝ) = ((15625 / 30163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (533090117 / 200000000) ≤ -Real.log (1087 / 15625) ∧
    -Real.log (1087 / 15625) ≤ (2665450589 / 1000000000) := by
  have h := checkLog_sound (w := (6929 / 24321)) (n := 12)
    (lo := (117201809 / 200000000)) (hi := (293004523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8696) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 8696) = 1/(1087 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2665450589 / 1000000000) (-533090117 / 200000000) (Real.log (1087 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (656217081 / 1000000000) ≤ -Real.log (1000000 / 1927487) ∧
    -Real.log (1000000 / 1927487) ≤ (328108541 / 500000000) := by
  have h := checkLog_sound (w := (927487 / 2927487)) (n := 12)
    (lo := (656217081 / 1000000000)) (hi := (328108541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1927487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1927487 / 1000000) = 1/(1000000 / 1927487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (656217081 / 1000000000) (328108541 / 500000000) (Real.log (1927487 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1927487 / 1000000) = -Real.log (1000000 / 1927487) := by
    rw [show ((1927487 / 1000000) : ℝ) = ((1000000 / 1927487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2623989421 / 1000000000) ≤ -Real.log (72513 / 1000000) ∧
    -Real.log (72513 / 1000000) ≤ (104959577 / 40000000) := by
  have h := checkLog_sound (w := (52487 / 197513)) (n := 12)
    (lo := (544547881 / 1000000000)) (hi := (272273941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72513) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 72513) = 1/(72513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-104959577 / 40000000) (-2623989421 / 1000000000) (Real.log (72513 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (328395101 / 500000000) ≤ -Real.log (62500 / 120537) ∧
    -Real.log (62500 / 120537) ≤ (656790203 / 1000000000) := by
  have h := checkLog_sound (w := (58037 / 183037)) (n := 12)
    (lo := (328395101 / 500000000)) (hi := (656790203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120537 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120537 / 62500) = 1/(62500 / 120537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (328395101 / 500000000) (656790203 / 1000000000) (Real.log (120537 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (120537 / 62500) = -Real.log (62500 / 120537) := by
    rw [show ((120537 / 62500) : ℝ) = ((62500 / 120537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2639345369 / 1000000000) ≤ -Real.log (4463 / 62500) ∧
    -Real.log (4463 / 62500) ≤ (2639345373 / 1000000000) := by
  have h := checkLog_sound (w := (6699 / 24551)) (n := 12)
    (lo := (559903829 / 1000000000)) (hi := (55990383 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8926) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 8926) = 1/(4463 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2639345373 / 1000000000) (-2639345369 / 1000000000) (Real.log (4463 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3307904841 / 1000000000) ≤ -Real.log (500000000000 / 13663904705249) ∧
    -Real.log (500000000000 / 13663904705249) ≤ (1653952423 / 500000000) := by
  have h := checkLog_sound (w := (5663904705249 / 21663904705249)) (n := 12)
    (lo := (535316121 / 1000000000)) (hi := (267658061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13663904705249 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13663904705249 / 8000000000000) = 1/(500000000000 / 13663904705249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3307904841 / 1000000000) (1653952423 / 500000000) (Real.log (13663904705249 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (13663904705249 / 500000000000) = -Real.log (500000000000 / 13663904705249) := by
    rw [show ((13663904705249 / 500000000000) : ℝ) = ((500000000000 / 13663904705249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3323194397 / 1000000000) ≤ -Real.log (500000000 / 13874425023) ∧
    -Real.log (500000000 / 13874425023) ≤ (1661597201 / 500000000) := by
  have h := checkLog_sound (w := (5874425023 / 21874425023)) (n := 12)
    (lo := (550605677 / 1000000000)) (hi := (275302839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13874425023 / 8000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13874425023 / 8000000000) = 1/(500000000 / 13874425023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3323194397 / 1000000000) (1661597201 / 500000000) (Real.log (13874425023 / 500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13874425023 / 500000000) = -Real.log (500000000 / 13874425023) := by
    rw [show ((13874425023 / 500000000) : ℝ) = ((500000000 / 13874425023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1640103251 / 500000000) ≤ -Real.log (500000000000 / 13290630645539) ∧
    -Real.log (500000000000 / 13290630645539) ≤ (3280206507 / 1000000000) := by
  have h := checkLog_sound (w := (5290630645539 / 21290630645539)) (n := 12)
    (lo := (253808891 / 500000000)) (hi := (507617783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13290630645539 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13290630645539 / 8000000000000) = 1/(500000000000 / 13290630645539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1640103251 / 500000000) (3280206507 / 1000000000) (Real.log (13290630645539 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13290630645539 / 500000000000) = -Real.log (500000000000 / 13290630645539) := by
    rw [show ((13290630645539 / 500000000000) : ℝ) = ((500000000000 / 13290630645539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3296135571 / 1000000000) ≤ -Real.log (500000000000 / 13504033161551) ∧
    -Real.log (500000000000 / 13504033161551) ≤ (412016947 / 125000000) := by
  have h := checkLog_sound (w := (5504033161551 / 21504033161551)) (n := 12)
    (lo := (523546851 / 1000000000)) (hi := (130886713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13504033161551 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13504033161551 / 8000000000000) = 1/(500000000000 / 13504033161551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3296135571 / 1000000000) (412016947 / 125000000) (Real.log (13504033161551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13504033161551 / 500000000000) = -Real.log (500000000000 / 13504033161551) := by
    rw [show ((13504033161551 / 500000000000) : ℝ) = ((500000000000 / 13504033161551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0158

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0159Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0159
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

theorem reflection_log_1_neg : (646448577 / 1000000000) ≤ -Real.log (800 / 1527) ∧
    -Real.log (800 / 1527) ≤ (323224289 / 500000000) := by
  have h := checkLog_sound (w := (727 / 2327)) (n := 12)
    (lo := (646448577 / 1000000000)) (hi := (323224289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1527 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1527 / 800) = 1/(800 / 1527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (646448577 / 1000000000) (323224289 / 500000000) (Real.log (1527 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1527 / 800) = -Real.log (800 / 1527) := by
    rw [show ((1527 / 800) : ℝ) = ((800 / 1527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (598538071 / 250000000) ≤ -Real.log (73 / 800) ∧
    -Real.log (73 / 800) ≤ (74817259 / 31250000) := by
  have h := checkLog_sound (w := (27 / 173)) (n := 12)
    (lo := (39338843 / 125000000)) (hi := (62942149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 73) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 73) = 1/(73 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-74817259 / 31250000) (-598538071 / 250000000) (Real.log (73 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (322835303 / 500000000) ≤ -Real.log (12800 / 24413) ∧
    -Real.log (12800 / 24413) ≤ (645670607 / 1000000000) := by
  have h := checkLog_sound (w := (11613 / 37213)) (n := 12)
    (lo := (322835303 / 500000000)) (hi := (645670607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24413 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24413 / 12800) = 1/(12800 / 24413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (322835303 / 500000000) (645670607 / 1000000000) (Real.log (24413 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24413 / 12800) = -Real.log (12800 / 24413) := by
    rw [show ((24413 / 12800) : ℝ) = ((12800 / 24413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2378016053 / 1000000000) ≤ -Real.log (1187 / 12800) ∧
    -Real.log (1187 / 12800) ≤ (2378016057 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 2787)) (n := 12)
    (lo := (298574513 / 1000000000)) (hi := (149287257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1187) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1187) = 1/(1187 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2378016057 / 1000000000) (-2378016053 / 1000000000) (Real.log (1187 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (59746193 / 100000000) ≤ -Real.log (400 / 727) ∧
    -Real.log (400 / 727) ≤ (597461931 / 1000000000) := by
  have h := checkLog_sound (w := (327 / 1127)) (n := 12)
    (lo := (59746193 / 100000000)) (hi := (597461931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727 / 400) = 1/(400 / 727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (59746193 / 100000000) (597461931 / 1000000000) (Real.log (727 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (727 / 400) = -Real.log (400 / 727) := by
    rw [show ((727 / 400) : ℝ) = ((400 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (106312819 / 62500000) ≤ -Real.log (73 / 400) ∧
    -Real.log (73 / 400) ≤ (1701005107 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 173)) (n := 12)
    (lo := (39338843 / 125000000)) (hi := (62942149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 73) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(100 / 73) = 1/(73 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1701005107 / 1000000000) (-106312819 / 62500000) (Real.log (73 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (595827169 / 1000000000) ≤ -Real.log (6400 / 11613) ∧
    -Real.log (6400 / 11613) ≤ (59582717 / 100000000) := by
  have h := checkLog_sound (w := (5213 / 18013)) (n := 12)
    (lo := (595827169 / 1000000000)) (hi := (59582717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11613 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11613 / 6400) = 1/(6400 / 11613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (595827169 / 1000000000) (59582717 / 100000000) (Real.log (11613 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11613 / 6400) = -Real.log (6400 / 11613) := by
    rw [show ((11613 / 6400) : ℝ) = ((6400 / 11613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1684868873 / 1000000000) ≤ -Real.log (1187 / 6400) ∧
    -Real.log (1187 / 6400) ≤ (421217219 / 250000000) := by
  have h := checkLog_sound (w := (413 / 2787)) (n := 12)
    (lo := (298574513 / 1000000000)) (hi := (149287257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1187) = 1/(1187 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-421217219 / 250000000) (-1684868873 / 1000000000) (Real.log (1187 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (656674049 / 1000000000) ≤ -Real.log (62500 / 120523) ∧
    -Real.log (62500 / 120523) ≤ (13133481 / 20000000) := by
  have h := checkLog_sound (w := (58023 / 183023)) (n := 12)
    (lo := (656674049 / 1000000000)) (hi := (13133481 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120523 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120523 / 62500) = 1/(62500 / 120523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (656674049 / 1000000000) (13133481 / 20000000) (Real.log (120523 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (120523 / 62500) = -Real.log (62500 / 120523) := by
    rw [show ((120523 / 62500) : ℝ) = ((62500 / 120523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21089707 / 8000000) ≤ -Real.log (4477 / 62500) ∧
    -Real.log (4477 / 62500) ≤ (2636213379 / 1000000000) := by
  have h := checkLog_sound (w := (6671 / 24579)) (n := 12)
    (lo := (111354367 / 200000000)) (hi := (139192959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8954) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 8954) = 1/(4477 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2636213379 / 1000000000) (-21089707 / 8000000) (Real.log (4477 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (131441711 / 200000000) ≤ -Real.log (1000000 / 1929399) ∧
    -Real.log (1000000 / 1929399) ≤ (164302139 / 250000000) := by
  have h := checkLog_sound (w := (929399 / 2929399)) (n := 12)
    (lo := (131441711 / 200000000)) (hi := (164302139 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1929399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1929399 / 1000000) = 1/(1000000 / 1929399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (131441711 / 200000000) (164302139 / 250000000) (Real.log (1929399 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1929399 / 1000000) = -Real.log (1000000 / 1929399) := by
    rw [show ((1929399 / 1000000) : ℝ) = ((1000000 / 1929399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (331338871 / 125000000) ≤ -Real.log (70601 / 1000000) ∧
    -Real.log (70601 / 1000000) ≤ (662677743 / 250000000) := by
  have h := checkLog_sound (w := (54399 / 195601)) (n := 12)
    (lo := (142817357 / 250000000)) (hi := (571269429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 70601) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 70601) = 1/(70601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-662677743 / 250000000) (-331338871 / 125000000) (Real.log (70601 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (65564467 / 100000000) ≤ -Real.log (62500 / 120399) ∧
    -Real.log (62500 / 120399) ≤ (655644671 / 1000000000) := by
  have h := checkLog_sound (w := (57899 / 182899)) (n := 12)
    (lo := (65564467 / 100000000)) (hi := (655644671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120399 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120399 / 62500) = 1/(62500 / 120399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (65564467 / 100000000) (655644671 / 1000000000) (Real.log (120399 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (120399 / 62500) = -Real.log (62500 / 120399) := by
    rw [show ((120399 / 62500) : ℝ) = ((62500 / 120399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2608892883 / 1000000000) ≤ -Real.log (4601 / 62500) ∧
    -Real.log (4601 / 62500) ≤ (2608892887 / 1000000000) := by
  have h := checkLog_sound (w := (6423 / 24827)) (n := 12)
    (lo := (529451343 / 1000000000)) (hi := (33090709 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9202) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 9202) = 1/(4601 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2608892887 / 1000000000) (-2608892883 / 1000000000) (Real.log (4601 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (51267 / 78125) ≤ -Real.log (15625 / 30117) ∧
    -Real.log (15625 / 30117) ≤ (656217601 / 1000000000) := by
  have h := checkLog_sound (w := (7246 / 22871)) (n := 12)
    (lo := (51267 / 78125)) (hi := (656217601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30117 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30117 / 15625) = 1/(15625 / 30117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (51267 / 78125) (656217601 / 1000000000) (Real.log (30117 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (30117 / 15625) = -Real.log (15625 / 30117) := by
    rw [show ((30117 / 15625) : ℝ) = ((15625 / 30117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2624003211 / 1000000000) ≤ -Real.log (1133 / 15625) ∧
    -Real.log (1133 / 15625) ≤ (524800643 / 200000000) := by
  have h := checkLog_sound (w := (6561 / 24689)) (n := 12)
    (lo := (544561671 / 1000000000)) (hi := (68070209 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9064) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 9064) = 1/(1133 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-524800643 / 200000000) (-2624003211 / 1000000000) (Real.log (1133 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (25725683 / 7812500) ≤ -Real.log (62500000000 / 1682530154121) ∧
    -Real.log (62500000000 / 1682530154121) ≤ (3292887429 / 1000000000) := by
  have h := checkLog_sound (w := (682530154121 / 2682530154121)) (n := 12)
    (lo := (32518669 / 62500000)) (hi := (104059741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1682530154121 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1682530154121 / 1000000000000) = 1/(62500000000 / 1682530154121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (25725683 / 7812500) (3292887429 / 1000000000) (Real.log (1682530154121 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1682530154121 / 62500000000) = -Real.log (62500000000 / 1682530154121) := by
    rw [show ((1682530154121 / 62500000000) : ℝ) = ((62500000000 / 1682530154121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3307919523 / 1000000000) ≤ -Real.log (1953125000 / 53375411423) ∧
    -Real.log (1953125000 / 53375411423) ≤ (413489941 / 125000000) := by
  have h := checkLog_sound (w := (22125411423 / 84625411423)) (n := 12)
    (lo := (535330803 / 1000000000)) (hi := (133832701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53375411423 / 31250000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(53375411423 / 31250000000) = 1/(1953125000 / 53375411423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3307919523 / 1000000000) (413489941 / 125000000) (Real.log (53375411423 / 1953125000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (53375411423 / 1953125000) = -Real.log (1953125000 / 53375411423) := by
    rw [show ((53375411423 / 1953125000) : ℝ) = ((1953125000 / 53375411423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3264537553 / 1000000000) ≤ -Real.log (244140625 / 6388673573) ∧
    -Real.log (244140625 / 6388673573) ≤ (1632268779 / 500000000) := by
  have h := checkLog_sound (w := (2482423573 / 10294923573)) (n := 12)
    (lo := (491948833 / 1000000000)) (hi := (245974417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6388673573 / 3906250000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6388673573 / 3906250000) = 1/(244140625 / 6388673573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3264537553 / 1000000000) (1632268779 / 500000000) (Real.log (6388673573 / 244140625)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6388673573 / 244140625) = -Real.log (244140625 / 6388673573) := by
    rw [show ((6388673573 / 244140625) : ℝ) = ((244140625 / 6388673573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (820055203 / 250000000) ≤ -Real.log (62500000000 / 1661352603707) ∧
    -Real.log (62500000000 / 1661352603707) ≤ (3280220817 / 1000000000) := by
  have h := checkLog_sound (w := (661352603707 / 2661352603707)) (n := 12)
    (lo := (126908023 / 250000000)) (hi := (507632093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1661352603707 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1661352603707 / 1000000000000) = 1/(62500000000 / 1661352603707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (820055203 / 250000000) (3280220817 / 1000000000) (Real.log (1661352603707 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1661352603707 / 62500000000) = -Real.log (62500000000 / 1661352603707) := by
    rw [show ((1661352603707 / 62500000000) : ℝ) = ((62500000000 / 1661352603707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0159

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0160Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0160
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

theorem reflection_log_1_neg : (322835303 / 500000000) ≤ -Real.log (12800 / 24413) ∧
    -Real.log (12800 / 24413) ≤ (645670607 / 1000000000) := by
  have h := checkLog_sound (w := (11613 / 37213)) (n := 12)
    (lo := (322835303 / 500000000)) (hi := (645670607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24413 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24413 / 12800) = 1/(12800 / 24413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (322835303 / 500000000) (645670607 / 1000000000) (Real.log (24413 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24413 / 12800) = -Real.log (12800 / 24413) := by
    rw [show ((24413 / 12800) : ℝ) = ((12800 / 24413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2378016053 / 1000000000) ≤ -Real.log (1187 / 12800) ∧
    -Real.log (1187 / 12800) ≤ (2378016057 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 2787)) (n := 12)
    (lo := (298574513 / 1000000000)) (hi := (149287257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1187) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1187) = 1/(1187 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2378016057 / 1000000000) (-2378016053 / 1000000000) (Real.log (1187 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (644892029 / 1000000000) ≤ -Real.log (6400 / 12197) ∧
    -Real.log (6400 / 12197) ≤ (64489203 / 100000000) := by
  have h := checkLog_sound (w := (5797 / 18597)) (n := 12)
    (lo := (644892029 / 1000000000)) (hi := (64489203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12197 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12197 / 6400) = 1/(6400 / 12197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (644892029 / 1000000000) (64489203 / 100000000) (Real.log (12197 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12197 / 6400) = -Real.log (6400 / 12197) := by
    rw [show ((12197 / 6400) : ℝ) = ((6400 / 12197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (236213607 / 100000000) ≤ -Real.log (603 / 6400) ∧
    -Real.log (603 / 6400) ≤ (1181068037 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1403)) (n := 12)
    (lo := (28269453 / 100000000)) (hi := (282694531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 603) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 603) = 1/(603 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1181068037 / 500000000) (-236213607 / 100000000) (Real.log (603 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (595827169 / 1000000000) ≤ -Real.log (6400 / 11613) ∧
    -Real.log (6400 / 11613) ≤ (59582717 / 100000000) := by
  have h := checkLog_sound (w := (5213 / 18013)) (n := 12)
    (lo := (595827169 / 1000000000)) (hi := (59582717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11613 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11613 / 6400) = 1/(6400 / 11613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (595827169 / 1000000000) (59582717 / 100000000) (Real.log (11613 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11613 / 6400) = -Real.log (6400 / 11613) := by
    rw [show ((11613 / 6400) : ℝ) = ((6400 / 11613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1684868873 / 1000000000) ≤ -Real.log (1187 / 6400) ∧
    -Real.log (1187 / 6400) ≤ (421217219 / 250000000) := by
  have h := checkLog_sound (w := (413 / 2787)) (n := 12)
    (lo := (298574513 / 1000000000)) (hi := (149287257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1187) = 1/(1187 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-421217219 / 250000000) (-1684868873 / 1000000000) (Real.log (1187 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (148547433 / 250000000) ≤ -Real.log (3200 / 5797) ∧
    -Real.log (3200 / 5797) ≤ (594189733 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 8997)) (n := 12)
    (lo := (148547433 / 250000000)) (hi := (594189733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5797 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5797 / 3200) = 1/(3200 / 5797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (148547433 / 250000000) (594189733 / 1000000000) (Real.log (5797 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5797 / 3200) = -Real.log (3200 / 5797) := by
    rw [show ((5797 / 3200) : ℝ) = ((3200 / 5797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (166898889 / 100000000) ≤ -Real.log (603 / 3200) ∧
    -Real.log (603 / 3200) ≤ (1668988893 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1403)) (n := 12)
    (lo := (28269453 / 100000000)) (hi := (282694531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 603) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 603) = 1/(603 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1668988893 / 1000000000) (-166898889 / 100000000) (Real.log (603 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (656141851 / 1000000000) ≤ -Real.log (500000 / 963671) ∧
    -Real.log (500000 / 963671) ≤ (164035463 / 250000000) := by
  have h := checkLog_sound (w := (463671 / 1463671)) (n := 12)
    (lo := (656141851 / 1000000000)) (hi := (164035463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963671 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(963671 / 500000) = 1/(500000 / 963671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (656141851 / 1000000000) (164035463 / 250000000) (Real.log (963671 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (963671 / 500000) = -Real.log (500000 / 963671) := by
    rw [show ((963671 / 500000) : ℝ) = ((500000 / 963671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81937243 / 31250000) ≤ -Real.log (36329 / 500000) ∧
    -Real.log (36329 / 500000) ≤ (131099589 / 50000000) := by
  have h := checkLog_sound (w := (26171 / 98829)) (n := 12)
    (lo := (135637559 / 250000000)) (hi := (542550237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36329) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 36329) = 1/(36329 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-131099589 / 50000000) (-81937243 / 31250000) (Real.log (36329 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (328337543 / 500000000) ≤ -Real.log (100000 / 192837) ∧
    -Real.log (100000 / 192837) ≤ (656675087 / 1000000000) := by
  have h := checkLog_sound (w := (92837 / 292837)) (n := 12)
    (lo := (328337543 / 500000000)) (hi := (656675087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192837 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192837 / 100000) = 1/(100000 / 192837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (328337543 / 500000000) (656675087 / 1000000000) (Real.log (192837 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (192837 / 100000) = -Real.log (100000 / 192837) := by
    rw [show ((192837 / 100000) : ℝ) = ((100000 / 192837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (164765081 / 62500000) ≤ -Real.log (7163 / 100000) ∧
    -Real.log (7163 / 100000) ≤ (26362413 / 10000000) := by
  have h := checkLog_sound (w := (5337 / 19663)) (n := 12)
    (lo := (139199939 / 250000000)) (hi := (556799757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7163) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 7163) = 1/(7163 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-26362413 / 10000000) (-164765081 / 62500000) (Real.log (7163 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (655072969 / 1000000000) ≤ -Real.log (1000000 / 1925283) ∧
    -Real.log (1000000 / 1925283) ≤ (65507297 / 100000000) := by
  have h := checkLog_sound (w := (925283 / 2925283)) (n := 12)
    (lo := (655072969 / 1000000000)) (hi := (65507297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1925283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1925283 / 1000000) = 1/(1000000 / 1925283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (655072969 / 1000000000) (65507297 / 100000000) (Real.log (1925283 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1925283 / 1000000) = -Real.log (1000000 / 1925283) := by
    rw [show ((1925283 / 1000000) : ℝ) = ((1000000 / 1925283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1297023817 / 500000000) ≤ -Real.log (74717 / 1000000) ∧
    -Real.log (74717 / 1000000) ≤ (1297023819 / 500000000) := by
  have h := checkLog_sound (w := (50283 / 199717)) (n := 12)
    (lo := (257303047 / 500000000)) (hi := (102921219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 74717) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 74717) = 1/(74717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1297023819 / 500000000) (-1297023817 / 500000000) (Real.log (74717 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (655645189 / 1000000000) ≤ -Real.log (200000 / 385277) ∧
    -Real.log (200000 / 385277) ≤ (65564519 / 100000000) := by
  have h := checkLog_sound (w := (185277 / 585277)) (n := 12)
    (lo := (655645189 / 1000000000)) (hi := (65564519 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((385277 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(385277 / 200000) = 1/(200000 / 385277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (655645189 / 1000000000) (65564519 / 100000000) (Real.log (385277 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (385277 / 200000) = -Real.log (200000 / 385277) := by
    rw [show ((385277 / 200000) : ℝ) = ((200000 / 385277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2608906467 / 1000000000) ≤ -Real.log (14723 / 200000) ∧
    -Real.log (14723 / 200000) ≤ (2608906471 / 1000000000) := by
  have h := checkLog_sound (w := (10277 / 39723)) (n := 12)
    (lo := (529464927 / 1000000000)) (hi := (16545779 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 14723) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 14723) = 1/(14723 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2608906471 / 1000000000) (-2608906467 / 1000000000) (Real.log (14723 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3278133627 / 1000000000) ≤ -Real.log (250000000000 / 6631554680833) ∧
    -Real.log (250000000000 / 6631554680833) ≤ (25610419 / 7812500) := by
  have h := checkLog_sound (w := (2631554680833 / 10631554680833)) (n := 12)
    (lo := (505544907 / 1000000000)) (hi := (126386227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6631554680833 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6631554680833 / 4000000000000) = 1/(250000000000 / 6631554680833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3278133627 / 1000000000) (25610419 / 7812500) (Real.log (6631554680833 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6631554680833 / 250000000000) = -Real.log (250000000000 / 6631554680833) := by
    rw [show ((6631554680833 / 250000000000) : ℝ) = ((250000000000 / 6631554680833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1646458191 / 500000000) ≤ -Real.log (500000000000 / 13460631020523) ∧
    -Real.log (500000000000 / 13460631020523) ≤ (3292916387 / 1000000000) := by
  have h := checkLog_sound (w := (5460631020523 / 21460631020523)) (n := 12)
    (lo := (260163831 / 500000000)) (hi := (520327663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13460631020523 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13460631020523 / 8000000000000) = 1/(500000000000 / 13460631020523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1646458191 / 500000000) (3292916387 / 1000000000) (Real.log (13460631020523 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13460631020523 / 500000000000) = -Real.log (500000000000 / 13460631020523) := by
    rw [show ((13460631020523 / 500000000000) : ℝ) = ((500000000000 / 13460631020523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3249120603 / 1000000000) ≤ -Real.log (250000000000 / 6441917502041) ∧
    -Real.log (250000000000 / 6441917502041) ≤ (101535019 / 31250000) := by
  have h := checkLog_sound (w := (2441917502041 / 10441917502041)) (n := 12)
    (lo := (476531883 / 1000000000)) (hi := (119132971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6441917502041 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6441917502041 / 4000000000000) = 1/(250000000000 / 6441917502041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3249120603 / 1000000000) (101535019 / 31250000) (Real.log (6441917502041 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6441917502041 / 250000000000) = -Real.log (250000000000 / 6441917502041) := by
    rw [show ((6441917502041 / 250000000000) : ℝ) = ((250000000000 / 6441917502041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (408068957 / 125000000) ≤ -Real.log (250000000000 / 6542094002581) ∧
    -Real.log (250000000000 / 6542094002581) ≤ (3264551661 / 1000000000) := by
  have h := checkLog_sound (w := (2542094002581 / 10542094002581)) (n := 12)
    (lo := (61495367 / 125000000)) (hi := (491962937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6542094002581 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6542094002581 / 4000000000000) = 1/(250000000000 / 6542094002581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (408068957 / 125000000) (3264551661 / 1000000000) (Real.log (6542094002581 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6542094002581 / 250000000000) = -Real.log (250000000000 / 6542094002581) := by
    rw [show ((6542094002581 / 250000000000) : ℝ) = ((250000000000 / 6542094002581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0160

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0161Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0161
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

theorem reflection_log_1_neg : (644892029 / 1000000000) ≤ -Real.log (6400 / 12197) ∧
    -Real.log (6400 / 12197) ≤ (64489203 / 100000000) := by
  have h := checkLog_sound (w := (5797 / 18597)) (n := 12)
    (lo := (644892029 / 1000000000)) (hi := (64489203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12197 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12197 / 6400) = 1/(6400 / 12197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (644892029 / 1000000000) (64489203 / 100000000) (Real.log (12197 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12197 / 6400) = -Real.log (6400 / 12197) := by
    rw [show ((12197 / 6400) : ℝ) = ((6400 / 12197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (236213607 / 100000000) ≤ -Real.log (603 / 6400) ∧
    -Real.log (603 / 6400) ≤ (1181068037 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1403)) (n := 12)
    (lo := (28269453 / 100000000)) (hi := (282694531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 603) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 603) = 1/(603 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1181068037 / 500000000) (-236213607 / 100000000) (Real.log (603 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128822569 / 200000000) ≤ -Real.log (512 / 975) ∧
    -Real.log (512 / 975) ≤ (322056423 / 500000000) := by
  have h := checkLog_sound (w := (463 / 1487)) (n := 12)
    (lo := (128822569 / 200000000)) (hi := (322056423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((975 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(975 / 512) = 1/(512 / 975) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128822569 / 200000000) (322056423 / 500000000) (Real.log (975 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (975 / 512) = -Real.log (512 / 975) := by
    rw [show ((975 / 512) : ℝ) = ((512 / 975) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (93860173 / 40000000) ≤ -Real.log (49 / 512) ∧
    -Real.log (49 / 512) ≤ (2346504329 / 1000000000) := by
  have h := checkLog_sound (w := (15 / 113)) (n := 12)
    (lo := (53412557 / 200000000)) (hi := (133531393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 49) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(64 / 49) = 1/(49 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2346504329 / 1000000000) (-93860173 / 40000000) (Real.log (49 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (148547433 / 250000000) ≤ -Real.log (3200 / 5797) ∧
    -Real.log (3200 / 5797) ≤ (594189733 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 8997)) (n := 12)
    (lo := (148547433 / 250000000)) (hi := (594189733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5797 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5797 / 3200) = 1/(3200 / 5797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (148547433 / 250000000) (594189733 / 1000000000) (Real.log (5797 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5797 / 3200) = -Real.log (3200 / 5797) := by
    rw [show ((5797 / 3200) : ℝ) = ((3200 / 5797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (166898889 / 100000000) ≤ -Real.log (603 / 3200) ∧
    -Real.log (603 / 3200) ≤ (1668988893 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1403)) (n := 12)
    (lo := (28269453 / 100000000)) (hi := (282694531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 603) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 603) = 1/(603 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1668988893 / 1000000000) (-166898889 / 100000000) (Real.log (603 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (592549609 / 1000000000) ≤ -Real.log (256 / 463) ∧
    -Real.log (256 / 463) ≤ (59254961 / 100000000) := by
  have h := checkLog_sound (w := (207 / 719)) (n := 12)
    (lo := (592549609 / 1000000000)) (hi := (59254961 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463 / 256) = 1/(256 / 463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (592549609 / 1000000000) (59254961 / 100000000) (Real.log (463 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (463 / 256) = -Real.log (256 / 463) := by
    rw [show ((463 / 256) : ℝ) = ((256 / 463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (330671429 / 200000000) ≤ -Real.log (49 / 256) ∧
    -Real.log (49 / 256) ≤ (413339287 / 250000000) := by
  have h := checkLog_sound (w := (15 / 113)) (n := 12)
    (lo := (53412557 / 200000000)) (hi := (133531393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 49) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 49) = 1/(49 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-413339287 / 250000000) (-330671429 / 200000000) (Real.log (49 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (655610927 / 1000000000) ≤ -Real.log (1000000 / 1926319) ∧
    -Real.log (1000000 / 1926319) ≤ (40975683 / 62500000) := by
  have h := checkLog_sound (w := (926319 / 2926319)) (n := 12)
    (lo := (655610927 / 1000000000)) (hi := (40975683 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1926319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1926319 / 1000000) = 1/(1000000 / 1926319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (655610927 / 1000000000) (40975683 / 62500000) (Real.log (1926319 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1926319 / 1000000) = -Real.log (1000000 / 1926319) := by
    rw [show ((1926319 / 1000000) : ℝ) = ((1000000 / 1926319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2608010313 / 1000000000) ≤ -Real.log (73681 / 1000000) ∧
    -Real.log (73681 / 1000000) ≤ (2608010317 / 1000000000) := by
  have h := checkLog_sound (w := (51319 / 198681)) (n := 12)
    (lo := (528568773 / 1000000000)) (hi := (264284387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 73681) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 73681) = 1/(73681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2608010317 / 1000000000) (-2608010313 / 1000000000) (Real.log (73681 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (65614237 / 100000000) ≤ -Real.log (1000000 / 1927343) ∧
    -Real.log (1000000 / 1927343) ≤ (656142371 / 1000000000) := by
  have h := checkLog_sound (w := (927343 / 2927343)) (n := 12)
    (lo := (65614237 / 100000000)) (hi := (656142371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1927343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1927343 / 1000000) = 1/(1000000 / 1927343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (65614237 / 100000000) (656142371 / 1000000000) (Real.log (1927343 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1927343 / 1000000) = -Real.log (1000000 / 1927343) := by
    rw [show ((1927343 / 1000000) : ℝ) = ((1000000 / 1927343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2622005539 / 1000000000) ≤ -Real.log (72657 / 1000000) ∧
    -Real.log (72657 / 1000000) ≤ (2622005543 / 1000000000) := by
  have h := checkLog_sound (w := (52343 / 197657)) (n := 12)
    (lo := (542563999 / 1000000000)) (hi := (135641 / 250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72657) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 72657) = 1/(72657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2622005543 / 1000000000) (-2622005539 / 1000000000) (Real.log (72657 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (327250731 / 500000000) ≤ -Real.log (1000000 / 1924183) ∧
    -Real.log (1000000 / 1924183) ≤ (654501463 / 1000000000) := by
  have h := checkLog_sound (w := (924183 / 2924183)) (n := 12)
    (lo := (327250731 / 500000000)) (hi := (654501463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1924183 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1924183 / 1000000) = 1/(1000000 / 1924183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (327250731 / 500000000) (654501463 / 1000000000) (Real.log (1924183 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1924183 / 1000000) = -Real.log (1000000 / 1924183) := by
    rw [show ((1924183 / 1000000) : ℝ) = ((1000000 / 1924183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (515886547 / 200000000) ≤ -Real.log (75817 / 1000000) ∧
    -Real.log (75817 / 1000000) ≤ (2579432739 / 1000000000) := by
  have h := checkLog_sound (w := (49183 / 200817)) (n := 12)
    (lo := (99998239 / 200000000)) (hi := (124997799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 75817) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 75817) = 1/(75817 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2579432739 / 1000000000) (-515886547 / 200000000) (Real.log (75817 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (655073489 / 1000000000) ≤ -Real.log (250000 / 481321) ∧
    -Real.log (250000 / 481321) ≤ (65507349 / 100000000) := by
  have h := checkLog_sound (w := (231321 / 731321)) (n := 12)
    (lo := (655073489 / 1000000000)) (hi := (65507349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481321 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481321 / 250000) = 1/(250000 / 481321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (655073489 / 1000000000) (65507349 / 100000000) (Real.log (481321 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (481321 / 250000) = -Real.log (250000 / 481321) := by
    rw [show ((481321 / 250000) : ℝ) = ((250000 / 481321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1297030509 / 500000000) ≤ -Real.log (18679 / 250000) ∧
    -Real.log (18679 / 250000) ≤ (1297030511 / 500000000) := by
  have h := checkLog_sound (w := (12571 / 49929)) (n := 12)
    (lo := (257309739 / 500000000)) (hi := (514619479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18679) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 18679) = 1/(18679 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1297030511 / 500000000) (-1297030509 / 500000000) (Real.log (18679 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (81590531 / 25000000) ≤ -Real.log (20000000000 / 522880796949) ∧
    -Real.log (20000000000 / 522880796949) ≤ (652724249 / 200000000) := by
  have h := checkLog_sound (w := (202880796949 / 842880796949)) (n := 12)
    (lo := (12275813 / 25000000)) (hi := (491032521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((522880796949 / 320000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(522880796949 / 320000000000) = 1/(20000000000 / 522880796949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (81590531 / 25000000) (652724249 / 200000000) (Real.log (522880796949 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (522880796949 / 20000000000) = -Real.log (20000000000 / 522880796949) := by
    rw [show ((522880796949 / 20000000000) : ℝ) = ((20000000000 / 522880796949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3278147909 / 1000000000) ≤ -Real.log (250000000000 / 6631649393727) ∧
    -Real.log (250000000000 / 6631649393727) ≤ (1639073957 / 500000000) := by
  have h := checkLog_sound (w := (2631649393727 / 10631649393727)) (n := 12)
    (lo := (505559189 / 1000000000)) (hi := (50555919 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6631649393727 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6631649393727 / 4000000000000) = 1/(250000000000 / 6631649393727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3278147909 / 1000000000) (1639073957 / 500000000) (Real.log (6631649393727 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (6631649393727 / 250000000000) = -Real.log (250000000000 / 6631649393727) := by
    rw [show ((6631649393727 / 250000000000) : ℝ) = ((250000000000 / 6631649393727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (808483549 / 250000000) ≤ -Real.log (250000000000 / 6344827017687) ∧
    -Real.log (250000000000 / 6344827017687) ≤ (3233934201 / 1000000000) := by
  have h := checkLog_sound (w := (2344827017687 / 10344827017687)) (n := 12)
    (lo := (115336369 / 250000000)) (hi := (461345477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6344827017687 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6344827017687 / 4000000000000) = 1/(250000000000 / 6344827017687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (808483549 / 250000000) (3233934201 / 1000000000) (Real.log (6344827017687 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6344827017687 / 250000000000) = -Real.log (250000000000 / 6344827017687) := by
    rw [show ((6344827017687 / 250000000000) : ℝ) = ((250000000000 / 6344827017687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1624567253 / 500000000) ≤ -Real.log (500000000000 / 12884014133519) ∧
    -Real.log (500000000000 / 12884014133519) ≤ (3249134511 / 1000000000) := by
  have h := checkLog_sound (w := (4884014133519 / 20884014133519)) (n := 12)
    (lo := (238272893 / 500000000)) (hi := (476545787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12884014133519 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12884014133519 / 8000000000000) = 1/(500000000000 / 12884014133519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1624567253 / 500000000) (3249134511 / 1000000000) (Real.log (12884014133519 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (12884014133519 / 500000000000) = -Real.log (500000000000 / 12884014133519) := by
    rw [show ((12884014133519 / 500000000000) : ℝ) = ((500000000000 / 12884014133519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0161

end


