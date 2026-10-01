-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0206Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0206Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:49:12.782893+00:00
-- url     : https://prove2.me/theorems/6c6f9058-e894-4c1a-9b36-886519eb7e25
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0206Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0207Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0206Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0207Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0208Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0209Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0210Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0211Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0212Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0206Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0207Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0208Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0209Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0210Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0211Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0212Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0206Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0207Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0208Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0209Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0210Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0211Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0212Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0206Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0207Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0208Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0209Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0210Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0211Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0212Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0206Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0206
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

theorem reflection_log_1_neg : (572214659 / 1000000000) ≤ -Real.log (3200 / 5671) ∧
    -Real.log (3200 / 5671) ≤ (28610733 / 50000000) := by
  have h := checkLog_sound (w := (2471 / 8871)) (n := 12)
    (lo := (572214659 / 1000000000)) (hi := (28610733 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5671 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5671 / 3200) = 1/(3200 / 5671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (572214659 / 1000000000) (28610733 / 50000000) (Real.log (5671 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5671 / 3200) = -Real.log (3200 / 5671) := by
    rw [show ((5671 / 3200) : ℝ) = ((3200 / 5671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (295846471 / 200000000) ≤ -Real.log (729 / 3200) ∧
    -Real.log (729 / 3200) ≤ (739616179 / 500000000) := by
  have h := checkLog_sound (w := (71 / 1529)) (n := 12)
    (lo := (18587599 / 200000000)) (hi := (23234499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 729) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 729) = 1/(729 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-739616179 / 500000000) (-295846471 / 200000000) (Real.log (729 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (113771731 / 200000000) ≤ -Real.log (800 / 1413) ∧
    -Real.log (800 / 1413) ≤ (17776833 / 31250000) := by
  have h := checkLog_sound (w := (613 / 2213)) (n := 12)
    (lo := (113771731 / 200000000)) (hi := (17776833 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1413 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1413 / 800) = 1/(800 / 1413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (113771731 / 200000000) (17776833 / 31250000) (Real.log (1413 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1413 / 800) = -Real.log (800 / 1413) := by
    rw [show ((1413 / 800) : ℝ) = ((800 / 1413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1453503109 / 1000000000) ≤ -Real.log (187 / 800) ∧
    -Real.log (187 / 800) ≤ (181687889 / 125000000) := by
  have h := checkLog_sound (w := (13 / 387)) (n := 12)
    (lo := (67208749 / 1000000000)) (hi := (53767 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 187) = 1/(187 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-181687889 / 125000000) (-1453503109 / 1000000000) (Real.log (187 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (434619297 / 1000000000) ≤ -Real.log (1600 / 2471) ∧
    -Real.log (1600 / 2471) ≤ (217309649 / 500000000) := by
  have h := checkLog_sound (w := (871 / 4071)) (n := 12)
    (lo := (434619297 / 1000000000)) (hi := (217309649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2471 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2471 / 1600) = 1/(1600 / 2471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (434619297 / 1000000000) (217309649 / 500000000) (Real.log (2471 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2471 / 1600) = -Real.log (1600 / 2471) := by
    rw [show ((2471 / 1600) : ℝ) = ((1600 / 2471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31443407 / 40000000) ≤ -Real.log (729 / 1600) ∧
    -Real.log (729 / 1600) ≤ (786085177 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 1529)) (n := 12)
    (lo := (18587599 / 200000000)) (hi := (23234499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 729) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 729) = 1/(729 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-786085177 / 1000000000) (-31443407 / 40000000) (Real.log (729 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (106725097 / 250000000) ≤ -Real.log (400 / 613) ∧
    -Real.log (400 / 613) ≤ (426900389 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 1013)) (n := 12)
    (lo := (106725097 / 250000000)) (hi := (426900389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613 / 400) = 1/(400 / 613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (106725097 / 250000000) (426900389 / 1000000000) (Real.log (613 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (613 / 400) = -Real.log (400 / 613) := by
    rw [show ((613 / 400) : ℝ) = ((400 / 613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (760355929 / 1000000000) ≤ -Real.log (187 / 400) ∧
    -Real.log (187 / 400) ≤ (760355931 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 387)) (n := 12)
    (lo := (67208749 / 1000000000)) (hi := (53767 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 187) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 187) = 1/(187 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-760355931 / 1000000000) (-760355929 / 1000000000) (Real.log (187 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (76600147 / 125000000) ≤ -Real.log (500000 / 922797) ∧
    -Real.log (500000 / 922797) ≤ (612801177 / 1000000000) := by
  have h := checkLog_sound (w := (422797 / 1422797)) (n := 12)
    (lo := (76600147 / 125000000)) (hi := (612801177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((922797 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(922797 / 500000) = 1/(500000 / 922797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (76600147 / 125000000) (612801177 / 1000000000) (Real.log (922797 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (922797 / 500000) = -Real.log (500000 / 922797) := by
    rw [show ((922797 / 500000) : ℝ) = ((500000 / 922797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (93408489 / 50000000) ≤ -Real.log (77203 / 500000) ∧
    -Real.log (77203 / 500000) ≤ (1868169783 / 1000000000) := by
  have h := checkLog_sound (w := (47797 / 202203)) (n := 12)
    (lo := (24093771 / 50000000)) (hi := (481875421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 77203) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 77203) = 1/(77203 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1868169783 / 1000000000) (-93408489 / 50000000) (Real.log (77203 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (153588891 / 250000000) ≤ -Real.log (200000 / 369693) ∧
    -Real.log (200000 / 369693) ≤ (122871113 / 200000000) := by
  have h := checkLog_sound (w := (169693 / 569693)) (n := 12)
    (lo := (153588891 / 250000000)) (hi := (122871113 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369693 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369693 / 200000) = 1/(200000 / 369693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (153588891 / 250000000) (122871113 / 200000000) (Real.log (369693 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (369693 / 200000) = -Real.log (200000 / 369693) := by
    rw [show ((369693 / 200000) : ℝ) = ((200000 / 369693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (58966833 / 31250000) ≤ -Real.log (30307 / 200000) ∧
    -Real.log (30307 / 200000) ≤ (1886938659 / 1000000000) := by
  have h := checkLog_sound (w := (19693 / 80307)) (n := 12)
    (lo := (62580537 / 125000000)) (hi := (500644297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30307) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 30307) = 1/(30307 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1886938659 / 1000000000) (-58966833 / 31250000) (Real.log (30307 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (24120189 / 40000000) ≤ -Real.log (500000 / 913801) ∧
    -Real.log (500000 / 913801) ≤ (301502363 / 500000000) := by
  have h := checkLog_sound (w := (413801 / 1413801)) (n := 12)
    (lo := (24120189 / 40000000)) (hi := (301502363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((913801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(913801 / 500000) = 1/(500000 / 913801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (24120189 / 40000000) (301502363 / 500000000) (Real.log (913801 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (913801 / 500000) = -Real.log (500000 / 913801) := by
    rw [show ((913801 / 500000) : ℝ) = ((500000 / 913801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (21974369 / 12500000) ≤ -Real.log (86199 / 500000) ∧
    -Real.log (86199 / 500000) ≤ (1757949523 / 1000000000) := by
  have h := checkLog_sound (w := (38801 / 211199)) (n := 12)
    (lo := (9291379 / 25000000)) (hi := (371655161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86199) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 86199) = 1/(86199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1757949523 / 1000000000) (-21974369 / 12500000) (Real.log (86199 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (302587307 / 500000000) ≤ -Real.log (250000 / 457893) ∧
    -Real.log (250000 / 457893) ≤ (121034923 / 200000000) := by
  have h := checkLog_sound (w := (207893 / 707893)) (n := 12)
    (lo := (302587307 / 500000000)) (hi := (121034923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457893 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457893 / 250000) = 1/(250000 / 457893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (302587307 / 500000000) (121034923 / 200000000) (Real.log (457893 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (457893 / 250000) = -Real.log (250000 / 457893) := by
    rw [show ((457893 / 250000) : ℝ) = ((250000 / 457893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1781246919 / 1000000000) ≤ -Real.log (42107 / 250000) ∧
    -Real.log (42107 / 250000) ≤ (890623461 / 500000000) := by
  have h := checkLog_sound (w := (20393 / 104607)) (n := 12)
    (lo := (394952559 / 1000000000)) (hi := (4936907 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42107) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 42107) = 1/(42107 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-890623461 / 500000000) (-1781246919 / 1000000000) (Real.log (42107 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2480970957 / 1000000000) ≤ -Real.log (250000000000 / 2988216131497) ∧
    -Real.log (250000000000 / 2988216131497) ≤ (2480970961 / 1000000000) := by
  have h := checkLog_sound (w := (988216131497 / 4988216131497)) (n := 12)
    (lo := (401529417 / 1000000000)) (hi := (200764709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2988216131497 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2988216131497 / 2000000000000) = 1/(250000000000 / 2988216131497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2480970957 / 1000000000) (2480970961 / 1000000000) (Real.log (2988216131497 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2988216131497 / 250000000000) = -Real.log (250000000000 / 2988216131497) := by
    rw [show ((2988216131497 / 250000000000) : ℝ) = ((250000000000 / 2988216131497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (125064711 / 50000000) ≤ -Real.log (15625000000 / 190597984789) ∧
    -Real.log (15625000000 / 190597984789) ≤ (156330889 / 62500000) := by
  have h := checkLog_sound (w := (65597984789 / 315597984789)) (n := 12)
    (lo := (10546317 / 25000000)) (hi := (421852681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190597984789 / 125000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(190597984789 / 125000000000) = 1/(15625000000 / 190597984789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (125064711 / 50000000) (156330889 / 62500000) (Real.log (190597984789 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (190597984789 / 15625000000) = -Real.log (15625000000 / 190597984789) := by
    rw [show ((190597984789 / 15625000000) : ℝ) = ((15625000000 / 190597984789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (472190849 / 200000000) ≤ -Real.log (500000000000 / 5300531328669) ∧
    -Real.log (500000000000 / 5300531328669) ≤ (2360954249 / 1000000000) := by
  have h := checkLog_sound (w := (1300531328669 / 9300531328669)) (n := 12)
    (lo := (56302541 / 200000000)) (hi := (140756353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5300531328669 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5300531328669 / 4000000000000) = 1/(500000000000 / 5300531328669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (472190849 / 200000000) (2360954249 / 1000000000) (Real.log (5300531328669 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5300531328669 / 500000000000) = -Real.log (500000000000 / 5300531328669) := by
    rw [show ((5300531328669 / 500000000000) : ℝ) = ((500000000000 / 5300531328669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2386421533 / 1000000000) ≤ -Real.log (125000000000 / 1359313772057) ∧
    -Real.log (125000000000 / 1359313772057) ≤ (2386421537 / 1000000000) := by
  have h := checkLog_sound (w := (359313772057 / 2359313772057)) (n := 12)
    (lo := (306979993 / 1000000000)) (hi := (153489997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359313772057 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1359313772057 / 1000000000000) = 1/(125000000000 / 1359313772057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2386421533 / 1000000000) (2386421537 / 1000000000) (Real.log (1359313772057 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1359313772057 / 125000000000) = -Real.log (125000000000 / 1359313772057) := by
    rw [show ((1359313772057 / 125000000000) : ℝ) = ((125000000000 / 1359313772057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0206

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0207Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0207
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

theorem reflection_log_1_neg : (113771731 / 200000000) ≤ -Real.log (800 / 1413) ∧
    -Real.log (800 / 1413) ≤ (17776833 / 31250000) := by
  have h := checkLog_sound (w := (613 / 2213)) (n := 12)
    (lo := (113771731 / 200000000)) (hi := (17776833 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1413 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1413 / 800) = 1/(800 / 1413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (113771731 / 200000000) (17776833 / 31250000) (Real.log (1413 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1413 / 800) = -Real.log (800 / 1413) := by
    rw [show ((1413 / 800) : ℝ) = ((800 / 1413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1453503109 / 1000000000) ≤ -Real.log (187 / 800) ∧
    -Real.log (187 / 800) ≤ (181687889 / 125000000) := by
  have h := checkLog_sound (w := (13 / 387)) (n := 12)
    (lo := (67208749 / 1000000000)) (hi := (53767 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 187) = 1/(187 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-181687889 / 125000000) (-1453503109 / 1000000000) (Real.log (187 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11309827 / 20000000) ≤ -Real.log (3200 / 5633) ∧
    -Real.log (3200 / 5633) ≤ (565491351 / 1000000000) := by
  have h := checkLog_sound (w := (2433 / 8833)) (n := 12)
    (lo := (11309827 / 20000000)) (hi := (565491351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5633 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5633 / 3200) = 1/(3200 / 5633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11309827 / 20000000) (565491351 / 1000000000) (Real.log (5633 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5633 / 3200) = -Real.log (3200 / 5633) := by
    rw [show ((5633 / 3200) : ℝ) = ((3200 / 5633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (714209643 / 500000000) ≤ -Real.log (767 / 3200) ∧
    -Real.log (767 / 3200) ≤ (1428419289 / 1000000000) := by
  have h := checkLog_sound (w := (33 / 1567)) (n := 12)
    (lo := (21062463 / 500000000)) (hi := (42124927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 767) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 767) = 1/(767 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1428419289 / 1000000000) (-714209643 / 500000000) (Real.log (767 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (106725097 / 250000000) ≤ -Real.log (400 / 613) ∧
    -Real.log (400 / 613) ≤ (426900389 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 1013)) (n := 12)
    (lo := (106725097 / 250000000)) (hi := (426900389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613 / 400) = 1/(400 / 613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (106725097 / 250000000) (426900389 / 1000000000) (Real.log (613 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613 / 400) = -Real.log (400 / 613) := by
    rw [show ((613 / 400) : ℝ) = ((400 / 613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (760355929 / 1000000000) ≤ -Real.log (187 / 400) ∧
    -Real.log (187 / 400) ≤ (760355931 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 387)) (n := 12)
    (lo := (67208749 / 1000000000)) (hi := (53767 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 187) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 187) = 1/(187 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-760355931 / 1000000000) (-760355929 / 1000000000) (Real.log (187 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (209560717 / 500000000) ≤ -Real.log (1600 / 2433) ∧
    -Real.log (1600 / 2433) ≤ (83824287 / 200000000) := by
  have h := checkLog_sound (w := (833 / 4033)) (n := 12)
    (lo := (209560717 / 500000000)) (hi := (83824287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2433 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2433 / 1600) = 1/(1600 / 2433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (209560717 / 500000000) (83824287 / 200000000) (Real.log (2433 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2433 / 1600) = -Real.log (1600 / 2433) := by
    rw [show ((2433 / 1600) : ℝ) = ((1600 / 2433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (367636053 / 500000000) ≤ -Real.log (767 / 1600) ∧
    -Real.log (767 / 1600) ≤ (183818027 / 250000000) := by
  have h := checkLog_sound (w := (33 / 1567)) (n := 12)
    (lo := (21062463 / 500000000)) (hi := (42124927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 767) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 767) = 1/(767 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-183818027 / 250000000) (-367636053 / 500000000) (Real.log (767 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (611275843 / 1000000000) ≤ -Real.log (1000000 / 1842781) ∧
    -Real.log (1000000 / 1842781) ≤ (152818961 / 250000000) := by
  have h := checkLog_sound (w := (842781 / 2842781)) (n := 12)
    (lo := (611275843 / 1000000000)) (hi := (152818961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1842781 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1842781 / 1000000) = 1/(1000000 / 1842781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (611275843 / 1000000000) (152818961 / 250000000) (Real.log (1842781 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1842781 / 1000000) = -Real.log (1000000 / 1842781) := by
    rw [show ((1842781 / 1000000) : ℝ) = ((1000000 / 1842781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (92505777 / 50000000) ≤ -Real.log (157219 / 1000000) ∧
    -Real.log (157219 / 1000000) ≤ (1850115543 / 1000000000) := by
  have h := checkLog_sound (w := (92781 / 407219)) (n := 12)
    (lo := (23191059 / 50000000)) (hi := (463821181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 157219) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 157219) = 1/(157219 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1850115543 / 1000000000) (-92505777 / 50000000) (Real.log (157219 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (306400859 / 500000000) ≤ -Real.log (200000 / 369119) ∧
    -Real.log (200000 / 369119) ≤ (612801719 / 1000000000) := by
  have h := checkLog_sound (w := (169119 / 569119)) (n := 12)
    (lo := (306400859 / 500000000)) (hi := (612801719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369119 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369119 / 200000) = 1/(200000 / 369119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (306400859 / 500000000) (612801719 / 1000000000) (Real.log (369119 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (369119 / 200000) = -Real.log (200000 / 369119) := by
    rw [show ((369119 / 200000) : ℝ) = ((200000 / 369119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1868176257 / 1000000000) ≤ -Real.log (30881 / 200000) ∧
    -Real.log (30881 / 200000) ≤ (93408813 / 50000000) := by
  have h := checkLog_sound (w := (19119 / 80881)) (n := 12)
    (lo := (481881897 / 1000000000)) (hi := (240940949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30881) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 30881) = 1/(30881 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-93408813 / 50000000) (-1868176257 / 1000000000) (Real.log (30881 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (300419171 / 500000000) ≤ -Real.log (1000000 / 1823647) ∧
    -Real.log (1000000 / 1823647) ≤ (600838343 / 1000000000) := by
  have h := checkLog_sound (w := (823647 / 2823647)) (n := 12)
    (lo := (300419171 / 500000000)) (hi := (600838343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1823647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1823647 / 1000000) = 1/(1000000 / 1823647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (300419171 / 500000000) (600838343 / 1000000000) (Real.log (1823647 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1823647 / 1000000) = -Real.log (1000000 / 1823647) := by
    rw [show ((1823647 / 1000000) : ℝ) = ((1000000 / 1823647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1735267609 / 1000000000) ≤ -Real.log (176353 / 1000000) ∧
    -Real.log (176353 / 1000000) ≤ (433816903 / 250000000) := by
  have h := checkLog_sound (w := (73647 / 426353)) (n := 12)
    (lo := (348973249 / 1000000000)) (hi := (1395893 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176353) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 176353) = 1/(176353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-433816903 / 250000000) (-1735267609 / 1000000000) (Real.log (176353 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (75375659 / 125000000) ≤ -Real.log (1000000 / 1827603) ∧
    -Real.log (1000000 / 1827603) ≤ (603005273 / 1000000000) := by
  have h := checkLog_sound (w := (827603 / 2827603)) (n := 12)
    (lo := (75375659 / 125000000)) (hi := (603005273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1827603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1827603 / 1000000) = 1/(1000000 / 1827603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (75375659 / 125000000) (603005273 / 1000000000) (Real.log (1827603 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1827603 / 1000000) = -Real.log (1000000 / 1827603) := by
    rw [show ((1827603 / 1000000) : ℝ) = ((1000000 / 1827603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1757955321 / 1000000000) ≤ -Real.log (172397 / 1000000) ∧
    -Real.log (172397 / 1000000) ≤ (439488831 / 250000000) := by
  have h := checkLog_sound (w := (77603 / 422397)) (n := 12)
    (lo := (371660961 / 1000000000)) (hi := (185830481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172397) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 172397) = 1/(172397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-439488831 / 250000000) (-1757955321 / 1000000000) (Real.log (172397 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2461391383 / 1000000000) ≤ -Real.log (195312500 / 2289279057) ∧
    -Real.log (195312500 / 2289279057) ≤ (2461391387 / 1000000000) := by
  have h := checkLog_sound (w := (726779057 / 3851779057)) (n := 12)
    (lo := (381949843 / 1000000000)) (hi := (95487461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2289279057 / 1562500000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2289279057 / 1562500000) = 1/(195312500 / 2289279057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2461391383 / 1000000000) (2461391387 / 1000000000) (Real.log (2289279057 / 195312500)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2289279057 / 195312500) = -Real.log (195312500 / 2289279057) := by
    rw [show ((2289279057 / 195312500) : ℝ) = ((195312500 / 2289279057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (99239119 / 40000000) ≤ -Real.log (250000000000 / 2988237103721) ∧
    -Real.log (250000000000 / 2988237103721) ≤ (2480977979 / 1000000000) := by
  have h := checkLog_sound (w := (988237103721 / 4988237103721)) (n := 12)
    (lo := (80307287 / 200000000)) (hi := (100384109 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2988237103721 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2988237103721 / 2000000000000) = 1/(250000000000 / 2988237103721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (99239119 / 40000000) (2480977979 / 1000000000) (Real.log (2988237103721 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2988237103721 / 250000000000) = -Real.log (250000000000 / 2988237103721) := by
    rw [show ((2988237103721 / 250000000000) : ℝ) = ((250000000000 / 2988237103721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2336105951 / 1000000000) ≤ -Real.log (500000000000 / 5170445073233) ∧
    -Real.log (500000000000 / 5170445073233) ≤ (467221191 / 200000000) := by
  have h := checkLog_sound (w := (1170445073233 / 9170445073233)) (n := 12)
    (lo := (256664411 / 1000000000)) (hi := (64166103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5170445073233 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5170445073233 / 4000000000000) = 1/(500000000000 / 5170445073233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2336105951 / 1000000000) (467221191 / 200000000) (Real.log (5170445073233 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5170445073233 / 500000000000) = -Real.log (500000000000 / 5170445073233) := by
    rw [show ((5170445073233 / 500000000000) : ℝ) = ((500000000000 / 5170445073233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (147560037 / 62500000) ≤ -Real.log (500000000000 / 5300564975029) ∧
    -Real.log (500000000000 / 5300564975029) ≤ (590240149 / 250000000) := by
  have h := checkLog_sound (w := (1300564975029 / 9300564975029)) (n := 12)
    (lo := (70379763 / 250000000)) (hi := (281519053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5300564975029 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5300564975029 / 4000000000000) = 1/(500000000000 / 5300564975029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (147560037 / 62500000) (590240149 / 250000000) (Real.log (5300564975029 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5300564975029 / 500000000000) = -Real.log (500000000000 / 5300564975029) := by
    rw [show ((5300564975029 / 500000000000) : ℝ) = ((500000000000 / 5300564975029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0207

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0208Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0208
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

theorem reflection_log_1_neg : (11309827 / 20000000) ≤ -Real.log (3200 / 5633) ∧
    -Real.log (3200 / 5633) ≤ (565491351 / 1000000000) := by
  have h := checkLog_sound (w := (2433 / 8833)) (n := 12)
    (lo := (11309827 / 20000000)) (hi := (565491351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5633 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5633 / 3200) = 1/(3200 / 5633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11309827 / 20000000) (565491351 / 1000000000) (Real.log (5633 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5633 / 3200) = -Real.log (3200 / 5633) := by
    rw [show ((5633 / 3200) : ℝ) = ((3200 / 5633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (714209643 / 500000000) ≤ -Real.log (767 / 3200) ∧
    -Real.log (767 / 3200) ≤ (1428419289 / 1000000000) := by
  have h := checkLog_sound (w := (33 / 1567)) (n := 12)
    (lo := (21062463 / 500000000)) (hi := (42124927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 767) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 767) = 1/(767 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1428419289 / 1000000000) (-714209643 / 500000000) (Real.log (767 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (140528167 / 250000000) ≤ -Real.log (1600 / 2807) ∧
    -Real.log (1600 / 2807) ≤ (562112669 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 4407)) (n := 12)
    (lo := (140528167 / 250000000)) (hi := (562112669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2807 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2807 / 1600) = 1/(1600 / 2807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (140528167 / 250000000) (562112669 / 1000000000) (Real.log (2807 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2807 / 1600) = -Real.log (1600 / 2807) := by
    rw [show ((2807 / 1600) : ℝ) = ((1600 / 2807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (280789859 / 200000000) ≤ -Real.log (393 / 1600) ∧
    -Real.log (393 / 1600) ≤ (701974649 / 500000000) := by
  have h := checkLog_sound (w := (7 / 793)) (n := 12)
    (lo := (3530987 / 200000000)) (hi := (2206867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 393) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 393) = 1/(393 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-701974649 / 500000000) (-280789859 / 200000000) (Real.log (393 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (209560717 / 500000000) ≤ -Real.log (1600 / 2433) ∧
    -Real.log (1600 / 2433) ≤ (83824287 / 200000000) := by
  have h := checkLog_sound (w := (833 / 4033)) (n := 12)
    (lo := (209560717 / 500000000)) (hi := (83824287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2433 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2433 / 1600) = 1/(1600 / 2433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (209560717 / 500000000) (83824287 / 200000000) (Real.log (2433 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2433 / 1600) = -Real.log (1600 / 2433) := by
    rw [show ((2433 / 1600) : ℝ) = ((1600 / 2433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (367636053 / 500000000) ≤ -Real.log (767 / 1600) ∧
    -Real.log (767 / 1600) ≤ (183818027 / 250000000) := by
  have h := checkLog_sound (w := (33 / 1567)) (n := 12)
    (lo := (21062463 / 500000000)) (hi := (42124927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 767) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 767) = 1/(767 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-183818027 / 250000000) (-367636053 / 500000000) (Real.log (767 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (411281493 / 1000000000) ≤ -Real.log (800 / 1207) ∧
    -Real.log (800 / 1207) ≤ (205640747 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2007)) (n := 12)
    (lo := (411281493 / 1000000000)) (hi := (205640747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207 / 800) = 1/(800 / 1207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (411281493 / 1000000000) (205640747 / 500000000) (Real.log (1207 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1207 / 800) = -Real.log (800 / 1207) := by
    rw [show ((1207 / 800) : ℝ) = ((800 / 1207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (142160423 / 200000000) ≤ -Real.log (393 / 800) ∧
    -Real.log (393 / 800) ≤ (710802117 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 793)) (n := 12)
    (lo := (3530987 / 200000000)) (hi := (2206867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 393) = 1/(393 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-710802117 / 1000000000) (-142160423 / 200000000) (Real.log (393 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (304889579 / 500000000) ≤ -Real.log (40000 / 73601) ∧
    -Real.log (40000 / 73601) ≤ (609779159 / 1000000000) := by
  have h := checkLog_sound (w := (33601 / 113601)) (n := 12)
    (lo := (304889579 / 500000000)) (hi := (609779159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73601 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73601 / 40000) = 1/(40000 / 73601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (304889579 / 500000000) (609779159 / 1000000000) (Real.log (73601 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (73601 / 40000) = -Real.log (40000 / 73601) := by
    rw [show ((73601 / 40000) : ℝ) = ((40000 / 73601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (458184431 / 250000000) ≤ -Real.log (6399 / 40000) ∧
    -Real.log (6399 / 40000) ≤ (1832737727 / 1000000000) := by
  have h := checkLog_sound (w := (3601 / 16399)) (n := 12)
    (lo := (111610841 / 250000000)) (hi := (89288673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 6399) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(10000 / 6399) = 1/(6399 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1832737727 / 1000000000) (-458184431 / 250000000) (Real.log (6399 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (305638193 / 500000000) ≤ -Real.log (500000 / 921391) ∧
    -Real.log (500000 / 921391) ≤ (611276387 / 1000000000) := by
  have h := checkLog_sound (w := (421391 / 1421391)) (n := 12)
    (lo := (305638193 / 500000000)) (hi := (611276387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921391 / 500000) = 1/(500000 / 921391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (305638193 / 500000000) (611276387 / 1000000000) (Real.log (921391 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (921391 / 500000) = -Real.log (500000 / 921391) := by
    rw [show ((921391 / 500000) : ℝ) = ((500000 / 921391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18501219 / 10000000) ≤ -Real.log (78609 / 500000) ∧
    -Real.log (78609 / 500000) ≤ (1850121903 / 1000000000) := by
  have h := checkLog_sound (w := (46391 / 203609)) (n := 12)
    (lo := (23191377 / 50000000)) (hi := (463827541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 78609) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 78609) = 1/(78609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1850121903 / 1000000000) (-18501219 / 10000000) (Real.log (78609 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (748343 / 1250000) ≤ -Real.log (200000 / 363941) ∧
    -Real.log (200000 / 363941) ≤ (598674401 / 1000000000) := by
  have h := checkLog_sound (w := (163941 / 563941)) (n := 12)
    (lo := (748343 / 1250000)) (hi := (598674401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363941 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363941 / 200000) = 1/(200000 / 363941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (748343 / 1250000) (598674401 / 1000000000) (Real.log (363941 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (363941 / 200000) = -Real.log (200000 / 363941) := by
    rw [show ((363941 / 200000) : ℝ) = ((200000 / 363941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1713160879 / 1000000000) ≤ -Real.log (36059 / 200000) ∧
    -Real.log (36059 / 200000) ≤ (856580441 / 500000000) := by
  have h := checkLog_sound (w := (13941 / 86059)) (n := 12)
    (lo := (326866519 / 1000000000)) (hi := (8171663 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36059) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 36059) = 1/(36059 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-856580441 / 500000000) (-1713160879 / 1000000000) (Real.log (36059 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (60083889 / 100000000) ≤ -Real.log (31250 / 56989) ∧
    -Real.log (31250 / 56989) ≤ (600838891 / 1000000000) := by
  have h := checkLog_sound (w := (25739 / 88239)) (n := 12)
    (lo := (60083889 / 100000000)) (hi := (600838891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56989 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56989 / 31250) = 1/(31250 / 56989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (60083889 / 100000000) (600838891 / 1000000000) (Real.log (56989 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (56989 / 31250) = -Real.log (31250 / 56989) := by
    rw [show ((56989 / 31250) : ℝ) = ((31250 / 56989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (5422729 / 3125000) ≤ -Real.log (5511 / 31250) ∧
    -Real.log (5511 / 31250) ≤ (1735273283 / 1000000000) := by
  have h := checkLog_sound (w := (4603 / 26647)) (n := 12)
    (lo := (8724473 / 25000000)) (hi := (348978921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11022) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 11022) = 1/(5511 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1735273283 / 1000000000) (-5422729 / 3125000) (Real.log (5511 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1221258441 / 500000000) ≤ -Real.log (500000000000 / 5750976715111) ∧
    -Real.log (500000000000 / 5750976715111) ≤ (1221258443 / 500000000) := by
  have h := checkLog_sound (w := (1750976715111 / 9750976715111)) (n := 12)
    (lo := (181537671 / 500000000)) (hi := (363075343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5750976715111 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5750976715111 / 4000000000000) = 1/(500000000000 / 5750976715111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1221258441 / 500000000) (1221258443 / 500000000) (Real.log (5750976715111 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5750976715111 / 500000000000) = -Real.log (500000000000 / 5750976715111) := by
    rw [show ((5750976715111 / 500000000000) : ℝ) = ((500000000000 / 5750976715111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1230699143 / 500000000) ≤ -Real.log (50000000000 / 586059484283) ∧
    -Real.log (50000000000 / 586059484283) ≤ (246139829 / 100000000) := by
  have h := checkLog_sound (w := (186059484283 / 986059484283)) (n := 12)
    (lo := (190978373 / 500000000)) (hi := (381956747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586059484283 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(586059484283 / 400000000000) = 1/(50000000000 / 586059484283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1230699143 / 500000000) (246139829 / 100000000) (Real.log (586059484283 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (586059484283 / 50000000000) = -Real.log (50000000000 / 586059484283) := by
    rw [show ((586059484283 / 50000000000) : ℝ) = ((50000000000 / 586059484283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2311835279 / 1000000000) ≤ -Real.log (10000000000 / 100929310297) ∧
    -Real.log (10000000000 / 100929310297) ≤ (2311835283 / 1000000000) := by
  have h := checkLog_sound (w := (20929310297 / 180929310297)) (n := 12)
    (lo := (232393739 / 1000000000)) (hi := (11619687 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100929310297 / 80000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100929310297 / 80000000000) = 1/(10000000000 / 100929310297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2311835279 / 1000000000) (2311835283 / 1000000000) (Real.log (100929310297 / 10000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (100929310297 / 10000000000) = -Real.log (10000000000 / 100929310297) := by
    rw [show ((100929310297 / 10000000000) : ℝ) = ((10000000000 / 100929310297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (233611217 / 100000000) ≤ -Real.log (125000000000 / 1292619306841) ∧
    -Real.log (125000000000 / 1292619306841) ≤ (1168056087 / 500000000) := by
  have h := checkLog_sound (w := (292619306841 / 2292619306841)) (n := 12)
    (lo := (25667063 / 100000000)) (hi := (256670631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292619306841 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1292619306841 / 1000000000000) = 1/(125000000000 / 1292619306841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (233611217 / 100000000) (1168056087 / 500000000) (Real.log (1292619306841 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1292619306841 / 125000000000) = -Real.log (125000000000 / 1292619306841) := by
    rw [show ((1292619306841 / 125000000000) : ℝ) = ((125000000000 / 1292619306841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0208

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0209Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0209
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

theorem reflection_log_1_neg : (140528167 / 250000000) ≤ -Real.log (1600 / 2807) ∧
    -Real.log (1600 / 2807) ≤ (562112669 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 4407)) (n := 12)
    (lo := (140528167 / 250000000)) (hi := (562112669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2807 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2807 / 1600) = 1/(1600 / 2807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (140528167 / 250000000) (562112669 / 1000000000) (Real.log (2807 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2807 / 1600) = -Real.log (1600 / 2807) := by
    rw [show ((2807 / 1600) : ℝ) = ((1600 / 2807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (280789859 / 200000000) ≤ -Real.log (393 / 1600) ∧
    -Real.log (393 / 1600) ≤ (701974649 / 500000000) := by
  have h := checkLog_sound (w := (7 / 793)) (n := 12)
    (lo := (3530987 / 200000000)) (hi := (2206867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 393) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 393) = 1/(393 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-701974649 / 500000000) (-280789859 / 200000000) (Real.log (393 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (558722531 / 1000000000) ≤ -Real.log (640 / 1119) ∧
    -Real.log (640 / 1119) ≤ (139680633 / 250000000) := by
  have h := checkLog_sound (w := (479 / 1759)) (n := 12)
    (lo := (558722531 / 1000000000)) (hi := (139680633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1119 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1119 / 640) = 1/(640 / 1119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (558722531 / 1000000000) (139680633 / 250000000) (Real.log (1119 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1119 / 640) = -Real.log (640 / 1119) := by
    rw [show ((1119 / 640) : ℝ) = ((640 / 1119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (138006381 / 100000000) ≤ -Real.log (161 / 640) ∧
    -Real.log (161 / 640) ≤ (345015953 / 250000000) := by
  have h := checkLog_sound (w := (159 / 481)) (n := 12)
    (lo := (68691663 / 100000000)) (hi := (686916631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 161) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 161) = 1/(161 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-345015953 / 250000000) (-138006381 / 100000000) (Real.log (161 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (411281493 / 1000000000) ≤ -Real.log (800 / 1207) ∧
    -Real.log (800 / 1207) ≤ (205640747 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2007)) (n := 12)
    (lo := (411281493 / 1000000000)) (hi := (205640747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207 / 800) = 1/(800 / 1207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (411281493 / 1000000000) (205640747 / 500000000) (Real.log (1207 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1207 / 800) = -Real.log (800 / 1207) := by
    rw [show ((1207 / 800) : ℝ) = ((800 / 1207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (142160423 / 200000000) ≤ -Real.log (393 / 800) ∧
    -Real.log (393 / 800) ≤ (710802117 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 793)) (n := 12)
    (lo := (3530987 / 200000000)) (hi := (2206867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 393) = 1/(393 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-710802117 / 1000000000) (-142160423 / 200000000) (Real.log (393 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (403379601 / 1000000000) ≤ -Real.log (320 / 479) ∧
    -Real.log (320 / 479) ≤ (201689801 / 500000000) := by
  have h := checkLog_sound (w := (159 / 799)) (n := 12)
    (lo := (403379601 / 1000000000)) (hi := (201689801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479 / 320) = 1/(320 / 479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (403379601 / 1000000000) (201689801 / 500000000) (Real.log (479 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (479 / 320) = -Real.log (320 / 479) := by
    rw [show ((479 / 320) : ℝ) = ((320 / 479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (68691663 / 100000000) ≤ -Real.log (161 / 320) ∧
    -Real.log (161 / 320) ≤ (686916631 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 481)) (n := 12)
    (lo := (68691663 / 100000000)) (hi := (686916631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 161) = 1/(161 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-686916631 / 1000000000) (-68691663 / 100000000) (Real.log (161 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (608311253 / 1000000000) ≤ -Real.log (500000 / 918663) ∧
    -Real.log (500000 / 918663) ≤ (304155627 / 500000000) := by
  have h := checkLog_sound (w := (418663 / 1418663)) (n := 12)
    (lo := (608311253 / 1000000000)) (hi := (304155627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918663 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918663 / 500000) = 1/(500000 / 918663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (608311253 / 1000000000) (304155627 / 500000000) (Real.log (918663 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (918663 / 500000) = -Real.log (500000 / 918663) := by
    rw [show ((918663 / 500000) : ℝ) = ((500000 / 918663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1816007079 / 1000000000) ≤ -Real.log (81337 / 500000) ∧
    -Real.log (81337 / 500000) ≤ (908003541 / 500000000) := by
  have h := checkLog_sound (w := (43663 / 206337)) (n := 12)
    (lo := (429712719 / 1000000000)) (hi := (5371409 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81337) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 81337) = 1/(81337 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-908003541 / 500000000) (-1816007079 / 1000000000) (Real.log (81337 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (609779701 / 1000000000) ≤ -Real.log (500000 / 920013) ∧
    -Real.log (500000 / 920013) ≤ (304889851 / 500000000) := by
  have h := checkLog_sound (w := (420013 / 1420013)) (n := 12)
    (lo := (609779701 / 1000000000)) (hi := (304889851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((920013 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(920013 / 500000) = 1/(500000 / 920013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (609779701 / 1000000000) (304889851 / 500000000) (Real.log (920013 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (920013 / 500000) = -Real.log (500000 / 920013) := by
    rw [show ((920013 / 500000) : ℝ) = ((500000 / 920013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (73309759 / 40000000) ≤ -Real.log (79987 / 500000) ∧
    -Real.log (79987 / 500000) ≤ (916371989 / 500000000) := by
  have h := checkLog_sound (w := (45013 / 204987)) (n := 12)
    (lo := (89289923 / 200000000)) (hi := (27903101 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 79987) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 79987) = 1/(79987 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-916371989 / 500000000) (-73309759 / 40000000) (Real.log (79987 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (149128231 / 250000000) ≤ -Real.log (31250 / 56743) ∧
    -Real.log (31250 / 56743) ≤ (23860517 / 40000000) := by
  have h := checkLog_sound (w := (25493 / 87993)) (n := 12)
    (lo := (149128231 / 250000000)) (hi := (23860517 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56743 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56743 / 31250) = 1/(31250 / 56743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (149128231 / 250000000) (23860517 / 40000000) (Real.log (56743 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (56743 / 31250) = -Real.log (31250 / 56743) := by
    rw [show ((56743 / 31250) : ℝ) = ((31250 / 56743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1691602869 / 1000000000) ≤ -Real.log (5757 / 31250) ∧
    -Real.log (5757 / 31250) ≤ (211450359 / 125000000) := by
  have h := checkLog_sound (w := (4111 / 27139)) (n := 12)
    (lo := (305308509 / 1000000000)) (hi := (30530851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11514) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 11514) = 1/(5757 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-211450359 / 125000000) (-1691602869 / 1000000000) (Real.log (5757 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (598674949 / 1000000000) ≤ -Real.log (500000 / 909853) ∧
    -Real.log (500000 / 909853) ≤ (11973499 / 20000000) := by
  have h := checkLog_sound (w := (409853 / 1409853)) (n := 12)
    (lo := (598674949 / 1000000000)) (hi := (11973499 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909853 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909853 / 500000) = 1/(500000 / 909853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (598674949 / 1000000000) (11973499 / 20000000) (Real.log (909853 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (909853 / 500000) = -Real.log (500000 / 909853) := by
    rw [show ((909853 / 500000) : ℝ) = ((500000 / 909853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (856583213 / 500000000) ≤ -Real.log (90147 / 500000) ∧
    -Real.log (90147 / 500000) ≤ (1713166429 / 1000000000) := by
  have h := checkLog_sound (w := (34853 / 215147)) (n := 12)
    (lo := (163436033 / 500000000)) (hi := (326872067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90147) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 90147) = 1/(90147 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1713166429 / 1000000000) (-856583213 / 500000000) (Real.log (90147 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (606079583 / 250000000) ≤ -Real.log (500000000000 / 5647263852859) ∧
    -Real.log (500000000000 / 5647263852859) ≤ (18939987 / 7812500) := by
  have h := checkLog_sound (w := (1647263852859 / 9647263852859)) (n := 12)
    (lo := (43109599 / 125000000)) (hi := (344876793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5647263852859 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5647263852859 / 4000000000000) = 1/(500000000000 / 5647263852859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (606079583 / 250000000) (18939987 / 7812500) (Real.log (5647263852859 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5647263852859 / 500000000000) = -Real.log (500000000000 / 5647263852859) := by
    rw [show ((5647263852859 / 500000000000) : ℝ) = ((500000000000 / 5647263852859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2442523677 / 1000000000) ≤ -Real.log (250000000000 / 2875507895033) ∧
    -Real.log (250000000000 / 2875507895033) ≤ (2442523681 / 1000000000) := by
  have h := checkLog_sound (w := (875507895033 / 4875507895033)) (n := 12)
    (lo := (363082137 / 1000000000)) (hi := (181541069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2875507895033 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2875507895033 / 2000000000000) = 1/(250000000000 / 2875507895033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2442523677 / 1000000000) (2442523681 / 1000000000) (Real.log (2875507895033 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2875507895033 / 250000000000) = -Real.log (250000000000 / 2875507895033) := by
    rw [show ((2875507895033 / 250000000000) : ℝ) = ((250000000000 / 2875507895033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2288115793 / 1000000000) ≤ -Real.log (500000000000 / 4928174396387) ∧
    -Real.log (500000000000 / 4928174396387) ≤ (2288115797 / 1000000000) := by
  have h := checkLog_sound (w := (928174396387 / 8928174396387)) (n := 12)
    (lo := (208674253 / 1000000000)) (hi := (104337127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4928174396387 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4928174396387 / 4000000000000) = 1/(500000000000 / 4928174396387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2288115793 / 1000000000) (2288115797 / 1000000000) (Real.log (4928174396387 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4928174396387 / 500000000000) = -Real.log (500000000000 / 4928174396387) := by
    rw [show ((4928174396387 / 500000000000) : ℝ) = ((500000000000 / 4928174396387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (18494731 / 8000000) ≤ -Real.log (500000000000 / 5046496278301) ∧
    -Real.log (500000000000 / 5046496278301) ≤ (2311841379 / 1000000000) := by
  have h := checkLog_sound (w := (1046496278301 / 9046496278301)) (n := 12)
    (lo := (46479967 / 200000000)) (hi := (58099959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5046496278301 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5046496278301 / 4000000000000) = 1/(500000000000 / 5046496278301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (18494731 / 8000000) (2311841379 / 1000000000) (Real.log (5046496278301 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5046496278301 / 500000000000) = -Real.log (500000000000 / 5046496278301) := by
    rw [show ((5046496278301 / 500000000000) : ℝ) = ((500000000000 / 5046496278301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0209

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0210Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0210
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

theorem reflection_log_1_neg : (558722531 / 1000000000) ≤ -Real.log (640 / 1119) ∧
    -Real.log (640 / 1119) ≤ (139680633 / 250000000) := by
  have h := checkLog_sound (w := (479 / 1759)) (n := 12)
    (lo := (558722531 / 1000000000)) (hi := (139680633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1119 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1119 / 640) = 1/(640 / 1119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (558722531 / 1000000000) (139680633 / 250000000) (Real.log (1119 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1119 / 640) = -Real.log (640 / 1119) := by
    rw [show ((1119 / 640) : ℝ) = ((640 / 1119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (138006381 / 100000000) ≤ -Real.log (161 / 640) ∧
    -Real.log (161 / 640) ≤ (345015953 / 250000000) := by
  have h := checkLog_sound (w := (159 / 481)) (n := 12)
    (lo := (68691663 / 100000000)) (hi := (686916631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 161) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 161) = 1/(161 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-345015953 / 250000000) (-138006381 / 100000000) (Real.log (161 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (555320863 / 1000000000) ≤ -Real.log (400 / 697) ∧
    -Real.log (400 / 697) ≤ (17353777 / 31250000) := by
  have h := checkLog_sound (w := (297 / 1097)) (n := 12)
    (lo := (555320863 / 1000000000)) (hi := (17353777 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697 / 400) = 1/(400 / 697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (555320863 / 1000000000) (17353777 / 31250000) (Real.log (697 / 400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (697 / 400) = -Real.log (400 / 697) := by
    rw [show ((697 / 400) : ℝ) = ((400 / 697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (678367779 / 500000000) ≤ -Real.log (103 / 400) ∧
    -Real.log (103 / 400) ≤ (33918389 / 25000000) := by
  have h := checkLog_sound (w := (97 / 303)) (n := 12)
    (lo := (331794189 / 500000000)) (hi := (663588379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 103) = 1/(103 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33918389 / 25000000) (-678367779 / 500000000) (Real.log (103 / 400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (403379601 / 1000000000) ≤ -Real.log (320 / 479) ∧
    -Real.log (320 / 479) ≤ (201689801 / 500000000) := by
  have h := checkLog_sound (w := (159 / 799)) (n := 12)
    (lo := (403379601 / 1000000000)) (hi := (201689801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479 / 320) = 1/(320 / 479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (403379601 / 1000000000) (201689801 / 500000000) (Real.log (479 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (479 / 320) = -Real.log (320 / 479) := by
    rw [show ((479 / 320) : ℝ) = ((320 / 479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (68691663 / 100000000) ≤ -Real.log (161 / 320) ∧
    -Real.log (161 / 320) ≤ (686916631 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 481)) (n := 12)
    (lo := (68691663 / 100000000)) (hi := (686916631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 161) = 1/(161 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-686916631 / 1000000000) (-68691663 / 100000000) (Real.log (161 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (98853693 / 250000000) ≤ -Real.log (200 / 297) ∧
    -Real.log (200 / 297) ≤ (395414773 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 497)) (n := 12)
    (lo := (98853693 / 250000000)) (hi := (395414773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297 / 200) = 1/(200 / 297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (98853693 / 250000000) (395414773 / 1000000000) (Real.log (297 / 200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (297 / 200) = -Real.log (200 / 297) := by
    rw [show ((297 / 200) : ℝ) = ((200 / 297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (331794189 / 500000000) ≤ -Real.log (103 / 200) ∧
    -Real.log (103 / 200) ≤ (663588379 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 303)) (n := 12)
    (lo := (331794189 / 500000000)) (hi := (663588379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 103) = 1/(103 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-663588379 / 1000000000) (-331794189 / 500000000) (Real.log (103 / 200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (606872259 / 1000000000) ≤ -Real.log (250000 / 458671) ∧
    -Real.log (250000 / 458671) ≤ (30343613 / 50000000) := by
  have h := checkLog_sound (w := (208671 / 708671)) (n := 12)
    (lo := (606872259 / 1000000000)) (hi := (30343613 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((458671 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(458671 / 250000) = 1/(250000 / 458671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (606872259 / 1000000000) (30343613 / 50000000) (Real.log (458671 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (458671 / 250000) = -Real.log (250000 / 458671) := by
    rw [show ((458671 / 250000) : ℝ) = ((250000 / 458671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (449974121 / 250000000) ≤ -Real.log (41329 / 250000) ∧
    -Real.log (41329 / 250000) ≤ (1799896487 / 1000000000) := by
  have h := checkLog_sound (w := (21171 / 103829)) (n := 12)
    (lo := (103400531 / 250000000)) (hi := (3308817 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41329) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 41329) = 1/(41329 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1799896487 / 1000000000) (-449974121 / 250000000) (Real.log (41329 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (304155899 / 500000000) ≤ -Real.log (1000000 / 1837327) ∧
    -Real.log (1000000 / 1837327) ≤ (608311799 / 1000000000) := by
  have h := checkLog_sound (w := (837327 / 2837327)) (n := 12)
    (lo := (304155899 / 500000000)) (hi := (608311799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1837327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1837327 / 1000000) = 1/(1000000 / 1837327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (304155899 / 500000000) (608311799 / 1000000000) (Real.log (1837327 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1837327 / 1000000) = -Real.log (1000000 / 1837327) := by
    rw [show ((1837327 / 1000000) : ℝ) = ((1000000 / 1837327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1816013227 / 1000000000) ≤ -Real.log (162673 / 1000000) ∧
    -Real.log (162673 / 1000000) ≤ (181601323 / 100000000) := by
  have h := checkLog_sound (w := (87327 / 412673)) (n := 12)
    (lo := (429718867 / 1000000000)) (hi := (107429717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 162673) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 162673) = 1/(162673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-181601323 / 100000000) (-1816013227 / 1000000000) (Real.log (162673 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (59435339 / 100000000) ≤ -Real.log (1000000 / 1811859) ∧
    -Real.log (1000000 / 1811859) ≤ (594353391 / 1000000000) := by
  have h := checkLog_sound (w := (811859 / 2811859)) (n := 12)
    (lo := (59435339 / 100000000)) (hi := (594353391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1811859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1811859 / 1000000) = 1/(1000000 / 1811859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (59435339 / 100000000) (594353391 / 1000000000) (Real.log (1811859 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1811859 / 1000000) = -Real.log (1000000 / 1811859) := by
    rw [show ((1811859 / 1000000) : ℝ) = ((1000000 / 1811859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (417640899 / 250000000) ≤ -Real.log (188141 / 1000000) ∧
    -Real.log (188141 / 1000000) ≤ (1670563599 / 1000000000) := by
  have h := checkLog_sound (w := (61859 / 438141)) (n := 12)
    (lo := (71067309 / 250000000)) (hi := (284269237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188141) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 188141) = 1/(188141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1670563599 / 1000000000) (-417640899 / 250000000) (Real.log (188141 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (23860539 / 40000000) ≤ -Real.log (1000000 / 1815777) ∧
    -Real.log (1000000 / 1815777) ≤ (149128369 / 250000000) := by
  have h := checkLog_sound (w := (815777 / 2815777)) (n := 12)
    (lo := (23860539 / 40000000)) (hi := (149128369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1815777 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1815777 / 1000000) = 1/(1000000 / 1815777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (23860539 / 40000000) (149128369 / 250000000) (Real.log (1815777 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1815777 / 1000000) = -Real.log (1000000 / 1815777) := by
    rw [show ((1815777 / 1000000) : ℝ) = ((1000000 / 1815777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1691608297 / 1000000000) ≤ -Real.log (184223 / 1000000) ∧
    -Real.log (184223 / 1000000) ≤ (16916083 / 10000000) := by
  have h := checkLog_sound (w := (65777 / 434223)) (n := 12)
    (lo := (305313937 / 1000000000)) (hi := (152656969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184223) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 184223) = 1/(184223 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-16916083 / 10000000) (-1691608297 / 1000000000) (Real.log (184223 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2406768743 / 1000000000) ≤ -Real.log (250000000000 / 2774510634179) ∧
    -Real.log (250000000000 / 2774510634179) ≤ (2406768747 / 1000000000) := by
  have h := checkLog_sound (w := (774510634179 / 4774510634179)) (n := 12)
    (lo := (327327203 / 1000000000)) (hi := (81831801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2774510634179 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2774510634179 / 2000000000000) = 1/(250000000000 / 2774510634179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2406768743 / 1000000000) (2406768747 / 1000000000) (Real.log (2774510634179 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2774510634179 / 250000000000) = -Real.log (250000000000 / 2774510634179) := by
    rw [show ((2774510634179 / 250000000000) : ℝ) = ((250000000000 / 2774510634179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (75760157 / 31250000) ≤ -Real.log (100000000000 / 1129460328389) ∧
    -Real.log (100000000000 / 1129460328389) ≤ (606081257 / 250000000) := by
  have h := checkLog_sound (w := (329460328389 / 1929460328389)) (n := 12)
    (lo := (86220871 / 250000000)) (hi := (68976697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129460328389 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1129460328389 / 800000000000) = 1/(100000000000 / 1129460328389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (75760157 / 31250000) (606081257 / 250000000) (Real.log (1129460328389 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1129460328389 / 100000000000) = -Real.log (100000000000 / 1129460328389) := by
    rw [show ((1129460328389 / 100000000000) : ℝ) = ((100000000000 / 1129460328389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (452983397 / 200000000) ≤ -Real.log (500000000000 / 4815162564247) ∧
    -Real.log (500000000000 / 4815162564247) ≤ (2264916989 / 1000000000) := by
  have h := checkLog_sound (w := (815162564247 / 8815162564247)) (n := 12)
    (lo := (37095089 / 200000000)) (hi := (92737723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4815162564247 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4815162564247 / 4000000000000) = 1/(500000000000 / 4815162564247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (452983397 / 200000000) (2264916989 / 1000000000) (Real.log (4815162564247 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4815162564247 / 500000000000) = -Real.log (500000000000 / 4815162564247) := by
    rw [show ((4815162564247 / 500000000000) : ℝ) = ((500000000000 / 4815162564247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (572030443 / 250000000) ≤ -Real.log (4000000000 / 39425630893) ∧
    -Real.log (4000000000 / 39425630893) ≤ (143007611 / 62500000) := by
  have h := checkLog_sound (w := (7425630893 / 71425630893)) (n := 12)
    (lo := (26085029 / 125000000)) (hi := (208680233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39425630893 / 32000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(39425630893 / 32000000000) = 1/(4000000000 / 39425630893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (572030443 / 250000000) (143007611 / 62500000) (Real.log (39425630893 / 4000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (39425630893 / 4000000000) = -Real.log (4000000000 / 39425630893) := by
    rw [show ((39425630893 / 4000000000) : ℝ) = ((4000000000 / 39425630893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0210

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0211Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0211
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

theorem reflection_log_1_neg : (555320863 / 1000000000) ≤ -Real.log (400 / 697) ∧
    -Real.log (400 / 697) ≤ (17353777 / 31250000) := by
  have h := checkLog_sound (w := (297 / 1097)) (n := 12)
    (lo := (555320863 / 1000000000)) (hi := (17353777 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697 / 400) = 1/(400 / 697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (555320863 / 1000000000) (17353777 / 31250000) (Real.log (697 / 400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (697 / 400) = -Real.log (400 / 697) := by
    rw [show ((697 / 400) : ℝ) = ((400 / 697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (678367779 / 500000000) ≤ -Real.log (103 / 400) ∧
    -Real.log (103 / 400) ≤ (33918389 / 25000000) := by
  have h := checkLog_sound (w := (97 / 303)) (n := 12)
    (lo := (331794189 / 500000000)) (hi := (663588379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 103) = 1/(103 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33918389 / 25000000) (-678367779 / 500000000) (Real.log (103 / 400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2155889 / 3906250) ≤ -Real.log (3200 / 5557) ∧
    -Real.log (3200 / 5557) ≤ (110381517 / 200000000) := by
  have h := checkLog_sound (w := (2357 / 8757)) (n := 12)
    (lo := (2155889 / 3906250)) (hi := (110381517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5557 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5557 / 3200) = 1/(3200 / 5557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2155889 / 3906250) (110381517 / 200000000) (Real.log (5557 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5557 / 3200) = -Real.log (3200 / 5557) := by
    rw [show ((5557 / 3200) : ℝ) = ((3200 / 5557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (133393913 / 100000000) ≤ -Real.log (843 / 3200) ∧
    -Real.log (843 / 3200) ≤ (333484783 / 250000000) := by
  have h := checkLog_sound (w := (757 / 2443)) (n := 12)
    (lo := (12815839 / 20000000)) (hi := (640791951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 843) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 843) = 1/(843 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-333484783 / 250000000) (-133393913 / 100000000) (Real.log (843 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (98853693 / 250000000) ≤ -Real.log (200 / 297) ∧
    -Real.log (200 / 297) ≤ (395414773 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 497)) (n := 12)
    (lo := (98853693 / 250000000)) (hi := (395414773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297 / 200) = 1/(200 / 297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (98853693 / 250000000) (395414773 / 1000000000) (Real.log (297 / 200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (297 / 200) = -Real.log (200 / 297) := by
    rw [show ((297 / 200) : ℝ) = ((200 / 297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (331794189 / 500000000) ≤ -Real.log (103 / 200) ∧
    -Real.log (103 / 200) ≤ (663588379 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 303)) (n := 12)
    (lo := (331794189 / 500000000)) (hi := (663588379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 103) = 1/(103 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-663588379 / 1000000000) (-331794189 / 500000000) (Real.log (103 / 200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (193692997 / 500000000) ≤ -Real.log (1600 / 2357) ∧
    -Real.log (1600 / 2357) ≤ (77477199 / 200000000) := by
  have h := checkLog_sound (w := (757 / 3957)) (n := 12)
    (lo := (193692997 / 500000000)) (hi := (77477199 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2357 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2357 / 1600) = 1/(1600 / 2357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (193692997 / 500000000) (77477199 / 200000000) (Real.log (2357 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2357 / 1600) = -Real.log (1600 / 2357) := by
    rw [show ((2357 / 1600) : ℝ) = ((1600 / 2357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12815839 / 20000000) ≤ -Real.log (843 / 1600) ∧
    -Real.log (843 / 1600) ≤ (640791951 / 1000000000) := by
  have h := checkLog_sound (w := (757 / 2443)) (n := 12)
    (lo := (12815839 / 20000000)) (hi := (640791951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 843) = 1/(843 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-640791951 / 1000000000) (-12815839 / 20000000) (Real.log (843 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (121092679 / 200000000) ≤ -Real.log (1000000 / 1832101) ∧
    -Real.log (1000000 / 1832101) ≤ (151365849 / 250000000) := by
  have h := checkLog_sound (w := (832101 / 2832101)) (n := 12)
    (lo := (121092679 / 200000000)) (hi := (151365849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1832101 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1832101 / 1000000) = 1/(1000000 / 1832101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (121092679 / 200000000) (151365849 / 250000000) (Real.log (1832101 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1832101 / 1000000) = -Real.log (1000000 / 1832101) := by
    rw [show ((1832101 / 1000000) : ℝ) = ((1000000 / 1832101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1784392669 / 1000000000) ≤ -Real.log (167899 / 1000000) ∧
    -Real.log (167899 / 1000000) ≤ (55762271 / 31250000) := by
  have h := checkLog_sound (w := (82101 / 417899)) (n := 12)
    (lo := (398098309 / 1000000000)) (hi := (39809831 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 167899) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 167899) = 1/(167899 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55762271 / 31250000) (-1784392669 / 1000000000) (Real.log (167899 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (151718201 / 250000000) ≤ -Real.log (200000 / 366937) ∧
    -Real.log (200000 / 366937) ≤ (121374561 / 200000000) := by
  have h := checkLog_sound (w := (166937 / 566937)) (n := 12)
    (lo := (151718201 / 250000000)) (hi := (121374561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366937 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366937 / 200000) = 1/(200000 / 366937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (151718201 / 250000000) (121374561 / 200000000) (Real.log (366937 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (366937 / 200000) = -Real.log (200000 / 366937) := by
    rw [show ((366937 / 200000) : ℝ) = ((200000 / 366937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1799902533 / 1000000000) ≤ -Real.log (33063 / 200000) ∧
    -Real.log (33063 / 200000) ≤ (224987817 / 125000000) := by
  have h := checkLog_sound (w := (16937 / 83063)) (n := 12)
    (lo := (413608173 / 1000000000)) (hi := (206804087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33063) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 33063) = 1/(33063 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-224987817 / 125000000) (-1799902533 / 1000000000) (Real.log (33063 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (592195819 / 1000000000) ≤ -Real.log (500000 / 903977) ∧
    -Real.log (500000 / 903977) ≤ (29609791 / 50000000) := by
  have h := checkLog_sound (w := (403977 / 1403977)) (n := 12)
    (lo := (592195819 / 1000000000)) (hi := (29609791 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903977 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903977 / 500000) = 1/(500000 / 903977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (592195819 / 1000000000) (29609791 / 50000000) (Real.log (903977 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (903977 / 500000) = -Real.log (500000 / 903977) := by
    rw [show ((903977 / 500000) : ℝ) = ((500000 / 903977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1650020351 / 1000000000) ≤ -Real.log (96023 / 500000) ∧
    -Real.log (96023 / 500000) ≤ (825010177 / 500000000) := by
  have h := checkLog_sound (w := (28977 / 221023)) (n := 12)
    (lo := (263725991 / 1000000000)) (hi := (32965749 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96023) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 96023) = 1/(96023 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-825010177 / 500000000) (-1650020351 / 1000000000) (Real.log (96023 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (594353941 / 1000000000) ≤ -Real.log (50000 / 90593) ∧
    -Real.log (50000 / 90593) ≤ (297176971 / 500000000) := by
  have h := checkLog_sound (w := (40593 / 140593)) (n := 12)
    (lo := (594353941 / 1000000000)) (hi := (297176971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90593 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90593 / 50000) = 1/(50000 / 90593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (594353941 / 1000000000) (297176971 / 500000000) (Real.log (90593 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (90593 / 50000) = -Real.log (50000 / 90593) := by
    rw [show ((90593 / 50000) : ℝ) = ((50000 / 90593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1670568911 / 1000000000) ≤ -Real.log (9407 / 50000) ∧
    -Real.log (9407 / 50000) ≤ (835284457 / 500000000) := by
  have h := checkLog_sound (w := (3093 / 21907)) (n := 12)
    (lo := (284274551 / 1000000000)) (hi := (35534319 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9407) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(12500 / 9407) = 1/(9407 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-835284457 / 500000000) (-1670568911 / 1000000000) (Real.log (9407 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (37341501 / 15625000) ≤ -Real.log (500000000000 / 5455961619783) ∧
    -Real.log (500000000000 / 5455961619783) ≤ (597464017 / 250000000) := by
  have h := checkLog_sound (w := (1455961619783 / 9455961619783)) (n := 12)
    (lo := (77603631 / 250000000)) (hi := (12416581 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5455961619783 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5455961619783 / 4000000000000) = 1/(500000000000 / 5455961619783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (37341501 / 15625000) (597464017 / 250000000) (Real.log (5455961619783 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5455961619783 / 500000000000) = -Real.log (500000000000 / 5455961619783) := by
    rw [show ((5455961619783 / 500000000000) : ℝ) = ((500000000000 / 5455961619783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2406775337 / 1000000000) ≤ -Real.log (500000000000 / 5549057859239) ∧
    -Real.log (500000000000 / 5549057859239) ≤ (2406775341 / 1000000000) := by
  have h := checkLog_sound (w := (1549057859239 / 9549057859239)) (n := 12)
    (lo := (327333797 / 1000000000)) (hi := (163666899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5549057859239 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5549057859239 / 4000000000000) = 1/(500000000000 / 5549057859239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2406775337 / 1000000000) (2406775341 / 1000000000) (Real.log (5549057859239 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5549057859239 / 500000000000) = -Real.log (500000000000 / 5549057859239) := by
    rw [show ((5549057859239 / 500000000000) : ℝ) = ((500000000000 / 5549057859239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2242216169 / 1000000000) ≤ -Real.log (500000000000 / 4707085802359) ∧
    -Real.log (500000000000 / 4707085802359) ≤ (2242216173 / 1000000000) := by
  have h := checkLog_sound (w := (707085802359 / 8707085802359)) (n := 12)
    (lo := (162774629 / 1000000000)) (hi := (16277463 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4707085802359 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4707085802359 / 4000000000000) = 1/(500000000000 / 4707085802359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2242216169 / 1000000000) (2242216173 / 1000000000) (Real.log (4707085802359 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4707085802359 / 500000000000) = -Real.log (500000000000 / 4707085802359) := by
    rw [show ((4707085802359 / 500000000000) : ℝ) = ((500000000000 / 4707085802359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (566230713 / 250000000) ≤ -Real.log (500000000000 / 4815190815351) ∧
    -Real.log (500000000000 / 4815190815351) ≤ (283115357 / 125000000) := by
  have h := checkLog_sound (w := (815190815351 / 8815190815351)) (n := 12)
    (lo := (5796291 / 31250000)) (hi := (185481313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4815190815351 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4815190815351 / 4000000000000) = 1/(500000000000 / 4815190815351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (566230713 / 250000000) (283115357 / 125000000) (Real.log (4815190815351 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4815190815351 / 500000000000) = -Real.log (500000000000 / 4815190815351) := by
    rw [show ((4815190815351 / 500000000000) : ℝ) = ((500000000000 / 4815190815351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0211

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0212Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0212
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

theorem reflection_log_1_neg : (2155889 / 3906250) ≤ -Real.log (3200 / 5557) ∧
    -Real.log (3200 / 5557) ≤ (110381517 / 200000000) := by
  have h := checkLog_sound (w := (2357 / 8757)) (n := 12)
    (lo := (2155889 / 3906250)) (hi := (110381517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5557 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5557 / 3200) = 1/(3200 / 5557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2155889 / 3906250) (110381517 / 200000000) (Real.log (5557 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5557 / 3200) = -Real.log (3200 / 5557) := by
    rw [show ((5557 / 3200) : ℝ) = ((3200 / 5557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (133393913 / 100000000) ≤ -Real.log (843 / 3200) ∧
    -Real.log (843 / 3200) ≤ (333484783 / 250000000) := by
  have h := checkLog_sound (w := (757 / 2443)) (n := 12)
    (lo := (12815839 / 20000000)) (hi := (640791951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 843) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 843) = 1/(843 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-333484783 / 250000000) (-133393913 / 100000000) (Real.log (843 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (274241307 / 500000000) ≤ -Real.log (1600 / 2769) ∧
    -Real.log (1600 / 2769) ≤ (109696523 / 200000000) := by
  have h := checkLog_sound (w := (1169 / 4369)) (n := 12)
    (lo := (274241307 / 500000000)) (hi := (109696523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2769 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2769 / 1600) = 1/(1600 / 2769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (274241307 / 500000000) (109696523 / 200000000) (Real.log (2769 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2769 / 1600) = -Real.log (1600 / 2769) := by
    rw [show ((2769 / 1600) : ℝ) = ((1600 / 2769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1311650817 / 1000000000) ≤ -Real.log (431 / 1600) ∧
    -Real.log (431 / 1600) ≤ (1311650819 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 1231)) (n := 12)
    (lo := (618503637 / 1000000000)) (hi := (309251819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 431) = 1/(431 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1311650819 / 1000000000) (-1311650817 / 1000000000) (Real.log (431 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (193692997 / 500000000) ≤ -Real.log (1600 / 2357) ∧
    -Real.log (1600 / 2357) ≤ (77477199 / 200000000) := by
  have h := checkLog_sound (w := (757 / 3957)) (n := 12)
    (lo := (193692997 / 500000000)) (hi := (77477199 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2357 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2357 / 1600) = 1/(1600 / 2357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (193692997 / 500000000) (77477199 / 200000000) (Real.log (2357 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2357 / 1600) = -Real.log (1600 / 2357) := by
    rw [show ((2357 / 1600) : ℝ) = ((1600 / 2357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12815839 / 20000000) ≤ -Real.log (843 / 1600) ∧
    -Real.log (843 / 1600) ≤ (640791951 / 1000000000) := by
  have h := checkLog_sound (w := (757 / 2443)) (n := 12)
    (lo := (12815839 / 20000000)) (hi := (640791951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 843) = 1/(843 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-640791951 / 1000000000) (-12815839 / 20000000) (Real.log (843 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (379292233 / 1000000000) ≤ -Real.log (800 / 1169) ∧
    -Real.log (800 / 1169) ≤ (189646117 / 500000000) := by
  have h := checkLog_sound (w := (369 / 1969)) (n := 12)
    (lo := (379292233 / 1000000000)) (hi := (189646117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169 / 800) = 1/(800 / 1169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (379292233 / 1000000000) (189646117 / 500000000) (Real.log (1169 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1169 / 800) = -Real.log (800 / 1169) := by
    rw [show ((1169 / 800) : ℝ) = ((800 / 1169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (618503637 / 1000000000) ≤ -Real.log (431 / 800) ∧
    -Real.log (431 / 800) ≤ (309251819 / 500000000) := by
  have h := checkLog_sound (w := (369 / 1231)) (n := 12)
    (lo := (618503637 / 1000000000)) (hi := (309251819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 431) = 1/(431 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-309251819 / 500000000) (-618503637 / 1000000000) (Real.log (431 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (604083699 / 1000000000) ≤ -Real.log (40000 / 73183) ∧
    -Real.log (40000 / 73183) ≤ (6040837 / 10000000) := by
  have h := checkLog_sound (w := (33183 / 113183)) (n := 12)
    (lo := (604083699 / 1000000000)) (hi := (6040837 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73183 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73183 / 40000) = 1/(40000 / 73183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (604083699 / 1000000000) (6040837 / 10000000) (Real.log (73183 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (73183 / 40000) = -Real.log (40000 / 73183) := by
    rw [show ((73183 / 40000) : ℝ) = ((40000 / 73183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (44236499 / 25000000) ≤ -Real.log (6817 / 40000) ∧
    -Real.log (6817 / 40000) ≤ (1769459963 / 1000000000) := by
  have h := checkLog_sound (w := (3183 / 16817)) (n := 12)
    (lo := (478957 / 1250000)) (hi := (383165601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 6817) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(10000 / 6817) = 1/(6817 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1769459963 / 1000000000) (-44236499 / 25000000) (Real.log (6817 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (605463941 / 1000000000) ≤ -Real.log (500000 / 916051) ∧
    -Real.log (500000 / 916051) ≤ (302731971 / 500000000) := by
  have h := checkLog_sound (w := (416051 / 1416051)) (n := 12)
    (lo := (605463941 / 1000000000)) (hi := (302731971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((916051 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(916051 / 500000) = 1/(500000 / 916051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (605463941 / 1000000000) (302731971 / 500000000) (Real.log (916051 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (916051 / 500000) = -Real.log (500000 / 916051) := by
    rw [show ((916051 / 500000) : ℝ) = ((500000 / 916051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (14275189 / 8000000) ≤ -Real.log (83949 / 500000) ∧
    -Real.log (83949 / 500000) ≤ (446099657 / 250000000) := by
  have h := checkLog_sound (w := (41051 / 208949)) (n := 12)
    (lo := (79620853 / 200000000)) (hi := (199052133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 83949) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 83949) = 1/(83949 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-446099657 / 250000000) (-14275189 / 8000000) (Real.log (83949 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (921937 / 1562500) ≤ -Real.log (50000 / 90203) ∧
    -Real.log (50000 / 90203) ≤ (590039681 / 1000000000) := by
  have h := checkLog_sound (w := (40203 / 140203)) (n := 12)
    (lo := (921937 / 1562500)) (hi := (590039681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90203 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90203 / 50000) = 1/(50000 / 90203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (921937 / 1562500) (590039681 / 1000000000) (Real.log (90203 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (90203 / 50000) = -Real.log (50000 / 90203) := by
    rw [show ((90203 / 50000) : ℝ) = ((50000 / 90203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1629946787 / 1000000000) ≤ -Real.log (9797 / 50000) ∧
    -Real.log (9797 / 50000) ≤ (162994679 / 100000000) := by
  have h := checkLog_sound (w := (2703 / 22297)) (n := 12)
    (lo := (243652427 / 1000000000)) (hi := (60913107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9797) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(12500 / 9797) = 1/(9797 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-162994679 / 100000000) (-1629946787 / 1000000000) (Real.log (9797 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (148049093 / 250000000) ≤ -Real.log (200000 / 361591) ∧
    -Real.log (200000 / 361591) ≤ (592196373 / 1000000000) := by
  have h := checkLog_sound (w := (161591 / 561591)) (n := 12)
    (lo := (148049093 / 250000000)) (hi := (592196373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361591 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361591 / 200000) = 1/(200000 / 361591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (148049093 / 250000000) (592196373 / 1000000000) (Real.log (361591 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (361591 / 200000) = -Real.log (200000 / 361591) := by
    rw [show ((361591 / 200000) : ℝ) = ((200000 / 361591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (825012779 / 500000000) ≤ -Real.log (38409 / 200000) ∧
    -Real.log (38409 / 200000) ≤ (1650025561 / 1000000000) := by
  have h := checkLog_sound (w := (11591 / 88409)) (n := 12)
    (lo := (131865599 / 500000000)) (hi := (263731199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38409) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 38409) = 1/(38409 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1650025561 / 1000000000) (-825012779 / 500000000) (Real.log (38409 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2373543659 / 1000000000) ≤ -Real.log (250000000000 / 2683841865923) ∧
    -Real.log (250000000000 / 2683841865923) ≤ (2373543663 / 1000000000) := by
  have h := checkLog_sound (w := (683841865923 / 4683841865923)) (n := 12)
    (lo := (294102119 / 1000000000)) (hi := (7352553 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2683841865923 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2683841865923 / 2000000000000) = 1/(250000000000 / 2683841865923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2373543659 / 1000000000) (2373543663 / 1000000000) (Real.log (2683841865923 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2683841865923 / 250000000000) = -Real.log (250000000000 / 2683841865923) := by
    rw [show ((2683841865923 / 250000000000) : ℝ) = ((250000000000 / 2683841865923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1194931283 / 500000000) ≤ -Real.log (250000000000 / 2727998546737) ∧
    -Real.log (250000000000 / 2727998546737) ≤ (238986257 / 100000000) := by
  have h := checkLog_sound (w := (727998546737 / 4727998546737)) (n := 12)
    (lo := (155210513 / 500000000)) (hi := (310421027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2727998546737 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2727998546737 / 2000000000000) = 1/(250000000000 / 2727998546737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1194931283 / 500000000) (238986257 / 100000000) (Real.log (2727998546737 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2727998546737 / 250000000000) = -Real.log (250000000000 / 2727998546737) := by
    rw [show ((2727998546737 / 250000000000) : ℝ) = ((250000000000 / 2727998546737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2219986467 / 1000000000) ≤ -Real.log (500000000000 / 4603603143819) ∧
    -Real.log (500000000000 / 4603603143819) ≤ (2219986471 / 1000000000) := by
  have h := checkLog_sound (w := (603603143819 / 8603603143819)) (n := 12)
    (lo := (140544927 / 1000000000)) (hi := (4392029 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4603603143819 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4603603143819 / 4000000000000) = 1/(500000000000 / 4603603143819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2219986467 / 1000000000) (2219986471 / 1000000000) (Real.log (4603603143819 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4603603143819 / 500000000000) = -Real.log (500000000000 / 4603603143819) := by
    rw [show ((4603603143819 / 500000000000) : ℝ) = ((500000000000 / 4603603143819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (224222193 / 100000000) ≤ -Real.log (125000000000 / 1176778229061) ∧
    -Real.log (125000000000 / 1176778229061) ≤ (1121110967 / 500000000) := by
  have h := checkLog_sound (w := (176778229061 / 2176778229061)) (n := 12)
    (lo := (16278039 / 100000000)) (hi := (162780391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176778229061 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1176778229061 / 1000000000000) = 1/(125000000000 / 1176778229061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (224222193 / 100000000) (1121110967 / 500000000) (Real.log (1176778229061 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1176778229061 / 125000000000) = -Real.log (125000000000 / 1176778229061) := by
    rw [show ((1176778229061 / 125000000000) : ℝ) = ((125000000000 / 1176778229061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0212

end


