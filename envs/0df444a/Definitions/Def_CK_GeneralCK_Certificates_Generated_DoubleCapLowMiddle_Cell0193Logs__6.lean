-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0193Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0193Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:08:59.779669+00:00
-- url     : https://prove2.me/theorems/60a6c142-60b2-40ca-b826-a04134f20680
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0193Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0194Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0193Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0194Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0195Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0196Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0197Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0198Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0193Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0194Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0195Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0196Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0197Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0198Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0193Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0194Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0195Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0196Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0197Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0198Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0193Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0194Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0195Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0196Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0197Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0198Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0193Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0193
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

theorem reflection_log_1_neg : (605169427 / 1000000000) ≤ -Real.log (3200 / 5861) ∧
    -Real.log (3200 / 5861) ≤ (151292357 / 250000000) := by
  have h := checkLog_sound (w := (2661 / 9061)) (n := 12)
    (lo := (605169427 / 1000000000)) (hi := (151292357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5861 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5861 / 3200) = 1/(3200 / 5861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (605169427 / 1000000000) (151292357 / 250000000) (Real.log (5861 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5861 / 3200) = -Real.log (3200 / 5861) := by
    rw [show ((5861 / 3200) : ℝ) = ((3200 / 5861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (445297629 / 250000000) ≤ -Real.log (539 / 3200) ∧
    -Real.log (539 / 3200) ≤ (1781190519 / 1000000000) := by
  have h := checkLog_sound (w := (261 / 1339)) (n := 12)
    (lo := (98724039 / 250000000)) (hi := (394896157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 539) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 539) = 1/(539 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1781190519 / 1000000000) (-445297629 / 250000000) (Real.log (539 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (150886807 / 250000000) ≤ -Real.log (6400 / 11703) ∧
    -Real.log (6400 / 11703) ≤ (603547229 / 1000000000) := by
  have h := checkLog_sound (w := (5303 / 18103)) (n := 12)
    (lo := (150886807 / 250000000)) (hi := (603547229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11703 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11703 / 6400) = 1/(6400 / 11703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (150886807 / 250000000) (603547229 / 1000000000) (Real.log (11703 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11703 / 6400) = -Real.log (6400 / 11703) := by
    rw [show ((11703 / 6400) : ℝ) = ((6400 / 11703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1763718807 / 1000000000) ≤ -Real.log (1097 / 6400) ∧
    -Real.log (1097 / 6400) ≤ (176371881 / 100000000) := by
  have h := checkLog_sound (w := (503 / 2697)) (n := 12)
    (lo := (377424447 / 1000000000)) (hi := (5897257 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1097) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1097) = 1/(1097 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-176371881 / 100000000) (-1763718807 / 1000000000) (Real.log (1097 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (254349181 / 500000000) ≤ -Real.log (1600 / 2661) ∧
    -Real.log (1600 / 2661) ≤ (508698363 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 4261)) (n := 12)
    (lo := (254349181 / 500000000)) (hi := (508698363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2661 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2661 / 1600) = 1/(1600 / 2661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (254349181 / 500000000) (508698363 / 1000000000) (Real.log (2661 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2661 / 1600) = -Real.log (1600 / 2661) := by
    rw [show ((2661 / 1600) : ℝ) = ((1600 / 2661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (136005417 / 125000000) ≤ -Real.log (539 / 1600) ∧
    -Real.log (539 / 1600) ≤ (544021669 / 500000000) := by
  have h := checkLog_sound (w := (261 / 1339)) (n := 12)
    (lo := (98724039 / 250000000)) (hi := (394896157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 539) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 539) = 1/(539 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-544021669 / 500000000) (-136005417 / 125000000) (Real.log (539 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (15785059 / 31250000) ≤ -Real.log (3200 / 5303) ∧
    -Real.log (3200 / 5303) ≤ (505121889 / 1000000000) := by
  have h := checkLog_sound (w := (2103 / 8503)) (n := 12)
    (lo := (15785059 / 31250000)) (hi := (505121889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5303 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5303 / 3200) = 1/(3200 / 5303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (15785059 / 31250000) (505121889 / 1000000000) (Real.log (5303 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5303 / 3200) = -Real.log (3200 / 5303) := by
    rw [show ((5303 / 3200) : ℝ) = ((3200 / 5303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1070571627 / 1000000000) ≤ -Real.log (1097 / 3200) ∧
    -Real.log (1097 / 3200) ≤ (1070571629 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 2697)) (n := 12)
    (lo := (377424447 / 1000000000)) (hi := (5897257 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1097) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1097) = 1/(1097 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1070571629 / 1000000000) (-1070571627 / 1000000000) (Real.log (1097 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (315231203 / 500000000) ≤ -Real.log (1000000 / 1878479) ∧
    -Real.log (1000000 / 1878479) ≤ (630462407 / 1000000000) := by
  have h := checkLog_sound (w := (878479 / 2878479)) (n := 12)
    (lo := (315231203 / 500000000)) (hi := (630462407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1878479 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1878479 / 1000000) = 1/(1000000 / 1878479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (315231203 / 500000000) (630462407 / 1000000000) (Real.log (1878479 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1878479 / 1000000) = -Real.log (1000000 / 1878479) := by
    rw [show ((1878479 / 1000000) : ℝ) = ((1000000 / 1878479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2107668189 / 1000000000) ≤ -Real.log (121521 / 1000000) ∧
    -Real.log (121521 / 1000000) ≤ (2107668193 / 1000000000) := by
  have h := checkLog_sound (w := (3479 / 246521)) (n := 12)
    (lo := (28226649 / 1000000000)) (hi := (564533 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 121521) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 121521) = 1/(121521 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2107668193 / 1000000000) (-2107668189 / 1000000000) (Real.log (121521 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (315687747 / 500000000) ≤ -Real.log (200000 / 376039) ∧
    -Real.log (200000 / 376039) ≤ (126275099 / 200000000) := by
  have h := checkLog_sound (w := (176039 / 576039)) (n := 12)
    (lo := (315687747 / 500000000)) (hi := (126275099 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376039 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376039 / 200000) = 1/(200000 / 376039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (315687747 / 500000000) (126275099 / 200000000) (Real.log (376039 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (376039 / 200000) = -Real.log (200000 / 376039) := by
    rw [show ((376039 / 200000) : ℝ) = ((200000 / 376039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (33154529 / 15625000) ≤ -Real.log (23961 / 200000) ∧
    -Real.log (23961 / 200000) ≤ (106094493 / 50000000) := by
  have h := checkLog_sound (w := (1039 / 48961)) (n := 12)
    (lo := (10612079 / 250000000)) (hi := (42448317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23961) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 23961) = 1/(23961 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-106094493 / 50000000) (-33154529 / 15625000) (Real.log (23961 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (39121319 / 62500000) ≤ -Real.log (200000 / 374001) ∧
    -Real.log (200000 / 374001) ≤ (125188221 / 200000000) := by
  have h := checkLog_sound (w := (174001 / 574001)) (n := 12)
    (lo := (39121319 / 62500000)) (hi := (125188221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374001 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374001 / 200000) = 1/(200000 / 374001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (39121319 / 62500000) (125188221 / 200000000) (Real.log (374001 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (374001 / 200000) = -Real.log (200000 / 374001) := by
    rw [show ((374001 / 200000) : ℝ) = ((200000 / 374001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2040259289 / 1000000000) ≤ -Real.log (25999 / 200000) ∧
    -Real.log (25999 / 200000) ≤ (510064823 / 250000000) := by
  have h := checkLog_sound (w := (24001 / 75999)) (n := 12)
    (lo := (653964929 / 1000000000)) (hi := (65396493 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 25999) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 25999) = 1/(25999 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-510064823 / 250000000) (-2040259289 / 1000000000) (Real.log (25999 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (156761059 / 250000000) ≤ -Real.log (1000000 / 1872069) ∧
    -Real.log (1000000 / 1872069) ≤ (627044237 / 1000000000) := by
  have h := checkLog_sound (w := (872069 / 2872069)) (n := 12)
    (lo := (156761059 / 250000000)) (hi := (627044237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1872069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1872069 / 1000000) = 1/(1000000 / 1872069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (156761059 / 250000000) (627044237 / 1000000000) (Real.log (1872069 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1872069 / 1000000) = -Real.log (1000000 / 1872069) := by
    rw [show ((1872069 / 1000000) : ℝ) = ((1000000 / 1872069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2056264221 / 1000000000) ≤ -Real.log (127931 / 1000000) ∧
    -Real.log (127931 / 1000000) ≤ (64258257 / 31250000) := by
  have h := checkLog_sound (w := (122069 / 377931)) (n := 12)
    (lo := (669969861 / 1000000000)) (hi := (334984931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 127931) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 127931) = 1/(127931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-64258257 / 31250000) (-2056264221 / 1000000000) (Real.log (127931 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (684532649 / 250000000) ≤ -Real.log (500000000000 / 7729030373351) ∧
    -Real.log (500000000000 / 7729030373351) ≤ (13690653 / 5000000) := by
  have h := checkLog_sound (w := (3729030373351 / 11729030373351)) (n := 12)
    (lo := (20584033 / 31250000)) (hi := (658689057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7729030373351 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7729030373351 / 4000000000000) = 1/(500000000000 / 7729030373351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (684532649 / 250000000) (13690653 / 5000000) (Real.log (7729030373351 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7729030373351 / 500000000000) = -Real.log (500000000000 / 7729030373351) := by
    rw [show ((7729030373351 / 500000000000) : ℝ) = ((500000000000 / 7729030373351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2753265351 / 1000000000) ≤ -Real.log (20000000000 / 313875881641) ∧
    -Real.log (20000000000 / 313875881641) ≤ (550653071 / 200000000) := by
  have h := checkLog_sound (w := (153875881641 / 473875881641)) (n := 12)
    (lo := (673823811 / 1000000000)) (hi := (168455953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313875881641 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(313875881641 / 160000000000) = 1/(20000000000 / 313875881641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2753265351 / 1000000000) (550653071 / 200000000) (Real.log (313875881641 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (313875881641 / 20000000000) = -Real.log (20000000000 / 313875881641) := by
    rw [show ((313875881641 / 20000000000) : ℝ) = ((20000000000 / 313875881641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2666200393 / 1000000000) ≤ -Real.log (20000000000 / 287704142467) ∧
    -Real.log (20000000000 / 287704142467) ≤ (2666200397 / 1000000000) := by
  have h := checkLog_sound (w := (127704142467 / 447704142467)) (n := 12)
    (lo := (586758853 / 1000000000)) (hi := (293379427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287704142467 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(287704142467 / 160000000000) = 1/(20000000000 / 287704142467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2666200393 / 1000000000) (2666200397 / 1000000000) (Real.log (287704142467 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (287704142467 / 20000000000) = -Real.log (20000000000 / 287704142467) := by
    rw [show ((287704142467 / 20000000000) : ℝ) = ((20000000000 / 287704142467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2683308457 / 1000000000) ≤ -Real.log (125000000000 / 1829178424307) ∧
    -Real.log (125000000000 / 1829178424307) ≤ (2683308461 / 1000000000) := by
  have h := checkLog_sound (w := (829178424307 / 2829178424307)) (n := 12)
    (lo := (603866917 / 1000000000)) (hi := (301933459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1829178424307 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1829178424307 / 1000000000000) = 1/(125000000000 / 1829178424307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2683308457 / 1000000000) (2683308461 / 1000000000) (Real.log (1829178424307 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1829178424307 / 125000000000) = -Real.log (125000000000 / 1829178424307) := by
    rw [show ((1829178424307 / 125000000000) : ℝ) = ((125000000000 / 1829178424307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0193

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0194Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0194
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

theorem reflection_log_1_neg : (150886807 / 250000000) ≤ -Real.log (6400 / 11703) ∧
    -Real.log (6400 / 11703) ≤ (603547229 / 1000000000) := by
  have h := checkLog_sound (w := (5303 / 18103)) (n := 12)
    (lo := (150886807 / 250000000)) (hi := (603547229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11703 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11703 / 6400) = 1/(6400 / 11703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (150886807 / 250000000) (603547229 / 1000000000) (Real.log (11703 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11703 / 6400) = -Real.log (6400 / 11703) := by
    rw [show ((11703 / 6400) : ℝ) = ((6400 / 11703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1763718807 / 1000000000) ≤ -Real.log (1097 / 6400) ∧
    -Real.log (1097 / 6400) ≤ (176371881 / 100000000) := by
  have h := checkLog_sound (w := (503 / 2697)) (n := 12)
    (lo := (377424447 / 1000000000)) (hi := (5897257 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1097) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1097) = 1/(1097 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-176371881 / 100000000) (-1763718807 / 1000000000) (Real.log (1097 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (300961197 / 500000000) ≤ -Real.log (1600 / 2921) ∧
    -Real.log (1600 / 2921) ≤ (120384479 / 200000000) := by
  have h := checkLog_sound (w := (1321 / 4521)) (n := 12)
    (lo := (300961197 / 500000000)) (hi := (120384479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2921 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2921 / 1600) = 1/(1600 / 2921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (300961197 / 500000000) (120384479 / 200000000) (Real.log (2921 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2921 / 1600) = -Real.log (1600 / 2921) := by
    rw [show ((2921 / 1600) : ℝ) = ((1600 / 2921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (13972377 / 8000000) ≤ -Real.log (279 / 1600) ∧
    -Real.log (279 / 1600) ≤ (218318391 / 125000000) := by
  have h := checkLog_sound (w := (121 / 679)) (n := 12)
    (lo := (72050553 / 200000000)) (hi := (180126383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 279) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 279) = 1/(279 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-218318391 / 125000000) (-13972377 / 8000000) (Real.log (279 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15785059 / 31250000) ≤ -Real.log (3200 / 5303) ∧
    -Real.log (3200 / 5303) ≤ (505121889 / 1000000000) := by
  have h := checkLog_sound (w := (2103 / 8503)) (n := 12)
    (lo := (15785059 / 31250000)) (hi := (505121889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5303 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5303 / 3200) = 1/(3200 / 5303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15785059 / 31250000) (505121889 / 1000000000) (Real.log (5303 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5303 / 3200) = -Real.log (3200 / 5303) := by
    rw [show ((5303 / 3200) : ℝ) = ((3200 / 5303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1070571627 / 1000000000) ≤ -Real.log (1097 / 3200) ∧
    -Real.log (1097 / 3200) ≤ (1070571629 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 2697)) (n := 12)
    (lo := (377424447 / 1000000000)) (hi := (5897257 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1097) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1097) = 1/(1097 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1070571629 / 1000000000) (-1070571627 / 1000000000) (Real.log (1097 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (15672893 / 31250000) ≤ -Real.log (800 / 1321) ∧
    -Real.log (800 / 1321) ≤ (501532577 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 2121)) (n := 12)
    (lo := (15672893 / 31250000)) (hi := (501532577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321 / 800) = 1/(800 / 1321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (15672893 / 31250000) (501532577 / 1000000000) (Real.log (1321 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1321 / 800) = -Real.log (800 / 1321) := by
    rw [show ((1321 / 800) : ℝ) = ((800 / 1321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (210679989 / 200000000) ≤ -Real.log (279 / 800) ∧
    -Real.log (279 / 800) ≤ (1053399947 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 679)) (n := 12)
    (lo := (72050553 / 200000000)) (hi := (180126383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 279) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 279) = 1/(279 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1053399947 / 1000000000) (-210679989 / 200000000) (Real.log (279 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (629555943 / 1000000000) ≤ -Real.log (1000000 / 1876777) ∧
    -Real.log (1000000 / 1876777) ≤ (78694493 / 125000000) := by
  have h := checkLog_sound (w := (876777 / 2876777)) (n := 12)
    (lo := (629555943 / 1000000000)) (hi := (78694493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1876777 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1876777 / 1000000) = 1/(1000000 / 1876777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (629555943 / 1000000000) (78694493 / 125000000) (Real.log (1876777 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1876777 / 1000000) = -Real.log (1000000 / 1876777) := by
    rw [show ((1876777 / 1000000) : ℝ) = ((1000000 / 1876777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (418751911 / 200000000) ≤ -Real.log (123223 / 1000000) ∧
    -Real.log (123223 / 1000000) ≤ (2093759559 / 1000000000) := by
  have h := checkLog_sound (w := (1777 / 248223)) (n := 12)
    (lo := (2863603 / 200000000)) (hi := (223719 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 123223) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 123223) = 1/(123223 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2093759559 / 1000000000) (-418751911 / 200000000) (Real.log (123223 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (630462939 / 1000000000) ≤ -Real.log (12500 / 23481) ∧
    -Real.log (12500 / 23481) ≤ (31523147 / 50000000) := by
  have h := checkLog_sound (w := (10981 / 35981)) (n := 12)
    (lo := (630462939 / 1000000000)) (hi := (31523147 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23481 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23481 / 12500) = 1/(12500 / 23481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (630462939 / 1000000000) (31523147 / 50000000) (Real.log (23481 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (23481 / 12500) = -Real.log (12500 / 23481) := by
    rw [show ((23481 / 12500) : ℝ) = ((12500 / 23481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2107676419 / 1000000000) ≤ -Real.log (1519 / 12500) ∧
    -Real.log (1519 / 12500) ≤ (2107676423 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 6163)) (n := 12)
    (lo := (28234879 / 1000000000)) (hi := (44117 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3038) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 3038) = 1/(1519 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2107676423 / 1000000000) (-2107676419 / 1000000000) (Real.log (1519 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (624839431 / 1000000000) ≤ -Real.log (500000 / 933973) ∧
    -Real.log (500000 / 933973) ≤ (78104929 / 125000000) := by
  have h := checkLog_sound (w := (433973 / 1433973)) (n := 12)
    (lo := (624839431 / 1000000000)) (hi := (78104929 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933973 / 500000) = 1/(500000 / 933973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (624839431 / 1000000000) (78104929 / 125000000) (Real.log (933973 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (933973 / 500000) = -Real.log (500000 / 933973) := by
    rw [show ((933973 / 500000) : ℝ) = ((500000 / 933973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (506136087 / 250000000) ≤ -Real.log (66027 / 500000) ∧
    -Real.log (66027 / 500000) ≤ (2024544351 / 1000000000) := by
  have h := checkLog_sound (w := (58973 / 191027)) (n := 12)
    (lo := (159562497 / 250000000)) (hi := (638249989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 66027) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 66027) = 1/(66027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2024544351 / 1000000000) (-506136087 / 250000000) (Real.log (66027 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (625941639 / 1000000000) ≤ -Real.log (500000 / 935003) ∧
    -Real.log (500000 / 935003) ≤ (15648541 / 25000000) := by
  have h := checkLog_sound (w := (435003 / 1435003)) (n := 12)
    (lo := (625941639 / 1000000000)) (hi := (15648541 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935003 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935003 / 500000) = 1/(500000 / 935003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (625941639 / 1000000000) (15648541 / 25000000) (Real.log (935003 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (935003 / 500000) = -Real.log (500000 / 935003) := by
    rw [show ((935003 / 500000) : ℝ) = ((500000 / 935003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1020133491 / 500000000) ≤ -Real.log (64997 / 500000) ∧
    -Real.log (64997 / 500000) ≤ (408053397 / 200000000) := by
  have h := checkLog_sound (w := (60003 / 189997)) (n := 12)
    (lo := (326986311 / 500000000)) (hi := (653972623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 64997) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 64997) = 1/(64997 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-408053397 / 200000000) (-1020133491 / 500000000) (Real.log (64997 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2723315499 / 1000000000) ≤ -Real.log (250000000000 / 3807684036259) ∧
    -Real.log (250000000000 / 3807684036259) ≤ (2723315503 / 1000000000) := by
  have h := checkLog_sound (w := (1807684036259 / 5807684036259)) (n := 12)
    (lo := (643873959 / 1000000000)) (hi := (16096849 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3807684036259 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3807684036259 / 2000000000000) = 1/(250000000000 / 3807684036259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2723315499 / 1000000000) (2723315503 / 1000000000) (Real.log (3807684036259 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3807684036259 / 250000000000) = -Real.log (250000000000 / 3807684036259) := by
    rw [show ((3807684036259 / 250000000000) : ℝ) = ((250000000000 / 3807684036259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1369069679 / 500000000) ≤ -Real.log (10000000000 / 154581961817) ∧
    -Real.log (10000000000 / 154581961817) ≤ (1369069681 / 500000000) := by
  have h := checkLog_sound (w := (74581961817 / 234581961817)) (n := 12)
    (lo := (329348909 / 500000000)) (hi := (658697819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154581961817 / 80000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(154581961817 / 80000000000) = 1/(10000000000 / 154581961817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1369069679 / 500000000) (1369069681 / 500000000) (Real.log (154581961817 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (154581961817 / 10000000000) = -Real.log (10000000000 / 154581961817) := by
    rw [show ((154581961817 / 10000000000) : ℝ) = ((10000000000 / 154581961817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1324691889 / 500000000) ≤ -Real.log (500000000000 / 7072659669529) ∧
    -Real.log (500000000000 / 7072659669529) ≤ (1324691891 / 500000000) := by
  have h := checkLog_sound (w := (3072659669529 / 11072659669529)) (n := 12)
    (lo := (284971119 / 500000000)) (hi := (569942239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7072659669529 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7072659669529 / 4000000000000) = 1/(500000000000 / 7072659669529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1324691889 / 500000000) (1324691891 / 500000000) (Real.log (7072659669529 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7072659669529 / 500000000000) = -Real.log (500000000000 / 7072659669529) := by
    rw [show ((7072659669529 / 500000000000) : ℝ) = ((500000000000 / 7072659669529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2666208621 / 1000000000) ≤ -Real.log (500000000000 / 7192662738281) ∧
    -Real.log (500000000000 / 7192662738281) ≤ (21329669 / 8000000) := by
  have h := checkLog_sound (w := (3192662738281 / 11192662738281)) (n := 12)
    (lo := (586767081 / 1000000000)) (hi := (293383541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7192662738281 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7192662738281 / 4000000000000) = 1/(500000000000 / 7192662738281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2666208621 / 1000000000) (21329669 / 8000000) (Real.log (7192662738281 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7192662738281 / 500000000000) = -Real.log (500000000000 / 7192662738281) := by
    rw [show ((7192662738281 / 500000000000) : ℝ) = ((500000000000 / 7192662738281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0194

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0195Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0195
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

theorem reflection_log_1_neg : (300961197 / 500000000) ≤ -Real.log (1600 / 2921) ∧
    -Real.log (1600 / 2921) ≤ (120384479 / 200000000) := by
  have h := checkLog_sound (w := (1321 / 4521)) (n := 12)
    (lo := (300961197 / 500000000)) (hi := (120384479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2921 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2921 / 1600) = 1/(1600 / 2921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (300961197 / 500000000) (120384479 / 200000000) (Real.log (2921 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2921 / 1600) = -Real.log (1600 / 2921) := by
    rw [show ((2921 / 1600) : ℝ) = ((1600 / 2921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (13972377 / 8000000) ≤ -Real.log (279 / 1600) ∧
    -Real.log (279 / 1600) ≤ (218318391 / 125000000) := by
  have h := checkLog_sound (w := (121 / 679)) (n := 12)
    (lo := (72050553 / 200000000)) (hi := (180126383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 279) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 279) = 1/(279 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-218318391 / 125000000) (-13972377 / 8000000) (Real.log (279 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (120058983 / 200000000) ≤ -Real.log (1280 / 2333) ∧
    -Real.log (1280 / 2333) ≤ (150073729 / 250000000) := by
  have h := checkLog_sound (w := (1053 / 3613)) (n := 12)
    (lo := (120058983 / 200000000)) (hi := (150073729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2333 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2333 / 1280) = 1/(1280 / 2333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (120058983 / 200000000) (150073729 / 250000000) (Real.log (2333 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2333 / 1280) = -Real.log (1280 / 2333) := by
    rw [show ((2333 / 1280) : ℝ) = ((1280 / 2333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (864832669 / 500000000) ≤ -Real.log (227 / 1280) ∧
    -Real.log (227 / 1280) ≤ (1729665341 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 547)) (n := 12)
    (lo := (171685489 / 500000000)) (hi := (343370979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 227) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 227) = 1/(227 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1729665341 / 1000000000) (-864832669 / 500000000) (Real.log (227 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15672893 / 31250000) ≤ -Real.log (800 / 1321) ∧
    -Real.log (800 / 1321) ≤ (501532577 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 2121)) (n := 12)
    (lo := (15672893 / 31250000)) (hi := (501532577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321 / 800) = 1/(800 / 1321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15672893 / 31250000) (501532577 / 1000000000) (Real.log (1321 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1321 / 800) = -Real.log (800 / 1321) := by
    rw [show ((1321 / 800) : ℝ) = ((800 / 1321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (210679989 / 200000000) ≤ -Real.log (279 / 800) ∧
    -Real.log (279 / 800) ≤ (1053399947 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 679)) (n := 12)
    (lo := (72050553 / 200000000)) (hi := (180126383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 279) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 279) = 1/(279 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1053399947 / 1000000000) (-210679989 / 200000000) (Real.log (279 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (99586067 / 200000000) ≤ -Real.log (640 / 1053) ∧
    -Real.log (640 / 1053) ≤ (15560323 / 31250000) := by
  have h := checkLog_sound (w := (413 / 1693)) (n := 12)
    (lo := (99586067 / 200000000)) (hi := (15560323 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1053 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1053 / 640) = 1/(640 / 1053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (99586067 / 200000000) (15560323 / 31250000) (Real.log (1053 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1053 / 640) = -Real.log (640 / 1053) := by
    rw [show ((1053 / 640) : ℝ) = ((640 / 1053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (518259079 / 500000000) ≤ -Real.log (227 / 640) ∧
    -Real.log (227 / 640) ≤ (12956477 / 12500000) := by
  have h := checkLog_sound (w := (93 / 547)) (n := 12)
    (lo := (171685489 / 500000000)) (hi := (343370979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 227) = 1/(227 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12956477 / 12500000) (-518259079 / 500000000) (Real.log (227 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (157164031 / 250000000) ≤ -Real.log (1000000 / 1875089) ∧
    -Real.log (1000000 / 1875089) ≤ (5029249 / 8000000) := by
  have h := checkLog_sound (w := (875089 / 2875089)) (n := 12)
    (lo := (157164031 / 250000000)) (hi := (5029249 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1875089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1875089 / 1000000) = 1/(1000000 / 1875089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (157164031 / 250000000) (5029249 / 8000000) (Real.log (1875089 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1875089 / 1000000) = -Real.log (1000000 / 1875089) := by
    rw [show ((1875089 / 1000000) : ℝ) = ((1000000 / 1875089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2080153793 / 1000000000) ≤ -Real.log (124911 / 1000000) ∧
    -Real.log (124911 / 1000000) ≤ (2080153797 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 249911)) (n := 12)
    (lo := (712253 / 1000000000)) (hi := (356127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124911) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 124911) = 1/(124911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2080153797 / 1000000000) (-2080153793 / 1000000000) (Real.log (124911 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (157389119 / 250000000) ≤ -Real.log (500000 / 938389) ∧
    -Real.log (500000 / 938389) ≤ (629556477 / 1000000000) := by
  have h := checkLog_sound (w := (438389 / 1438389)) (n := 12)
    (lo := (157389119 / 250000000)) (hi := (629556477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((938389 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(938389 / 500000) = 1/(500000 / 938389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (157389119 / 250000000) (629556477 / 1000000000) (Real.log (938389 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (938389 / 500000) = -Real.log (500000 / 938389) := by
    rw [show ((938389 / 500000) : ℝ) = ((500000 / 938389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (209376767 / 100000000) ≤ -Real.log (61611 / 500000) ∧
    -Real.log (61611 / 500000) ≤ (1046883837 / 500000000) := by
  have h := checkLog_sound (w := (889 / 124111)) (n := 12)
    (lo := (1432613 / 100000000)) (hi := (14326131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 61611) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 61611) = 1/(61611 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1046883837 / 500000000) (-209376767 / 100000000) (Real.log (61611 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (311869343 / 500000000) ≤ -Real.log (1000000 / 1865891) ∧
    -Real.log (1000000 / 1865891) ≤ (9745917 / 15625000) := by
  have h := checkLog_sound (w := (865891 / 2865891)) (n := 12)
    (lo := (311869343 / 500000000)) (hi := (9745917 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1865891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1865891 / 1000000) = 1/(1000000 / 1865891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (311869343 / 500000000) (9745917 / 15625000) (Real.log (1865891 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1865891 / 1000000) = -Real.log (1000000 / 1865891) := by
    rw [show ((1865891 / 1000000) : ℝ) = ((1000000 / 1865891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16072819 / 8000000) ≤ -Real.log (134109 / 1000000) ∧
    -Real.log (134109 / 1000000) ≤ (1004551189 / 500000000) := by
  have h := checkLog_sound (w := (115891 / 384109)) (n := 12)
    (lo := (124561603 / 200000000)) (hi := (38925501 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 134109) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 134109) = 1/(134109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1004551189 / 500000000) (-16072819 / 8000000) (Real.log (134109 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (312419983 / 500000000) ≤ -Real.log (1000000 / 1867947) ∧
    -Real.log (1000000 / 1867947) ≤ (624839967 / 1000000000) := by
  have h := checkLog_sound (w := (867947 / 2867947)) (n := 12)
    (lo := (312419983 / 500000000)) (hi := (624839967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1867947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1867947 / 1000000) = 1/(1000000 / 1867947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (312419983 / 500000000) (624839967 / 1000000000) (Real.log (1867947 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1867947 / 1000000) = -Real.log (1000000 / 1867947) := by
    rw [show ((1867947 / 1000000) : ℝ) = ((1000000 / 1867947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25306899 / 12500000) ≤ -Real.log (132053 / 1000000) ∧
    -Real.log (132053 / 1000000) ≤ (2024551923 / 1000000000) := by
  have h := checkLog_sound (w := (117947 / 382053)) (n := 12)
    (lo := (15956439 / 25000000)) (hi := (638257561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 132053) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 132053) = 1/(132053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2024551923 / 1000000000) (-25306899 / 12500000) (Real.log (132053 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1354404959 / 500000000) ≤ -Real.log (500000000000 / 7505700058441) ∧
    -Real.log (500000000000 / 7505700058441) ≤ (1354404961 / 500000000) := by
  have h := checkLog_sound (w := (3505700058441 / 11505700058441)) (n := 12)
    (lo := (314684189 / 500000000)) (hi := (629368379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7505700058441 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7505700058441 / 4000000000000) = 1/(500000000000 / 7505700058441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1354404959 / 500000000) (1354404961 / 500000000) (Real.log (7505700058441 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7505700058441 / 500000000000) = -Real.log (500000000000 / 7505700058441) := by
    rw [show ((7505700058441 / 500000000000) : ℝ) = ((500000000000 / 7505700058441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2723324147 / 1000000000) ≤ -Real.log (500000000000 / 7615433932253) ∧
    -Real.log (500000000000 / 7615433932253) ≤ (2723324151 / 1000000000) := by
  have h := checkLog_sound (w := (3615433932253 / 11615433932253)) (n := 12)
    (lo := (643882607 / 1000000000)) (hi := (40242663 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7615433932253 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7615433932253 / 4000000000000) = 1/(500000000000 / 7615433932253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2723324147 / 1000000000) (2723324151 / 1000000000) (Real.log (7615433932253 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7615433932253 / 500000000000) = -Real.log (500000000000 / 7615433932253) := by
    rw [show ((7615433932253 / 500000000000) : ℝ) = ((500000000000 / 7615433932253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1316420531 / 500000000) ≤ -Real.log (500000000000 / 6956621106711) ∧
    -Real.log (500000000000 / 6956621106711) ≤ (1316420533 / 500000000) := by
  have h := checkLog_sound (w := (2956621106711 / 10956621106711)) (n := 12)
    (lo := (276699761 / 500000000)) (hi := (553399523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6956621106711 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6956621106711 / 4000000000000) = 1/(500000000000 / 6956621106711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1316420531 / 500000000) (1316420533 / 500000000) (Real.log (6956621106711 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6956621106711 / 500000000000) = -Real.log (500000000000 / 6956621106711) := by
    rw [show ((6956621106711 / 500000000000) : ℝ) = ((500000000000 / 6956621106711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1324695943 / 500000000) ≤ -Real.log (250000000000 / 3536358507569) ∧
    -Real.log (250000000000 / 3536358507569) ≤ (264939189 / 100000000) := by
  have h := checkLog_sound (w := (1536358507569 / 5536358507569)) (n := 12)
    (lo := (284975173 / 500000000)) (hi := (569950347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3536358507569 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3536358507569 / 2000000000000) = 1/(250000000000 / 3536358507569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1324695943 / 500000000) (264939189 / 100000000) (Real.log (3536358507569 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3536358507569 / 250000000000) = -Real.log (250000000000 / 3536358507569) := by
    rw [show ((3536358507569 / 250000000000) : ℝ) = ((250000000000 / 3536358507569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0195

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0196Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0196
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

theorem reflection_log_1_neg : (120058983 / 200000000) ≤ -Real.log (1280 / 2333) ∧
    -Real.log (1280 / 2333) ≤ (150073729 / 250000000) := by
  have h := checkLog_sound (w := (1053 / 3613)) (n := 12)
    (lo := (120058983 / 200000000)) (hi := (150073729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2333 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2333 / 1280) = 1/(1280 / 2333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (120058983 / 200000000) (150073729 / 250000000) (Real.log (2333 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2333 / 1280) = -Real.log (1280 / 2333) := by
    rw [show ((2333 / 1280) : ℝ) = ((1280 / 2333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (864832669 / 500000000) ≤ -Real.log (227 / 1280) ∧
    -Real.log (227 / 1280) ≤ (1729665341 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 547)) (n := 12)
    (lo := (171685489 / 500000000)) (hi := (343370979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 227) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 227) = 1/(227 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1729665341 / 1000000000) (-864832669 / 500000000) (Real.log (227 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (598664783 / 1000000000) ≤ -Real.log (3200 / 5823) ∧
    -Real.log (3200 / 5823) ≤ (37416549 / 62500000) := by
  have h := checkLog_sound (w := (2623 / 9023)) (n := 12)
    (lo := (598664783 / 1000000000)) (hi := (37416549 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5823 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5823 / 3200) = 1/(3200 / 5823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (598664783 / 1000000000) (37416549 / 62500000) (Real.log (5823 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5823 / 3200) = -Real.log (3200 / 5823) := by
    rw [show ((5823 / 3200) : ℝ) = ((3200 / 5823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1713063821 / 1000000000) ≤ -Real.log (577 / 3200) ∧
    -Real.log (577 / 3200) ≤ (107066489 / 62500000) := by
  have h := checkLog_sound (w := (223 / 1377)) (n := 12)
    (lo := (326769461 / 1000000000)) (hi := (163384731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 577) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 577) = 1/(577 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-107066489 / 62500000) (-1713063821 / 1000000000) (Real.log (577 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (99586067 / 200000000) ≤ -Real.log (640 / 1053) ∧
    -Real.log (640 / 1053) ≤ (15560323 / 31250000) := by
  have h := checkLog_sound (w := (413 / 1693)) (n := 12)
    (lo := (99586067 / 200000000)) (hi := (15560323 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1053 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1053 / 640) = 1/(640 / 1053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (99586067 / 200000000) (15560323 / 31250000) (Real.log (1053 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1053 / 640) = -Real.log (640 / 1053) := by
    rw [show ((1053 / 640) : ℝ) = ((640 / 1053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (518259079 / 500000000) ≤ -Real.log (227 / 640) ∧
    -Real.log (227 / 640) ≤ (12956477 / 12500000) := by
  have h := checkLog_sound (w := (93 / 547)) (n := 12)
    (lo := (171685489 / 500000000)) (hi := (343370979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 227) = 1/(227 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12956477 / 12500000) (-518259079 / 500000000) (Real.log (227 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (494315071 / 1000000000) ≤ -Real.log (1600 / 2623) ∧
    -Real.log (1600 / 2623) ≤ (7723673 / 15625000) := by
  have h := checkLog_sound (w := (1023 / 4223)) (n := 12)
    (lo := (494315071 / 1000000000)) (hi := (7723673 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2623 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2623 / 1600) = 1/(1600 / 2623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (494315071 / 1000000000) (7723673 / 15625000) (Real.log (2623 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2623 / 1600) = -Real.log (1600 / 2623) := by
    rw [show ((2623 / 1600) : ℝ) = ((1600 / 2623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1019916641 / 1000000000) ≤ -Real.log (577 / 1600) ∧
    -Real.log (577 / 1600) ≤ (1019916643 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 1377)) (n := 12)
    (lo := (326769461 / 1000000000)) (hi := (163384731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 577) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 577) = 1/(577 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1019916643 / 1000000000) (-1019916641 / 1000000000) (Real.log (577 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (313881217 / 500000000) ≤ -Real.log (500000 / 936707) ∧
    -Real.log (500000 / 936707) ≤ (125552487 / 200000000) := by
  have h := checkLog_sound (w := (436707 / 1436707)) (n := 12)
    (lo := (313881217 / 500000000)) (hi := (125552487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((936707 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(936707 / 500000) = 1/(500000 / 936707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (313881217 / 500000000) (125552487 / 200000000) (Real.log (936707 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (936707 / 500000) = -Real.log (500000 / 936707) := by
    rw [show ((936707 / 500000) : ℝ) = ((500000 / 936707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1033416679 / 500000000) ≤ -Real.log (63293 / 500000) ∧
    -Real.log (63293 / 500000) ≤ (2066833361 / 1000000000) := by
  have h := checkLog_sound (w := (61707 / 188293)) (n := 12)
    (lo := (340269499 / 500000000)) (hi := (680538999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 63293) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 63293) = 1/(63293 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2066833361 / 1000000000) (-1033416679 / 500000000) (Real.log (63293 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (314328329 / 500000000) ≤ -Real.log (100000 / 187509) ∧
    -Real.log (100000 / 187509) ≤ (628656659 / 1000000000) := by
  have h := checkLog_sound (w := (87509 / 287509)) (n := 12)
    (lo := (314328329 / 500000000)) (hi := (628656659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187509 / 100000) = 1/(100000 / 187509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (314328329 / 500000000) (628656659 / 1000000000) (Real.log (187509 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (187509 / 100000) = -Real.log (100000 / 187509) := by
    rw [show ((187509 / 100000) : ℝ) = ((100000 / 187509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2080161799 / 1000000000) ≤ -Real.log (12491 / 100000) ∧
    -Real.log (12491 / 100000) ≤ (2080161803 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 24991)) (n := 12)
    (lo := (720259 / 1000000000)) (hi := (36013 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12491) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 12491) = 1/(12491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2080161803 / 1000000000) (-2080161799 / 1000000000) (Real.log (12491 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (155659853 / 250000000) ≤ -Real.log (1000000 / 1863841) ∧
    -Real.log (1000000 / 1863841) ≤ (622639413 / 1000000000) := by
  have h := checkLog_sound (w := (863841 / 2863841)) (n := 12)
    (lo := (155659853 / 250000000)) (hi := (622639413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1863841 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1863841 / 1000000) = 1/(1000000 / 1863841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (155659853 / 250000000) (622639413 / 1000000000) (Real.log (1863841 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1863841 / 1000000) = -Real.log (1000000 / 1863841) := by
    rw [show ((1863841 / 1000000) : ℝ) = ((1000000 / 1863841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1993931957 / 1000000000) ≤ -Real.log (136159 / 1000000) ∧
    -Real.log (136159 / 1000000) ≤ (49848299 / 25000000) := by
  have h := checkLog_sound (w := (113841 / 386159)) (n := 12)
    (lo := (607637597 / 1000000000)) (hi := (303818799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 136159) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 136159) = 1/(136159 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-49848299 / 25000000) (-1993931957 / 1000000000) (Real.log (136159 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (311869611 / 500000000) ≤ -Real.log (250000 / 466473) ∧
    -Real.log (250000 / 466473) ≤ (623739223 / 1000000000) := by
  have h := checkLog_sound (w := (216473 / 716473)) (n := 12)
    (lo := (311869611 / 500000000)) (hi := (623739223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((466473 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(466473 / 250000) = 1/(250000 / 466473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (311869611 / 500000000) (623739223 / 1000000000) (Real.log (466473 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (466473 / 250000) = -Real.log (250000 / 466473) := by
    rw [show ((466473 / 250000) : ℝ) = ((250000 / 466473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (251138729 / 125000000) ≤ -Real.log (33527 / 250000) ∧
    -Real.log (33527 / 250000) ≤ (401821967 / 200000000) := by
  have h := checkLog_sound (w := (28973 / 96027)) (n := 12)
    (lo := (38925967 / 62500000)) (hi := (622815473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33527) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 33527) = 1/(33527 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-401821967 / 200000000) (-251138729 / 125000000) (Real.log (33527 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2694595793 / 1000000000) ≤ -Real.log (125000000000 / 1849941936707) ∧
    -Real.log (125000000000 / 1849941936707) ≤ (2694595797 / 1000000000) := by
  have h := checkLog_sound (w := (849941936707 / 2849941936707)) (n := 12)
    (lo := (615154253 / 1000000000)) (hi := (307577127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1849941936707 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1849941936707 / 1000000000000) = 1/(125000000000 / 1849941936707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2694595793 / 1000000000) (2694595797 / 1000000000) (Real.log (1849941936707 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1849941936707 / 125000000000) = -Real.log (125000000000 / 1849941936707) := by
    rw [show ((1849941936707 / 125000000000) : ℝ) = ((125000000000 / 1849941936707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2708818457 / 1000000000) ≤ -Real.log (500000000000 / 7505764150189) ∧
    -Real.log (500000000000 / 7505764150189) ≤ (2708818461 / 1000000000) := by
  have h := checkLog_sound (w := (3505764150189 / 11505764150189)) (n := 12)
    (lo := (629376917 / 1000000000)) (hi := (314688459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7505764150189 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7505764150189 / 4000000000000) = 1/(500000000000 / 7505764150189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2708818457 / 1000000000) (2708818461 / 1000000000) (Real.log (7505764150189 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7505764150189 / 500000000000) = -Real.log (500000000000 / 7505764150189) := by
    rw [show ((7505764150189 / 500000000000) : ℝ) = ((500000000000 / 7505764150189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2616571369 / 1000000000) ≤ -Real.log (31250000000 / 427772172607) ∧
    -Real.log (31250000000 / 427772172607) ≤ (2616571373 / 1000000000) := by
  have h := checkLog_sound (w := (177772172607 / 677772172607)) (n := 12)
    (lo := (537129829 / 1000000000)) (hi := (53712983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427772172607 / 250000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(427772172607 / 250000000000) = 1/(31250000000 / 427772172607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2616571369 / 1000000000) (2616571373 / 1000000000) (Real.log (427772172607 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (427772172607 / 31250000000) = -Real.log (31250000000 / 427772172607) := by
    rw [show ((427772172607 / 31250000000) : ℝ) = ((31250000000 / 427772172607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1316424527 / 500000000) ≤ -Real.log (20000000000 / 278267068333) ∧
    -Real.log (20000000000 / 278267068333) ≤ (1316424529 / 500000000) := by
  have h := checkLog_sound (w := (118267068333 / 438267068333)) (n := 12)
    (lo := (276703757 / 500000000)) (hi := (110681503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278267068333 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(278267068333 / 160000000000) = 1/(20000000000 / 278267068333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1316424527 / 500000000) (1316424529 / 500000000) (Real.log (278267068333 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (278267068333 / 20000000000) = -Real.log (20000000000 / 278267068333) := by
    rw [show ((278267068333 / 20000000000) : ℝ) = ((20000000000 / 278267068333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0196

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0197Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0197
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

theorem reflection_log_1_neg : (598664783 / 1000000000) ≤ -Real.log (3200 / 5823) ∧
    -Real.log (3200 / 5823) ≤ (37416549 / 62500000) := by
  have h := checkLog_sound (w := (2623 / 9023)) (n := 12)
    (lo := (598664783 / 1000000000)) (hi := (37416549 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5823 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5823 / 3200) = 1/(3200 / 5823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (598664783 / 1000000000) (37416549 / 62500000) (Real.log (5823 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5823 / 3200) = -Real.log (3200 / 5823) := by
    rw [show ((5823 / 3200) : ℝ) = ((3200 / 5823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1713063821 / 1000000000) ≤ -Real.log (577 / 3200) ∧
    -Real.log (577 / 3200) ≤ (107066489 / 62500000) := by
  have h := checkLog_sound (w := (223 / 1377)) (n := 12)
    (lo := (326769461 / 1000000000)) (hi := (163384731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 577) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 577) = 1/(577 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-107066489 / 62500000) (-1713063821 / 1000000000) (Real.log (577 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (597031989 / 1000000000) ≤ -Real.log (6400 / 11627) ∧
    -Real.log (6400 / 11627) ≤ (59703199 / 100000000) := by
  have h := checkLog_sound (w := (5227 / 18027)) (n := 12)
    (lo := (597031989 / 1000000000)) (hi := (59703199 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11627 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11627 / 6400) = 1/(6400 / 11627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (597031989 / 1000000000) (59703199 / 100000000) (Real.log (11627 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11627 / 6400) = -Real.log (6400 / 11627) := by
    rw [show ((11627 / 6400) : ℝ) = ((6400 / 11627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1696733419 / 1000000000) ≤ -Real.log (1173 / 6400) ∧
    -Real.log (1173 / 6400) ≤ (848366711 / 500000000) := by
  have h := checkLog_sound (w := (427 / 2773)) (n := 12)
    (lo := (310439059 / 1000000000)) (hi := (15521953 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1173) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1173) = 1/(1173 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-848366711 / 500000000) (-1696733419 / 1000000000) (Real.log (1173 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (494315071 / 1000000000) ≤ -Real.log (1600 / 2623) ∧
    -Real.log (1600 / 2623) ≤ (7723673 / 15625000) := by
  have h := checkLog_sound (w := (1023 / 4223)) (n := 12)
    (lo := (494315071 / 1000000000)) (hi := (7723673 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2623 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2623 / 1600) = 1/(1600 / 2623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (494315071 / 1000000000) (7723673 / 15625000) (Real.log (2623 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2623 / 1600) = -Real.log (1600 / 2623) := by
    rw [show ((2623 / 1600) : ℝ) = ((1600 / 2623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1019916641 / 1000000000) ≤ -Real.log (577 / 1600) ∧
    -Real.log (577 / 1600) ≤ (1019916643 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 1377)) (n := 12)
    (lo := (326769461 / 1000000000)) (hi := (163384731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 577) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 577) = 1/(577 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1019916643 / 1000000000) (-1019916641 / 1000000000) (Real.log (577 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (490686689 / 1000000000) ≤ -Real.log (3200 / 5227) ∧
    -Real.log (3200 / 5227) ≤ (49068669 / 100000000) := by
  have h := checkLog_sound (w := (2027 / 8427)) (n := 12)
    (lo := (490686689 / 1000000000)) (hi := (49068669 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5227 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5227 / 3200) = 1/(3200 / 5227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (490686689 / 1000000000) (49068669 / 100000000) (Real.log (5227 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5227 / 3200) = -Real.log (3200 / 5227) := by
    rw [show ((5227 / 3200) : ℝ) = ((3200 / 5227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1003586239 / 1000000000) ≤ -Real.log (1173 / 3200) ∧
    -Real.log (1173 / 3200) ≤ (1003586241 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 2773)) (n := 12)
    (lo := (310439059 / 1000000000)) (hi := (15521953 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1173) = 1/(1173 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1003586241 / 1000000000) (-1003586239 / 1000000000) (Real.log (1173 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (62687489 / 100000000) ≤ -Real.log (125000 / 233969) ∧
    -Real.log (125000 / 233969) ≤ (626874891 / 1000000000) := by
  have h := checkLog_sound (w := (108969 / 358969)) (n := 12)
    (lo := (62687489 / 100000000)) (hi := (626874891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233969 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233969 / 125000) = 1/(125000 / 233969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (62687489 / 100000000) (626874891 / 1000000000) (Real.log (233969 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (233969 / 125000) = -Real.log (125000 / 233969) := by
    rw [show ((233969 / 125000) : ℝ) = ((125000 / 233969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (513447347 / 250000000) ≤ -Real.log (16031 / 125000) ∧
    -Real.log (16031 / 125000) ≤ (2053789391 / 1000000000) := by
  have h := checkLog_sound (w := (15219 / 47281)) (n := 12)
    (lo := (166873757 / 250000000)) (hi := (667495029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16031) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 16031) = 1/(16031 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2053789391 / 1000000000) (-513447347 / 250000000) (Real.log (16031 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (78470371 / 125000000) ≤ -Real.log (200000 / 374683) ∧
    -Real.log (200000 / 374683) ≤ (627762969 / 1000000000) := by
  have h := checkLog_sound (w := (174683 / 574683)) (n := 12)
    (lo := (78470371 / 125000000)) (hi := (627762969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374683 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374683 / 200000) = 1/(200000 / 374683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (78470371 / 125000000) (627762969 / 1000000000) (Real.log (374683 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (374683 / 200000) = -Real.log (200000 / 374683) := by
    rw [show ((374683 / 200000) : ℝ) = ((200000 / 374683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1033420629 / 500000000) ≤ -Real.log (25317 / 200000) ∧
    -Real.log (25317 / 200000) ≤ (2066841261 / 1000000000) := by
  have h := checkLog_sound (w := (24683 / 75317)) (n := 12)
    (lo := (340273449 / 500000000)) (hi := (680546899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 25317) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 25317) = 1/(25317 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2066841261 / 1000000000) (-1033420629 / 500000000) (Real.log (25317 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (621540539 / 1000000000) ≤ -Real.log (500000 / 930897) ∧
    -Real.log (500000 / 930897) ≤ (31077027 / 50000000) := by
  have h := checkLog_sound (w := (430897 / 1430897)) (n := 12)
    (lo := (621540539 / 1000000000)) (hi := (31077027 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((930897 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(930897 / 500000) = 1/(500000 / 930897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (621540539 / 1000000000) (31077027 / 50000000) (Real.log (930897 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (930897 / 500000) = -Real.log (500000 / 930897) := by
    rw [show ((930897 / 500000) : ℝ) = ((500000 / 930897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (61844061 / 31250000) ≤ -Real.log (69103 / 500000) ∧
    -Real.log (69103 / 500000) ≤ (395801991 / 200000000) := by
  have h := checkLog_sound (w := (55897 / 194103)) (n := 12)
    (lo := (74089449 / 125000000)) (hi := (592715593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 69103) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 69103) = 1/(69103 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-395801991 / 200000000) (-61844061 / 31250000) (Real.log (69103 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (155659987 / 250000000) ≤ -Real.log (500000 / 931921) ∧
    -Real.log (500000 / 931921) ≤ (622639949 / 1000000000) := by
  have h := checkLog_sound (w := (431921 / 1431921)) (n := 12)
    (lo := (155659987 / 250000000)) (hi := (622639949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((931921 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(931921 / 500000) = 1/(500000 / 931921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (155659987 / 250000000) (622639949 / 1000000000) (Real.log (931921 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (931921 / 500000) = -Real.log (500000 / 931921) := by
    rw [show ((931921 / 500000) : ℝ) = ((500000 / 931921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1993939301 / 1000000000) ≤ -Real.log (68079 / 500000) ∧
    -Real.log (68079 / 500000) ≤ (249242413 / 125000000) := by
  have h := checkLog_sound (w := (56921 / 193079)) (n := 12)
    (lo := (607644941 / 1000000000)) (hi := (303822471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 68079) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 68079) = 1/(68079 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-249242413 / 125000000) (-1993939301 / 1000000000) (Real.log (68079 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1340332139 / 500000000) ≤ -Real.log (50000000000 / 729739255193) ∧
    -Real.log (50000000000 / 729739255193) ≤ (1340332141 / 500000000) := by
  have h := checkLog_sound (w := (329739255193 / 1129739255193)) (n := 12)
    (lo := (300611369 / 500000000)) (hi := (601222739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729739255193 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(729739255193 / 400000000000) = 1/(50000000000 / 729739255193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1340332139 / 500000000) (1340332141 / 500000000) (Real.log (729739255193 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (729739255193 / 50000000000) = -Real.log (50000000000 / 729739255193) := by
    rw [show ((729739255193 / 50000000000) : ℝ) = ((50000000000 / 729739255193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1347302113 / 500000000) ≤ -Real.log (125000000000 / 1849957538413) ∧
    -Real.log (125000000000 / 1849957538413) ≤ (269460423 / 100000000) := by
  have h := checkLog_sound (w := (849957538413 / 2849957538413)) (n := 12)
    (lo := (307581343 / 500000000)) (hi := (615162687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1849957538413 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1849957538413 / 1000000000000) = 1/(125000000000 / 1849957538413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1347302113 / 500000000) (269460423 / 100000000) (Real.log (1849957538413 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1849957538413 / 125000000000) = -Real.log (125000000000 / 1849957538413) := by
    rw [show ((1849957538413 / 125000000000) : ℝ) = ((125000000000 / 1849957538413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (260055049 / 100000000) ≤ -Real.log (125000000000 / 1683893969871) ∧
    -Real.log (125000000000 / 1683893969871) ≤ (1300275247 / 500000000) := by
  have h := checkLog_sound (w := (683893969871 / 2683893969871)) (n := 12)
    (lo := (10422179 / 20000000)) (hi := (521108951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683893969871 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1683893969871 / 1000000000000) = 1/(125000000000 / 1683893969871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (260055049 / 100000000) (1300275247 / 500000000) (Real.log (1683893969871 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1683893969871 / 125000000000) = -Real.log (125000000000 / 1683893969871) := by
    rw [show ((1683893969871 / 125000000000) : ℝ) = ((125000000000 / 1683893969871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2616579249 / 1000000000) ≤ -Real.log (62500000000 / 855551087707) ∧
    -Real.log (62500000000 / 855551087707) ≤ (2616579253 / 1000000000) := by
  have h := checkLog_sound (w := (355551087707 / 1355551087707)) (n := 12)
    (lo := (537137709 / 1000000000)) (hi := (53713771 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855551087707 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(855551087707 / 500000000000) = 1/(62500000000 / 855551087707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2616579249 / 1000000000) (2616579253 / 1000000000) (Real.log (855551087707 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (855551087707 / 62500000000) = -Real.log (62500000000 / 855551087707) := by
    rw [show ((855551087707 / 62500000000) : ℝ) = ((62500000000 / 855551087707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0197

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0198Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0198
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

theorem reflection_log_1_neg : (597031989 / 1000000000) ≤ -Real.log (6400 / 11627) ∧
    -Real.log (6400 / 11627) ≤ (59703199 / 100000000) := by
  have h := checkLog_sound (w := (5227 / 18027)) (n := 12)
    (lo := (597031989 / 1000000000)) (hi := (59703199 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11627 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11627 / 6400) = 1/(6400 / 11627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (597031989 / 1000000000) (59703199 / 100000000) (Real.log (11627 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11627 / 6400) = -Real.log (6400 / 11627) := by
    rw [show ((11627 / 6400) : ℝ) = ((6400 / 11627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1696733419 / 1000000000) ≤ -Real.log (1173 / 6400) ∧
    -Real.log (1173 / 6400) ≤ (848366711 / 500000000) := by
  have h := checkLog_sound (w := (427 / 2773)) (n := 12)
    (lo := (310439059 / 1000000000)) (hi := (15521953 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1173) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1173) = 1/(1173 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-848366711 / 500000000) (-1696733419 / 1000000000) (Real.log (1173 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (23815861 / 40000000) ≤ -Real.log (800 / 1451) ∧
    -Real.log (800 / 1451) ≤ (297698263 / 500000000) := by
  have h := checkLog_sound (w := (651 / 2251)) (n := 12)
    (lo := (23815861 / 40000000)) (hi := (297698263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 800) = 1/(800 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (23815861 / 40000000) (297698263 / 500000000) (Real.log (1451 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1451 / 800) = -Real.log (800 / 1451) := by
    rw [show ((1451 / 800) : ℝ) = ((800 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (84033271 / 50000000) ≤ -Real.log (149 / 800) ∧
    -Real.log (149 / 800) ≤ (1680665423 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 349)) (n := 12)
    (lo := (14718553 / 50000000)) (hi := (294371061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 149) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 149) = 1/(149 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1680665423 / 1000000000) (-84033271 / 50000000) (Real.log (149 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (490686689 / 1000000000) ≤ -Real.log (3200 / 5227) ∧
    -Real.log (3200 / 5227) ≤ (49068669 / 100000000) := by
  have h := checkLog_sound (w := (2027 / 8427)) (n := 12)
    (lo := (490686689 / 1000000000)) (hi := (49068669 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5227 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5227 / 3200) = 1/(3200 / 5227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (490686689 / 1000000000) (49068669 / 100000000) (Real.log (5227 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5227 / 3200) = -Real.log (3200 / 5227) := by
    rw [show ((5227 / 3200) : ℝ) = ((3200 / 5227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1003586239 / 1000000000) ≤ -Real.log (1173 / 3200) ∧
    -Real.log (1173 / 3200) ≤ (1003586241 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 2773)) (n := 12)
    (lo := (310439059 / 1000000000)) (hi := (15521953 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1173) = 1/(1173 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1003586241 / 1000000000) (-1003586239 / 1000000000) (Real.log (1173 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97409019 / 200000000) ≤ -Real.log (400 / 651) ∧
    -Real.log (400 / 651) ≤ (60880637 / 125000000) := by
  have h := checkLog_sound (w := (251 / 1051)) (n := 12)
    (lo := (97409019 / 200000000)) (hi := (60880637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651 / 400) = 1/(400 / 651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97409019 / 200000000) (60880637 / 125000000) (Real.log (651 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (651 / 400) = -Real.log (400 / 651) := by
    rw [show ((651 / 400) : ℝ) = ((400 / 651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6171989 / 6250000) ≤ -Real.log (149 / 400) ∧
    -Real.log (149 / 400) ≤ (493759121 / 500000000) := by
  have h := checkLog_sound (w := (51 / 349)) (n := 12)
    (lo := (14718553 / 50000000)) (hi := (294371061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 149) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 149) = 1/(149 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-493759121 / 500000000) (-6171989 / 6250000) (Real.log (149 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (156498511 / 250000000) ≤ -Real.log (125000 / 233763) ∧
    -Real.log (125000 / 233763) ≤ (125198809 / 200000000) := by
  have h := checkLog_sound (w := (108763 / 358763)) (n := 12)
    (lo := (156498511 / 250000000)) (hi := (125198809 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233763 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233763 / 125000) = 1/(125000 / 233763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (156498511 / 250000000) (125198809 / 200000000) (Real.log (233763 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (233763 / 125000) = -Real.log (125000 / 233763) := by
    rw [show ((233763 / 125000) : ℝ) = ((125000 / 233763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2041021147 / 1000000000) ≤ -Real.log (16237 / 125000) ∧
    -Real.log (16237 / 125000) ≤ (40820423 / 20000000) := by
  have h := checkLog_sound (w := (15013 / 47487)) (n := 12)
    (lo := (654726787 / 1000000000)) (hi := (163681697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16237) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 16237) = 1/(16237 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-40820423 / 20000000) (-2041021147 / 1000000000) (Real.log (16237 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (19589857 / 31250000) ≤ -Real.log (1000000 / 1871753) ∧
    -Real.log (1000000 / 1871753) ≤ (25075017 / 40000000) := by
  have h := checkLog_sound (w := (871753 / 2871753)) (n := 12)
    (lo := (19589857 / 31250000)) (hi := (25075017 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1871753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1871753 / 1000000) = 1/(1000000 / 1871753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (19589857 / 31250000) (25075017 / 40000000) (Real.log (1871753 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1871753 / 1000000) = -Real.log (1000000 / 1871753) := by
    rw [show ((1871753 / 1000000) : ℝ) = ((1000000 / 1871753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (410759437 / 200000000) ≤ -Real.log (128247 / 1000000) ∧
    -Real.log (128247 / 1000000) ≤ (513449297 / 250000000) := by
  have h := checkLog_sound (w := (121753 / 378247)) (n := 12)
    (lo := (26700113 / 40000000)) (hi := (333751413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 128247) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 128247) = 1/(128247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-513449297 / 250000000) (-410759437 / 200000000) (Real.log (128247 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (124088629 / 200000000) ≤ -Real.log (125000 / 232469) ∧
    -Real.log (125000 / 232469) ≤ (310221573 / 500000000) := by
  have h := checkLog_sound (w := (107469 / 357469)) (n := 12)
    (lo := (124088629 / 200000000)) (hi := (310221573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232469 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(232469 / 125000) = 1/(125000 / 232469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (124088629 / 200000000) (310221573 / 500000000) (Real.log (232469 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (232469 / 125000) = -Real.log (125000 / 232469) := by
    rw [show ((232469 / 125000) : ℝ) = ((125000 / 232469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1964342993 / 1000000000) ≤ -Real.log (17531 / 125000) ∧
    -Real.log (17531 / 125000) ≤ (491085749 / 250000000) := by
  have h := checkLog_sound (w := (13719 / 48781)) (n := 12)
    (lo := (578048633 / 1000000000)) (hi := (289024317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17531) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 17531) = 1/(17531 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-491085749 / 250000000) (-1964342993 / 1000000000) (Real.log (17531 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (155385269 / 250000000) ≤ -Real.log (200000 / 372359) ∧
    -Real.log (200000 / 372359) ≤ (621541077 / 1000000000) := by
  have h := checkLog_sound (w := (172359 / 572359)) (n := 12)
    (lo := (155385269 / 250000000)) (hi := (621541077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372359 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372359 / 200000) = 1/(200000 / 372359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (155385269 / 250000000) (621541077 / 1000000000) (Real.log (372359 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (372359 / 200000) = -Real.log (200000 / 372359) := by
    rw [show ((372359 / 200000) : ℝ) = ((200000 / 372359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1979017187 / 1000000000) ≤ -Real.log (27641 / 200000) ∧
    -Real.log (27641 / 200000) ≤ (197901719 / 100000000) := by
  have h := checkLog_sound (w := (22359 / 77641)) (n := 12)
    (lo := (592722827 / 1000000000)) (hi := (148180707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 27641) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 27641) = 1/(27641 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-197901719 / 100000000) (-1979017187 / 1000000000) (Real.log (27641 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2667015191 / 1000000000) ≤ -Real.log (12500000000 / 179961661637) ∧
    -Real.log (12500000000 / 179961661637) ≤ (533403039 / 200000000) := by
  have h := checkLog_sound (w := (79961661637 / 279961661637)) (n := 12)
    (lo := (587573651 / 1000000000)) (hi := (146893413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179961661637 / 100000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(179961661637 / 100000000000) = 1/(12500000000 / 179961661637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2667015191 / 1000000000) (533403039 / 200000000) (Real.log (179961661637 / 12500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (179961661637 / 12500000000) = -Real.log (12500000000 / 179961661637) := by
    rw [show ((179961661637 / 12500000000) : ℝ) = ((12500000000 / 179961661637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (268067261 / 100000000) ≤ -Real.log (62500000000 / 912181668967) ∧
    -Real.log (62500000000 / 912181668967) ≤ (1340336307 / 500000000) := by
  have h := checkLog_sound (w := (412181668967 / 1412181668967)) (n := 12)
    (lo := (60123107 / 100000000)) (hi := (601231071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((912181668967 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(912181668967 / 500000000000) = 1/(62500000000 / 912181668967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (268067261 / 100000000) (1340336307 / 500000000) (Real.log (912181668967 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (912181668967 / 62500000000) = -Real.log (62500000000 / 912181668967) := by
    rw [show ((912181668967 / 62500000000) : ℝ) = ((62500000000 / 912181668967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1292393069 / 500000000) ≤ -Real.log (62500000000 / 828778306999) ∧
    -Real.log (62500000000 / 828778306999) ≤ (1292393071 / 500000000) := by
  have h := checkLog_sound (w := (328778306999 / 1328778306999)) (n := 12)
    (lo := (252672299 / 500000000)) (hi := (505344599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((828778306999 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(828778306999 / 500000000000) = 1/(62500000000 / 828778306999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1292393069 / 500000000) (1292393071 / 500000000) (Real.log (828778306999 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (828778306999 / 62500000000) = -Real.log (62500000000 / 828778306999) := by
    rw [show ((828778306999 / 62500000000) : ℝ) = ((62500000000 / 828778306999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2600558263 / 1000000000) ≤ -Real.log (250000000000 / 3367814116711) ∧
    -Real.log (250000000000 / 3367814116711) ≤ (2600558267 / 1000000000) := by
  have h := checkLog_sound (w := (1367814116711 / 5367814116711)) (n := 12)
    (lo := (521116723 / 1000000000)) (hi := (130279181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3367814116711 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3367814116711 / 2000000000000) = 1/(250000000000 / 3367814116711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2600558263 / 1000000000) (2600558267 / 1000000000) (Real.log (3367814116711 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3367814116711 / 250000000000) = -Real.log (250000000000 / 3367814116711) := by
    rw [show ((3367814116711 / 250000000000) : ℝ) = ((250000000000 / 3367814116711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0198

end


