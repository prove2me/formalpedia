-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0133Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0133Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:00:42.205977+00:00
-- url     : https://prove2.me/theorems/e949b671-82aa-4712-9449-183c46089b07
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0133Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0134Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0133Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0134Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0135Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0136Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0137Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0138Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0133Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0134Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0135Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0136Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0137Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0138Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0133Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0134Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0135Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0136Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0137Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0138Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0133Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0134Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0135Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0136Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0137Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0138Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0133Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0133
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

theorem reflection_log_1_neg : (82639523 / 125000000) ≤ -Real.log (12800 / 24793) ∧
    -Real.log (12800 / 24793) ≤ (132223237 / 200000000) := by
  have h := checkLog_sound (w := (11993 / 37593)) (n := 12)
    (lo := (82639523 / 125000000)) (hi := (132223237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24793 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24793 / 12800) = 1/(12800 / 24793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (82639523 / 125000000) (132223237 / 200000000) (Real.log (24793 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24793 / 12800) = -Real.log (12800 / 24793) := by
    rw [show ((24793 / 12800) : ℝ) = ((12800 / 24793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2763876779 / 1000000000) ≤ -Real.log (807 / 12800) ∧
    -Real.log (807 / 12800) ≤ (2763876783 / 1000000000) := by
  have h := checkLog_sound (w := (793 / 2407)) (n := 12)
    (lo := (684435239 / 1000000000)) (hi := (17110881 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 807) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 807) = 1/(807 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2763876783 / 1000000000) (-2763876779 / 1000000000) (Real.log (807 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (330366469 / 500000000) ≤ -Real.log (25600 / 49567) ∧
    -Real.log (25600 / 49567) ≤ (660732939 / 1000000000) := by
  have h := checkLog_sound (w := (23967 / 75167)) (n := 12)
    (lo := (330366469 / 500000000)) (hi := (660732939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49567 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49567 / 25600) = 1/(25600 / 49567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (330366469 / 500000000) (660732939 / 1000000000) (Real.log (49567 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49567 / 25600) = -Real.log (25600 / 49567) := by
    rw [show ((49567 / 25600) : ℝ) = ((25600 / 49567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (550434707 / 200000000) ≤ -Real.log (1633 / 25600) ∧
    -Real.log (1633 / 25600) ≤ (2752173539 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 4833)) (n := 12)
    (lo := (134546399 / 200000000)) (hi := (168182999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1633) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1633) = 1/(1633 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2752173539 / 1000000000) (-550434707 / 200000000) (Real.log (1633 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (125605031 / 200000000) ≤ -Real.log (6400 / 11993) ∧
    -Real.log (6400 / 11993) ≤ (157006289 / 250000000) := by
  have h := checkLog_sound (w := (5593 / 18393)) (n := 12)
    (lo := (125605031 / 200000000)) (hi := (157006289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11993 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11993 / 6400) = 1/(6400 / 11993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (125605031 / 200000000) (157006289 / 250000000) (Real.log (11993 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11993 / 6400) = -Real.log (6400 / 11993) := by
    rw [show ((11993 / 6400) : ℝ) = ((6400 / 11993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2070729599 / 1000000000) ≤ -Real.log (807 / 6400) ∧
    -Real.log (807 / 6400) ≤ (1035364801 / 500000000) := by
  have h := checkLog_sound (w := (793 / 2407)) (n := 12)
    (lo := (684435239 / 1000000000)) (hi := (17110881 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 807) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 807) = 1/(807 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1035364801 / 500000000) (-2070729599 / 1000000000) (Real.log (807 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (627232713 / 1000000000) ≤ -Real.log (12800 / 23967) ∧
    -Real.log (12800 / 23967) ≤ (313616357 / 500000000) := by
  have h := checkLog_sound (w := (11167 / 36767)) (n := 12)
    (lo := (627232713 / 1000000000)) (hi := (313616357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23967 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23967 / 12800) = 1/(12800 / 23967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (627232713 / 1000000000) (313616357 / 500000000) (Real.log (23967 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23967 / 12800) = -Real.log (12800 / 23967) := by
    rw [show ((23967 / 12800) : ℝ) = ((12800 / 23967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (411805271 / 200000000) ≤ -Real.log (1633 / 12800) ∧
    -Real.log (1633 / 12800) ≤ (1029513179 / 500000000) := by
  have h := checkLog_sound (w := (1567 / 4833)) (n := 12)
    (lo := (134546399 / 200000000)) (hi := (168182999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1633) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1633) = 1/(1633 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1029513179 / 500000000) (-411805271 / 200000000) (Real.log (1633 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (333672063 / 500000000) ≤ -Real.log (500000 / 974527) ∧
    -Real.log (500000 / 974527) ≤ (667344127 / 1000000000) := by
  have h := checkLog_sound (w := (474527 / 1474527)) (n := 12)
    (lo := (333672063 / 500000000)) (hi := (667344127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974527 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974527 / 500000) = 1/(500000 / 974527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (333672063 / 500000000) (667344127 / 1000000000) (Real.log (974527 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (974527 / 500000) = -Real.log (500000 / 974527) := by
    rw [show ((974527 / 500000) : ℝ) = ((500000 / 974527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (744247257 / 250000000) ≤ -Real.log (25473 / 500000) ∧
    -Real.log (25473 / 500000) ≤ (2976989033 / 1000000000) := by
  have h := checkLog_sound (w := (5777 / 56723)) (n := 12)
    (lo := (51100077 / 250000000)) (hi := (204400309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25473) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 25473) = 1/(25473 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2976989033 / 1000000000) (-744247257 / 250000000) (Real.log (25473 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (333812881 / 500000000) ≤ -Real.log (1000000 / 1949603) ∧
    -Real.log (1000000 / 1949603) ≤ (667625763 / 1000000000) := by
  have h := checkLog_sound (w := (949603 / 2949603)) (n := 12)
    (lo := (333812881 / 500000000)) (hi := (667625763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1949603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1949603 / 1000000) = 1/(1000000 / 1949603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (333812881 / 500000000) (667625763 / 1000000000) (Real.log (1949603 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1949603 / 1000000) = -Real.log (1000000 / 1949603) := by
    rw [show ((1949603 / 1000000) : ℝ) = ((1000000 / 1949603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2987823627 / 1000000000) ≤ -Real.log (50397 / 1000000) ∧
    -Real.log (50397 / 1000000) ≤ (186738977 / 62500000) := by
  have h := checkLog_sound (w := (12103 / 112897)) (n := 12)
    (lo := (215234907 / 1000000000)) (hi := (53808727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50397) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 50397) = 1/(50397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-186738977 / 62500000) (-2987823627 / 1000000000) (Real.log (50397 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (133382919 / 200000000) ≤ -Real.log (1000000 / 1948217) ∧
    -Real.log (1000000 / 1948217) ≤ (166728649 / 250000000) := by
  have h := checkLog_sound (w := (948217 / 2948217)) (n := 12)
    (lo := (133382919 / 200000000)) (hi := (166728649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1948217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1948217 / 1000000) = 1/(1000000 / 1948217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (133382919 / 200000000) (166728649 / 250000000) (Real.log (1948217 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1948217 / 1000000) = -Real.log (1000000 / 1948217) := by
    rw [show ((1948217 / 1000000) : ℝ) = ((1000000 / 1948217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1480346683 / 500000000) ≤ -Real.log (51783 / 1000000) ∧
    -Real.log (51783 / 1000000) ≤ (2960693371 / 1000000000) := by
  have h := checkLog_sound (w := (10717 / 114283)) (n := 12)
    (lo := (94052323 / 500000000)) (hi := (188104647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51783) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 51783) = 1/(51783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2960693371 / 1000000000) (-1480346683 / 500000000) (Real.log (51783 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (16680191 / 25000000) ≤ -Real.log (250000 / 487197) ∧
    -Real.log (250000 / 487197) ≤ (667207641 / 1000000000) := by
  have h := checkLog_sound (w := (237197 / 737197)) (n := 12)
    (lo := (16680191 / 25000000)) (hi := (667207641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487197 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487197 / 250000) = 1/(250000 / 487197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (16680191 / 25000000) (667207641 / 1000000000) (Real.log (487197 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (487197 / 250000) = -Real.log (250000 / 487197) := by
    rw [show ((487197 / 250000) : ℝ) = ((250000 / 487197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2971781397 / 1000000000) ≤ -Real.log (12803 / 250000) ∧
    -Real.log (12803 / 250000) ≤ (1485890701 / 500000000) := by
  have h := checkLog_sound (w := (1411 / 14214)) (n := 12)
    (lo := (199192677 / 1000000000)) (hi := (99596339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12803) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 12803) = 1/(12803 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1485890701 / 500000000) (-2971781397 / 1000000000) (Real.log (12803 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1822166577 / 500000000) ≤ -Real.log (20000000000 / 765145055549) ∧
    -Real.log (20000000000 / 765145055549) ≤ (91108329 / 25000000) := by
  have h := checkLog_sound (w := (125145055549 / 1405145055549)) (n := 12)
    (lo := (89298627 / 500000000)) (hi := (35719451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765145055549 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(765145055549 / 640000000000) = 1/(20000000000 / 765145055549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1822166577 / 500000000) (91108329 / 25000000) (Real.log (765145055549 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (765145055549 / 20000000000) = -Real.log (20000000000 / 765145055549) := by
    rw [show ((765145055549 / 20000000000) : ℝ) = ((20000000000 / 765145055549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (913862347 / 250000000) ≤ -Real.log (500000000000 / 19342450939541) ∧
    -Real.log (500000000000 / 19342450939541) ≤ (1827724697 / 500000000) := by
  have h := checkLog_sound (w := (3342450939541 / 35342450939541)) (n := 12)
    (lo := (11857093 / 62500000)) (hi := (189713489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19342450939541 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19342450939541 / 16000000000000) = 1/(500000000000 / 19342450939541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (913862347 / 250000000) (1827724697 / 500000000) (Real.log (19342450939541 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (19342450939541 / 500000000000) = -Real.log (500000000000 / 19342450939541) := by
    rw [show ((19342450939541 / 500000000000) : ℝ) = ((500000000000 / 19342450939541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3627607961 / 1000000000) ≤ -Real.log (500000000000 / 18811357009057) ∧
    -Real.log (500000000000 / 18811357009057) ≤ (3627607967 / 1000000000) := by
  have h := checkLog_sound (w := (2811357009057 / 34811357009057)) (n := 12)
    (lo := (161872061 / 1000000000)) (hi := (80936031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18811357009057 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18811357009057 / 16000000000000) = 1/(500000000000 / 18811357009057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3627607961 / 1000000000) (3627607967 / 1000000000) (Real.log (18811357009057 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (18811357009057 / 500000000000) = -Real.log (500000000000 / 18811357009057) := by
    rw [show ((18811357009057 / 500000000000) : ℝ) = ((500000000000 / 18811357009057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3638989037 / 1000000000) ≤ -Real.log (250000000000 / 9513336717957) ∧
    -Real.log (250000000000 / 9513336717957) ≤ (3638989043 / 1000000000) := by
  have h := checkLog_sound (w := (1513336717957 / 17513336717957)) (n := 12)
    (lo := (173253137 / 1000000000)) (hi := (86626569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9513336717957 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9513336717957 / 8000000000000) = 1/(250000000000 / 9513336717957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3638989037 / 1000000000) (3638989043 / 1000000000) (Real.log (9513336717957 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9513336717957 / 250000000000) = -Real.log (250000000000 / 9513336717957) := by
    rw [show ((9513336717957 / 250000000000) : ℝ) = ((250000000000 / 9513336717957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0133

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0134Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0134
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

theorem reflection_log_1_neg : (330366469 / 500000000) ≤ -Real.log (25600 / 49567) ∧
    -Real.log (25600 / 49567) ≤ (660732939 / 1000000000) := by
  have h := checkLog_sound (w := (23967 / 75167)) (n := 12)
    (lo := (330366469 / 500000000)) (hi := (660732939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49567 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49567 / 25600) = 1/(25600 / 49567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (330366469 / 500000000) (660732939 / 1000000000) (Real.log (49567 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49567 / 25600) = -Real.log (25600 / 49567) := by
    rw [show ((49567 / 25600) : ℝ) = ((25600 / 49567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (550434707 / 200000000) ≤ -Real.log (1633 / 25600) ∧
    -Real.log (1633 / 25600) ≤ (2752173539 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 4833)) (n := 12)
    (lo := (134546399 / 200000000)) (hi := (168182999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1633) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1633) = 1/(1633 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2752173539 / 1000000000) (-550434707 / 200000000) (Real.log (1633 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132069909 / 200000000) ≤ -Real.log (6400 / 12387) ∧
    -Real.log (6400 / 12387) ≤ (330174773 / 500000000) := by
  have h := checkLog_sound (w := (5987 / 18787)) (n := 12)
    (lo := (132069909 / 200000000)) (hi := (330174773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12387 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12387 / 6400) = 1/(6400 / 12387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132069909 / 200000000) (330174773 / 500000000) (Real.log (12387 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12387 / 6400) = -Real.log (6400 / 12387) := by
    rw [show ((12387 / 6400) : ℝ) = ((6400 / 12387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1370302837 / 500000000) ≤ -Real.log (413 / 6400) ∧
    -Real.log (413 / 6400) ≤ (1370302839 / 500000000) := by
  have h := checkLog_sound (w := (387 / 1213)) (n := 12)
    (lo := (330582067 / 500000000)) (hi := (132232827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 413) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 413) = 1/(413 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1370302839 / 500000000) (-1370302837 / 500000000) (Real.log (413 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (627232713 / 1000000000) ≤ -Real.log (12800 / 23967) ∧
    -Real.log (12800 / 23967) ≤ (313616357 / 500000000) := by
  have h := checkLog_sound (w := (11167 / 36767)) (n := 12)
    (lo := (627232713 / 1000000000)) (hi := (313616357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23967 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23967 / 12800) = 1/(12800 / 23967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (627232713 / 1000000000) (313616357 / 500000000) (Real.log (23967 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23967 / 12800) = -Real.log (12800 / 23967) := by
    rw [show ((23967 / 12800) : ℝ) = ((12800 / 23967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (411805271 / 200000000) ≤ -Real.log (1633 / 12800) ∧
    -Real.log (1633 / 12800) ≤ (1029513179 / 500000000) := by
  have h := checkLog_sound (w := (1567 / 4833)) (n := 12)
    (lo := (134546399 / 200000000)) (hi := (168182999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1633) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1633) = 1/(1633 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1029513179 / 500000000) (-411805271 / 200000000) (Real.log (1633 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (313219821 / 500000000) ≤ -Real.log (3200 / 5987) ∧
    -Real.log (3200 / 5987) ≤ (626439643 / 1000000000) := by
  have h := checkLog_sound (w := (2787 / 9187)) (n := 12)
    (lo := (313219821 / 500000000)) (hi := (626439643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5987 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5987 / 3200) = 1/(3200 / 5987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (313219821 / 500000000) (626439643 / 1000000000) (Real.log (5987 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5987 / 3200) = -Real.log (3200 / 5987) := by
    rw [show ((5987 / 3200) : ℝ) = ((3200 / 5987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1023729247 / 500000000) ≤ -Real.log (413 / 3200) ∧
    -Real.log (413 / 3200) ≤ (2047458497 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 1213)) (n := 12)
    (lo := (330582067 / 500000000)) (hi := (132232827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 413) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 413) = 1/(413 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2047458497 / 1000000000) (-1023729247 / 500000000) (Real.log (413 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (333531719 / 500000000) ≤ -Real.log (1000000 / 1948507) ∧
    -Real.log (1000000 / 1948507) ≤ (667063439 / 1000000000) := by
  have h := checkLog_sound (w := (948507 / 2948507)) (n := 12)
    (lo := (333531719 / 500000000)) (hi := (667063439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1948507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1948507 / 1000000) = 1/(1000000 / 1948507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (333531719 / 500000000) (667063439 / 1000000000) (Real.log (1948507 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1948507 / 1000000) = -Real.log (1000000 / 1948507) := by
    rw [show ((1948507 / 1000000) : ℝ) = ((1000000 / 1948507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (14831547 / 5000000) ≤ -Real.log (51493 / 1000000) ∧
    -Real.log (51493 / 1000000) ≤ (593261881 / 200000000) := by
  have h := checkLog_sound (w := (11007 / 113993)) (n := 12)
    (lo := (4843017 / 25000000)) (hi := (193720681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51493) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 51493) = 1/(51493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-593261881 / 200000000) (-14831547 / 5000000) (Real.log (51493 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (667344639 / 1000000000) ≤ -Real.log (200000 / 389811) ∧
    -Real.log (200000 / 389811) ≤ (521363 / 781250) := by
  have h := checkLog_sound (w := (189811 / 589811)) (n := 12)
    (lo := (667344639 / 1000000000)) (hi := (521363 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389811 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389811 / 200000) = 1/(200000 / 389811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (667344639 / 1000000000) (521363 / 781250) (Real.log (389811 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (389811 / 200000) = -Real.log (200000 / 389811) := by
    rw [show ((389811 / 200000) : ℝ) = ((200000 / 389811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2977008657 / 1000000000) ≤ -Real.log (10189 / 200000) ∧
    -Real.log (10189 / 200000) ≤ (1488504331 / 500000000) := by
  have h := checkLog_sound (w := (2311 / 22689)) (n := 12)
    (lo := (204419937 / 1000000000)) (hi := (102209969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10189) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 10189) = 1/(10189 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1488504331 / 500000000) (-2977008657 / 1000000000) (Real.log (10189 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (66662249 / 100000000) ≤ -Real.log (15625 / 30432) ∧
    -Real.log (15625 / 30432) ≤ (666622491 / 1000000000) := by
  have h := checkLog_sound (w := (14807 / 46057)) (n := 12)
    (lo := (66662249 / 100000000)) (hi := (666622491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30432 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30432 / 15625) = 1/(15625 / 30432) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (66662249 / 100000000) (666622491 / 1000000000) (Real.log (30432 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (30432 / 15625) = -Real.log (15625 / 30432) := by
    rw [show ((30432 / 15625) : ℝ) = ((15625 / 30432) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (589953027 / 200000000) ≤ -Real.log (818 / 15625) ∧
    -Real.log (818 / 15625) ≤ (147488257 / 50000000) := by
  have h := checkLog_sound (w := (2537 / 28713)) (n := 12)
    (lo := (35435283 / 200000000)) (hi := (5536763 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13088) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 13088) = 1/(818 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-147488257 / 50000000) (-589953027 / 200000000) (Real.log (818 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (166728777 / 250000000) ≤ -Real.log (500000 / 974109) ∧
    -Real.log (500000 / 974109) ≤ (666915109 / 1000000000) := by
  have h := checkLog_sound (w := (474109 / 1474109)) (n := 12)
    (lo := (166728777 / 250000000)) (hi := (666915109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974109 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974109 / 500000) = 1/(500000 / 974109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (166728777 / 250000000) (666915109 / 1000000000) (Real.log (974109 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (974109 / 500000) = -Real.log (500000 / 974109) := by
    rw [show ((974109 / 500000) : ℝ) = ((500000 / 974109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1480356339 / 500000000) ≤ -Real.log (25891 / 500000) ∧
    -Real.log (25891 / 500000) ≤ (2960712683 / 1000000000) := by
  have h := checkLog_sound (w := (5359 / 57141)) (n := 12)
    (lo := (94061979 / 500000000)) (hi := (188123959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25891) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 25891) = 1/(25891 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2960712683 / 1000000000) (-1480356339 / 500000000) (Real.log (25891 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1816686419 / 500000000) ≤ -Real.log (100000000000 / 3784023071097) ∧
    -Real.log (100000000000 / 3784023071097) ≤ (908343211 / 250000000) := by
  have h := checkLog_sound (w := (584023071097 / 6984023071097)) (n := 12)
    (lo := (83818469 / 500000000)) (hi := (167636939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3784023071097 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3784023071097 / 3200000000000) = 1/(100000000000 / 3784023071097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1816686419 / 500000000) (908343211 / 250000000) (Real.log (3784023071097 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3784023071097 / 100000000000) = -Real.log (100000000000 / 3784023071097) := by
    rw [show ((3784023071097 / 100000000000) : ℝ) = ((100000000000 / 3784023071097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (227772081 / 62500000) ≤ -Real.log (250000000000 / 9564505839631) ∧
    -Real.log (250000000000 / 9564505839631) ≤ (1822176651 / 500000000) := by
  have h := checkLog_sound (w := (1564505839631 / 17564505839631)) (n := 12)
    (lo := (44654349 / 250000000)) (hi := (178617397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9564505839631 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9564505839631 / 8000000000000) = 1/(250000000000 / 9564505839631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (227772081 / 62500000) (1822176651 / 500000000) (Real.log (9564505839631 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9564505839631 / 250000000000) = -Real.log (250000000000 / 9564505839631) := by
    rw [show ((9564505839631 / 250000000000) : ℝ) = ((250000000000 / 9564505839631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (28931101 / 8000000) ≤ -Real.log (100000000000 / 3720293398533) ∧
    -Real.log (100000000000 / 3720293398533) ≤ (3616387631 / 1000000000) := by
  have h := checkLog_sound (w := (520293398533 / 6920293398533)) (n := 12)
    (lo := (6026069 / 40000000)) (hi := (75325863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3720293398533 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3720293398533 / 3200000000000) = 1/(100000000000 / 3720293398533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (28931101 / 8000000) (3616387631 / 1000000000) (Real.log (3720293398533 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3720293398533 / 100000000000) = -Real.log (100000000000 / 3720293398533) := by
    rw [show ((3720293398533 / 100000000000) : ℝ) = ((100000000000 / 3720293398533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1813813893 / 500000000) ≤ -Real.log (500000000000 / 18811729944769) ∧
    -Real.log (500000000000 / 18811729944769) ≤ (226726737 / 62500000) := by
  have h := checkLog_sound (w := (2811729944769 / 34811729944769)) (n := 12)
    (lo := (80945943 / 500000000)) (hi := (161891887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18811729944769 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18811729944769 / 16000000000000) = 1/(500000000000 / 18811729944769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1813813893 / 500000000) (226726737 / 62500000) (Real.log (18811729944769 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (18811729944769 / 500000000000) = -Real.log (500000000000 / 18811729944769) := by
    rw [show ((18811729944769 / 500000000000) : ℝ) = ((500000000000 / 18811729944769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0134

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0135Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0135
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

theorem reflection_log_1_neg : (132069909 / 200000000) ≤ -Real.log (6400 / 12387) ∧
    -Real.log (6400 / 12387) ≤ (330174773 / 500000000) := by
  have h := checkLog_sound (w := (5987 / 18787)) (n := 12)
    (lo := (132069909 / 200000000)) (hi := (330174773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12387 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12387 / 6400) = 1/(6400 / 12387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132069909 / 200000000) (330174773 / 500000000) (Real.log (12387 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12387 / 6400) = -Real.log (6400 / 12387) := by
    rw [show ((12387 / 6400) : ℝ) = ((6400 / 12387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1370302837 / 500000000) ≤ -Real.log (413 / 6400) ∧
    -Real.log (413 / 6400) ≤ (1370302839 / 500000000) := by
  have h := checkLog_sound (w := (387 / 1213)) (n := 12)
    (lo := (330582067 / 500000000)) (hi := (132232827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 413) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 413) = 1/(413 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1370302839 / 500000000) (-1370302837 / 500000000) (Real.log (413 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (131993201 / 200000000) ≤ -Real.log (25600 / 49529) ∧
    -Real.log (25600 / 49529) ≤ (329983003 / 500000000) := by
  have h := checkLog_sound (w := (23929 / 75129)) (n := 12)
    (lo := (131993201 / 200000000)) (hi := (329983003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49529 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49529 / 25600) = 1/(25600 / 49529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (131993201 / 200000000) (329983003 / 500000000) (Real.log (49529 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49529 / 25600) = -Real.log (25600 / 49529) := by
    rw [show ((49529 / 25600) : ℝ) = ((25600 / 49529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (27291701 / 10000000) ≤ -Real.log (1671 / 25600) ∧
    -Real.log (1671 / 25600) ≤ (341146263 / 125000000) := by
  have h := checkLog_sound (w := (1529 / 4871)) (n := 12)
    (lo := (8121607 / 12500000)) (hi := (649728561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1671) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1671) = 1/(1671 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-341146263 / 125000000) (-27291701 / 10000000) (Real.log (1671 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (313219821 / 500000000) ≤ -Real.log (3200 / 5987) ∧
    -Real.log (3200 / 5987) ≤ (626439643 / 1000000000) := by
  have h := checkLog_sound (w := (2787 / 9187)) (n := 12)
    (lo := (313219821 / 500000000)) (hi := (626439643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5987 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5987 / 3200) = 1/(3200 / 5987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (313219821 / 500000000) (626439643 / 1000000000) (Real.log (5987 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5987 / 3200) = -Real.log (3200 / 5987) := by
    rw [show ((5987 / 3200) : ℝ) = ((3200 / 5987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1023729247 / 500000000) ≤ -Real.log (413 / 3200) ∧
    -Real.log (413 / 3200) ≤ (2047458497 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 1213)) (n := 12)
    (lo := (330582067 / 500000000)) (hi := (132232827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 413) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 413) = 1/(413 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2047458497 / 1000000000) (-1023729247 / 500000000) (Real.log (413 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (625645941 / 1000000000) ≤ -Real.log (12800 / 23929) ∧
    -Real.log (12800 / 23929) ≤ (312822971 / 500000000) := by
  have h := checkLog_sound (w := (11129 / 36729)) (n := 12)
    (lo := (625645941 / 1000000000)) (hi := (312822971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23929 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23929 / 12800) = 1/(12800 / 23929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (625645941 / 1000000000) (312822971 / 500000000) (Real.log (23929 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23929 / 12800) = -Real.log (12800 / 23929) := by
    rw [show ((23929 / 12800) : ℝ) = ((12800 / 23929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50900573 / 25000000) ≤ -Real.log (1671 / 12800) ∧
    -Real.log (1671 / 12800) ≤ (2036022923 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 4871)) (n := 12)
    (lo := (8121607 / 12500000)) (hi := (649728561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1671) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1671) = 1/(1671 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2036022923 / 1000000000) (-50900573 / 25000000) (Real.log (1671 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (666783697 / 1000000000) ≤ -Real.log (500000 / 973981) ∧
    -Real.log (500000 / 973981) ≤ (333391849 / 500000000) := by
  have h := checkLog_sound (w := (473981 / 1473981)) (n := 12)
    (lo := (666783697 / 1000000000)) (hi := (333391849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973981 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973981 / 500000) = 1/(500000 / 973981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (666783697 / 1000000000) (333391849 / 500000000) (Real.log (973981 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (973981 / 500000) = -Real.log (500000 / 973981) := by
    rw [show ((973981 / 500000) : ℝ) = ((500000 / 973981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (591156211 / 200000000) ≤ -Real.log (26019 / 500000) ∧
    -Real.log (26019 / 500000) ≤ (147789053 / 50000000) := by
  have h := checkLog_sound (w := (5231 / 57269)) (n := 12)
    (lo := (36638467 / 200000000)) (hi := (11449521 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26019) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 26019) = 1/(26019 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-147789053 / 50000000) (-591156211 / 200000000) (Real.log (26019 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (667063951 / 1000000000) ≤ -Real.log (250000 / 487127) ∧
    -Real.log (250000 / 487127) ≤ (41691497 / 62500000) := by
  have h := checkLog_sound (w := (237127 / 737127)) (n := 12)
    (lo := (667063951 / 1000000000)) (hi := (41691497 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487127 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487127 / 250000) = 1/(250000 / 487127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (667063951 / 1000000000) (41691497 / 62500000) (Real.log (487127 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (487127 / 250000) = -Real.log (250000 / 487127) := by
    rw [show ((487127 / 250000) : ℝ) = ((250000 / 487127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (148316441 / 50000000) ≤ -Real.log (12873 / 250000) ∧
    -Real.log (12873 / 250000) ≤ (118653153 / 40000000) := by
  have h := checkLog_sound (w := (1376 / 14249)) (n := 12)
    (lo := (1937401 / 10000000)) (hi := (193740101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12873) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 12873) = 1/(12873 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-118653153 / 40000000) (-148316441 / 50000000) (Real.log (12873 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6663303 / 10000000) ≤ -Real.log (1000000 / 1947079) ∧
    -Real.log (1000000 / 1947079) ≤ (666330301 / 1000000000) := by
  have h := checkLog_sound (w := (947079 / 2947079)) (n := 12)
    (lo := (6663303 / 10000000)) (hi := (666330301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1947079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1947079 / 1000000) = 1/(1000000 / 1947079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6663303 / 10000000) (666330301 / 1000000000) (Real.log (1947079 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1947079 / 1000000) = -Real.log (1000000 / 1947079) := by
    rw [show ((1947079 / 1000000) : ℝ) = ((1000000 / 1947079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2938955041 / 1000000000) ≤ -Real.log (52921 / 1000000) ∧
    -Real.log (52921 / 1000000) ≤ (1469477523 / 500000000) := by
  have h := checkLog_sound (w := (9579 / 115421)) (n := 12)
    (lo := (166366321 / 1000000000)) (hi := (83183161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52921) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 52921) = 1/(52921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1469477523 / 500000000) (-2938955041 / 1000000000) (Real.log (52921 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (166655751 / 250000000) ≤ -Real.log (1000000 / 1947649) ∧
    -Real.log (1000000 / 1947649) ≤ (133324601 / 200000000) := by
  have h := checkLog_sound (w := (947649 / 2947649)) (n := 12)
    (lo := (166655751 / 250000000)) (hi := (133324601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1947649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1947649 / 1000000) = 1/(1000000 / 1947649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (166655751 / 250000000) (133324601 / 200000000) (Real.log (1947649 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1947649 / 1000000) = -Real.log (1000000 / 1947649) := by
    rw [show ((1947649 / 1000000) : ℝ) = ((1000000 / 1947649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2949784237 / 1000000000) ≤ -Real.log (52351 / 1000000) ∧
    -Real.log (52351 / 1000000) ≤ (1474892121 / 500000000) := by
  have h := checkLog_sound (w := (10149 / 114851)) (n := 12)
    (lo := (177195517 / 1000000000)) (hi := (88597759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52351) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 52351) = 1/(52351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1474892121 / 500000000) (-2949784237 / 1000000000) (Real.log (52351 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3622564753 / 1000000000) ≤ -Real.log (250000000000 / 9358363119259) ∧
    -Real.log (250000000000 / 9358363119259) ≤ (3622564759 / 1000000000) := by
  have h := checkLog_sound (w := (1358363119259 / 17358363119259)) (n := 12)
    (lo := (156828853 / 1000000000)) (hi := (78414427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9358363119259 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9358363119259 / 8000000000000) = 1/(250000000000 / 9358363119259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3622564753 / 1000000000) (3622564759 / 1000000000) (Real.log (9358363119259 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9358363119259 / 250000000000) = -Real.log (250000000000 / 9358363119259) := by
    rw [show ((9358363119259 / 250000000000) : ℝ) = ((250000000000 / 9358363119259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3633392771 / 1000000000) ≤ -Real.log (50000000000 / 1892049250369) ∧
    -Real.log (50000000000 / 1892049250369) ≤ (3633392777 / 1000000000) := by
  have h := checkLog_sound (w := (292049250369 / 3492049250369)) (n := 12)
    (lo := (167656871 / 1000000000)) (hi := (20957109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1892049250369 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1892049250369 / 1600000000000) = 1/(50000000000 / 1892049250369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3633392771 / 1000000000) (3633392777 / 1000000000) (Real.log (1892049250369 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1892049250369 / 50000000000) = -Real.log (50000000000 / 1892049250369) := by
    rw [show ((1892049250369 / 50000000000) : ℝ) = ((50000000000 / 1892049250369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3605285341 / 1000000000) ≤ -Real.log (31250000000 / 1149755649931) ∧
    -Real.log (31250000000 / 1149755649931) ≤ (3605285347 / 1000000000) := by
  have h := checkLog_sound (w := (149755649931 / 2149755649931)) (n := 12)
    (lo := (139549441 / 1000000000)) (hi := (69774721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149755649931 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1149755649931 / 1000000000000) = 1/(31250000000 / 1149755649931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3605285341 / 1000000000) (3605285347 / 1000000000) (Real.log (1149755649931 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1149755649931 / 31250000000) = -Real.log (31250000000 / 1149755649931) := by
    rw [show ((1149755649931 / 31250000000) : ℝ) = ((31250000000 / 1149755649931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3616407241 / 1000000000) ≤ -Real.log (125000000000 / 4650457966419) ∧
    -Real.log (125000000000 / 4650457966419) ≤ (3616407247 / 1000000000) := by
  have h := checkLog_sound (w := (650457966419 / 8650457966419)) (n := 12)
    (lo := (150671341 / 1000000000)) (hi := (75335671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4650457966419 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4650457966419 / 4000000000000) = 1/(125000000000 / 4650457966419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3616407241 / 1000000000) (3616407247 / 1000000000) (Real.log (4650457966419 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4650457966419 / 125000000000) = -Real.log (125000000000 / 4650457966419) := by
    rw [show ((4650457966419 / 125000000000) : ℝ) = ((125000000000 / 4650457966419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0135

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0136Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0136
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

theorem reflection_log_1_neg : (131993201 / 200000000) ≤ -Real.log (25600 / 49529) ∧
    -Real.log (25600 / 49529) ≤ (329983003 / 500000000) := by
  have h := checkLog_sound (w := (23929 / 75129)) (n := 12)
    (lo := (131993201 / 200000000)) (hi := (329983003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49529 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49529 / 25600) = 1/(25600 / 49529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (131993201 / 200000000) (329983003 / 500000000) (Real.log (49529 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49529 / 25600) = -Real.log (25600 / 49529) := by
    rw [show ((49529 / 25600) : ℝ) = ((25600 / 49529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (27291701 / 10000000) ≤ -Real.log (1671 / 25600) ∧
    -Real.log (1671 / 25600) ≤ (341146263 / 125000000) := by
  have h := checkLog_sound (w := (1529 / 4871)) (n := 12)
    (lo := (8121607 / 12500000)) (hi := (649728561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1671) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1671) = 1/(1671 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-341146263 / 125000000) (-27291701 / 10000000) (Real.log (1671 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (659582317 / 1000000000) ≤ -Real.log (2560 / 4951) ∧
    -Real.log (2560 / 4951) ≤ (329791159 / 500000000) := by
  have h := checkLog_sound (w := (2391 / 7511)) (n := 12)
    (lo := (659582317 / 1000000000)) (hi := (329791159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4951 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4951 / 2560) = 1/(2560 / 4951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (659582317 / 1000000000) (329791159 / 500000000) (Real.log (4951 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4951 / 2560) = -Real.log (2560 / 4951) := by
    rw [show ((4951 / 2560) : ℝ) = ((2560 / 4951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (135893191 / 50000000) ≤ -Real.log (169 / 2560) ∧
    -Real.log (169 / 2560) ≤ (169866489 / 62500000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 169) = 1/(169 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-169866489 / 62500000) (-135893191 / 50000000) (Real.log (169 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (625645941 / 1000000000) ≤ -Real.log (12800 / 23929) ∧
    -Real.log (12800 / 23929) ≤ (312822971 / 500000000) := by
  have h := checkLog_sound (w := (11129 / 36729)) (n := 12)
    (lo := (625645941 / 1000000000)) (hi := (312822971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23929 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23929 / 12800) = 1/(12800 / 23929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (625645941 / 1000000000) (312822971 / 500000000) (Real.log (23929 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23929 / 12800) = -Real.log (12800 / 23929) := by
    rw [show ((23929 / 12800) : ℝ) = ((12800 / 23929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (50900573 / 25000000) ≤ -Real.log (1671 / 12800) ∧
    -Real.log (1671 / 12800) ≤ (2036022923 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 4871)) (n := 12)
    (lo := (8121607 / 12500000)) (hi := (649728561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1671) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1671) = 1/(1671 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2036022923 / 1000000000) (-50900573 / 25000000) (Real.log (1671 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (62485161 / 100000000) ≤ -Real.log (1280 / 2391) ∧
    -Real.log (1280 / 2391) ≤ (624851611 / 1000000000) := by
  have h := checkLog_sound (w := (1111 / 3671)) (n := 12)
    (lo := (62485161 / 100000000)) (hi := (624851611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2391 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2391 / 1280) = 1/(1280 / 2391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (62485161 / 100000000) (624851611 / 1000000000) (Real.log (2391 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2391 / 1280) = -Real.log (1280 / 2391) := by
    rw [show ((2391 / 1280) : ℝ) = ((1280 / 2391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12654479 / 6250000) ≤ -Real.log (169 / 1280) ∧
    -Real.log (169 / 1280) ≤ (2024716643 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 169) = 1/(169 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2024716643 / 1000000000) (-12654479 / 6250000) (Real.log (169 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (666503879 / 1000000000) ≤ -Real.log (1000000 / 1947417) ∧
    -Real.log (1000000 / 1947417) ≤ (16662597 / 25000000) := by
  have h := checkLog_sound (w := (947417 / 2947417)) (n := 12)
    (lo := (666503879 / 1000000000)) (hi := (16662597 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1947417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1947417 / 1000000) = 1/(1000000 / 1947417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (666503879 / 1000000000) (16662597 / 25000000) (Real.log (1947417 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1947417 / 1000000) = -Real.log (1000000 / 1947417) := by
    rw [show ((1947417 / 1000000) : ℝ) = ((1000000 / 1947417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2945362403 / 1000000000) ≤ -Real.log (52583 / 1000000) ∧
    -Real.log (52583 / 1000000) ≤ (368170301 / 125000000) := by
  have h := checkLog_sound (w := (9917 / 115083)) (n := 12)
    (lo := (172773683 / 1000000000)) (hi := (43193421 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52583) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 52583) = 1/(52583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-368170301 / 125000000) (-2945362403 / 1000000000) (Real.log (52583 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (666784211 / 1000000000) ≤ -Real.log (1000000 / 1947963) ∧
    -Real.log (1000000 / 1947963) ≤ (166696053 / 250000000) := by
  have h := checkLog_sound (w := (947963 / 2947963)) (n := 12)
    (lo := (666784211 / 1000000000)) (hi := (166696053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1947963 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1947963 / 1000000) = 1/(1000000 / 1947963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (666784211 / 1000000000) (166696053 / 250000000) (Real.log (1947963 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1947963 / 1000000) = -Real.log (1000000 / 1947963) := by
    rw [show ((1947963 / 1000000) : ℝ) = ((1000000 / 1947963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (184737517 / 62500000) ≤ -Real.log (52037 / 1000000) ∧
    -Real.log (52037 / 1000000) ≤ (2955800277 / 1000000000) := by
  have h := checkLog_sound (w := (10463 / 114537)) (n := 12)
    (lo := (5725361 / 31250000)) (hi := (183211553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52037) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 52037) = 1/(52037 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2955800277 / 1000000000) (-184737517 / 62500000) (Real.log (52037 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (666038539 / 1000000000) ≤ -Real.log (1000000 / 1946511) ∧
    -Real.log (1000000 / 1946511) ≤ (33301927 / 50000000) := by
  have h := checkLog_sound (w := (946511 / 2946511)) (n := 12)
    (lo := (666038539 / 1000000000)) (hi := (33301927 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1946511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1946511 / 1000000) = 1/(1000000 / 1946511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (666038539 / 1000000000) (33301927 / 50000000) (Real.log (1946511 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1946511 / 1000000) = -Real.log (1000000 / 1946511) := by
    rw [show ((1946511 / 1000000) : ℝ) = ((1000000 / 1946511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2928279251 / 1000000000) ≤ -Real.log (53489 / 1000000) ∧
    -Real.log (53489 / 1000000) ≤ (366034907 / 125000000) := by
  have h := checkLog_sound (w := (9011 / 115989)) (n := 12)
    (lo := (155690531 / 1000000000)) (hi := (38922633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53489) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 53489) = 1/(53489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-366034907 / 125000000) (-2928279251 / 1000000000) (Real.log (53489 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (333165407 / 500000000) ≤ -Real.log (25000 / 48677) ∧
    -Real.log (25000 / 48677) ≤ (133266163 / 200000000) := by
  have h := checkLog_sound (w := (23677 / 73677)) (n := 12)
    (lo := (333165407 / 500000000)) (hi := (133266163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48677 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48677 / 25000) = 1/(25000 / 48677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (333165407 / 500000000) (133266163 / 200000000) (Real.log (48677 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48677 / 25000) = -Real.log (25000 / 48677) := by
    rw [show ((48677 / 25000) : ℝ) = ((25000 / 48677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2938973937 / 1000000000) ≤ -Real.log (1323 / 25000) ∧
    -Real.log (1323 / 25000) ≤ (1469486971 / 500000000) := by
  have h := checkLog_sound (w := (479 / 5771)) (n := 12)
    (lo := (166385217 / 1000000000)) (hi := (83192609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2646) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2646) = 1/(1323 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1469486971 / 500000000) (-2938973937 / 1000000000) (Real.log (1323 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3611866281 / 1000000000) ≤ -Real.log (100000000000 / 3703510640321) ∧
    -Real.log (100000000000 / 3703510640321) ≤ (3611866287 / 1000000000) := by
  have h := checkLog_sound (w := (503510640321 / 6903510640321)) (n := 12)
    (lo := (146130381 / 1000000000)) (hi := (73065191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3703510640321 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3703510640321 / 3200000000000) = 1/(100000000000 / 3703510640321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3611866281 / 1000000000) (3611866287 / 1000000000) (Real.log (3703510640321 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3703510640321 / 100000000000) = -Real.log (100000000000 / 3703510640321) := by
    rw [show ((3703510640321 / 100000000000) : ℝ) = ((100000000000 / 3703510640321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3622584483 / 1000000000) ≤ -Real.log (250000000000 / 9358547764091) ∧
    -Real.log (250000000000 / 9358547764091) ≤ (3622584489 / 1000000000) := by
  have h := checkLog_sound (w := (1358547764091 / 17358547764091)) (n := 12)
    (lo := (156848583 / 1000000000)) (hi := (19606073 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9358547764091 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9358547764091 / 8000000000000) = 1/(250000000000 / 9358547764091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3622584483 / 1000000000) (3622584489 / 1000000000) (Real.log (9358547764091 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9358547764091 / 250000000000) = -Real.log (250000000000 / 9358547764091) := by
    rw [show ((9358547764091 / 250000000000) : ℝ) = ((250000000000 / 9358547764091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (359431779 / 100000000) ≤ -Real.log (500000000000 / 18195432705789) ∧
    -Real.log (500000000000 / 18195432705789) ≤ (898579449 / 250000000) := by
  have h := checkLog_sound (w := (2195432705789 / 34195432705789)) (n := 12)
    (lo := (12858189 / 100000000)) (hi := (128581891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18195432705789 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18195432705789 / 16000000000000) = 1/(500000000000 / 18195432705789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (359431779 / 100000000) (898579449 / 250000000) (Real.log (18195432705789 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (18195432705789 / 500000000000) = -Real.log (500000000000 / 18195432705789) := by
    rw [show ((18195432705789 / 500000000000) : ℝ) = ((500000000000 / 18195432705789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3605304751 / 1000000000) ≤ -Real.log (500000000000 / 18396447467877) ∧
    -Real.log (500000000000 / 18396447467877) ≤ (3605304757 / 1000000000) := by
  have h := checkLog_sound (w := (2396447467877 / 34396447467877)) (n := 12)
    (lo := (139568851 / 1000000000)) (hi := (34892213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18396447467877 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18396447467877 / 16000000000000) = 1/(500000000000 / 18396447467877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3605304751 / 1000000000) (3605304757 / 1000000000) (Real.log (18396447467877 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (18396447467877 / 500000000000) = -Real.log (500000000000 / 18396447467877) := by
    rw [show ((18396447467877 / 500000000000) : ℝ) = ((500000000000 / 18396447467877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0136

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0137Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0137
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

theorem reflection_log_1_neg : (659582317 / 1000000000) ≤ -Real.log (2560 / 4951) ∧
    -Real.log (2560 / 4951) ≤ (329791159 / 500000000) := by
  have h := checkLog_sound (w := (2391 / 7511)) (n := 12)
    (lo := (659582317 / 1000000000)) (hi := (329791159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4951 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4951 / 2560) = 1/(2560 / 4951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (659582317 / 1000000000) (329791159 / 500000000) (Real.log (4951 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4951 / 2560) = -Real.log (2560 / 4951) := by
    rw [show ((4951 / 2560) : ℝ) = ((2560 / 4951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (135893191 / 50000000) ≤ -Real.log (169 / 2560) ∧
    -Real.log (169 / 2560) ≤ (169866489 / 62500000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 169) = 1/(169 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-169866489 / 62500000) (-135893191 / 50000000) (Real.log (169 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (659198483 / 1000000000) ≤ -Real.log (25600 / 49491) ∧
    -Real.log (25600 / 49491) ≤ (164799621 / 250000000) := by
  have h := checkLog_sound (w := (23891 / 75091)) (n := 12)
    (lo := (659198483 / 1000000000)) (hi := (164799621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49491 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49491 / 25600) = 1/(25600 / 49491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (659198483 / 1000000000) (164799621 / 250000000) (Real.log (49491 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49491 / 25600) = -Real.log (25600 / 49491) := by
    rw [show ((49491 / 25600) : ℝ) = ((25600 / 49491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (541336789 / 200000000) ≤ -Real.log (1709 / 25600) ∧
    -Real.log (1709 / 25600) ≤ (2706683949 / 1000000000) := by
  have h := checkLog_sound (w := (1491 / 4909)) (n := 12)
    (lo := (125448481 / 200000000)) (hi := (313621203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1709) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1709) = 1/(1709 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2706683949 / 1000000000) (-541336789 / 200000000) (Real.log (1709 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (62485161 / 100000000) ≤ -Real.log (1280 / 2391) ∧
    -Real.log (1280 / 2391) ≤ (624851611 / 1000000000) := by
  have h := checkLog_sound (w := (1111 / 3671)) (n := 12)
    (lo := (62485161 / 100000000)) (hi := (624851611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2391 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2391 / 1280) = 1/(1280 / 2391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (62485161 / 100000000) (624851611 / 1000000000) (Real.log (2391 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2391 / 1280) = -Real.log (1280 / 2391) := by
    rw [show ((2391 / 1280) : ℝ) = ((1280 / 2391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12654479 / 6250000) ≤ -Real.log (169 / 1280) ∧
    -Real.log (169 / 1280) ≤ (2024716643 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 169) = 1/(169 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2024716643 / 1000000000) (-12654479 / 6250000) (Real.log (169 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (78007081 / 125000000) ≤ -Real.log (12800 / 23891) ∧
    -Real.log (12800 / 23891) ≤ (624056649 / 1000000000) := by
  have h := checkLog_sound (w := (11091 / 36691)) (n := 12)
    (lo := (78007081 / 125000000)) (hi := (624056649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23891 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23891 / 12800) = 1/(12800 / 23891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (78007081 / 125000000) (624056649 / 1000000000) (Real.log (23891 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23891 / 12800) = -Real.log (12800 / 23891) := by
    rw [show ((23891 / 12800) : ℝ) = ((12800 / 23891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (402707353 / 200000000) ≤ -Real.log (1709 / 12800) ∧
    -Real.log (1709 / 12800) ≤ (3932689 / 1953125) := by
  have h := checkLog_sound (w := (1491 / 4909)) (n := 12)
    (lo := (125448481 / 200000000)) (hi := (313621203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1709) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1709) = 1/(1709 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3932689 / 1953125) (-402707353 / 200000000) (Real.log (1709 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (133244899 / 200000000) ≤ -Real.log (1000000 / 1946873) ∧
    -Real.log (1000000 / 1946873) ≤ (41639031 / 62500000) := by
  have h := checkLog_sound (w := (946873 / 2946873)) (n := 12)
    (lo := (133244899 / 200000000)) (hi := (41639031 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1946873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1946873 / 1000000) = 1/(1000000 / 1946873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (133244899 / 200000000) (41639031 / 62500000) (Real.log (1946873 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1946873 / 1000000) = -Real.log (1000000 / 1946873) := by
    rw [show ((1946873 / 1000000) : ℝ) = ((1000000 / 1946873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2935070003 / 1000000000) ≤ -Real.log (53127 / 1000000) ∧
    -Real.log (53127 / 1000000) ≤ (366883751 / 125000000) := by
  have h := checkLog_sound (w := (9373 / 115627)) (n := 12)
    (lo := (162481283 / 1000000000)) (hi := (40620321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53127) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 53127) = 1/(53127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-366883751 / 125000000) (-2935070003 / 1000000000) (Real.log (53127 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83313049 / 125000000) ≤ -Real.log (500000 / 973709) ∧
    -Real.log (500000 / 973709) ≤ (666504393 / 1000000000) := by
  have h := checkLog_sound (w := (473709 / 1473709)) (n := 12)
    (lo := (83313049 / 125000000)) (hi := (666504393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973709 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973709 / 500000) = 1/(500000 / 973709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83313049 / 125000000) (666504393 / 1000000000) (Real.log (973709 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (973709 / 500000) = -Real.log (500000 / 973709) := by
    rw [show ((973709 / 500000) : ℝ) = ((500000 / 973709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (147269071 / 50000000) ≤ -Real.log (26291 / 500000) ∧
    -Real.log (26291 / 500000) ≤ (117815257 / 40000000) := by
  have h := checkLog_sound (w := (4959 / 57541)) (n := 12)
    (lo := (1727927 / 10000000)) (hi := (172792701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26291) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 26291) = 1/(26291 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-117815257 / 40000000) (-147269071 / 50000000) (Real.log (26291 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (332873603 / 500000000) ≤ -Real.log (125000 / 243243) ∧
    -Real.log (125000 / 243243) ≤ (665747207 / 1000000000) := by
  have h := checkLog_sound (w := (118243 / 368243)) (n := 12)
    (lo := (332873603 / 500000000)) (hi := (665747207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243243 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243243 / 125000) = 1/(125000 / 243243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (332873603 / 500000000) (665747207 / 1000000000) (Real.log (243243 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (243243 / 125000) = -Real.log (125000 / 243243) := by
    rw [show ((243243 / 125000) : ℝ) = ((125000 / 243243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (291773473 / 100000000) ≤ -Real.log (6757 / 125000) ∧
    -Real.log (6757 / 125000) ≤ (583546947 / 200000000) := by
  have h := checkLog_sound (w := (2111 / 29139)) (n := 12)
    (lo := (14514601 / 100000000)) (hi := (145146011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13514) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 13514) = 1/(6757 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-583546947 / 200000000) (-291773473 / 100000000) (Real.log (6757 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (166509763 / 250000000) ≤ -Real.log (62500 / 121657) ∧
    -Real.log (62500 / 121657) ≤ (666039053 / 1000000000) := by
  have h := checkLog_sound (w := (59157 / 184157)) (n := 12)
    (lo := (166509763 / 250000000)) (hi := (666039053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121657 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121657 / 62500) = 1/(62500 / 121657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (166509763 / 250000000) (666039053 / 1000000000) (Real.log (121657 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (121657 / 62500) = -Real.log (62500 / 121657) := by
    rw [show ((121657 / 62500) : ℝ) = ((62500 / 121657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2928297947 / 1000000000) ≤ -Real.log (3343 / 62500) ∧
    -Real.log (3343 / 62500) ≤ (91509311 / 31250000) := by
  have h := checkLog_sound (w := (2253 / 28997)) (n := 12)
    (lo := (155709227 / 1000000000)) (hi := (38927307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13372) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 13372) = 1/(3343 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-91509311 / 31250000) (-2928297947 / 1000000000) (Real.log (3343 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1800647249 / 500000000) ≤ -Real.log (500000000000 / 18322820787923) ∧
    -Real.log (500000000000 / 18322820787923) ≤ (450161813 / 125000000) := by
  have h := checkLog_sound (w := (2322820787923 / 34322820787923)) (n := 12)
    (lo := (67779299 / 500000000)) (hi := (135558599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18322820787923 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18322820787923 / 16000000000000) = 1/(500000000000 / 18322820787923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1800647249 / 500000000) (450161813 / 125000000) (Real.log (18322820787923 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (18322820787923 / 500000000000) = -Real.log (500000000000 / 18322820787923) := by
    rw [show ((18322820787923 / 500000000000) : ℝ) = ((500000000000 / 18322820787923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (902971453 / 250000000) ≤ -Real.log (250000000000 / 9258957437907) ∧
    -Real.log (250000000000 / 9258957437907) ≤ (1805942909 / 500000000) := by
  have h := checkLog_sound (w := (1258957437907 / 17258957437907)) (n := 12)
    (lo := (18268739 / 125000000)) (hi := (146149913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9258957437907 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9258957437907 / 8000000000000) = 1/(250000000000 / 9258957437907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (902971453 / 250000000) (1805942909 / 500000000) (Real.log (9258957437907 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9258957437907 / 250000000000) = -Real.log (250000000000 / 9258957437907) := by
    rw [show ((9258957437907 / 250000000000) : ℝ) = ((250000000000 / 9258957437907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (223967621 / 62500000) ≤ -Real.log (20000000000 / 719973360959) ∧
    -Real.log (20000000000 / 719973360959) ≤ (1791740971 / 500000000) := by
  have h := checkLog_sound (w := (79973360959 / 1359973360959)) (n := 12)
    (lo := (29436509 / 250000000)) (hi := (117746037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719973360959 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(719973360959 / 640000000000) = 1/(20000000000 / 719973360959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (223967621 / 62500000) (1791740971 / 500000000) (Real.log (719973360959 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (719973360959 / 20000000000) = -Real.log (20000000000 / 719973360959) := by
    rw [show ((719973360959 / 20000000000) : ℝ) = ((20000000000 / 719973360959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3594336999 / 1000000000) ≤ -Real.log (500000000000 / 18195782231529) ∧
    -Real.log (500000000000 / 18195782231529) ≤ (718867401 / 200000000) := by
  have h := checkLog_sound (w := (2195782231529 / 34195782231529)) (n := 12)
    (lo := (128601099 / 1000000000)) (hi := (1286011 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18195782231529 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18195782231529 / 16000000000000) = 1/(500000000000 / 18195782231529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3594336999 / 1000000000) (718867401 / 200000000) (Real.log (18195782231529 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (18195782231529 / 500000000000) = -Real.log (500000000000 / 18195782231529) := by
    rw [show ((18195782231529 / 500000000000) : ℝ) = ((500000000000 / 18195782231529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0137

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0138Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0138
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

theorem reflection_log_1_neg : (659198483 / 1000000000) ≤ -Real.log (25600 / 49491) ∧
    -Real.log (25600 / 49491) ≤ (164799621 / 250000000) := by
  have h := checkLog_sound (w := (23891 / 75091)) (n := 12)
    (lo := (659198483 / 1000000000)) (hi := (164799621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49491 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49491 / 25600) = 1/(25600 / 49491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (659198483 / 1000000000) (164799621 / 250000000) (Real.log (49491 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49491 / 25600) = -Real.log (25600 / 49491) := by
    rw [show ((49491 / 25600) : ℝ) = ((25600 / 49491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (541336789 / 200000000) ≤ -Real.log (1709 / 25600) ∧
    -Real.log (1709 / 25600) ≤ (2706683949 / 1000000000) := by
  have h := checkLog_sound (w := (1491 / 4909)) (n := 12)
    (lo := (125448481 / 200000000)) (hi := (313621203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1709) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1709) = 1/(1709 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2706683949 / 1000000000) (-541336789 / 200000000) (Real.log (1709 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (658814501 / 1000000000) ≤ -Real.log (400 / 773) ∧
    -Real.log (400 / 773) ≤ (329407251 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1173)) (n := 12)
    (lo := (658814501 / 1000000000)) (hi := (329407251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773 / 400) = 1/(400 / 773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (658814501 / 1000000000) (329407251 / 500000000) (Real.log (773 / 400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (773 / 400) = -Real.log (400 / 773) := by
    rw [show ((773 / 400) : ℝ) = ((400 / 773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2695627679 / 1000000000) ≤ -Real.log (27 / 400) ∧
    -Real.log (27 / 400) ≤ (2695627683 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 77)) (n := 12)
    (lo := (616186139 / 1000000000)) (hi := (30809307 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(50 / 27) = 1/(27 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2695627683 / 1000000000) (-2695627679 / 1000000000) (Real.log (27 / 400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (78007081 / 125000000) ≤ -Real.log (12800 / 23891) ∧
    -Real.log (12800 / 23891) ≤ (624056649 / 1000000000) := by
  have h := checkLog_sound (w := (11091 / 36691)) (n := 12)
    (lo := (78007081 / 125000000)) (hi := (624056649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23891 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23891 / 12800) = 1/(12800 / 23891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (78007081 / 125000000) (624056649 / 1000000000) (Real.log (23891 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23891 / 12800) = -Real.log (12800 / 23891) := by
    rw [show ((23891 / 12800) : ℝ) = ((12800 / 23891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (402707353 / 200000000) ≤ -Real.log (1709 / 12800) ∧
    -Real.log (1709 / 12800) ≤ (3932689 / 1953125) := by
  have h := checkLog_sound (w := (1491 / 4909)) (n := 12)
    (lo := (125448481 / 200000000)) (hi := (313621203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1709) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1709) = 1/(1709 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3932689 / 1953125) (-402707353 / 200000000) (Real.log (1709 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (623261053 / 1000000000) ≤ -Real.log (200 / 373) ∧
    -Real.log (200 / 373) ≤ (311630527 / 500000000) := by
  have h := checkLog_sound (w := (173 / 573)) (n := 12)
    (lo := (623261053 / 1000000000)) (hi := (311630527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373 / 200) = 1/(200 / 373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (623261053 / 1000000000) (311630527 / 500000000) (Real.log (373 / 200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (373 / 200) = -Real.log (200 / 373) := by
    rw [show ((373 / 200) : ℝ) = ((200 / 373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2002480499 / 1000000000) ≤ -Real.log (27 / 200) ∧
    -Real.log (27 / 200) ≤ (1001240251 / 500000000) := by
  have h := checkLog_sound (w := (23 / 77)) (n := 12)
    (lo := (616186139 / 1000000000)) (hi := (30809307 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50 / 27) = 1/(27 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1001240251 / 500000000) (-2002480499 / 1000000000) (Real.log (27 / 200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (166486387 / 250000000) ≤ -Real.log (100000 / 194633) ∧
    -Real.log (100000 / 194633) ≤ (665945549 / 1000000000) := by
  have h := checkLog_sound (w := (94633 / 294633)) (n := 12)
    (lo := (166486387 / 250000000)) (hi := (665945549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194633 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194633 / 100000) = 1/(100000 / 194633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (166486387 / 250000000) (665945549 / 1000000000) (Real.log (194633 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (194633 / 100000) = -Real.log (100000 / 194633) := by
    rw [show ((194633 / 100000) : ℝ) = ((100000 / 194633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (292490109 / 100000000) ≤ -Real.log (5367 / 100000) ∧
    -Real.log (5367 / 100000) ≤ (584980219 / 200000000) := by
  have h := checkLog_sound (w := (883 / 11617)) (n := 12)
    (lo := (15231237 / 100000000)) (hi := (152312371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5367) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 5367) = 1/(5367 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-584980219 / 200000000) (-292490109 / 100000000) (Real.log (5367 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (666225009 / 1000000000) ≤ -Real.log (500000 / 973437) ∧
    -Real.log (500000 / 973437) ≤ (66622501 / 100000000) := by
  have h := checkLog_sound (w := (473437 / 1473437)) (n := 12)
    (lo := (666225009 / 1000000000)) (hi := (66622501 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973437 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973437 / 500000) = 1/(500000 / 973437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (666225009 / 1000000000) (66622501 / 100000000) (Real.log (973437 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (973437 / 500000) = -Real.log (500000 / 973437) := by
    rw [show ((973437 / 500000) : ℝ) = ((500000 / 973437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1467544413 / 500000000) ≤ -Real.log (26563 / 500000) ∧
    -Real.log (26563 / 500000) ≤ (2935088831 / 1000000000) := by
  have h := checkLog_sound (w := (4687 / 57813)) (n := 12)
    (lo := (81250053 / 500000000)) (hi := (162500107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26563) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 26563) = 1/(26563 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2935088831 / 1000000000) (-1467544413 / 500000000) (Real.log (26563 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (166363947 / 250000000) ≤ -Real.log (1000000 / 1945377) ∧
    -Real.log (1000000 / 1945377) ≤ (665455789 / 1000000000) := by
  have h := checkLog_sound (w := (945377 / 2945377)) (n := 12)
    (lo := (166363947 / 250000000)) (hi := (665455789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1945377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1945377 / 1000000) = 1/(1000000 / 1945377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (166363947 / 250000000) (665455789 / 1000000000) (Real.log (1945377 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1945377 / 1000000) = -Real.log (1000000 / 1945377) := by
    rw [show ((1945377 / 1000000) : ℝ) = ((1000000 / 1945377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2907300237 / 1000000000) ≤ -Real.log (54623 / 1000000) ∧
    -Real.log (54623 / 1000000) ≤ (1453650121 / 500000000) := by
  have h := checkLog_sound (w := (7877 / 117123)) (n := 12)
    (lo := (134711517 / 1000000000)) (hi := (67355759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54623) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 54623) = 1/(54623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1453650121 / 500000000) (-2907300237 / 1000000000) (Real.log (54623 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (16643693 / 25000000) ≤ -Real.log (200000 / 389189) ∧
    -Real.log (200000 / 389189) ≤ (665747721 / 1000000000) := by
  have h := checkLog_sound (w := (189189 / 589189)) (n := 12)
    (lo := (16643693 / 25000000)) (hi := (665747721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389189 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389189 / 200000) = 1/(200000 / 389189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (16643693 / 25000000) (665747721 / 1000000000) (Real.log (389189 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (389189 / 200000) = -Real.log (200000 / 389189) := by
    rw [show ((389189 / 200000) : ℝ) = ((200000 / 389189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2917753229 / 1000000000) ≤ -Real.log (10811 / 200000) ∧
    -Real.log (10811 / 200000) ≤ (1458876617 / 500000000) := by
  have h := checkLog_sound (w := (1689 / 23311)) (n := 12)
    (lo := (145164509 / 1000000000)) (hi := (14516451 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10811) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 10811) = 1/(10811 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1458876617 / 500000000) (-2917753229 / 1000000000) (Real.log (10811 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1795423319 / 500000000) ≤ -Real.log (125000000000 / 4533095770449) ∧
    -Real.log (125000000000 / 4533095770449) ≤ (897711661 / 250000000) := by
  have h := checkLog_sound (w := (533095770449 / 8533095770449)) (n := 12)
    (lo := (62555369 / 500000000)) (hi := (125110739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4533095770449 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4533095770449 / 4000000000000) = 1/(125000000000 / 4533095770449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1795423319 / 500000000) (897711661 / 250000000) (Real.log (4533095770449 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4533095770449 / 125000000000) = -Real.log (125000000000 / 4533095770449) := by
    rw [show ((4533095770449 / 125000000000) : ℝ) = ((125000000000 / 4533095770449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1800656917 / 500000000) ≤ -Real.log (20000000000 / 732927003727) ∧
    -Real.log (20000000000 / 732927003727) ≤ (45016423 / 12500000) := by
  have h := checkLog_sound (w := (92927003727 / 1372927003727)) (n := 12)
    (lo := (67788967 / 500000000)) (hi := (27115587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732927003727 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(732927003727 / 640000000000) = 1/(20000000000 / 732927003727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1800656917 / 500000000) (45016423 / 12500000) (Real.log (732927003727 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (732927003727 / 20000000000) = -Real.log (20000000000 / 732927003727) := by
    rw [show ((732927003727 / 20000000000) : ℝ) = ((20000000000 / 732927003727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (142910241 / 40000000) ≤ -Real.log (250000000000 / 8903653223001) ∧
    -Real.log (250000000000 / 8903653223001) ≤ (3572756031 / 1000000000) := by
  have h := checkLog_sound (w := (903653223001 / 16903653223001)) (n := 12)
    (lo := (856161 / 8000000)) (hi := (53510063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8903653223001 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8903653223001 / 8000000000000) = 1/(250000000000 / 8903653223001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (142910241 / 40000000) (3572756031 / 1000000000) (Real.log (8903653223001 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8903653223001 / 250000000000) = -Real.log (250000000000 / 8903653223001) := by
    rw [show ((8903653223001 / 250000000000) : ℝ) = ((250000000000 / 8903653223001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3583500949 / 1000000000) ≤ -Real.log (250000000000 / 8999838127833) ∧
    -Real.log (250000000000 / 8999838127833) ≤ (716700191 / 200000000) := by
  have h := checkLog_sound (w := (999838127833 / 16999838127833)) (n := 12)
    (lo := (117765049 / 1000000000)) (hi := (2355301 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8999838127833 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8999838127833 / 8000000000000) = 1/(250000000000 / 8999838127833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3583500949 / 1000000000) (716700191 / 200000000) (Real.log (8999838127833 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8999838127833 / 250000000000) = -Real.log (250000000000 / 8999838127833) := by
    rw [show ((8999838127833 / 250000000000) : ℝ) = ((250000000000 / 8999838127833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0138

end


