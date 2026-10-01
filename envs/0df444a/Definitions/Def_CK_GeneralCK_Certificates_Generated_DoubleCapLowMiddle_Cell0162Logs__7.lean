-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0162Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0162Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:41:57.895055+00:00
-- url     : https://prove2.me/theorems/31c8f46c-8935-4b67-ae0b-b9dd5444f490
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0162Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0163Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0162Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0163Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0164Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0165Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0166Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0167Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0168Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0162Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0163Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0164Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0165Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0166Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0167Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0168Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0162Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0163Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0164Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0165Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0166Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0167Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0168Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0162Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0163Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0164Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0165Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0166Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0167Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0168Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0162Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0162
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

theorem reflection_log_1_neg : (128822569 / 200000000) ≤ -Real.log (512 / 975) ∧
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


theorem reflection_log_1 : Bounds (128822569 / 200000000) (322056423 / 500000000) (Real.log (975 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (975 / 512) = -Real.log (512 / 975) := by
    rw [show ((975 / 512) : ℝ) = ((512 / 975) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (93860173 / 40000000) ≤ -Real.log (49 / 512) ∧
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


theorem reflection_log_2 : Bounds (-2346504329 / 1000000000) (-93860173 / 40000000) (Real.log (49 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (321666527 / 500000000) ≤ -Real.log (3200 / 6089) ∧
    -Real.log (3200 / 6089) ≤ (128666611 / 200000000) := by
  have h := checkLog_sound (w := (2889 / 9289)) (n := 12)
    (lo := (321666527 / 500000000)) (hi := (128666611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6089 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6089 / 3200) = 1/(3200 / 6089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (321666527 / 500000000) (128666611 / 200000000) (Real.log (6089 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6089 / 3200) = -Real.log (3200 / 6089) := by
    rw [show ((6089 / 3200) : ℝ) = ((3200 / 6089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1165556587 / 500000000) ≤ -Real.log (311 / 3200) ∧
    -Real.log (311 / 3200) ≤ (1165556589 / 500000000) := by
  have h := checkLog_sound (w := (89 / 711)) (n := 12)
    (lo := (125835817 / 500000000)) (hi := (50334327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 311) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 311) = 1/(311 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1165556589 / 500000000) (-1165556587 / 500000000) (Real.log (311 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (592549609 / 1000000000) ≤ -Real.log (256 / 463) ∧
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


theorem reflection_log_5 : Bounds (592549609 / 1000000000) (59254961 / 100000000) (Real.log (463 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (463 / 256) = -Real.log (256 / 463) := by
    rw [show ((463 / 256) : ℝ) = ((256 / 463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (330671429 / 200000000) ≤ -Real.log (49 / 256) ∧
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


theorem reflection_log_6 : Bounds (-413339287 / 250000000) (-330671429 / 200000000) (Real.log (49 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (73863349 / 125000000) ≤ -Real.log (1600 / 2889) ∧
    -Real.log (1600 / 2889) ≤ (590906793 / 1000000000) := by
  have h := checkLog_sound (w := (1289 / 4489)) (n := 12)
    (lo := (73863349 / 125000000)) (hi := (590906793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2889 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2889 / 1600) = 1/(1600 / 2889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (73863349 / 125000000) (590906793 / 1000000000) (Real.log (2889 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2889 / 1600) = -Real.log (1600 / 2889) := by
    rw [show ((2889 / 1600) : ℝ) = ((1600 / 2889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (818982997 / 500000000) ≤ -Real.log (311 / 1600) ∧
    -Real.log (311 / 1600) ≤ (1637965997 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 711)) (n := 12)
    (lo := (125835817 / 500000000)) (hi := (50334327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 311) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 311) = 1/(311 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1637965997 / 1000000000) (-818982997 / 500000000) (Real.log (311 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2047129 / 3125000) ≤ -Real.log (1000000 / 1925299) ∧
    -Real.log (1000000 / 1925299) ≤ (655081281 / 1000000000) := by
  have h := checkLog_sound (w := (925299 / 2925299)) (n := 12)
    (lo := (2047129 / 3125000)) (hi := (655081281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1925299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1925299 / 1000000) = 1/(1000000 / 1925299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2047129 / 3125000) (655081281 / 1000000000) (Real.log (1925299 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1925299 / 1000000) = -Real.log (1000000 / 1925299) := by
    rw [show ((1925299 / 1000000) : ℝ) = ((1000000 / 1925299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1297130899 / 500000000) ≤ -Real.log (74701 / 1000000) ∧
    -Real.log (74701 / 1000000) ≤ (1297130901 / 500000000) := by
  have h := checkLog_sound (w := (50299 / 199701)) (n := 12)
    (lo := (257410129 / 500000000)) (hi := (514820259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 74701) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 74701) = 1/(74701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1297130901 / 500000000) (-1297130899 / 500000000) (Real.log (74701 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (655611447 / 1000000000) ≤ -Real.log (12500 / 24079) ∧
    -Real.log (12500 / 24079) ≤ (81951431 / 125000000) := by
  have h := checkLog_sound (w := (11579 / 36579)) (n := 12)
    (lo := (655611447 / 1000000000)) (hi := (81951431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24079 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24079 / 12500) = 1/(12500 / 24079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (655611447 / 1000000000) (81951431 / 125000000) (Real.log (24079 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (24079 / 12500) = -Real.log (12500 / 24079) := by
    rw [show ((24079 / 12500) : ℝ) = ((12500 / 24079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (521604777 / 200000000) ≤ -Real.log (921 / 12500) ∧
    -Real.log (921 / 12500) ≤ (2608023889 / 1000000000) := by
  have h := checkLog_sound (w := (1283 / 4967)) (n := 12)
    (lo := (105716469 / 200000000)) (hi := (264291173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1842) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 1842) = 1/(921 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2608023889 / 1000000000) (-521604777 / 200000000) (Real.log (921 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (653930667 / 1000000000) ≤ -Real.log (200000 / 384617) ∧
    -Real.log (200000 / 384617) ≤ (163482667 / 250000000) := by
  have h := checkLog_sound (w := (184617 / 584617)) (n := 12)
    (lo := (653930667 / 1000000000)) (hi := (163482667 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384617 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384617 / 200000) = 1/(200000 / 384617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (653930667 / 1000000000) (163482667 / 250000000) (Real.log (384617 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (384617 / 200000) = -Real.log (200000 / 384617) := by
    rw [show ((384617 / 200000) : ℝ) = ((200000 / 384617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2565054361 / 1000000000) ≤ -Real.log (15383 / 200000) ∧
    -Real.log (15383 / 200000) ≤ (513010873 / 200000000) := by
  have h := checkLog_sound (w := (9617 / 40383)) (n := 12)
    (lo := (485612821 / 1000000000)) (hi := (242806411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 15383) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 15383) = 1/(15383 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-513010873 / 200000000) (-2565054361 / 1000000000) (Real.log (15383 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (654501981 / 1000000000) ≤ -Real.log (125000 / 240523) ∧
    -Real.log (125000 / 240523) ≤ (327250991 / 500000000) := by
  have h := checkLog_sound (w := (115523 / 365523)) (n := 12)
    (lo := (654501981 / 1000000000)) (hi := (327250991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240523 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(240523 / 125000) = 1/(125000 / 240523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (654501981 / 1000000000) (327250991 / 500000000) (Real.log (240523 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (240523 / 125000) = -Real.log (125000 / 240523) := by
    rw [show ((240523 / 125000) : ℝ) = ((125000 / 240523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (103177837 / 40000000) ≤ -Real.log (9477 / 125000) ∧
    -Real.log (9477 / 125000) ≤ (2579445929 / 1000000000) := by
  have h := checkLog_sound (w := (3074 / 12551)) (n := 12)
    (lo := (100000877 / 200000000)) (hi := (250002193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9477) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 9477) = 1/(9477 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2579445929 / 1000000000) (-103177837 / 40000000) (Real.log (9477 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1624671539 / 500000000) ≤ -Real.log (25000000000 / 644335082529) ∧
    -Real.log (25000000000 / 644335082529) ≤ (3249343083 / 1000000000) := by
  have h := checkLog_sound (w := (244335082529 / 1044335082529)) (n := 12)
    (lo := (238377179 / 500000000)) (hi := (476754359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644335082529 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(644335082529 / 400000000000) = 1/(25000000000 / 644335082529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1624671539 / 500000000) (3249343083 / 1000000000) (Real.log (644335082529 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (644335082529 / 25000000000) = -Real.log (25000000000 / 644335082529) := by
    rw [show ((644335082529 / 25000000000) : ℝ) = ((25000000000 / 644335082529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3263635331 / 1000000000) ≤ -Real.log (500000000000 / 13072204125951) ∧
    -Real.log (500000000000 / 13072204125951) ≤ (407954417 / 125000000) := by
  have h := checkLog_sound (w := (5072204125951 / 21072204125951)) (n := 12)
    (lo := (491046611 / 1000000000)) (hi := (122761653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13072204125951 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13072204125951 / 8000000000000) = 1/(500000000000 / 13072204125951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3263635331 / 1000000000) (407954417 / 125000000) (Real.log (13072204125951 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13072204125951 / 500000000000) = -Real.log (500000000000 / 13072204125951) := by
    rw [show ((13072204125951 / 500000000000) : ℝ) = ((500000000000 / 13072204125951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (804746257 / 250000000) ≤ -Real.log (25000000000 / 625068257167) ∧
    -Real.log (25000000000 / 625068257167) ≤ (3218985033 / 1000000000) := by
  have h := checkLog_sound (w := (225068257167 / 1025068257167)) (n := 12)
    (lo := (111599077 / 250000000)) (hi := (446396309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625068257167 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625068257167 / 400000000000) = 1/(25000000000 / 625068257167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (804746257 / 250000000) (3218985033 / 1000000000) (Real.log (625068257167 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (625068257167 / 25000000000) = -Real.log (25000000000 / 625068257167) := by
    rw [show ((625068257167 / 25000000000) : ℝ) = ((25000000000 / 625068257167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1616973953 / 500000000) ≤ -Real.log (500000000000 / 12689828004643) ∧
    -Real.log (500000000000 / 12689828004643) ≤ (3233947911 / 1000000000) := by
  have h := checkLog_sound (w := (4689828004643 / 20689828004643)) (n := 12)
    (lo := (230679593 / 500000000)) (hi := (461359187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12689828004643 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12689828004643 / 8000000000000) = 1/(500000000000 / 12689828004643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1616973953 / 500000000) (3233947911 / 1000000000) (Real.log (12689828004643 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (12689828004643 / 500000000000) = -Real.log (500000000000 / 12689828004643) := by
    rw [show ((12689828004643 / 500000000000) : ℝ) = ((500000000000 / 12689828004643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0162

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0163Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0163
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

theorem reflection_log_1_neg : (321666527 / 500000000) ≤ -Real.log (3200 / 6089) ∧
    -Real.log (3200 / 6089) ≤ (128666611 / 200000000) := by
  have h := checkLog_sound (w := (2889 / 9289)) (n := 12)
    (lo := (321666527 / 500000000)) (hi := (128666611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6089 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6089 / 3200) = 1/(3200 / 6089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (321666527 / 500000000) (128666611 / 200000000) (Real.log (6089 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6089 / 3200) = -Real.log (3200 / 6089) := by
    rw [show ((6089 / 3200) : ℝ) = ((3200 / 6089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1165556587 / 500000000) ≤ -Real.log (311 / 3200) ∧
    -Real.log (311 / 3200) ≤ (1165556589 / 500000000) := by
  have h := checkLog_sound (w := (89 / 711)) (n := 12)
    (lo := (125835817 / 500000000)) (hi := (50334327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 311) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 311) = 1/(311 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1165556589 / 500000000) (-1165556587 / 500000000) (Real.log (311 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128510531 / 200000000) ≤ -Real.log (12800 / 24337) ∧
    -Real.log (12800 / 24337) ≤ (40159541 / 62500000) := by
  have h := checkLog_sound (w := (11537 / 37137)) (n := 12)
    (lo := (128510531 / 200000000)) (hi := (40159541 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24337 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24337 / 12800) = 1/(12800 / 24337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128510531 / 200000000) (40159541 / 62500000) (Real.log (24337 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24337 / 12800) = -Real.log (12800 / 24337) := by
    rw [show ((24337 / 12800) : ℝ) = ((12800 / 24337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (92638213 / 40000000) ≤ -Real.log (1263 / 12800) ∧
    -Real.log (1263 / 12800) ≤ (2315955329 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 2863)) (n := 12)
    (lo := (47302757 / 200000000)) (hi := (118256893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1263) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1263) = 1/(1263 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2315955329 / 1000000000) (-92638213 / 40000000) (Real.log (1263 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (73863349 / 125000000) ≤ -Real.log (1600 / 2889) ∧
    -Real.log (1600 / 2889) ≤ (590906793 / 1000000000) := by
  have h := checkLog_sound (w := (1289 / 4489)) (n := 12)
    (lo := (73863349 / 125000000)) (hi := (590906793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2889 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2889 / 1600) = 1/(1600 / 2889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (73863349 / 125000000) (590906793 / 1000000000) (Real.log (2889 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2889 / 1600) = -Real.log (1600 / 2889) := by
    rw [show ((2889 / 1600) : ℝ) = ((1600 / 2889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (818982997 / 500000000) ≤ -Real.log (311 / 1600) ∧
    -Real.log (311 / 1600) ≤ (1637965997 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 711)) (n := 12)
    (lo := (125835817 / 500000000)) (hi := (50334327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 311) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 311) = 1/(311 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1637965997 / 1000000000) (-818982997 / 500000000) (Real.log (311 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (589261271 / 1000000000) ≤ -Real.log (6400 / 11537) ∧
    -Real.log (6400 / 11537) ≤ (73657659 / 125000000) := by
  have h := checkLog_sound (w := (5137 / 17937)) (n := 12)
    (lo := (589261271 / 1000000000)) (hi := (73657659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11537 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11537 / 6400) = 1/(6400 / 11537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (589261271 / 1000000000) (73657659 / 125000000) (Real.log (11537 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11537 / 6400) = -Real.log (6400 / 11537) := by
    rw [show ((11537 / 6400) : ℝ) = ((6400 / 11537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (324561629 / 200000000) ≤ -Real.log (1263 / 6400) ∧
    -Real.log (1263 / 6400) ≤ (405702037 / 250000000) := by
  have h := checkLog_sound (w := (337 / 2863)) (n := 12)
    (lo := (47302757 / 200000000)) (hi := (118256893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1263) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1263) = 1/(1263 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-405702037 / 250000000) (-324561629 / 200000000) (Real.log (1263 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (65455343 / 100000000) ≤ -Real.log (1000000 / 1924283) ∧
    -Real.log (1000000 / 1924283) ≤ (654553431 / 1000000000) := by
  have h := checkLog_sound (w := (924283 / 2924283)) (n := 12)
    (lo := (65455343 / 100000000)) (hi := (654553431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1924283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1924283 / 1000000) = 1/(1000000 / 1924283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (65455343 / 100000000) (654553431 / 1000000000) (Real.log (1924283 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1924283 / 1000000) = -Real.log (1000000 / 1924283) := by
    rw [show ((1924283 / 1000000) : ℝ) = ((1000000 / 1924283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2580752571 / 1000000000) ≤ -Real.log (75717 / 1000000) ∧
    -Real.log (75717 / 1000000) ≤ (103230103 / 40000000) := by
  have h := checkLog_sound (w := (49283 / 200717)) (n := 12)
    (lo := (501311031 / 1000000000)) (hi := (62663879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 75717) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 75717) = 1/(75717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-103230103 / 40000000) (-2580752571 / 1000000000) (Real.log (75717 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (655081799 / 1000000000) ≤ -Real.log (10000 / 19253) ∧
    -Real.log (10000 / 19253) ≤ (3275409 / 5000000) := by
  have h := checkLog_sound (w := (9253 / 29253)) (n := 12)
    (lo := (655081799 / 1000000000)) (hi := (3275409 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19253 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19253 / 10000) = 1/(10000 / 19253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (655081799 / 1000000000) (3275409 / 5000000) (Real.log (19253 / 10000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (19253 / 10000) = -Real.log (10000 / 19253) := by
    rw [show ((19253 / 10000) : ℝ) = ((10000 / 19253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (518855037 / 200000000) ≤ -Real.log (747 / 10000) ∧
    -Real.log (747 / 10000) ≤ (2594275189 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 1997)) (n := 12)
    (lo := (102966729 / 200000000)) (hi := (257416823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 747) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1250 / 747) = 1/(747 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2594275189 / 1000000000) (-518855037 / 200000000) (Real.log (747 / 10000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (653360587 / 1000000000) ≤ -Real.log (1000000 / 1921989) ∧
    -Real.log (1000000 / 1921989) ≤ (163340147 / 250000000) := by
  have h := checkLog_sound (w := (921989 / 2921989)) (n := 12)
    (lo := (653360587 / 1000000000)) (hi := (163340147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1921989 / 1000000) = 1/(1000000 / 1921989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (653360587 / 1000000000) (163340147 / 250000000) (Real.log (1921989 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1921989 / 1000000) = -Real.log (1000000 / 1921989) := by
    rw [show ((1921989 / 1000000) : ℝ) = ((1000000 / 1921989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1275452717 / 500000000) ≤ -Real.log (78011 / 1000000) ∧
    -Real.log (78011 / 1000000) ≤ (1275452719 / 500000000) := by
  have h := checkLog_sound (w := (46989 / 203011)) (n := 12)
    (lo := (235731947 / 500000000)) (hi := (94292779 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 78011) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 78011) = 1/(78011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1275452719 / 500000000) (-1275452717 / 500000000) (Real.log (78011 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (653931187 / 1000000000) ≤ -Real.log (500000 / 961543) ∧
    -Real.log (500000 / 961543) ≤ (163482797 / 250000000) := by
  have h := checkLog_sound (w := (461543 / 1461543)) (n := 12)
    (lo := (653931187 / 1000000000)) (hi := (163482797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961543 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(961543 / 500000) = 1/(500000 / 961543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (653931187 / 1000000000) (163482797 / 250000000) (Real.log (961543 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (961543 / 500000) = -Real.log (500000 / 961543) := by
    rw [show ((961543 / 500000) : ℝ) = ((500000 / 961543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1282533681 / 500000000) ≤ -Real.log (38457 / 500000) ∧
    -Real.log (38457 / 500000) ≤ (1282533683 / 500000000) := by
  have h := checkLog_sound (w := (24043 / 100957)) (n := 12)
    (lo := (242812911 / 500000000)) (hi := (485625823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38457) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 38457) = 1/(38457 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1282533683 / 500000000) (-1282533681 / 500000000) (Real.log (38457 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3235306001 / 1000000000) ≤ -Real.log (250000000000 / 6353536854339) ∧
    -Real.log (250000000000 / 6353536854339) ≤ (1617653003 / 500000000) := by
  have h := checkLog_sound (w := (2353536854339 / 10353536854339)) (n := 12)
    (lo := (462717281 / 1000000000)) (hi := (231358641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6353536854339 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6353536854339 / 4000000000000) = 1/(250000000000 / 6353536854339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3235306001 / 1000000000) (1617653003 / 500000000) (Real.log (6353536854339 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6353536854339 / 250000000000) = -Real.log (250000000000 / 6353536854339) := by
    rw [show ((6353536854339 / 250000000000) : ℝ) = ((250000000000 / 6353536854339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (406169623 / 125000000) ≤ -Real.log (500000000000 / 12886880856761) ∧
    -Real.log (500000000000 / 12886880856761) ≤ (3249356989 / 1000000000) := by
  have h := checkLog_sound (w := (4886880856761 / 20886880856761)) (n := 12)
    (lo := (59596033 / 125000000)) (hi := (95353653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12886880856761 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12886880856761 / 8000000000000) = 1/(500000000000 / 12886880856761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (406169623 / 125000000) (3249356989 / 1000000000) (Real.log (12886880856761 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12886880856761 / 500000000000) = -Real.log (500000000000 / 12886880856761) := by
    rw [show ((12886880856761 / 500000000000) : ℝ) = ((500000000000 / 12886880856761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3204266021 / 1000000000) ≤ -Real.log (100000000000 / 2463741010883) ∧
    -Real.log (100000000000 / 2463741010883) ≤ (1602133013 / 500000000) := by
  have h := checkLog_sound (w := (863741010883 / 4063741010883)) (n := 12)
    (lo := (431677301 / 1000000000)) (hi := (215838651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2463741010883 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2463741010883 / 1600000000000) = 1/(100000000000 / 2463741010883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3204266021 / 1000000000) (1602133013 / 500000000) (Real.log (2463741010883 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2463741010883 / 100000000000) = -Real.log (100000000000 / 2463741010883) := by
    rw [show ((2463741010883 / 100000000000) : ℝ) = ((100000000000 / 2463741010883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3218998549 / 1000000000) ≤ -Real.log (250000000000 / 6250767090517) ∧
    -Real.log (250000000000 / 6250767090517) ≤ (1609499277 / 500000000) := by
  have h := checkLog_sound (w := (2250767090517 / 10250767090517)) (n := 12)
    (lo := (446409829 / 1000000000)) (hi := (44640983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250767090517 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250767090517 / 4000000000000) = 1/(250000000000 / 6250767090517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3218998549 / 1000000000) (1609499277 / 500000000) (Real.log (6250767090517 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6250767090517 / 250000000000) = -Real.log (250000000000 / 6250767090517) := by
    rw [show ((6250767090517 / 250000000000) : ℝ) = ((250000000000 / 6250767090517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0163

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0164Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0164
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

theorem reflection_log_1_neg : (128510531 / 200000000) ≤ -Real.log (12800 / 24337) ∧
    -Real.log (12800 / 24337) ≤ (40159541 / 62500000) := by
  have h := checkLog_sound (w := (11537 / 37137)) (n := 12)
    (lo := (128510531 / 200000000)) (hi := (40159541 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24337 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24337 / 12800) = 1/(12800 / 24337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128510531 / 200000000) (40159541 / 62500000) (Real.log (24337 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24337 / 12800) = -Real.log (12800 / 24337) := by
    rw [show ((24337 / 12800) : ℝ) = ((12800 / 24337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (92638213 / 40000000) ≤ -Real.log (1263 / 12800) ∧
    -Real.log (1263 / 12800) ≤ (2315955329 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 2863)) (n := 12)
    (lo := (47302757 / 200000000)) (hi := (118256893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1263) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1263) = 1/(1263 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2315955329 / 1000000000) (-92638213 / 40000000) (Real.log (1263 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128354329 / 200000000) ≤ -Real.log (6400 / 12159) ∧
    -Real.log (6400 / 12159) ≤ (320885823 / 500000000) := by
  have h := checkLog_sound (w := (5759 / 18559)) (n := 12)
    (lo := (128354329 / 200000000)) (hi := (320885823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12159 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12159 / 6400) = 1/(6400 / 12159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128354329 / 200000000) (320885823 / 500000000) (Real.log (12159 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12159 / 6400) = -Real.log (6400 / 12159) := by
    rw [show ((12159 / 6400) : ℝ) = ((6400 / 12159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (230102381 / 100000000) ≤ -Real.log (641 / 6400) ∧
    -Real.log (641 / 6400) ≤ (1150511907 / 500000000) := by
  have h := checkLog_sound (w := (159 / 1441)) (n := 12)
    (lo := (22158227 / 100000000)) (hi := (221582271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 641) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 641) = 1/(641 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1150511907 / 500000000) (-230102381 / 100000000) (Real.log (641 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (589261271 / 1000000000) ≤ -Real.log (6400 / 11537) ∧
    -Real.log (6400 / 11537) ≤ (73657659 / 125000000) := by
  have h := checkLog_sound (w := (5137 / 17937)) (n := 12)
    (lo := (589261271 / 1000000000)) (hi := (73657659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11537 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11537 / 6400) = 1/(6400 / 11537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (589261271 / 1000000000) (73657659 / 125000000) (Real.log (11537 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11537 / 6400) = -Real.log (6400 / 11537) := by
    rw [show ((11537 / 6400) : ℝ) = ((6400 / 11537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (324561629 / 200000000) ≤ -Real.log (1263 / 6400) ∧
    -Real.log (1263 / 6400) ≤ (405702037 / 250000000) := by
  have h := checkLog_sound (w := (337 / 2863)) (n := 12)
    (lo := (47302757 / 200000000)) (hi := (118256893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1263) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1263) = 1/(1263 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-405702037 / 250000000) (-324561629 / 200000000) (Real.log (1263 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (293806519 / 500000000) ≤ -Real.log (3200 / 5759) ∧
    -Real.log (3200 / 5759) ≤ (587613039 / 1000000000) := by
  have h := checkLog_sound (w := (2559 / 8959)) (n := 12)
    (lo := (293806519 / 500000000)) (hi := (587613039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5759 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5759 / 3200) = 1/(3200 / 5759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (293806519 / 500000000) (587613039 / 1000000000) (Real.log (5759 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5759 / 3200) = -Real.log (3200 / 5759) := by
    rw [show ((5759 / 3200) : ℝ) = ((3200 / 5759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (160787663 / 100000000) ≤ -Real.log (641 / 3200) ∧
    -Real.log (641 / 3200) ≤ (1607876633 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 1441)) (n := 12)
    (lo := (22158227 / 100000000)) (hi := (221582271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 641) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 641) = 1/(641 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1607876633 / 1000000000) (-160787663 / 100000000) (Real.log (641 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (327013171 / 500000000) ≤ -Real.log (1000000 / 1923269) ∧
    -Real.log (1000000 / 1923269) ≤ (654026343 / 1000000000) := by
  have h := checkLog_sound (w := (923269 / 2923269)) (n := 12)
    (lo := (327013171 / 500000000)) (hi := (654026343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1923269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1923269 / 1000000) = 1/(1000000 / 1923269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (327013171 / 500000000) (654026343 / 1000000000) (Real.log (1923269 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1923269 / 1000000) = -Real.log (1000000 / 1923269) := by
    rw [show ((1923269 / 1000000) : ℝ) = ((1000000 / 1923269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1283724739 / 500000000) ≤ -Real.log (76731 / 1000000) ∧
    -Real.log (76731 / 1000000) ≤ (1283724741 / 500000000) := by
  have h := checkLog_sound (w := (48269 / 201731)) (n := 12)
    (lo := (244003969 / 500000000)) (hi := (488007939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 76731) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 76731) = 1/(76731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1283724741 / 500000000) (-1283724739 / 500000000) (Real.log (76731 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (13091079 / 20000000) ≤ -Real.log (250000 / 481071) ∧
    -Real.log (250000 / 481071) ≤ (654553951 / 1000000000) := by
  have h := checkLog_sound (w := (231071 / 731071)) (n := 12)
    (lo := (13091079 / 20000000)) (hi := (654553951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481071 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481071 / 250000) = 1/(250000 / 481071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (13091079 / 20000000) (654553951 / 1000000000) (Real.log (481071 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (481071 / 250000) = -Real.log (250000 / 481071) := by
    rw [show ((481071 / 250000) : ℝ) = ((250000 / 481071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1290382889 / 500000000) ≤ -Real.log (18929 / 250000) ∧
    -Real.log (18929 / 250000) ≤ (1290382891 / 500000000) := by
  have h := checkLog_sound (w := (12321 / 50179)) (n := 12)
    (lo := (250662119 / 500000000)) (hi := (501324239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18929) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 18929) = 1/(18929 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1290382891 / 500000000) (-1290382889 / 500000000) (Real.log (18929 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (326395351 / 500000000) ≤ -Real.log (500000 / 960447) ∧
    -Real.log (500000 / 960447) ≤ (652790703 / 1000000000) := by
  have h := checkLog_sound (w := (460447 / 1460447)) (n := 12)
    (lo := (326395351 / 500000000)) (hi := (652790703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960447 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(960447 / 500000) = 1/(500000 / 960447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (326395351 / 500000000) (652790703 / 1000000000) (Real.log (960447 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (960447 / 500000) = -Real.log (500000 / 960447) := by
    rw [show ((960447 / 500000) : ℝ) = ((500000 / 960447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (317120819 / 125000000) ≤ -Real.log (39553 / 500000) ∧
    -Real.log (39553 / 500000) ≤ (634241639 / 250000000) := by
  have h := checkLog_sound (w := (22947 / 102053)) (n := 12)
    (lo := (114381253 / 250000000)) (hi := (457525013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39553) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 39553) = 1/(39553 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-634241639 / 250000000) (-317120819 / 125000000) (Real.log (39553 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (653361107 / 1000000000) ≤ -Real.log (100000 / 192199) ∧
    -Real.log (100000 / 192199) ≤ (163340277 / 250000000) := by
  have h := checkLog_sound (w := (92199 / 292199)) (n := 12)
    (lo := (653361107 / 1000000000)) (hi := (163340277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192199 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192199 / 100000) = 1/(100000 / 192199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (653361107 / 1000000000) (163340277 / 250000000) (Real.log (192199 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (192199 / 100000) = -Real.log (100000 / 192199) := by
    rw [show ((192199 / 100000) : ℝ) = ((100000 / 192199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2550918253 / 1000000000) ≤ -Real.log (7801 / 100000) ∧
    -Real.log (7801 / 100000) ≤ (2550918257 / 1000000000) := by
  have h := checkLog_sound (w := (4699 / 20301)) (n := 12)
    (lo := (471476713 / 1000000000)) (hi := (235738357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7801) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 7801) = 1/(7801 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2550918257 / 1000000000) (-2550918253 / 1000000000) (Real.log (7801 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (161073791 / 50000000) ≤ -Real.log (250000000000 / 6266271129009) ∧
    -Real.log (250000000000 / 6266271129009) ≤ (128859033 / 40000000) := by
  have h := checkLog_sound (w := (2266271129009 / 10266271129009)) (n := 12)
    (lo := (4488871 / 10000000)) (hi := (448887101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6266271129009 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6266271129009 / 4000000000000) = 1/(250000000000 / 6266271129009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (161073791 / 50000000) (128859033 / 40000000) (Real.log (6266271129009 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6266271129009 / 250000000000) = -Real.log (250000000000 / 6266271129009) := by
    rw [show ((6266271129009 / 250000000000) : ℝ) = ((250000000000 / 6266271129009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (202207483 / 62500000) ≤ -Real.log (500000000000 / 12707248137779) ∧
    -Real.log (500000000000 / 12707248137779) ≤ (3235319733 / 1000000000) := by
  have h := checkLog_sound (w := (4707248137779 / 20707248137779)) (n := 12)
    (lo := (1807543 / 3906250)) (hi := (462731009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12707248137779 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12707248137779 / 8000000000000) = 1/(500000000000 / 12707248137779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (202207483 / 62500000) (3235319733 / 1000000000) (Real.log (12707248137779 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12707248137779 / 500000000000) = -Real.log (500000000000 / 12707248137779) := by
    rw [show ((12707248137779 / 500000000000) : ℝ) = ((500000000000 / 12707248137779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1594878627 / 500000000) ≤ -Real.log (500000000000 / 12141266149217) ∧
    -Real.log (500000000000 / 12141266149217) ≤ (3189757259 / 1000000000) := by
  have h := checkLog_sound (w := (4141266149217 / 20141266149217)) (n := 12)
    (lo := (208584267 / 500000000)) (hi := (83433707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12141266149217 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12141266149217 / 8000000000000) = 1/(500000000000 / 12141266149217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1594878627 / 500000000) (3189757259 / 1000000000) (Real.log (12141266149217 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (12141266149217 / 500000000000) = -Real.log (500000000000 / 12141266149217) := by
    rw [show ((12141266149217 / 500000000000) : ℝ) = ((500000000000 / 12141266149217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (10013373 / 3125000) ≤ -Real.log (250000000000 / 6159434687861) ∧
    -Real.log (250000000000 / 6159434687861) ≤ (640855873 / 200000000) := by
  have h := checkLog_sound (w := (2159434687861 / 10159434687861)) (n := 12)
    (lo := (5396133 / 12500000)) (hi := (431690641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6159434687861 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6159434687861 / 4000000000000) = 1/(250000000000 / 6159434687861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (10013373 / 3125000) (640855873 / 200000000) (Real.log (6159434687861 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6159434687861 / 250000000000) = -Real.log (250000000000 / 6159434687861) := by
    rw [show ((6159434687861 / 250000000000) : ℝ) = ((250000000000 / 6159434687861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0164

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0165Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0165
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

theorem reflection_log_1_neg : (128354329 / 200000000) ≤ -Real.log (6400 / 12159) ∧
    -Real.log (6400 / 12159) ≤ (320885823 / 500000000) := by
  have h := checkLog_sound (w := (5759 / 18559)) (n := 12)
    (lo := (128354329 / 200000000)) (hi := (320885823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12159 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12159 / 6400) = 1/(6400 / 12159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128354329 / 200000000) (320885823 / 500000000) (Real.log (12159 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12159 / 6400) = -Real.log (6400 / 12159) := by
    rw [show ((12159 / 6400) : ℝ) = ((6400 / 12159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (230102381 / 100000000) ≤ -Real.log (641 / 6400) ∧
    -Real.log (641 / 6400) ≤ (1150511907 / 500000000) := by
  have h := checkLog_sound (w := (159 / 1441)) (n := 12)
    (lo := (22158227 / 100000000)) (hi := (221582271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 641) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 641) = 1/(641 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1150511907 / 500000000) (-230102381 / 100000000) (Real.log (641 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (320495013 / 500000000) ≤ -Real.log (12800 / 24299) ∧
    -Real.log (12800 / 24299) ≤ (640990027 / 1000000000) := by
  have h := checkLog_sound (w := (11499 / 37099)) (n := 12)
    (lo := (320495013 / 500000000)) (hi := (640990027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24299 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24299 / 12800) = 1/(12800 / 24299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (320495013 / 500000000) (640990027 / 1000000000) (Real.log (24299 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24299 / 12800) = -Real.log (12800 / 24299) := by
    rw [show ((24299 / 12800) : ℝ) = ((12800 / 24299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2286311969 / 1000000000) ≤ -Real.log (1301 / 12800) ∧
    -Real.log (1301 / 12800) ≤ (2286311973 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2901)) (n := 12)
    (lo := (206870429 / 1000000000)) (hi := (20687043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1301) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1301) = 1/(1301 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2286311973 / 1000000000) (-2286311969 / 1000000000) (Real.log (1301 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (293806519 / 500000000) ≤ -Real.log (3200 / 5759) ∧
    -Real.log (3200 / 5759) ≤ (587613039 / 1000000000) := by
  have h := checkLog_sound (w := (2559 / 8959)) (n := 12)
    (lo := (293806519 / 500000000)) (hi := (587613039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5759 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5759 / 3200) = 1/(3200 / 5759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (293806519 / 500000000) (587613039 / 1000000000) (Real.log (5759 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5759 / 3200) = -Real.log (3200 / 5759) := by
    rw [show ((5759 / 3200) : ℝ) = ((3200 / 5759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (160787663 / 100000000) ≤ -Real.log (641 / 3200) ∧
    -Real.log (641 / 3200) ≤ (1607876633 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 1441)) (n := 12)
    (lo := (22158227 / 100000000)) (hi := (221582271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 641) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 641) = 1/(641 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1607876633 / 1000000000) (-160787663 / 100000000) (Real.log (641 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (146490521 / 250000000) ≤ -Real.log (6400 / 11499) ∧
    -Real.log (6400 / 11499) ≤ (117192417 / 200000000) := by
  have h := checkLog_sound (w := (5099 / 17899)) (n := 12)
    (lo := (146490521 / 250000000)) (hi := (117192417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11499 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11499 / 6400) = 1/(6400 / 11499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (146490521 / 250000000) (117192417 / 200000000) (Real.log (11499 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11499 / 6400) = -Real.log (6400 / 11499) := by
    rw [show ((11499 / 6400) : ℝ) = ((6400 / 11499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1593164789 / 1000000000) ≤ -Real.log (1301 / 6400) ∧
    -Real.log (1301 / 6400) ≤ (199145599 / 125000000) := by
  have h := checkLog_sound (w := (299 / 2901)) (n := 12)
    (lo := (206870429 / 1000000000)) (hi := (20687043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1301) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1301) = 1/(1301 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-199145599 / 125000000) (-1593164789 / 1000000000) (Real.log (1301 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (5105477 / 7812500) ≤ -Real.log (1000000 / 1922259) ∧
    -Real.log (1000000 / 1922259) ≤ (653501057 / 1000000000) := by
  have h := checkLog_sound (w := (922259 / 2922259)) (n := 12)
    (lo := (5105477 / 7812500)) (hi := (653501057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1922259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1922259 / 1000000) = 1/(1000000 / 1922259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (5105477 / 7812500) (653501057 / 1000000000) (Real.log (1922259 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1922259 / 1000000) = -Real.log (1000000 / 1922259) := by
    rw [show ((1922259 / 1000000) : ℝ) = ((1000000 / 1922259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (319296561 / 125000000) ≤ -Real.log (77741 / 1000000) ∧
    -Real.log (77741 / 1000000) ≤ (638593123 / 250000000) := by
  have h := checkLog_sound (w := (47259 / 202741)) (n := 12)
    (lo := (118732737 / 250000000)) (hi := (474930949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 77741) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 77741) = 1/(77741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-638593123 / 250000000) (-319296561 / 125000000) (Real.log (77741 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (327013431 / 500000000) ≤ -Real.log (100000 / 192327) ∧
    -Real.log (100000 / 192327) ≤ (654026863 / 1000000000) := by
  have h := checkLog_sound (w := (92327 / 292327)) (n := 12)
    (lo := (327013431 / 500000000)) (hi := (654026863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192327 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192327 / 100000) = 1/(100000 / 192327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (327013431 / 500000000) (654026863 / 1000000000) (Real.log (192327 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (192327 / 100000) = -Real.log (100000 / 192327) := by
    rw [show ((192327 / 100000) : ℝ) = ((100000 / 192327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2567462511 / 1000000000) ≤ -Real.log (7673 / 100000) ∧
    -Real.log (7673 / 100000) ≤ (513492503 / 200000000) := by
  have h := checkLog_sound (w := (4827 / 20173)) (n := 12)
    (lo := (488020971 / 1000000000)) (hi := (122005243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7673) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 7673) = 1/(7673 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-513492503 / 200000000) (-2567462511 / 1000000000) (Real.log (7673 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (326110767 / 500000000) ≤ -Real.log (1000000 / 1919801) ∧
    -Real.log (1000000 / 1919801) ≤ (130444307 / 200000000) := by
  have h := checkLog_sound (w := (919801 / 2919801)) (n := 12)
    (lo := (326110767 / 500000000)) (hi := (130444307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1919801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1919801 / 1000000) = 1/(1000000 / 1919801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (326110767 / 500000000) (130444307 / 200000000) (Real.log (1919801 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1919801 / 1000000) = -Real.log (1000000 / 1919801) := by
    rw [show ((1919801 / 1000000) : ℝ) = ((1000000 / 1919801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2523244231 / 1000000000) ≤ -Real.log (80199 / 1000000) ∧
    -Real.log (80199 / 1000000) ≤ (504648847 / 200000000) := by
  have h := checkLog_sound (w := (44801 / 205199)) (n := 12)
    (lo := (443802691 / 1000000000)) (hi := (110950673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80199) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 80199) = 1/(80199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-504648847 / 200000000) (-2523244231 / 1000000000) (Real.log (80199 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (652791223 / 1000000000) ≤ -Real.log (200000 / 384179) ∧
    -Real.log (200000 / 384179) ≤ (81598903 / 125000000) := by
  have h := checkLog_sound (w := (184179 / 584179)) (n := 12)
    (lo := (652791223 / 1000000000)) (hi := (81598903 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384179 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384179 / 200000) = 1/(200000 / 384179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (652791223 / 1000000000) (81598903 / 125000000) (Real.log (384179 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (384179 / 200000) = -Real.log (200000 / 384179) := by
    rw [show ((384179 / 200000) : ℝ) = ((200000 / 384179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2536979193 / 1000000000) ≤ -Real.log (15821 / 200000) ∧
    -Real.log (15821 / 200000) ≤ (2536979197 / 1000000000) := by
  have h := checkLog_sound (w := (9179 / 40821)) (n := 12)
    (lo := (457537653 / 1000000000)) (hi := (228768827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 15821) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 15821) = 1/(15821 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2536979197 / 1000000000) (-2536979193 / 1000000000) (Real.log (15821 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (400984193 / 125000000) ≤ -Real.log (250000000000 / 6181612662559) ∧
    -Real.log (250000000000 / 6181612662559) ≤ (3207873549 / 1000000000) := by
  have h := checkLog_sound (w := (2181612662559 / 10181612662559)) (n := 12)
    (lo := (54410603 / 125000000)) (hi := (17411393 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6181612662559 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6181612662559 / 4000000000000) = 1/(250000000000 / 6181612662559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (400984193 / 125000000) (3207873549 / 1000000000) (Real.log (6181612662559 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6181612662559 / 250000000000) = -Real.log (250000000000 / 6181612662559) := by
    rw [show ((6181612662559 / 250000000000) : ℝ) = ((250000000000 / 6181612662559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (805372343 / 250000000) ≤ -Real.log (50000000000 / 1253271210739) ∧
    -Real.log (50000000000 / 1253271210739) ≤ (3221489377 / 1000000000) := by
  have h := checkLog_sound (w := (453271210739 / 2053271210739)) (n := 12)
    (lo := (112225163 / 250000000)) (hi := (448900653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253271210739 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1253271210739 / 800000000000) = 1/(50000000000 / 1253271210739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (805372343 / 250000000) (3221489377 / 1000000000) (Real.log (1253271210739 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1253271210739 / 50000000000) = -Real.log (50000000000 / 1253271210739) := by
    rw [show ((1253271210739 / 50000000000) : ℝ) = ((50000000000 / 1253271210739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (635093153 / 200000000) ≤ -Real.log (500000000000 / 11968983403783) ∧
    -Real.log (500000000000 / 11968983403783) ≤ (317546577 / 100000000) := by
  have h := checkLog_sound (w := (3968983403783 / 19968983403783)) (n := 12)
    (lo := (80575409 / 200000000)) (hi := (201438523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11968983403783 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11968983403783 / 8000000000000) = 1/(500000000000 / 11968983403783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (635093153 / 200000000) (317546577 / 100000000) (Real.log (11968983403783 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11968983403783 / 500000000000) = -Real.log (500000000000 / 11968983403783) := by
    rw [show ((11968983403783 / 500000000000) : ℝ) = ((500000000000 / 11968983403783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (199360651 / 62500000) ≤ -Real.log (31250000000 / 758839122053) ∧
    -Real.log (31250000000 / 758839122053) ≤ (3189770421 / 1000000000) := by
  have h := checkLog_sound (w := (258839122053 / 1258839122053)) (n := 12)
    (lo := (814808 / 1953125)) (hi := (417181697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758839122053 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(758839122053 / 500000000000) = 1/(31250000000 / 758839122053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (199360651 / 62500000) (3189770421 / 1000000000) (Real.log (758839122053 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (758839122053 / 31250000000) = -Real.log (31250000000 / 758839122053) := by
    rw [show ((758839122053 / 31250000000) : ℝ) = ((31250000000 / 758839122053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0165

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0166Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0166
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

theorem reflection_log_1_neg : (320495013 / 500000000) ≤ -Real.log (12800 / 24299) ∧
    -Real.log (12800 / 24299) ≤ (640990027 / 1000000000) := by
  have h := checkLog_sound (w := (11499 / 37099)) (n := 12)
    (lo := (320495013 / 500000000)) (hi := (640990027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24299 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24299 / 12800) = 1/(12800 / 24299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (320495013 / 500000000) (640990027 / 1000000000) (Real.log (24299 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24299 / 12800) = -Real.log (12800 / 24299) := by
    rw [show ((24299 / 12800) : ℝ) = ((12800 / 24299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2286311969 / 1000000000) ≤ -Real.log (1301 / 12800) ∧
    -Real.log (1301 / 12800) ≤ (2286311973 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2901)) (n := 12)
    (lo := (206870429 / 1000000000)) (hi := (20687043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1301) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1301) = 1/(1301 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2286311973 / 1000000000) (-2286311969 / 1000000000) (Real.log (1301 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128041559 / 200000000) ≤ -Real.log (320 / 607) ∧
    -Real.log (320 / 607) ≤ (160051949 / 250000000) := by
  have h := checkLog_sound (w := (287 / 927)) (n := 12)
    (lo := (128041559 / 200000000)) (hi := (160051949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607 / 320) = 1/(320 / 607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128041559 / 200000000) (160051949 / 250000000) (Real.log (607 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (607 / 320) = -Real.log (320 / 607) := by
    rw [show ((607 / 320) : ℝ) = ((320 / 607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (283976679 / 125000000) ≤ -Real.log (33 / 320) ∧
    -Real.log (33 / 320) ≤ (567953359 / 250000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 33) = 1/(33 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-567953359 / 250000000) (-283976679 / 125000000) (Real.log (33 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (146490521 / 250000000) ≤ -Real.log (6400 / 11499) ∧
    -Real.log (6400 / 11499) ≤ (117192417 / 200000000) := by
  have h := checkLog_sound (w := (5099 / 17899)) (n := 12)
    (lo := (146490521 / 250000000)) (hi := (117192417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11499 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11499 / 6400) = 1/(6400 / 11499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (146490521 / 250000000) (117192417 / 200000000) (Real.log (11499 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11499 / 6400) = -Real.log (6400 / 11499) := by
    rw [show ((11499 / 6400) : ℝ) = ((6400 / 11499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1593164789 / 1000000000) ≤ -Real.log (1301 / 6400) ∧
    -Real.log (1301 / 6400) ≤ (199145599 / 125000000) := by
  have h := checkLog_sound (w := (299 / 2901)) (n := 12)
    (lo := (206870429 / 1000000000)) (hi := (20687043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1301) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1301) = 1/(1301 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-199145599 / 125000000) (-1593164789 / 1000000000) (Real.log (1301 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1460771 / 2500000) ≤ -Real.log (160 / 287) ∧
    -Real.log (160 / 287) ≤ (584308401 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 447)) (n := 12)
    (lo := (1460771 / 2500000)) (hi := (584308401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287 / 160) = 1/(160 / 287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1460771 / 2500000) (584308401 / 1000000000) (Real.log (287 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (287 / 160) = -Real.log (160 / 287) := by
    rw [show ((287 / 160) : ℝ) = ((160 / 287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (394666563 / 250000000) ≤ -Real.log (33 / 160) ∧
    -Real.log (33 / 160) ≤ (315733251 / 200000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 33) = 1/(33 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-315733251 / 200000000) (-394666563 / 250000000) (Real.log (33 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (652977577 / 1000000000) ≤ -Real.log (1000000 / 1921253) ∧
    -Real.log (1000000 / 1921253) ≤ (326488789 / 500000000) := by
  have h := checkLog_sound (w := (921253 / 2921253)) (n := 12)
    (lo := (652977577 / 1000000000)) (hi := (326488789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1921253 / 1000000) = 1/(1000000 / 1921253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (652977577 / 1000000000) (326488789 / 500000000) (Real.log (1921253 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1921253 / 1000000) = -Real.log (1000000 / 1921253) := by
    rw [show ((1921253 / 1000000) : ℝ) = ((1000000 / 1921253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (508303019 / 200000000) ≤ -Real.log (78747 / 1000000) ∧
    -Real.log (78747 / 1000000) ≤ (2541515099 / 1000000000) := by
  have h := checkLog_sound (w := (46253 / 203747)) (n := 12)
    (lo := (92414711 / 200000000)) (hi := (115518389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 78747) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 78747) = 1/(78747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2541515099 / 1000000000) (-508303019 / 200000000) (Real.log (78747 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (653501577 / 1000000000) ≤ -Real.log (50000 / 96113) ∧
    -Real.log (50000 / 96113) ≤ (326750789 / 500000000) := by
  have h := checkLog_sound (w := (46113 / 146113)) (n := 12)
    (lo := (653501577 / 1000000000)) (hi := (326750789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96113 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96113 / 50000) = 1/(50000 / 96113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (653501577 / 1000000000) (326750789 / 500000000) (Real.log (96113 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (96113 / 50000) = -Real.log (50000 / 96113) := by
    rw [show ((96113 / 50000) : ℝ) = ((50000 / 96113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2554385351 / 1000000000) ≤ -Real.log (3887 / 50000) ∧
    -Real.log (3887 / 50000) ≤ (510877071 / 200000000) := by
  have h := checkLog_sound (w := (2363 / 10137)) (n := 12)
    (lo := (474943811 / 1000000000)) (hi := (118735953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3887) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 3887) = 1/(3887 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-510877071 / 200000000) (-2554385351 / 1000000000) (Real.log (3887 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (130330617 / 200000000) ≤ -Real.log (100000 / 191871) ∧
    -Real.log (100000 / 191871) ≤ (325826543 / 500000000) := by
  have h := checkLog_sound (w := (91871 / 291871)) (n := 12)
    (lo := (130330617 / 200000000)) (hi := (325826543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191871 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191871 / 100000) = 1/(100000 / 191871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (130330617 / 200000000) (325826543 / 500000000) (Real.log (191871 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (191871 / 100000) = -Real.log (100000 / 191871) := by
    rw [show ((191871 / 100000) : ℝ) = ((100000 / 191871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2509732269 / 1000000000) ≤ -Real.log (8129 / 100000) ∧
    -Real.log (8129 / 100000) ≤ (2509732273 / 1000000000) := by
  have h := checkLog_sound (w := (4371 / 20629)) (n := 12)
    (lo := (430290729 / 1000000000)) (hi := (43029073 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 8129) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 8129) = 1/(8129 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2509732273 / 1000000000) (-2509732269 / 1000000000) (Real.log (8129 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (130444411 / 200000000) ≤ -Real.log (500000 / 959901) ∧
    -Real.log (500000 / 959901) ≤ (81527757 / 125000000) := by
  have h := checkLog_sound (w := (459901 / 1459901)) (n := 12)
    (lo := (130444411 / 200000000)) (hi := (81527757 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959901 / 500000) = 1/(500000 / 959901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (130444411 / 200000000) (81527757 / 125000000) (Real.log (959901 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (959901 / 500000) = -Real.log (500000 / 959901) := by
    rw [show ((959901 / 500000) : ℝ) = ((500000 / 959901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25232567 / 10000000) ≤ -Real.log (40099 / 500000) ∧
    -Real.log (40099 / 500000) ≤ (19712943 / 7812500) := by
  have h := checkLog_sound (w := (22401 / 102599)) (n := 12)
    (lo := (11095379 / 25000000)) (hi := (443815161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40099) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 40099) = 1/(40099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-19712943 / 7812500) (-25232567 / 10000000) (Real.log (40099 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (12478487 / 3906250) ≤ -Real.log (500000000000 / 12198896465897) ∧
    -Real.log (500000000000 / 12198896465897) ≤ (3194492677 / 1000000000) := by
  have h := checkLog_sound (w := (4198896465897 / 20198896465897)) (n := 12)
    (lo := (26368997 / 62500000)) (hi := (421903953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12198896465897 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12198896465897 / 8000000000000) = 1/(500000000000 / 12198896465897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (12478487 / 3906250) (3194492677 / 1000000000) (Real.log (12198896465897 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12198896465897 / 500000000000) = -Real.log (500000000000 / 12198896465897) := by
    rw [show ((12198896465897 / 500000000000) : ℝ) = ((500000000000 / 12198896465897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (200492933 / 62500000) ≤ -Real.log (500000000000 / 12363390789813) ∧
    -Real.log (500000000000 / 12363390789813) ≤ (3207886933 / 1000000000) := by
  have h := checkLog_sound (w := (4363390789813 / 20363390789813)) (n := 12)
    (lo := (13603069 / 31250000)) (hi := (435298209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12363390789813 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12363390789813 / 8000000000000) = 1/(500000000000 / 12363390789813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (200492933 / 62500000) (3207886933 / 1000000000) (Real.log (12363390789813 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12363390789813 / 500000000000) = -Real.log (500000000000 / 12363390789813) := by
    rw [show ((12363390789813 / 500000000000) : ℝ) = ((500000000000 / 12363390789813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1580692677 / 500000000) ≤ -Real.log (500000000000 / 11801636117603) ∧
    -Real.log (500000000000 / 11801636117603) ≤ (3161385359 / 1000000000) := by
  have h := checkLog_sound (w := (3801636117603 / 19801636117603)) (n := 12)
    (lo := (194398317 / 500000000)) (hi := (77759327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11801636117603 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11801636117603 / 8000000000000) = 1/(500000000000 / 11801636117603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1580692677 / 500000000) (3161385359 / 1000000000) (Real.log (11801636117603 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11801636117603 / 500000000000) = -Real.log (500000000000 / 11801636117603) := by
    rw [show ((11801636117603 / 500000000000) : ℝ) = ((500000000000 / 11801636117603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (635095751 / 200000000) ≤ -Real.log (500000000000 / 11969138881269) ∧
    -Real.log (500000000000 / 11969138881269) ≤ (79386969 / 25000000) := by
  have h := checkLog_sound (w := (3969138881269 / 19969138881269)) (n := 12)
    (lo := (80578007 / 200000000)) (hi := (100722509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11969138881269 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11969138881269 / 8000000000000) = 1/(500000000000 / 11969138881269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (635095751 / 200000000) (79386969 / 25000000) (Real.log (11969138881269 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11969138881269 / 500000000000) = -Real.log (500000000000 / 11969138881269) := by
    rw [show ((11969138881269 / 500000000000) : ℝ) = ((500000000000 / 11969138881269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0166

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0167Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0167
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

theorem reflection_log_1_neg : (128041559 / 200000000) ≤ -Real.log (320 / 607) ∧
    -Real.log (320 / 607) ≤ (160051949 / 250000000) := by
  have h := checkLog_sound (w := (287 / 927)) (n := 12)
    (lo := (128041559 / 200000000)) (hi := (160051949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607 / 320) = 1/(320 / 607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128041559 / 200000000) (160051949 / 250000000) (Real.log (607 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (607 / 320) = -Real.log (320 / 607) := by
    rw [show ((607 / 320) : ℝ) = ((320 / 607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (283976679 / 125000000) ≤ -Real.log (33 / 320) ∧
    -Real.log (33 / 320) ≤ (567953359 / 250000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 33) = 1/(33 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-567953359 / 250000000) (-283976679 / 125000000) (Real.log (33 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (639424951 / 1000000000) ≤ -Real.log (12800 / 24261) ∧
    -Real.log (12800 / 24261) ≤ (79928119 / 125000000) := by
  have h := checkLog_sound (w := (11461 / 37061)) (n := 12)
    (lo := (639424951 / 1000000000)) (hi := (79928119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24261 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24261 / 12800) = 1/(12800 / 24261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (639424951 / 1000000000) (79928119 / 125000000) (Real.log (24261 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24261 / 12800) = -Real.log (12800 / 24261) := by
    rw [show ((24261 / 12800) : ℝ) = ((12800 / 24261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1128761051 / 500000000) ≤ -Real.log (1339 / 12800) ∧
    -Real.log (1339 / 12800) ≤ (1128761053 / 500000000) := by
  have h := checkLog_sound (w := (261 / 2939)) (n := 12)
    (lo := (89040281 / 500000000)) (hi := (178080563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1339) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1339) = 1/(1339 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1128761053 / 500000000) (-1128761051 / 500000000) (Real.log (1339 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1460771 / 2500000) ≤ -Real.log (160 / 287) ∧
    -Real.log (160 / 287) ≤ (584308401 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 447)) (n := 12)
    (lo := (1460771 / 2500000)) (hi := (584308401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287 / 160) = 1/(160 / 287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1460771 / 2500000) (584308401 / 1000000000) (Real.log (287 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (287 / 160) = -Real.log (160 / 287) := by
    rw [show ((287 / 160) : ℝ) = ((160 / 287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (394666563 / 250000000) ≤ -Real.log (33 / 160) ∧
    -Real.log (33 / 160) ≤ (315733251 / 200000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 33) = 1/(33 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-315733251 / 200000000) (-394666563 / 250000000) (Real.log (33 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (582651977 / 1000000000) ≤ -Real.log (6400 / 11461) ∧
    -Real.log (6400 / 11461) ≤ (291325989 / 500000000) := by
  have h := checkLog_sound (w := (5061 / 17861)) (n := 12)
    (lo := (582651977 / 1000000000)) (hi := (291325989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11461 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11461 / 6400) = 1/(6400 / 11461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (582651977 / 1000000000) (291325989 / 500000000) (Real.log (11461 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11461 / 6400) = -Real.log (6400 / 11461) := by
    rw [show ((11461 / 6400) : ℝ) = ((6400 / 11461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (782187461 / 500000000) ≤ -Real.log (1339 / 6400) ∧
    -Real.log (1339 / 6400) ≤ (62574997 / 40000000) := by
  have h := checkLog_sound (w := (261 / 2939)) (n := 12)
    (lo := (89040281 / 500000000)) (hi := (178080563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1339) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1339) = 1/(1339 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-62574997 / 40000000) (-782187461 / 500000000) (Real.log (1339 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (130490973 / 200000000) ≤ -Real.log (1000000 / 1920249) ∧
    -Real.log (1000000 / 1920249) ≤ (326227433 / 500000000) := by
  have h := checkLog_sound (w := (920249 / 2920249)) (n := 12)
    (lo := (130490973 / 200000000)) (hi := (326227433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1920249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1920249 / 1000000) = 1/(1000000 / 1920249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (130490973 / 200000000) (326227433 / 500000000) (Real.log (1920249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1920249 / 1000000) = -Real.log (1000000 / 1920249) := by
    rw [show ((1920249 / 1000000) : ℝ) = ((1000000 / 1920249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (632211499 / 250000000) ≤ -Real.log (79751 / 1000000) ∧
    -Real.log (79751 / 1000000) ≤ (1264423 / 500000) := by
  have h := checkLog_sound (w := (45249 / 204751)) (n := 12)
    (lo := (56175557 / 125000000)) (hi := (449404457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 79751) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 79751) = 1/(79751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1264423 / 500000) (-632211499 / 250000000) (Real.log (79751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (652978097 / 1000000000) ≤ -Real.log (500000 / 960627) ∧
    -Real.log (500000 / 960627) ≤ (326489049 / 500000000) := by
  have h := checkLog_sound (w := (460627 / 1460627)) (n := 12)
    (lo := (652978097 / 1000000000)) (hi := (326489049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960627 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(960627 / 500000) = 1/(500000 / 960627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (652978097 / 1000000000) (326489049 / 500000000) (Real.log (960627 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (960627 / 500000) = -Real.log (500000 / 960627) := by
    rw [show ((960627 / 500000) : ℝ) = ((500000 / 960627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1270763897 / 500000000) ≤ -Real.log (39373 / 500000) ∧
    -Real.log (39373 / 500000) ≤ (1270763899 / 500000000) := by
  have h := checkLog_sound (w := (23127 / 101873)) (n := 12)
    (lo := (231043127 / 500000000)) (hi := (92417251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39373) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 39373) = 1/(39373 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1270763899 / 500000000) (-1270763897 / 500000000) (Real.log (39373 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (651084833 / 1000000000) ≤ -Real.log (50000 / 95881) ∧
    -Real.log (50000 / 95881) ≤ (325542417 / 500000000) := by
  have h := checkLog_sound (w := (45881 / 145881)) (n := 12)
    (lo := (651084833 / 1000000000)) (hi := (325542417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95881 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95881 / 50000) = 1/(50000 / 95881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (651084833 / 1000000000) (325542417 / 500000000) (Real.log (95881 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (95881 / 50000) = -Real.log (50000 / 95881) := by
    rw [show ((95881 / 50000) : ℝ) = ((50000 / 95881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (624103147 / 250000000) ≤ -Real.log (4119 / 50000) ∧
    -Real.log (4119 / 50000) ≤ (156025787 / 62500000) := by
  have h := checkLog_sound (w := (2131 / 10369)) (n := 12)
    (lo := (52121381 / 125000000)) (hi := (416971049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4119) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 4119) = 1/(4119 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-156025787 / 62500000) (-624103147 / 250000000) (Real.log (4119 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (325826803 / 500000000) ≤ -Real.log (1000000 / 1918711) ∧
    -Real.log (1000000 / 1918711) ≤ (651653607 / 1000000000) := by
  have h := checkLog_sound (w := (918711 / 2918711)) (n := 12)
    (lo := (325826803 / 500000000)) (hi := (651653607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1918711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1918711 / 1000000) = 1/(1000000 / 1918711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (325826803 / 500000000) (651653607 / 1000000000) (Real.log (1918711 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1918711 / 1000000) = -Real.log (1000000 / 1918711) := by
    rw [show ((1918711 / 1000000) : ℝ) = ((1000000 / 1918711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2509744571 / 1000000000) ≤ -Real.log (81289 / 1000000) ∧
    -Real.log (81289 / 1000000) ≤ (100389783 / 40000000) := by
  have h := checkLog_sound (w := (43711 / 206289)) (n := 12)
    (lo := (430303031 / 1000000000)) (hi := (53787879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81289) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 81289) = 1/(81289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-100389783 / 40000000) (-2509744571 / 1000000000) (Real.log (81289 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3181300861 / 1000000000) ≤ -Real.log (50000000000 / 1203902772379) ∧
    -Real.log (50000000000 / 1203902772379) ≤ (1590650433 / 500000000) := by
  have h := checkLog_sound (w := (403902772379 / 2003902772379)) (n := 12)
    (lo := (408712141 / 1000000000)) (hi := (204356071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203902772379 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1203902772379 / 800000000000) = 1/(50000000000 / 1203902772379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3181300861 / 1000000000) (1590650433 / 500000000) (Real.log (1203902772379 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1203902772379 / 50000000000) = -Real.log (50000000000 / 1203902772379) := by
    rw [show ((1203902772379 / 50000000000) : ℝ) = ((50000000000 / 1203902772379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3194505891 / 1000000000) ≤ -Real.log (500000000000 / 12199057729917) ∧
    -Real.log (500000000000 / 12199057729917) ≤ (399313237 / 125000000) := by
  have h := checkLog_sound (w := (4199057729917 / 20199057729917)) (n := 12)
    (lo := (421917171 / 1000000000)) (hi := (105479293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12199057729917 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12199057729917 / 8000000000000) = 1/(500000000000 / 12199057729917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3194505891 / 1000000000) (399313237 / 125000000) (Real.log (12199057729917 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12199057729917 / 500000000000) = -Real.log (500000000000 / 12199057729917) := by
    rw [show ((12199057729917 / 500000000000) : ℝ) = ((500000000000 / 12199057729917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3147497421 / 1000000000) ≤ -Real.log (500000000000 / 11638868657441) ∧
    -Real.log (500000000000 / 11638868657441) ≤ (1573748713 / 500000000) := by
  have h := checkLog_sound (w := (3638868657441 / 19638868657441)) (n := 12)
    (lo := (374908701 / 1000000000)) (hi := (187454351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11638868657441 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11638868657441 / 8000000000000) = 1/(500000000000 / 11638868657441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3147497421 / 1000000000) (1573748713 / 500000000) (Real.log (11638868657441 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11638868657441 / 500000000000) = -Real.log (500000000000 / 11638868657441) := by
    rw [show ((11638868657441 / 500000000000) : ℝ) = ((500000000000 / 11638868657441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3161398177 / 1000000000) ≤ -Real.log (500000000000 / 11801787449717) ∧
    -Real.log (500000000000 / 11801787449717) ≤ (1580699091 / 500000000) := by
  have h := checkLog_sound (w := (3801787449717 / 19801787449717)) (n := 12)
    (lo := (388809457 / 1000000000)) (hi := (194404729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11801787449717 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11801787449717 / 8000000000000) = 1/(500000000000 / 11801787449717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3161398177 / 1000000000) (1580699091 / 500000000) (Real.log (11801787449717 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11801787449717 / 500000000000) = -Real.log (500000000000 / 11801787449717) := by
    rw [show ((11801787449717 / 500000000000) : ℝ) = ((500000000000 / 11801787449717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0167

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0168Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0168
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

theorem reflection_log_1_neg : (639424951 / 1000000000) ≤ -Real.log (12800 / 24261) ∧
    -Real.log (12800 / 24261) ≤ (79928119 / 125000000) := by
  have h := checkLog_sound (w := (11461 / 37061)) (n := 12)
    (lo := (639424951 / 1000000000)) (hi := (79928119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24261 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24261 / 12800) = 1/(12800 / 24261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (639424951 / 1000000000) (79928119 / 125000000) (Real.log (24261 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24261 / 12800) = -Real.log (12800 / 24261) := by
    rw [show ((24261 / 12800) : ℝ) = ((12800 / 24261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1128761051 / 500000000) ≤ -Real.log (1339 / 12800) ∧
    -Real.log (1339 / 12800) ≤ (1128761053 / 500000000) := by
  have h := checkLog_sound (w := (261 / 2939)) (n := 12)
    (lo := (89040281 / 500000000)) (hi := (178080563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1339) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1339) = 1/(1339 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1128761053 / 500000000) (-1128761051 / 500000000) (Real.log (1339 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (127728299 / 200000000) ≤ -Real.log (6400 / 12121) ∧
    -Real.log (6400 / 12121) ≤ (79830187 / 125000000) := by
  have h := checkLog_sound (w := (5721 / 18521)) (n := 12)
    (lo := (127728299 / 200000000)) (hi := (79830187 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12121 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12121 / 6400) = 1/(6400 / 12121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (127728299 / 200000000) (79830187 / 125000000) (Real.log (12121 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12121 / 6400) = -Real.log (6400 / 12121) := by
    rw [show ((12121 / 6400) : ℝ) = ((6400 / 12121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (112171607 / 50000000) ≤ -Real.log (679 / 6400) ∧
    -Real.log (679 / 6400) ≤ (140214509 / 62500000) := by
  have h := checkLog_sound (w := (121 / 1479)) (n := 12)
    (lo := (819953 / 5000000)) (hi := (163990601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 679) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 679) = 1/(679 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-140214509 / 62500000) (-112171607 / 50000000) (Real.log (679 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (582651977 / 1000000000) ≤ -Real.log (6400 / 11461) ∧
    -Real.log (6400 / 11461) ≤ (291325989 / 500000000) := by
  have h := checkLog_sound (w := (5061 / 17861)) (n := 12)
    (lo := (582651977 / 1000000000)) (hi := (291325989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11461 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11461 / 6400) = 1/(6400 / 11461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (582651977 / 1000000000) (291325989 / 500000000) (Real.log (11461 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11461 / 6400) = -Real.log (6400 / 11461) := by
    rw [show ((11461 / 6400) : ℝ) = ((6400 / 11461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (782187461 / 500000000) ≤ -Real.log (1339 / 6400) ∧
    -Real.log (1339 / 6400) ≤ (62574997 / 40000000) := by
  have h := checkLog_sound (w := (261 / 2939)) (n := 12)
    (lo := (89040281 / 500000000)) (hi := (178080563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1339) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1339) = 1/(1339 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-62574997 / 40000000) (-782187461 / 500000000) (Real.log (1339 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (116198561 / 200000000) ≤ -Real.log (3200 / 5721) ∧
    -Real.log (3200 / 5721) ≤ (290496403 / 500000000) := by
  have h := checkLog_sound (w := (2521 / 8921)) (n := 12)
    (lo := (116198561 / 200000000)) (hi := (290496403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5721 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5721 / 3200) = 1/(3200 / 5721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (116198561 / 200000000) (290496403 / 500000000) (Real.log (5721 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5721 / 3200) = -Real.log (3200 / 5721) := by
    rw [show ((5721 / 3200) : ℝ) = ((3200 / 5721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9689281 / 6250000) ≤ -Real.log (679 / 3200) ∧
    -Real.log (679 / 3200) ≤ (1550284963 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 1479)) (n := 12)
    (lo := (819953 / 5000000)) (hi := (163990601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 679) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 679) = 1/(679 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1550284963 / 1000000000) (-9689281 / 6250000) (Real.log (679 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (651933963 / 1000000000) ≤ -Real.log (1000000 / 1919249) ∧
    -Real.log (1000000 / 1919249) ≤ (162983491 / 250000000) := by
  have h := checkLog_sound (w := (919249 / 2919249)) (n := 12)
    (lo := (651933963 / 1000000000)) (hi := (162983491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1919249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1919249 / 1000000) = 1/(1000000 / 1919249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (651933963 / 1000000000) (162983491 / 250000000) (Real.log (1919249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1919249 / 1000000) = -Real.log (1000000 / 1919249) := by
    rw [show ((1919249 / 1000000) : ℝ) = ((1000000 / 1919249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2516384931 / 1000000000) ≤ -Real.log (80751 / 1000000) ∧
    -Real.log (80751 / 1000000) ≤ (503276987 / 200000000) := by
  have h := checkLog_sound (w := (44249 / 205751)) (n := 12)
    (lo := (436943391 / 1000000000)) (hi := (13654481 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80751) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 80751) = 1/(80751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-503276987 / 200000000) (-2516384931 / 1000000000) (Real.log (80751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (130491077 / 200000000) ≤ -Real.log (4000 / 7681) ∧
    -Real.log (4000 / 7681) ≤ (326227693 / 500000000) := by
  have h := checkLog_sound (w := (3681 / 11681)) (n := 12)
    (lo := (130491077 / 200000000)) (hi := (326227693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7681 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7681 / 4000) = 1/(4000 / 7681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (130491077 / 200000000) (326227693 / 500000000) (Real.log (7681 / 4000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (7681 / 4000) = -Real.log (4000 / 7681) := by
    rw [show ((7681 / 4000) : ℝ) = ((4000 / 7681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (505771707 / 200000000) ≤ -Real.log (319 / 4000) ∧
    -Real.log (319 / 4000) ≤ (2528858539 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 819)) (n := 12)
    (lo := (89883399 / 200000000)) (hi := (112354249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 319) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(500 / 319) = 1/(319 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2528858539 / 1000000000) (-505771707 / 200000000) (Real.log (319 / 4000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (325258651 / 500000000) ≤ -Real.log (250000 / 479133) ∧
    -Real.log (250000 / 479133) ≤ (650517303 / 1000000000) := by
  have h := checkLog_sound (w := (229133 / 729133)) (n := 12)
    (lo := (325258651 / 500000000)) (hi := (650517303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479133 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479133 / 250000) = 1/(250000 / 479133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (325258651 / 500000000) (650517303 / 1000000000) (Real.log (479133 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (479133 / 250000) = -Real.log (250000 / 479133) := by
    rw [show ((479133 / 250000) : ℝ) = ((250000 / 479133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (155205747 / 62500000) ≤ -Real.log (20867 / 250000) ∧
    -Real.log (20867 / 250000) ≤ (620822989 / 250000000) := by
  have h := checkLog_sound (w := (10383 / 52117)) (n := 12)
    (lo := (100962603 / 250000000)) (hi := (403850413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20867) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 20867) = 1/(20867 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-620822989 / 250000000) (-155205747 / 62500000) (Real.log (20867 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (130217071 / 200000000) ≤ -Real.log (1000000 / 1917621) ∧
    -Real.log (1000000 / 1917621) ≤ (162771339 / 250000000) := by
  have h := checkLog_sound (w := (917621 / 2917621)) (n := 12)
    (lo := (130217071 / 200000000)) (hi := (162771339 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1917621 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1917621 / 1000000) = 1/(1000000 / 1917621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (130217071 / 200000000) (162771339 / 250000000) (Real.log (1917621 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1917621 / 1000000) = -Real.log (1000000 / 1917621) := by
    rw [show ((1917621 / 1000000) : ℝ) = ((1000000 / 1917621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2496424727 / 1000000000) ≤ -Real.log (82379 / 1000000) ∧
    -Real.log (82379 / 1000000) ≤ (2496424731 / 1000000000) := by
  have h := checkLog_sound (w := (42621 / 207379)) (n := 12)
    (lo := (416983187 / 1000000000)) (hi := (104245797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82379) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 82379) = 1/(82379 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2496424731 / 1000000000) (-2496424727 / 1000000000) (Real.log (82379 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1584159447 / 500000000) ≤ -Real.log (500000000000 / 11883747569689) ∧
    -Real.log (500000000000 / 11883747569689) ≤ (3168318899 / 1000000000) := by
  have h := checkLog_sound (w := (3883747569689 / 19883747569689)) (n := 12)
    (lo := (197865087 / 500000000)) (hi := (15829207 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11883747569689 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11883747569689 / 8000000000000) = 1/(500000000000 / 11883747569689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1584159447 / 500000000) (3168318899 / 1000000000) (Real.log (11883747569689 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11883747569689 / 500000000000) = -Real.log (500000000000 / 11883747569689) := by
    rw [show ((11883747569689 / 500000000000) : ℝ) = ((500000000000 / 11883747569689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4970803 / 1562500) ≤ -Real.log (500000000000 / 12039184952979) ∧
    -Real.log (500000000000 / 12039184952979) ≤ (127252557 / 40000000) := by
  have h := checkLog_sound (w := (4039184952979 / 20039184952979)) (n := 12)
    (lo := (1021813 / 2500000)) (hi := (408725201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12039184952979 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12039184952979 / 8000000000000) = 1/(500000000000 / 12039184952979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4970803 / 1562500) (127252557 / 40000000) (Real.log (12039184952979 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12039184952979 / 500000000000) = -Real.log (500000000000 / 12039184952979) := by
    rw [show ((12039184952979 / 500000000000) : ℝ) = ((500000000000 / 12039184952979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1566904627 / 500000000) ≤ -Real.log (3906250000 / 89692494429) ∧
    -Real.log (3906250000 / 89692494429) ≤ (3133809259 / 1000000000) := by
  have h := checkLog_sound (w := (27192494429 / 152192494429)) (n := 12)
    (lo := (180610267 / 500000000)) (hi := (72244107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89692494429 / 62500000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(89692494429 / 62500000000) = 1/(3906250000 / 89692494429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1566904627 / 500000000) (3133809259 / 1000000000) (Real.log (89692494429 / 3906250000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (89692494429 / 3906250000) = -Real.log (3906250000 / 89692494429) := by
    rw [show ((89692494429 / 3906250000) : ℝ) = ((3906250000 / 89692494429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3147510081 / 1000000000) ≤ -Real.log (500000000000 / 11639016011363) ∧
    -Real.log (500000000000 / 11639016011363) ≤ (1573755043 / 500000000) := by
  have h := checkLog_sound (w := (3639016011363 / 19639016011363)) (n := 12)
    (lo := (374921361 / 1000000000)) (hi := (187460681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11639016011363 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11639016011363 / 8000000000000) = 1/(500000000000 / 11639016011363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3147510081 / 1000000000) (1573755043 / 500000000) (Real.log (11639016011363 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11639016011363 / 500000000000) = -Real.log (500000000000 / 11639016011363) := by
    rw [show ((11639016011363 / 500000000000) : ℝ) = ((500000000000 / 11639016011363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0168

end


