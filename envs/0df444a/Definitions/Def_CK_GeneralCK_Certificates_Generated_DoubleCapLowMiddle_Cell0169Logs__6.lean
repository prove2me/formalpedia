-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0169Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0169Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:54:14.743975+00:00
-- url     : https://prove2.me/theorems/6672526a-f9ad-4485-8408-4268ac4e7616
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0169Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0170Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0169Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0170Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0171Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0172Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0173Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0174Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0169Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0170Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0171Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0172Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0173Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0174Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0169Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0170Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0171Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0172Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0173Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0174Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0169Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0170Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0171Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0172Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0173Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0174Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0169Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0169
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

theorem reflection_log_1_neg : (127728299 / 200000000) ≤ -Real.log (6400 / 12121) ∧
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


theorem reflection_log_1 : Bounds (127728299 / 200000000) (79830187 / 125000000) (Real.log (12121 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12121 / 6400) = -Real.log (6400 / 12121) := by
    rw [show ((12121 / 6400) : ℝ) = ((6400 / 12121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (112171607 / 50000000) ≤ -Real.log (679 / 6400) ∧
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


theorem reflection_log_2 : Bounds (-140214509 / 62500000) (-112171607 / 50000000) (Real.log (679 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (39866089 / 62500000) ≤ -Real.log (12800 / 24223) ∧
    -Real.log (12800 / 24223) ≤ (25514297 / 40000000) := by
  have h := checkLog_sound (w := (11423 / 37023)) (n := 12)
    (lo := (39866089 / 62500000)) (hi := (25514297 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24223 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24223 / 12800) = 1/(12800 / 24223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (39866089 / 62500000) (25514297 / 40000000) (Real.log (24223 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24223 / 12800) = -Real.log (12800 / 24223) := by
    rw [show ((24223 / 12800) : ℝ) = ((12800 / 24223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2229537949 / 1000000000) ≤ -Real.log (1377 / 12800) ∧
    -Real.log (1377 / 12800) ≤ (2229537953 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 2977)) (n := 12)
    (lo := (150096409 / 1000000000)) (hi := (15009641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1377) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1377) = 1/(1377 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2229537953 / 1000000000) (-2229537949 / 1000000000) (Real.log (1377 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (116198561 / 200000000) ≤ -Real.log (3200 / 5721) ∧
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


theorem reflection_log_5 : Bounds (116198561 / 200000000) (290496403 / 500000000) (Real.log (5721 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5721 / 3200) = -Real.log (3200 / 5721) := by
    rw [show ((5721 / 3200) : ℝ) = ((3200 / 5721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9689281 / 6250000) ≤ -Real.log (679 / 3200) ∧
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


theorem reflection_log_6 : Bounds (-1550284963 / 1000000000) (-9689281 / 6250000) (Real.log (679 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (144832719 / 250000000) ≤ -Real.log (6400 / 11423) ∧
    -Real.log (6400 / 11423) ≤ (579330877 / 1000000000) := by
  have h := checkLog_sound (w := (5023 / 17823)) (n := 12)
    (lo := (144832719 / 250000000)) (hi := (579330877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11423 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11423 / 6400) = 1/(6400 / 11423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (144832719 / 250000000) (579330877 / 1000000000) (Real.log (11423 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11423 / 6400) = -Real.log (6400 / 11423) := by
    rw [show ((11423 / 6400) : ℝ) = ((6400 / 11423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1536390769 / 1000000000) ≤ -Real.log (1377 / 6400) ∧
    -Real.log (1377 / 6400) ≤ (384097693 / 250000000) := by
  have h := checkLog_sound (w := (223 / 2977)) (n := 12)
    (lo := (150096409 / 1000000000)) (hi := (15009641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1377) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1377) = 1/(1377 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-384097693 / 250000000) (-1536390769 / 1000000000) (Real.log (1377 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (325707177 / 500000000) ≤ -Real.log (250000 / 479563) ∧
    -Real.log (250000 / 479563) ≤ (130282871 / 200000000) := by
  have h := checkLog_sound (w := (229563 / 729563)) (n := 12)
    (lo := (325707177 / 500000000)) (hi := (130282871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479563 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479563 / 250000) = 1/(250000 / 479563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (325707177 / 500000000) (130282871 / 200000000) (Real.log (479563 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (479563 / 250000) = -Real.log (250000 / 479563) := by
    rw [show ((479563 / 250000) : ℝ) = ((250000 / 479563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (626028483 / 250000000) ≤ -Real.log (20437 / 250000) ∧
    -Real.log (20437 / 250000) ≤ (156507121 / 62500000) := by
  have h := checkLog_sound (w := (10813 / 51687)) (n := 12)
    (lo := (53084049 / 125000000)) (hi := (424672393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20437) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 20437) = 1/(20437 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-156507121 / 62500000) (-626028483 / 250000000) (Real.log (20437 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (162983621 / 250000000) ≤ -Real.log (4000 / 7677) ∧
    -Real.log (4000 / 7677) ≤ (130386897 / 200000000) := by
  have h := checkLog_sound (w := (3677 / 11677)) (n := 12)
    (lo := (162983621 / 250000000)) (hi := (130386897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7677 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7677 / 4000) = 1/(4000 / 7677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (162983621 / 250000000) (130386897 / 200000000) (Real.log (7677 / 4000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (7677 / 4000) = -Real.log (4000 / 7677) := by
    rw [show ((7677 / 4000) : ℝ) = ((4000 / 7677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (503279463 / 200000000) ≤ -Real.log (323 / 4000) ∧
    -Real.log (323 / 4000) ≤ (2516397319 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 823)) (n := 12)
    (lo := (17478231 / 40000000)) (hi := (3413717 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 323) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(500 / 323) = 1/(323 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2516397319 / 1000000000) (-503279463 / 200000000) (Real.log (323 / 4000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (649949971 / 1000000000) ≤ -Real.log (200000 / 383089) ∧
    -Real.log (200000 / 383089) ≤ (162487493 / 250000000) := by
  have h := checkLog_sound (w := (183089 / 583089)) (n := 12)
    (lo := (649949971 / 1000000000)) (hi := (162487493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383089 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383089 / 200000) = 1/(200000 / 383089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (649949971 / 1000000000) (162487493 / 250000000) (Real.log (383089 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (383089 / 200000) = -Real.log (200000 / 383089) := by
    rw [show ((383089 / 200000) : ℝ) = ((200000 / 383089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2470353067 / 1000000000) ≤ -Real.log (16911 / 200000) ∧
    -Real.log (16911 / 200000) ≤ (2470353071 / 1000000000) := by
  have h := checkLog_sound (w := (8089 / 41911)) (n := 12)
    (lo := (390911527 / 1000000000)) (hi := (48863941 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 16911) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 16911) = 1/(16911 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2470353071 / 1000000000) (-2470353067 / 1000000000) (Real.log (16911 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (10164341 / 15625000) ≤ -Real.log (1000000 / 1916533) ∧
    -Real.log (1000000 / 1916533) ≤ (26020713 / 40000000) := by
  have h := checkLog_sound (w := (916533 / 2916533)) (n := 12)
    (lo := (10164341 / 15625000)) (hi := (26020713 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1916533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1916533 / 1000000) = 1/(1000000 / 1916533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (10164341 / 15625000) (26020713 / 40000000) (Real.log (1916533 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1916533 / 1000000) = -Real.log (1000000 / 1916533) := by
    rw [show ((1916533 / 1000000) : ℝ) = ((1000000 / 1916533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2483303933 / 1000000000) ≤ -Real.log (83467 / 1000000) ∧
    -Real.log (83467 / 1000000) ≤ (2483303937 / 1000000000) := by
  have h := checkLog_sound (w := (41533 / 208467)) (n := 12)
    (lo := (403862393 / 1000000000)) (hi := (201931197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 83467) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 83467) = 1/(83467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2483303937 / 1000000000) (-2483303933 / 1000000000) (Real.log (83467 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1577764143 / 500000000) ≤ -Real.log (500000000000 / 11732715173459) ∧
    -Real.log (500000000000 / 11732715173459) ≤ (3155528291 / 1000000000) := by
  have h := checkLog_sound (w := (3732715173459 / 19732715173459)) (n := 12)
    (lo := (191469783 / 500000000)) (hi := (382939567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11732715173459 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11732715173459 / 8000000000000) = 1/(500000000000 / 11732715173459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1577764143 / 500000000) (3155528291 / 1000000000) (Real.log (11732715173459 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11732715173459 / 500000000000) = -Real.log (500000000000 / 11732715173459) := by
    rw [show ((11732715173459 / 500000000000) : ℝ) = ((500000000000 / 11732715173459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3168331799 / 1000000000) ≤ -Real.log (500000000000 / 11883900928793) ∧
    -Real.log (500000000000 / 11883900928793) ≤ (792082951 / 250000000) := by
  have h := checkLog_sound (w := (3883900928793 / 19883900928793)) (n := 12)
    (lo := (395743079 / 1000000000)) (hi := (9893577 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11883900928793 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11883900928793 / 8000000000000) = 1/(500000000000 / 11883900928793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3168331799 / 1000000000) (792082951 / 250000000) (Real.log (11883900928793 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11883900928793 / 500000000000) = -Real.log (500000000000 / 11883900928793) := by
    rw [show ((11883900928793 / 500000000000) : ℝ) = ((500000000000 / 11883900928793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1560151519 / 500000000) ≤ -Real.log (7812500000 / 176978464461) ∧
    -Real.log (7812500000 / 176978464461) ≤ (3120303043 / 1000000000) := by
  have h := checkLog_sound (w := (51978464461 / 301978464461)) (n := 12)
    (lo := (173857159 / 500000000)) (hi := (347714319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176978464461 / 125000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(176978464461 / 125000000000) = 1/(7812500000 / 176978464461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1560151519 / 500000000) (3120303043 / 1000000000) (Real.log (176978464461 / 7812500000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (176978464461 / 7812500000) = -Real.log (7812500000 / 176978464461) := by
    rw [show ((176978464461 / 7812500000) : ℝ) = ((7812500000 / 176978464461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3133821757 / 1000000000) ≤ -Real.log (10000000000 / 229615656487) ∧
    -Real.log (10000000000 / 229615656487) ≤ (1566910881 / 500000000) := by
  have h := checkLog_sound (w := (69615656487 / 389615656487)) (n := 12)
    (lo := (361233037 / 1000000000)) (hi := (180616519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229615656487 / 160000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(229615656487 / 160000000000) = 1/(10000000000 / 229615656487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3133821757 / 1000000000) (1566910881 / 500000000) (Real.log (229615656487 / 10000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (229615656487 / 10000000000) = -Real.log (10000000000 / 229615656487) := by
    rw [show ((229615656487 / 10000000000) : ℝ) = ((10000000000 / 229615656487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0169

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0170Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0170
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

theorem reflection_log_1_neg : (39866089 / 62500000) ≤ -Real.log (12800 / 24223) ∧
    -Real.log (12800 / 24223) ≤ (25514297 / 40000000) := by
  have h := checkLog_sound (w := (11423 / 37023)) (n := 12)
    (lo := (39866089 / 62500000)) (hi := (25514297 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24223 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24223 / 12800) = 1/(12800 / 24223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (39866089 / 62500000) (25514297 / 40000000) (Real.log (24223 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24223 / 12800) = -Real.log (12800 / 24223) := by
    rw [show ((24223 / 12800) : ℝ) = ((12800 / 24223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2229537949 / 1000000000) ≤ -Real.log (1377 / 12800) ∧
    -Real.log (1377 / 12800) ≤ (2229537953 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 2977)) (n := 12)
    (lo := (150096409 / 1000000000)) (hi := (15009641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1377) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1377) = 1/(1377 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2229537953 / 1000000000) (-2229537949 / 1000000000) (Real.log (1377 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (637072737 / 1000000000) ≤ -Real.log (3200 / 6051) ∧
    -Real.log (3200 / 6051) ≤ (318536369 / 500000000) := by
  have h := checkLog_sound (w := (2851 / 9251)) (n := 12)
    (lo := (637072737 / 1000000000)) (hi := (318536369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6051 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6051 / 3200) = 1/(3200 / 6051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (637072737 / 1000000000) (318536369 / 500000000) (Real.log (6051 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6051 / 3200) = -Real.log (3200 / 6051) := by
    rw [show ((6051 / 3200) : ℝ) = ((3200 / 6051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (553958541 / 250000000) ≤ -Real.log (349 / 3200) ∧
    -Real.log (349 / 3200) ≤ (276979271 / 125000000) := by
  have h := checkLog_sound (w := (51 / 749)) (n := 12)
    (lo := (8524539 / 62500000)) (hi := (1091141 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 349) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 349) = 1/(349 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-276979271 / 125000000) (-553958541 / 250000000) (Real.log (349 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (144832719 / 250000000) ≤ -Real.log (6400 / 11423) ∧
    -Real.log (6400 / 11423) ≤ (579330877 / 1000000000) := by
  have h := checkLog_sound (w := (5023 / 17823)) (n := 12)
    (lo := (144832719 / 250000000)) (hi := (579330877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11423 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11423 / 6400) = 1/(6400 / 11423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (144832719 / 250000000) (579330877 / 1000000000) (Real.log (11423 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11423 / 6400) = -Real.log (6400 / 11423) := by
    rw [show ((11423 / 6400) : ℝ) = ((6400 / 11423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1536390769 / 1000000000) ≤ -Real.log (1377 / 6400) ∧
    -Real.log (1377 / 6400) ≤ (384097693 / 250000000) := by
  have h := checkLog_sound (w := (223 / 2977)) (n := 12)
    (lo := (150096409 / 1000000000)) (hi := (15009641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1377) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1377) = 1/(1377 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-384097693 / 250000000) (-1536390769 / 1000000000) (Real.log (1377 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (28883309 / 50000000) ≤ -Real.log (1600 / 2851) ∧
    -Real.log (1600 / 2851) ≤ (577666181 / 1000000000) := by
  have h := checkLog_sound (w := (1251 / 4451)) (n := 12)
    (lo := (28883309 / 50000000)) (hi := (577666181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2851 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2851 / 1600) = 1/(1600 / 2851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (28883309 / 50000000) (577666181 / 1000000000) (Real.log (2851 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2851 / 1600) = -Real.log (1600 / 2851) := by
    rw [show ((2851 / 1600) : ℝ) = ((1600 / 2851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (190335873 / 125000000) ≤ -Real.log (349 / 1600) ∧
    -Real.log (349 / 1600) ≤ (1522686987 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 749)) (n := 12)
    (lo := (8524539 / 62500000)) (hi := (1091141 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 349) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 349) = 1/(349 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1522686987 / 1000000000) (-190335873 / 125000000) (Real.log (349 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (650896561 / 1000000000) ≤ -Real.log (1000000 / 1917259) ∧
    -Real.log (1000000 / 1917259) ≤ (325448281 / 500000000) := by
  have h := checkLog_sound (w := (917259 / 2917259)) (n := 12)
    (lo := (650896561 / 1000000000)) (hi := (325448281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1917259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1917259 / 1000000) = 1/(1000000 / 1917259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (650896561 / 1000000000) (325448281 / 500000000) (Real.log (1917259 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1917259 / 1000000) = -Real.log (1000000 / 1917259) := by
    rw [show ((1917259 / 1000000) : ℝ) = ((1000000 / 1917259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (249204003 / 100000000) ≤ -Real.log (82741 / 1000000) ∧
    -Real.log (82741 / 1000000) ≤ (1246020017 / 500000000) := by
  have h := checkLog_sound (w := (42259 / 207741)) (n := 12)
    (lo := (41259849 / 100000000)) (hi := (412598491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82741) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 82741) = 1/(82741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1246020017 / 500000000) (-249204003 / 100000000) (Real.log (82741 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (5211319 / 8000000) ≤ -Real.log (1000000 / 1918253) ∧
    -Real.log (1000000 / 1918253) ≤ (651414877 / 1000000000) := by
  have h := checkLog_sound (w := (918253 / 2918253)) (n := 12)
    (lo := (5211319 / 8000000)) (hi := (651414877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1918253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1918253 / 1000000) = 1/(1000000 / 1918253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (5211319 / 8000000) (651414877 / 1000000000) (Real.log (1918253 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1918253 / 1000000) = -Real.log (1000000 / 1918253) := by
    rw [show ((1918253 / 1000000) : ℝ) = ((1000000 / 1918253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (500825233 / 200000000) ≤ -Real.log (81747 / 1000000) ∧
    -Real.log (81747 / 1000000) ≤ (2504126169 / 1000000000) := by
  have h := checkLog_sound (w := (43253 / 206747)) (n := 12)
    (lo := (3397477 / 8000000)) (hi := (212342313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81747) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 81747) = 1/(81747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2504126169 / 1000000000) (-500825233 / 200000000) (Real.log (81747 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (649383363 / 1000000000) ≤ -Real.log (25000 / 47859) ∧
    -Real.log (25000 / 47859) ≤ (162345841 / 250000000) := by
  have h := checkLog_sound (w := (22859 / 72859)) (n := 12)
    (lo := (649383363 / 1000000000)) (hi := (162345841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47859 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47859 / 25000) = 1/(25000 / 47859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (649383363 / 1000000000) (162345841 / 250000000) (Real.log (47859 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (47859 / 25000) = -Real.log (25000 / 47859) := by
    rw [show ((47859 / 25000) : ℝ) = ((25000 / 47859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2457602813 / 1000000000) ≤ -Real.log (2141 / 25000) ∧
    -Real.log (2141 / 25000) ≤ (2457602817 / 1000000000) := by
  have h := checkLog_sound (w := (492 / 2633)) (n := 12)
    (lo := (378161273 / 1000000000)) (hi := (189080637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2141) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 2141) = 1/(2141 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2457602817 / 1000000000) (-2457602813 / 1000000000) (Real.log (2141 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (649950493 / 1000000000) ≤ -Real.log (500000 / 957723) ∧
    -Real.log (500000 / 957723) ≤ (324975247 / 500000000) := by
  have h := checkLog_sound (w := (457723 / 1457723)) (n := 12)
    (lo := (649950493 / 1000000000)) (hi := (324975247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957723 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957723 / 500000) = 1/(500000 / 957723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (649950493 / 1000000000) (324975247 / 500000000) (Real.log (957723 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (957723 / 500000) = -Real.log (500000 / 957723) := by
    rw [show ((957723 / 500000) : ℝ) = ((500000 / 957723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2470364893 / 1000000000) ≤ -Real.log (42277 / 500000) ∧
    -Real.log (42277 / 500000) ≤ (2470364897 / 1000000000) := by
  have h := checkLog_sound (w := (20223 / 104777)) (n := 12)
    (lo := (390923353 / 1000000000)) (hi := (195461677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42277) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 42277) = 1/(42277 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2470364897 / 1000000000) (-2470364893 / 1000000000) (Real.log (42277 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3142936591 / 1000000000) ≤ -Real.log (100000000000 / 2317181324857) ∧
    -Real.log (100000000000 / 2317181324857) ≤ (785734149 / 250000000) := by
  have h := checkLog_sound (w := (717181324857 / 3917181324857)) (n := 12)
    (lo := (370347871 / 1000000000)) (hi := (11573371 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2317181324857 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2317181324857 / 1600000000000) = 1/(100000000000 / 2317181324857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3142936591 / 1000000000) (785734149 / 250000000) (Real.log (2317181324857 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2317181324857 / 100000000000) = -Real.log (100000000000 / 2317181324857) := by
    rw [show ((2317181324857 / 100000000000) : ℝ) = ((100000000000 / 2317181324857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (39444263 / 12500000) ≤ -Real.log (500000000000 / 11732864814611) ∧
    -Real.log (500000000000 / 11732864814611) ≤ (631108209 / 200000000) := by
  have h := checkLog_sound (w := (3732864814611 / 19732864814611)) (n := 12)
    (lo := (598363 / 1562500)) (hi := (382952321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11732864814611 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11732864814611 / 8000000000000) = 1/(500000000000 / 11732864814611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (39444263 / 12500000) (631108209 / 200000000) (Real.log (11732864814611 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11732864814611 / 500000000000) = -Real.log (500000000000 / 11732864814611) := by
    rw [show ((11732864814611 / 500000000000) : ℝ) = ((500000000000 / 11732864814611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (48546659 / 15625000) ≤ -Real.log (500000000000 / 11176786548341) ∧
    -Real.log (500000000000 / 11176786548341) ≤ (3106986181 / 1000000000) := by
  have h := checkLog_sound (w := (3176786548341 / 19176786548341)) (n := 12)
    (lo := (20899841 / 62500000)) (hi := (334397457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11176786548341 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11176786548341 / 8000000000000) = 1/(500000000000 / 11176786548341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (48546659 / 15625000) (3106986181 / 1000000000) (Real.log (11176786548341 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11176786548341 / 500000000000) = -Real.log (500000000000 / 11176786548341) := by
    rw [show ((11176786548341 / 500000000000) : ℝ) = ((500000000000 / 11176786548341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1560157693 / 500000000) ≤ -Real.log (25000000000 / 566338079807) ∧
    -Real.log (25000000000 / 566338079807) ≤ (3120315391 / 1000000000) := by
  have h := checkLog_sound (w := (166338079807 / 966338079807)) (n := 12)
    (lo := (173863333 / 500000000)) (hi := (347726667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566338079807 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(566338079807 / 400000000000) = 1/(25000000000 / 566338079807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1560157693 / 500000000) (3120315391 / 1000000000) (Real.log (566338079807 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (566338079807 / 25000000000) = -Real.log (25000000000 / 566338079807) := by
    rw [show ((566338079807 / 25000000000) : ℝ) = ((25000000000 / 566338079807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0170

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0171Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0171
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

theorem reflection_log_1_neg : (637072737 / 1000000000) ≤ -Real.log (3200 / 6051) ∧
    -Real.log (3200 / 6051) ≤ (318536369 / 500000000) := by
  have h := checkLog_sound (w := (2851 / 9251)) (n := 12)
    (lo := (637072737 / 1000000000)) (hi := (318536369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6051 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6051 / 3200) = 1/(3200 / 6051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (637072737 / 1000000000) (318536369 / 500000000) (Real.log (6051 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6051 / 3200) = -Real.log (3200 / 6051) := by
    rw [show ((6051 / 3200) : ℝ) = ((3200 / 6051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (553958541 / 250000000) ≤ -Real.log (349 / 3200) ∧
    -Real.log (349 / 3200) ≤ (276979271 / 125000000) := by
  have h := checkLog_sound (w := (51 / 749)) (n := 12)
    (lo := (8524539 / 62500000)) (hi := (1091141 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 349) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 349) = 1/(349 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-276979271 / 125000000) (-553958541 / 250000000) (Real.log (349 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (127257487 / 200000000) ≤ -Real.log (2560 / 4837) ∧
    -Real.log (2560 / 4837) ≤ (159071859 / 250000000) := by
  have h := checkLog_sound (w := (2277 / 7397)) (n := 12)
    (lo := (127257487 / 200000000)) (hi := (159071859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4837 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4837 / 2560) = 1/(2560 / 4837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (127257487 / 200000000) (159071859 / 250000000) (Real.log (4837 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4837 / 2560) = -Real.log (2560 / 4837) := by
    rw [show ((4837 / 2560) : ℝ) = ((2560 / 4837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1101157819 / 500000000) ≤ -Real.log (283 / 2560) ∧
    -Real.log (283 / 2560) ≤ (1101157821 / 500000000) := by
  have h := checkLog_sound (w := (37 / 603)) (n := 12)
    (lo := (61437049 / 500000000)) (hi := (122874099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 283) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 283) = 1/(283 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1101157821 / 500000000) (-1101157819 / 500000000) (Real.log (283 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (28883309 / 50000000) ≤ -Real.log (1600 / 2851) ∧
    -Real.log (1600 / 2851) ≤ (577666181 / 1000000000) := by
  have h := checkLog_sound (w := (1251 / 4451)) (n := 12)
    (lo := (28883309 / 50000000)) (hi := (577666181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2851 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2851 / 1600) = 1/(1600 / 2851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (28883309 / 50000000) (577666181 / 1000000000) (Real.log (2851 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2851 / 1600) = -Real.log (1600 / 2851) := by
    rw [show ((2851 / 1600) : ℝ) = ((1600 / 2851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (190335873 / 125000000) ≤ -Real.log (349 / 1600) ∧
    -Real.log (349 / 1600) ≤ (1522686987 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 749)) (n := 12)
    (lo := (8524539 / 62500000)) (hi := (1091141 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 349) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 349) = 1/(349 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1522686987 / 1000000000) (-190335873 / 125000000) (Real.log (349 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (575998709 / 1000000000) ≤ -Real.log (1280 / 2277) ∧
    -Real.log (1280 / 2277) ≤ (57599871 / 100000000) := by
  have h := checkLog_sound (w := (997 / 3557)) (n := 12)
    (lo := (575998709 / 1000000000)) (hi := (57599871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2277 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2277 / 1280) = 1/(1280 / 2277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (575998709 / 1000000000) (57599871 / 100000000) (Real.log (2277 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2277 / 1280) = -Real.log (1280 / 2277) := by
    rw [show ((2277 / 1280) : ℝ) = ((1280 / 2277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (754584229 / 500000000) ≤ -Real.log (283 / 1280) ∧
    -Real.log (283 / 1280) ≤ (1509168461 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 603)) (n := 12)
    (lo := (61437049 / 500000000)) (hi := (122874099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 283) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 283) = 1/(283 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1509168461 / 1000000000) (-754584229 / 500000000) (Real.log (283 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (81297443 / 125000000) ≤ -Real.log (250000 / 479067) ∧
    -Real.log (250000 / 479067) ≤ (130075909 / 200000000) := by
  have h := checkLog_sound (w := (229067 / 729067)) (n := 12)
    (lo := (81297443 / 125000000)) (hi := (130075909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479067 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479067 / 250000) = 1/(250000 / 479067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (81297443 / 125000000) (130075909 / 200000000) (Real.log (479067 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (479067 / 250000) = -Real.log (250000 / 479067) := by
    rw [show ((479067 / 250000) : ℝ) = ((250000 / 479067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (496026811 / 200000000) ≤ -Real.log (20933 / 250000) ∧
    -Real.log (20933 / 250000) ≤ (2480134059 / 1000000000) := by
  have h := checkLog_sound (w := (10317 / 52183)) (n := 12)
    (lo := (80138503 / 200000000)) (hi := (100173129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20933) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 20933) = 1/(20933 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2480134059 / 1000000000) (-496026811 / 200000000) (Real.log (20933 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (650897083 / 1000000000) ≤ -Real.log (50000 / 95863) ∧
    -Real.log (50000 / 95863) ≤ (162724271 / 250000000) := by
  have h := checkLog_sound (w := (45863 / 145863)) (n := 12)
    (lo := (650897083 / 1000000000)) (hi := (162724271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95863 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95863 / 50000) = 1/(50000 / 95863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (650897083 / 1000000000) (162724271 / 250000000) (Real.log (95863 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (95863 / 50000) = -Real.log (50000 / 95863) := by
    rw [show ((95863 / 50000) : ℝ) = ((50000 / 95863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (623013029 / 250000000) ≤ -Real.log (4137 / 50000) ∧
    -Real.log (4137 / 50000) ≤ (62301303 / 25000000) := by
  have h := checkLog_sound (w := (2113 / 10387)) (n := 12)
    (lo := (25788161 / 62500000)) (hi := (412610577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4137) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 4137) = 1/(4137 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-62301303 / 25000000) (-623013029 / 250000000) (Real.log (4137 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (162204239 / 250000000) ≤ -Real.log (250000 / 478319) ∧
    -Real.log (250000 / 478319) ≤ (648816957 / 1000000000) := by
  have h := checkLog_sound (w := (228319 / 728319)) (n := 12)
    (lo := (162204239 / 250000000)) (hi := (648816957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((478319 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(478319 / 250000) = 1/(250000 / 478319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (162204239 / 250000000) (648816957 / 1000000000) (Real.log (478319 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (478319 / 250000) = -Real.log (250000 / 478319) := by
    rw [show ((478319 / 250000) : ℝ) = ((250000 / 478319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (489004923 / 200000000) ≤ -Real.log (21681 / 250000) ∧
    -Real.log (21681 / 250000) ≤ (2445024619 / 1000000000) := by
  have h := checkLog_sound (w := (9569 / 52931)) (n := 12)
    (lo := (14623323 / 40000000)) (hi := (91395769 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21681) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 21681) = 1/(21681 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2445024619 / 1000000000) (-489004923 / 200000000) (Real.log (21681 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (129876777 / 200000000) ≤ -Real.log (1000000 / 1914361) ∧
    -Real.log (1000000 / 1914361) ≤ (324691943 / 500000000) := by
  have h := checkLog_sound (w := (914361 / 2914361)) (n := 12)
    (lo := (129876777 / 200000000)) (hi := (324691943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1914361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1914361 / 1000000) = 1/(1000000 / 1914361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (129876777 / 200000000) (324691943 / 500000000) (Real.log (1914361 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1914361 / 1000000) = -Real.log (1000000 / 1914361) := by
    rw [show ((1914361 / 1000000) : ℝ) = ((1000000 / 1914361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (245761449 / 100000000) ≤ -Real.log (85639 / 1000000) ∧
    -Real.log (85639 / 1000000) ≤ (1228807247 / 500000000) := by
  have h := checkLog_sound (w := (39361 / 210639)) (n := 12)
    (lo := (7563459 / 20000000)) (hi := (378172951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 85639) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 85639) = 1/(85639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1228807247 / 500000000) (-245761449 / 100000000) (Real.log (85639 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3130513599 / 1000000000) ≤ -Real.log (2000000000 / 45771461329) ∧
    -Real.log (2000000000 / 45771461329) ≤ (782628401 / 250000000) := by
  have h := checkLog_sound (w := (13771461329 / 77771461329)) (n := 12)
    (lo := (357924879 / 1000000000)) (hi := (4474061 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45771461329 / 32000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(45771461329 / 32000000000) = 1/(2000000000 / 45771461329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3130513599 / 1000000000) (782628401 / 250000000) (Real.log (45771461329 / 2000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (45771461329 / 2000000000) = -Real.log (2000000000 / 45771461329) := by
    rw [show ((45771461329 / 2000000000) : ℝ) = ((2000000000 / 45771461329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3142949199 / 1000000000) ≤ -Real.log (50000000000 / 1158605269519) ∧
    -Real.log (50000000000 / 1158605269519) ≤ (785737301 / 250000000) := by
  have h := checkLog_sound (w := (358605269519 / 1958605269519)) (n := 12)
    (lo := (370360479 / 1000000000)) (hi := (2314753 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158605269519 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1158605269519 / 800000000000) = 1/(50000000000 / 1158605269519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3142949199 / 1000000000) (785737301 / 250000000) (Real.log (1158605269519 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1158605269519 / 50000000000) = -Real.log (50000000000 / 1158605269519) := by
    rw [show ((1158605269519 / 50000000000) : ℝ) = ((50000000000 / 1158605269519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (309384157 / 100000000) ≤ -Real.log (500000000000 / 11030833448641) ∧
    -Real.log (500000000000 / 11030833448641) ≤ (123753663 / 40000000) := by
  have h := checkLog_sound (w := (3030833448641 / 19030833448641)) (n := 12)
    (lo := (6425057 / 20000000)) (hi := (321252851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11030833448641 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11030833448641 / 8000000000000) = 1/(500000000000 / 11030833448641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (309384157 / 100000000) (123753663 / 40000000) (Real.log (11030833448641 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11030833448641 / 500000000000) = -Real.log (500000000000 / 11030833448641) := by
    rw [show ((11030833448641 / 500000000000) : ℝ) = ((500000000000 / 11030833448641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (24855987 / 8000000) ≤ -Real.log (500000000000 / 11176922897279) ∧
    -Real.log (500000000000 / 11176922897279) ≤ (155349919 / 50000000) := by
  have h := checkLog_sound (w := (3176922897279 / 19176922897279)) (n := 12)
    (lo := (66881931 / 200000000)) (hi := (41801207 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11176922897279 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11176922897279 / 8000000000000) = 1/(500000000000 / 11176922897279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (24855987 / 8000000) (155349919 / 50000000) (Real.log (11176922897279 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11176922897279 / 500000000000) = -Real.log (500000000000 / 11176922897279) := by
    rw [show ((11176922897279 / 500000000000) : ℝ) = ((500000000000 / 11176922897279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0171

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0172Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0172
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

theorem reflection_log_1_neg : (127257487 / 200000000) ≤ -Real.log (2560 / 4837) ∧
    -Real.log (2560 / 4837) ≤ (159071859 / 250000000) := by
  have h := checkLog_sound (w := (2277 / 7397)) (n := 12)
    (lo := (127257487 / 200000000)) (hi := (159071859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4837 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4837 / 2560) = 1/(2560 / 4837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (127257487 / 200000000) (159071859 / 250000000) (Real.log (4837 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4837 / 2560) = -Real.log (2560 / 4837) := by
    rw [show ((4837 / 2560) : ℝ) = ((2560 / 4837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1101157819 / 500000000) ≤ -Real.log (283 / 2560) ∧
    -Real.log (283 / 2560) ≤ (1101157821 / 500000000) := by
  have h := checkLog_sound (w := (37 / 603)) (n := 12)
    (lo := (61437049 / 500000000)) (hi := (122874099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 283) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 283) = 1/(283 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1101157821 / 500000000) (-1101157819 / 500000000) (Real.log (283 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (127100303 / 200000000) ≤ -Real.log (6400 / 12083) ∧
    -Real.log (6400 / 12083) ≤ (158875379 / 250000000) := by
  have h := checkLog_sound (w := (5683 / 18483)) (n := 12)
    (lo := (127100303 / 200000000)) (hi := (158875379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12083 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12083 / 6400) = 1/(6400 / 12083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (127100303 / 200000000) (158875379 / 250000000) (Real.log (12083 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12083 / 6400) = -Real.log (6400 / 12083) := by
    rw [show ((12083 / 6400) : ℝ) = ((6400 / 12083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2188977427 / 1000000000) ≤ -Real.log (717 / 6400) ∧
    -Real.log (717 / 6400) ≤ (2188977431 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 1517)) (n := 12)
    (lo := (109535887 / 1000000000)) (hi := (6845993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 717) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 717) = 1/(717 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2188977431 / 1000000000) (-2188977427 / 1000000000) (Real.log (717 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (575998709 / 1000000000) ≤ -Real.log (1280 / 2277) ∧
    -Real.log (1280 / 2277) ≤ (57599871 / 100000000) := by
  have h := checkLog_sound (w := (997 / 3557)) (n := 12)
    (lo := (575998709 / 1000000000)) (hi := (57599871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2277 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2277 / 1280) = 1/(1280 / 2277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (575998709 / 1000000000) (57599871 / 100000000) (Real.log (2277 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2277 / 1280) = -Real.log (1280 / 2277) := by
    rw [show ((2277 / 1280) : ℝ) = ((1280 / 2277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (754584229 / 500000000) ≤ -Real.log (283 / 1280) ∧
    -Real.log (283 / 1280) ≤ (1509168461 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 603)) (n := 12)
    (lo := (61437049 / 500000000)) (hi := (122874099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 283) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 283) = 1/(283 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1509168461 / 1000000000) (-754584229 / 500000000) (Real.log (283 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (143582113 / 250000000) ≤ -Real.log (3200 / 5683) ∧
    -Real.log (3200 / 5683) ≤ (574328453 / 1000000000) := by
  have h := checkLog_sound (w := (2483 / 8883)) (n := 12)
    (lo := (143582113 / 250000000)) (hi := (574328453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5683 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5683 / 3200) = 1/(3200 / 5683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (143582113 / 250000000) (574328453 / 1000000000) (Real.log (5683 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5683 / 3200) = -Real.log (3200 / 5683) := by
    rw [show ((5683 / 3200) : ℝ) = ((3200 / 5683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1495830247 / 1000000000) ≤ -Real.log (717 / 3200) ∧
    -Real.log (717 / 3200) ≤ (5983321 / 4000000) := by
  have h := checkLog_sound (w := (83 / 1517)) (n := 12)
    (lo := (109535887 / 1000000000)) (hi := (6845993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 717) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 717) = 1/(717 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5983321 / 4000000) (-1495830247 / 1000000000) (Real.log (717 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (162466087 / 250000000) ≤ -Real.log (1000000 / 1915281) ∧
    -Real.log (1000000 / 1915281) ≤ (649864349 / 1000000000) := by
  have h := checkLog_sound (w := (915281 / 2915281)) (n := 12)
    (lo := (162466087 / 250000000)) (hi := (649864349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1915281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1915281 / 1000000) = 1/(1000000 / 1915281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (162466087 / 250000000) (649864349 / 1000000000) (Real.log (1915281 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1915281 / 1000000) = -Real.log (1000000 / 1915281) := by
    rw [show ((1915281 / 1000000) : ℝ) = ((1000000 / 1915281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2468415379 / 1000000000) ≤ -Real.log (84719 / 1000000) ∧
    -Real.log (84719 / 1000000) ≤ (2468415383 / 1000000000) := by
  have h := checkLog_sound (w := (40281 / 209719)) (n := 12)
    (lo := (388973839 / 1000000000)) (hi := (4862173 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84719) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 84719) = 1/(84719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2468415383 / 1000000000) (-2468415379 / 1000000000) (Real.log (84719 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (325190033 / 500000000) ≤ -Real.log (1000000 / 1916269) ∧
    -Real.log (1000000 / 1916269) ≤ (650380067 / 1000000000) := by
  have h := checkLog_sound (w := (916269 / 2916269)) (n := 12)
    (lo := (325190033 / 500000000)) (hi := (650380067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1916269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1916269 / 1000000) = 1/(1000000 / 1916269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (325190033 / 500000000) (650380067 / 1000000000) (Real.log (1916269 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1916269 / 1000000) = -Real.log (1000000 / 1916269) := by
    rw [show ((1916269 / 1000000) : ℝ) = ((1000000 / 1916269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1240072999 / 500000000) ≤ -Real.log (83731 / 1000000) ∧
    -Real.log (83731 / 1000000) ≤ (1240073001 / 500000000) := by
  have h := checkLog_sound (w := (41269 / 208731)) (n := 12)
    (lo := (200352229 / 500000000)) (hi := (400704459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 83731) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 83731) = 1/(83731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1240073001 / 500000000) (-1240072999 / 500000000) (Real.log (83731 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (648251273 / 1000000000) ≤ -Real.log (500000 / 956097) ∧
    -Real.log (500000 / 956097) ≤ (324125637 / 500000000) := by
  have h := checkLog_sound (w := (456097 / 1456097)) (n := 12)
    (lo := (648251273 / 1000000000)) (hi := (324125637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956097 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956097 / 500000) = 1/(500000 / 956097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (648251273 / 1000000000) (324125637 / 500000000) (Real.log (956097 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (956097 / 500000) = -Real.log (500000 / 956097) := by
    rw [show ((956097 / 500000) : ℝ) = ((500000 / 956097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2432625441 / 1000000000) ≤ -Real.log (43903 / 500000) ∧
    -Real.log (43903 / 500000) ≤ (486525089 / 200000000) := by
  have h := checkLog_sound (w := (18597 / 106403)) (n := 12)
    (lo := (353183901 / 1000000000)) (hi := (176591951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43903) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 43903) = 1/(43903 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-486525089 / 200000000) (-2432625441 / 1000000000) (Real.log (43903 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (324408739 / 500000000) ≤ -Real.log (1000000 / 1913277) ∧
    -Real.log (1000000 / 1913277) ≤ (648817479 / 1000000000) := by
  have h := checkLog_sound (w := (913277 / 2913277)) (n := 12)
    (lo := (324408739 / 500000000)) (hi := (648817479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1913277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1913277 / 1000000) = 1/(1000000 / 1913277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (324408739 / 500000000) (648817479 / 1000000000) (Real.log (1913277 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1913277 / 1000000) = -Real.log (1000000 / 1913277) := by
    rw [show ((1913277 / 1000000) : ℝ) = ((1000000 / 1913277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1222518073 / 500000000) ≤ -Real.log (86723 / 1000000) ∧
    -Real.log (86723 / 1000000) ≤ (48900723 / 20000000) := by
  have h := checkLog_sound (w := (38277 / 211723)) (n := 12)
    (lo := (182797303 / 500000000)) (hi := (365594607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86723) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 86723) = 1/(86723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-48900723 / 20000000) (-1222518073 / 500000000) (Real.log (86723 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3118279727 / 1000000000) ≤ -Real.log (500000000000 / 11303727617181) ∧
    -Real.log (500000000000 / 11303727617181) ≤ (779569933 / 250000000) := by
  have h := checkLog_sound (w := (3303727617181 / 19303727617181)) (n := 12)
    (lo := (345691007 / 1000000000)) (hi := (2700711 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11303727617181 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11303727617181 / 8000000000000) = 1/(500000000000 / 11303727617181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3118279727 / 1000000000) (779569933 / 250000000) (Real.log (11303727617181 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11303727617181 / 500000000000) = -Real.log (500000000000 / 11303727617181) := by
    rw [show ((11303727617181 / 500000000000) : ℝ) = ((500000000000 / 11303727617181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3130526063 / 1000000000) ≤ -Real.log (500000000000 / 11443007965987) ∧
    -Real.log (500000000000 / 11443007965987) ≤ (782631517 / 250000000) := by
  have h := checkLog_sound (w := (3443007965987 / 19443007965987)) (n := 12)
    (lo := (357937343 / 1000000000)) (hi := (5592771 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11443007965987 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11443007965987 / 8000000000000) = 1/(500000000000 / 11443007965987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3130526063 / 1000000000) (782631517 / 250000000) (Real.log (11443007965987 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11443007965987 / 500000000000) = -Real.log (500000000000 / 11443007965987) := by
    rw [show ((11443007965987 / 500000000000) : ℝ) = ((500000000000 / 11443007965987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (616175343 / 200000000) ≤ -Real.log (62500000000 / 1361092920757) ∧
    -Real.log (62500000000 / 1361092920757) ≤ (38510959 / 12500000) := by
  have h := checkLog_sound (w := (361092920757 / 2361092920757)) (n := 12)
    (lo := (61657599 / 200000000)) (hi := (77071999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361092920757 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1361092920757 / 1000000000000) = 1/(62500000000 / 1361092920757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (616175343 / 200000000) (38510959 / 12500000) (Real.log (1361092920757 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1361092920757 / 62500000000) = -Real.log (62500000000 / 1361092920757) := by
    rw [show ((1361092920757 / 62500000000) : ℝ) = ((62500000000 / 1361092920757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (386731703 / 125000000) ≤ -Real.log (100000000000 / 2206193282059) ∧
    -Real.log (100000000000 / 2206193282059) ≤ (3093853629 / 1000000000) := by
  have h := checkLog_sound (w := (606193282059 / 3806193282059)) (n := 12)
    (lo := (40158113 / 125000000)) (hi := (64252981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2206193282059 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2206193282059 / 1600000000000) = 1/(100000000000 / 2206193282059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (386731703 / 125000000) (3093853629 / 1000000000) (Real.log (2206193282059 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2206193282059 / 100000000000) = -Real.log (100000000000 / 2206193282059) := by
    rw [show ((2206193282059 / 100000000000) : ℝ) = ((100000000000 / 2206193282059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0172

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0173Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0173
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

theorem reflection_log_1_neg : (127100303 / 200000000) ≤ -Real.log (6400 / 12083) ∧
    -Real.log (6400 / 12083) ≤ (158875379 / 250000000) := by
  have h := checkLog_sound (w := (5683 / 18483)) (n := 12)
    (lo := (127100303 / 200000000)) (hi := (158875379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12083 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12083 / 6400) = 1/(6400 / 12083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (127100303 / 200000000) (158875379 / 250000000) (Real.log (12083 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12083 / 6400) = -Real.log (6400 / 12083) := by
    rw [show ((12083 / 6400) : ℝ) = ((6400 / 12083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2188977427 / 1000000000) ≤ -Real.log (717 / 6400) ∧
    -Real.log (717 / 6400) ≤ (2188977431 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 1517)) (n := 12)
    (lo := (109535887 / 1000000000)) (hi := (6845993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 717) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 717) = 1/(717 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2188977431 / 1000000000) (-2188977427 / 1000000000) (Real.log (717 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (634714977 / 1000000000) ≤ -Real.log (12800 / 24147) ∧
    -Real.log (12800 / 24147) ≤ (317357489 / 500000000) := by
  have h := checkLog_sound (w := (11347 / 36947)) (n := 12)
    (lo := (634714977 / 1000000000)) (hi := (317357489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24147 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24147 / 12800) = 1/(12800 / 24147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (634714977 / 1000000000) (317357489 / 500000000) (Real.log (24147 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24147 / 12800) = -Real.log (12800 / 24147) := by
    rw [show ((24147 / 12800) : ℝ) = ((12800 / 24147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16998553 / 7812500) ≤ -Real.log (1453 / 12800) ∧
    -Real.log (1453 / 12800) ≤ (543953697 / 250000000) := by
  have h := checkLog_sound (w := (147 / 3053)) (n := 12)
    (lo := (24093311 / 250000000)) (hi := (19274649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1453) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1453) = 1/(1453 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-543953697 / 250000000) (-16998553 / 7812500) (Real.log (1453 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (143582113 / 250000000) ≤ -Real.log (3200 / 5683) ∧
    -Real.log (3200 / 5683) ≤ (574328453 / 1000000000) := by
  have h := checkLog_sound (w := (2483 / 8883)) (n := 12)
    (lo := (143582113 / 250000000)) (hi := (574328453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5683 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5683 / 3200) = 1/(3200 / 5683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (143582113 / 250000000) (574328453 / 1000000000) (Real.log (5683 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5683 / 3200) = -Real.log (3200 / 5683) := by
    rw [show ((5683 / 3200) : ℝ) = ((3200 / 5683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1495830247 / 1000000000) ≤ -Real.log (717 / 3200) ∧
    -Real.log (717 / 3200) ≤ (5983321 / 4000000) := by
  have h := checkLog_sound (w := (83 / 1517)) (n := 12)
    (lo := (109535887 / 1000000000)) (hi := (6845993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 717) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 717) = 1/(717 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5983321 / 4000000) (-1495830247 / 1000000000) (Real.log (717 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (572655401 / 1000000000) ≤ -Real.log (6400 / 11347) ∧
    -Real.log (6400 / 11347) ≤ (286327701 / 500000000) := by
  have h := checkLog_sound (w := (4947 / 17747)) (n := 12)
    (lo := (572655401 / 1000000000)) (hi := (286327701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11347 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11347 / 6400) = 1/(6400 / 11347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (572655401 / 1000000000) (286327701 / 500000000) (Real.log (11347 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11347 / 6400) = -Real.log (6400 / 11347) := by
    rw [show ((11347 / 6400) : ℝ) = ((6400 / 11347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (370666901 / 250000000) ≤ -Real.log (1453 / 6400) ∧
    -Real.log (1453 / 6400) ≤ (1482667607 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 3053)) (n := 12)
    (lo := (24093311 / 250000000)) (hi := (19274649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1453) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1453) = 1/(1453 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1482667607 / 1000000000) (-370666901 / 250000000) (Real.log (1453 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (649350453 / 1000000000) ≤ -Real.log (1000000 / 1914297) ∧
    -Real.log (1000000 / 1914297) ≤ (324675227 / 500000000) := by
  have h := checkLog_sound (w := (914297 / 2914297)) (n := 12)
    (lo := (649350453 / 1000000000)) (hi := (324675227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1914297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1914297 / 1000000) = 1/(1000000 / 1914297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (649350453 / 1000000000) (324675227 / 500000000) (Real.log (1914297 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1914297 / 1000000) = -Real.log (1000000 / 1914297) := by
    rw [show ((1914297 / 1000000) : ℝ) = ((1000000 / 1914297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1228433723 / 500000000) ≤ -Real.log (85703 / 1000000) ∧
    -Real.log (85703 / 1000000) ≤ (49137349 / 20000000) := by
  have h := checkLog_sound (w := (39297 / 210703)) (n := 12)
    (lo := (188712953 / 500000000)) (hi := (377425907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 85703) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 85703) = 1/(85703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-49137349 / 20000000) (-1228433723 / 500000000) (Real.log (85703 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64986487 / 100000000) ≤ -Real.log (500000 / 957641) ∧
    -Real.log (500000 / 957641) ≤ (649864871 / 1000000000) := by
  have h := checkLog_sound (w := (457641 / 1457641)) (n := 12)
    (lo := (64986487 / 100000000)) (hi := (649864871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957641 / 500000) = 1/(500000 / 957641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64986487 / 100000000) (649864871 / 1000000000) (Real.log (957641 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (957641 / 500000) = -Real.log (500000 / 957641) := by
    rw [show ((957641 / 500000) : ℝ) = ((500000 / 957641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2468427183 / 1000000000) ≤ -Real.log (42359 / 500000) ∧
    -Real.log (42359 / 500000) ≤ (2468427187 / 1000000000) := by
  have h := checkLog_sound (w := (20141 / 104859)) (n := 12)
    (lo := (388985643 / 1000000000)) (hi := (97246411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42359) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 42359) = 1/(42359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2468427187 / 1000000000) (-2468427183 / 1000000000) (Real.log (42359 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (323842897 / 500000000) ≤ -Real.log (1000000 / 1911113) ∧
    -Real.log (1000000 / 1911113) ≤ (129537159 / 200000000) := by
  have h := checkLog_sound (w := (911113 / 2911113)) (n := 12)
    (lo := (323842897 / 500000000)) (hi := (129537159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1911113 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1911113 / 1000000) = 1/(1000000 / 1911113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (323842897 / 500000000) (129537159 / 200000000) (Real.log (1911113 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1911113 / 1000000) = -Real.log (1000000 / 1911113) := by
    rw [show ((1911113 / 1000000) : ℝ) = ((1000000 / 1911113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2420389377 / 1000000000) ≤ -Real.log (88887 / 1000000) ∧
    -Real.log (88887 / 1000000) ≤ (2420389381 / 1000000000) := by
  have h := checkLog_sound (w := (36113 / 213887)) (n := 12)
    (lo := (340947837 / 1000000000)) (hi := (170473919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88887) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 88887) = 1/(88887 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2420389381 / 1000000000) (-2420389377 / 1000000000) (Real.log (88887 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (162062949 / 250000000) ≤ -Real.log (200000 / 382439) ∧
    -Real.log (200000 / 382439) ≤ (648251797 / 1000000000) := by
  have h := checkLog_sound (w := (182439 / 582439)) (n := 12)
    (lo := (162062949 / 250000000)) (hi := (648251797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382439 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382439 / 200000) = 1/(200000 / 382439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (162062949 / 250000000) (648251797 / 1000000000) (Real.log (382439 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (382439 / 200000) = -Real.log (200000 / 382439) := by
    rw [show ((382439 / 200000) : ℝ) = ((200000 / 382439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (243263683 / 100000000) ≤ -Real.log (17561 / 200000) ∧
    -Real.log (17561 / 200000) ≤ (1216318417 / 500000000) := by
  have h := checkLog_sound (w := (7439 / 42561)) (n := 12)
    (lo := (35319529 / 100000000)) (hi := (353195291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17561) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 17561) = 1/(17561 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1216318417 / 500000000) (-243263683 / 100000000) (Real.log (17561 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3106217899 / 1000000000) ≤ -Real.log (500000000000 / 11168202980059) ∧
    -Real.log (500000000000 / 11168202980059) ≤ (194138619 / 62500000) := by
  have h := checkLog_sound (w := (3168202980059 / 19168202980059)) (n := 12)
    (lo := (333629179 / 1000000000)) (hi := (16681459 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11168202980059 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11168202980059 / 8000000000000) = 1/(500000000000 / 11168202980059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3106217899 / 1000000000) (194138619 / 62500000) (Real.log (11168202980059 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11168202980059 / 500000000000) = -Real.log (500000000000 / 11168202980059) := by
    rw [show ((11168202980059 / 500000000000) : ℝ) = ((500000000000 / 11168202980059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3118292053 / 1000000000) ≤ -Real.log (125000000000 / 2825966736703) ∧
    -Real.log (125000000000 / 2825966736703) ≤ (1559146029 / 500000000) := by
  have h := checkLog_sound (w := (825966736703 / 4825966736703)) (n := 12)
    (lo := (345703333 / 1000000000)) (hi := (172851667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2825966736703 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2825966736703 / 2000000000000) = 1/(125000000000 / 2825966736703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3118292053 / 1000000000) (1559146029 / 500000000) (Real.log (2825966736703 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2825966736703 / 125000000000) = -Real.log (125000000000 / 2825966736703) := by
    rw [show ((2825966736703 / 125000000000) : ℝ) = ((125000000000 / 2825966736703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3068075171 / 1000000000) ≤ -Real.log (25000000000 / 537511953379) ∧
    -Real.log (25000000000 / 537511953379) ≤ (383509397 / 125000000) := by
  have h := checkLog_sound (w := (137511953379 / 937511953379)) (n := 12)
    (lo := (295486451 / 1000000000)) (hi := (73871613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537511953379 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(537511953379 / 400000000000) = 1/(25000000000 / 537511953379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3068075171 / 1000000000) (383509397 / 125000000) (Real.log (537511953379 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (537511953379 / 25000000000) = -Real.log (25000000000 / 537511953379) := by
    rw [show ((537511953379 / 25000000000) : ℝ) = ((25000000000 / 537511953379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1540444313 / 500000000) ≤ -Real.log (50000000000 / 1088887307101) ∧
    -Real.log (50000000000 / 1088887307101) ≤ (3080888631 / 1000000000) := by
  have h := checkLog_sound (w := (288887307101 / 1888887307101)) (n := 12)
    (lo := (154149953 / 500000000)) (hi := (308299907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088887307101 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1088887307101 / 800000000000) = 1/(50000000000 / 1088887307101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1540444313 / 500000000) (3080888631 / 1000000000) (Real.log (1088887307101 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1088887307101 / 50000000000) = -Real.log (50000000000 / 1088887307101) := by
    rw [show ((1088887307101 / 50000000000) : ℝ) = ((50000000000 / 1088887307101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0173

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0174Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0174
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

theorem reflection_log_1_neg : (634714977 / 1000000000) ≤ -Real.log (12800 / 24147) ∧
    -Real.log (12800 / 24147) ≤ (317357489 / 500000000) := by
  have h := checkLog_sound (w := (11347 / 36947)) (n := 12)
    (lo := (634714977 / 1000000000)) (hi := (317357489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24147 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24147 / 12800) = 1/(12800 / 24147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (634714977 / 1000000000) (317357489 / 500000000) (Real.log (24147 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24147 / 12800) = -Real.log (12800 / 24147) := by
    rw [show ((24147 / 12800) : ℝ) = ((12800 / 24147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16998553 / 7812500) ≤ -Real.log (1453 / 12800) ∧
    -Real.log (1453 / 12800) ≤ (543953697 / 250000000) := by
  have h := checkLog_sound (w := (147 / 3053)) (n := 12)
    (lo := (24093311 / 250000000)) (hi := (19274649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1453) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1453) = 1/(1453 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-543953697 / 250000000) (-16998553 / 7812500) (Real.log (1453 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (31696391 / 50000000) ≤ -Real.log (200 / 377) ∧
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


theorem reflection_log_3 : Bounds (31696391 / 50000000) (633927821 / 1000000000) (Real.log (377 / 200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (377 / 200) = -Real.log (200 / 377) := by
    rw [show ((377 / 200) : ℝ) = ((200 / 377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (540705787 / 250000000) ≤ -Real.log (23 / 200) ∧
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


theorem reflection_log_4 : Bounds (-135176447 / 62500000) (-540705787 / 250000000) (Real.log (23 / 200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (572655401 / 1000000000) ≤ -Real.log (6400 / 11347) ∧
    -Real.log (6400 / 11347) ≤ (286327701 / 500000000) := by
  have h := checkLog_sound (w := (4947 / 17747)) (n := 12)
    (lo := (572655401 / 1000000000)) (hi := (286327701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11347 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11347 / 6400) = 1/(6400 / 11347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (572655401 / 1000000000) (286327701 / 500000000) (Real.log (11347 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11347 / 6400) = -Real.log (6400 / 11347) := by
    rw [show ((11347 / 6400) : ℝ) = ((6400 / 11347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (370666901 / 250000000) ≤ -Real.log (1453 / 6400) ∧
    -Real.log (1453 / 6400) ≤ (1482667607 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 3053)) (n := 12)
    (lo := (24093311 / 250000000)) (hi := (19274649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1453) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1453) = 1/(1453 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1482667607 / 1000000000) (-370666901 / 250000000) (Real.log (1453 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (285489773 / 500000000) ≤ -Real.log (100 / 177) ∧
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


theorem reflection_log_7 : Bounds (285489773 / 500000000) (570979547 / 1000000000) (Real.log (177 / 100)) := by
  have h := reflection_log_7_neg
  have he : Real.log (177 / 100) = -Real.log (100 / 177) := by
    rw [show ((177 / 100) : ℝ) = ((100 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (22963687 / 15625000) ≤ -Real.log (23 / 100) ∧
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


theorem reflection_log_8 : Bounds (-1469675971 / 1000000000) (-22963687 / 15625000) (Real.log (23 / 100)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (129767677 / 200000000) ≤ -Real.log (1000000 / 1913317) ∧
    -Real.log (1000000 / 1913317) ≤ (324419193 / 500000000) := by
  have h := checkLog_sound (w := (913317 / 2913317)) (n := 12)
    (lo := (129767677 / 200000000)) (hi := (324419193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1913317 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1913317 / 1000000) = 1/(1000000 / 1913317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (129767677 / 200000000) (324419193 / 500000000) (Real.log (1913317 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1913317 / 1000000) = -Real.log (1000000 / 1913317) := by
    rw [show ((1913317 / 1000000) : ℝ) = ((1000000 / 1913317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2445497491 / 1000000000) ≤ -Real.log (86683 / 1000000) ∧
    -Real.log (86683 / 1000000) ≤ (489099499 / 200000000) := by
  have h := checkLog_sound (w := (38317 / 211683)) (n := 12)
    (lo := (366055951 / 1000000000)) (hi := (22878497 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86683) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 86683) = 1/(86683 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-489099499 / 200000000) (-2445497491 / 1000000000) (Real.log (86683 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (25974039 / 40000000) ≤ -Real.log (500000 / 957149) ∧
    -Real.log (500000 / 957149) ≤ (10146109 / 15625000) := by
  have h := checkLog_sound (w := (457149 / 1457149)) (n := 12)
    (lo := (25974039 / 40000000)) (hi := (10146109 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957149 / 500000) = 1/(500000 / 957149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (25974039 / 40000000) (10146109 / 15625000) (Real.log (957149 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (957149 / 500000) = -Real.log (500000 / 957149) := by
    rw [show ((957149 / 500000) : ℝ) = ((500000 / 957149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1228439557 / 500000000) ≤ -Real.log (42851 / 500000) ∧
    -Real.log (42851 / 500000) ≤ (1228439559 / 500000000) := by
  have h := checkLog_sound (w := (19649 / 105351)) (n := 12)
    (lo := (188718787 / 500000000)) (hi := (15097503 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42851) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 42851) = 1/(42851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1228439559 / 500000000) (-1228439557 / 500000000) (Real.log (42851 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (323560521 / 500000000) ≤ -Real.log (500000 / 955017) ∧
    -Real.log (500000 / 955017) ≤ (647121043 / 1000000000) := by
  have h := checkLog_sound (w := (455017 / 1455017)) (n := 12)
    (lo := (323560521 / 500000000)) (hi := (647121043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955017 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955017 / 500000) = 1/(500000 / 955017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (323560521 / 500000000) (647121043 / 1000000000) (Real.log (955017 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (955017 / 500000) = -Real.log (500000 / 955017) := by
    rw [show ((955017 / 500000) : ℝ) = ((500000 / 955017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (18815027 / 7812500) ≤ -Real.log (44983 / 500000) ∧
    -Real.log (44983 / 500000) ≤ (120416173 / 50000000) := by
  have h := checkLog_sound (w := (17517 / 107483)) (n := 12)
    (lo := (82220479 / 250000000)) (hi := (328881917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44983) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 44983) = 1/(44983 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-120416173 / 50000000) (-18815027 / 7812500) (Real.log (44983 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (323843159 / 500000000) ≤ -Real.log (500000 / 955557) ∧
    -Real.log (500000 / 955557) ≤ (647686319 / 1000000000) := by
  have h := checkLog_sound (w := (455557 / 1455557)) (n := 12)
    (lo := (323843159 / 500000000)) (hi := (647686319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955557 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955557 / 500000) = 1/(500000 / 955557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (323843159 / 500000000) (647686319 / 1000000000) (Real.log (955557 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (955557 / 500000) = -Real.log (500000 / 955557) := by
    rw [show ((955557 / 500000) : ℝ) = ((500000 / 955557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2420400627 / 1000000000) ≤ -Real.log (44443 / 500000) ∧
    -Real.log (44443 / 500000) ≤ (2420400631 / 1000000000) := by
  have h := checkLog_sound (w := (18057 / 106943)) (n := 12)
    (lo := (340959087 / 1000000000)) (hi := (21309943 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44443) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 44443) = 1/(44443 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2420400631 / 1000000000) (-2420400627 / 1000000000) (Real.log (44443 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (24754687 / 8000000) ≤ -Real.log (500000000000 / 11036287391991) ∧
    -Real.log (500000000000 / 11036287391991) ≤ (77358397 / 25000000) := by
  have h := checkLog_sound (w := (3036287391991 / 19036287391991)) (n := 12)
    (lo := (64349431 / 200000000)) (hi := (80436789 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11036287391991 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11036287391991 / 8000000000000) = 1/(500000000000 / 11036287391991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (24754687 / 8000000) (77358397 / 25000000) (Real.log (11036287391991 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11036287391991 / 500000000000) = -Real.log (500000000000 / 11036287391991) := by
    rw [show ((11036287391991 / 500000000000) : ℝ) = ((500000000000 / 11036287391991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3106230089 / 1000000000) ≤ -Real.log (500000000000 / 11168339128609) ∧
    -Real.log (500000000000 / 11168339128609) ≤ (1553115047 / 500000000) := by
  have h := checkLog_sound (w := (3168339128609 / 19168339128609)) (n := 12)
    (lo := (333641369 / 1000000000)) (hi := (33364137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11168339128609 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11168339128609 / 8000000000000) = 1/(500000000000 / 11168339128609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3106230089 / 1000000000) (1553115047 / 500000000) (Real.log (11168339128609 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11168339128609 / 500000000000) = -Real.log (500000000000 / 11168339128609) := by
    rw [show ((11168339128609 / 500000000000) : ℝ) = ((500000000000 / 11168339128609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1527722249 / 500000000) ≤ -Real.log (125000000000 / 2653827557077) ∧
    -Real.log (125000000000 / 2653827557077) ≤ (3055444503 / 1000000000) := by
  have h := checkLog_sound (w := (653827557077 / 4653827557077)) (n := 12)
    (lo := (141427889 / 500000000)) (hi := (282855779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2653827557077 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2653827557077 / 2000000000000) = 1/(125000000000 / 2653827557077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1527722249 / 500000000) (3055444503 / 1000000000) (Real.log (2653827557077 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2653827557077 / 125000000000) = -Real.log (125000000000 / 2653827557077) := by
    rw [show ((2653827557077 / 125000000000) : ℝ) = ((125000000000 / 2653827557077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (613617389 / 200000000) ≤ -Real.log (125000000000 / 2687591409221) ∧
    -Real.log (125000000000 / 2687591409221) ≤ (61361739 / 20000000) := by
  have h := checkLog_sound (w := (687591409221 / 4687591409221)) (n := 12)
    (lo := (11819929 / 40000000)) (hi := (147749113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2687591409221 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2687591409221 / 2000000000000) = 1/(125000000000 / 2687591409221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (613617389 / 200000000) (61361739 / 20000000) (Real.log (2687591409221 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2687591409221 / 125000000000) = -Real.log (125000000000 / 2687591409221) := by
    rw [show ((2687591409221 / 125000000000) : ℝ) = ((125000000000 / 2687591409221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0174

end


