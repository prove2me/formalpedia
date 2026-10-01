-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0114Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0114Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:50:28.099979+00:00
-- url     : https://prove2.me/theorems/a25f695f-a2a0-4baf-9e4d-cd64b9b96c35
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0114Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0115Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0114Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0115Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0116Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0117Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0118Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0119Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0120Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0114Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0115Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0116Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0117Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0118Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0119Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0120Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0114Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0115Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0116Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0117Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0118Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0119Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0120Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0114Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0115Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0116Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0117Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0118Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0119Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0120Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0114Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0114
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

theorem reflection_log_1_neg : (668370091 / 1000000000) ≤ -Real.log (25600 / 49947) ∧
    -Real.log (25600 / 49947) ≤ (167092523 / 250000000) := by
  have h := checkLog_sound (w := (24347 / 75547)) (n := 12)
    (lo := (668370091 / 1000000000)) (hi := (167092523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49947 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49947 / 25600) = 1/(25600 / 49947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (668370091 / 1000000000) (167092523 / 250000000) (Real.log (49947 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49947 / 25600) = -Real.log (25600 / 49947) := by
    rw [show ((49947 / 25600) : ℝ) = ((25600 / 49947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3017051673 / 1000000000) ≤ -Real.log (1253 / 25600) ∧
    -Real.log (1253 / 25600) ≤ (1508525839 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2853)) (n := 12)
    (lo := (244462953 / 1000000000)) (hi := (122231477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1253) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1253) = 1/(1253 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1508525839 / 500000000) (-3017051673 / 1000000000) (Real.log (1253 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (41749351 / 62500000) ≤ -Real.log (3200 / 6241) ∧
    -Real.log (3200 / 6241) ≤ (667989617 / 1000000000) := by
  have h := checkLog_sound (w := (3041 / 9441)) (n := 12)
    (lo := (41749351 / 62500000)) (hi := (667989617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6241 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6241 / 3200) = 1/(3200 / 6241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (41749351 / 62500000) (667989617 / 1000000000) (Real.log (6241 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6241 / 3200) = -Real.log (3200 / 6241) := by
    rw [show ((6241 / 3200) : ℝ) = ((3200 / 6241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (750500471 / 250000000) ≤ -Real.log (159 / 3200) ∧
    -Real.log (159 / 3200) ≤ (3002001889 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 359)) (n := 12)
    (lo := (57353291 / 250000000)) (hi := (45882633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 159) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 159) = 1/(159 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3002001889 / 1000000000) (-750500471 / 250000000) (Real.log (159 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (642963467 / 1000000000) ≤ -Real.log (12800 / 24347) ∧
    -Real.log (12800 / 24347) ≤ (160740867 / 250000000) := by
  have h := checkLog_sound (w := (11547 / 37147)) (n := 12)
    (lo := (642963467 / 1000000000)) (hi := (160740867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24347 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24347 / 12800) = 1/(12800 / 24347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (642963467 / 1000000000) (160740867 / 250000000) (Real.log (24347 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24347 / 12800) = -Real.log (12800 / 24347) := by
    rw [show ((24347 / 12800) : ℝ) = ((12800 / 24347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2323904493 / 1000000000) ≤ -Real.log (1253 / 12800) ∧
    -Real.log (1253 / 12800) ≤ (2323904497 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 2853)) (n := 12)
    (lo := (244462953 / 1000000000)) (hi := (122231477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1253) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1253) = 1/(1253 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2323904497 / 1000000000) (-2323904493 / 1000000000) (Real.log (1253 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (642182779 / 1000000000) ≤ -Real.log (1600 / 3041) ∧
    -Real.log (1600 / 3041) ≤ (32109139 / 50000000) := by
  have h := checkLog_sound (w := (1441 / 4641)) (n := 12)
    (lo := (642182779 / 1000000000)) (hi := (32109139 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3041 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3041 / 1600) = 1/(1600 / 3041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (642182779 / 1000000000) (32109139 / 50000000) (Real.log (3041 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3041 / 1600) = -Real.log (1600 / 3041) := by
    rw [show ((3041 / 1600) : ℝ) = ((1600 / 3041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (144303419 / 62500000) ≤ -Real.log (159 / 1600) ∧
    -Real.log (159 / 1600) ≤ (577213677 / 250000000) := by
  have h := checkLog_sound (w := (41 / 359)) (n := 12)
    (lo := (57353291 / 250000000)) (hi := (45882633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 159) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 159) = 1/(159 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-577213677 / 250000000) (-144303419 / 62500000) (Real.log (159 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (672745473 / 1000000000) ≤ -Real.log (100000 / 195961) ∧
    -Real.log (100000 / 195961) ≤ (336372737 / 500000000) := by
  have h := checkLog_sound (w := (95961 / 295961)) (n := 12)
    (lo := (672745473 / 1000000000)) (hi := (336372737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195961 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195961 / 100000) = 1/(100000 / 195961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (672745473 / 1000000000) (336372737 / 500000000) (Real.log (195961 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (195961 / 100000) = -Real.log (100000 / 195961) := by
    rw [show ((195961 / 100000) : ℝ) = ((100000 / 195961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3209173047 / 1000000000) ≤ -Real.log (4039 / 100000) ∧
    -Real.log (4039 / 100000) ≤ (802293263 / 250000000) := by
  have h := checkLog_sound (w := (2211 / 10289)) (n := 12)
    (lo := (436584327 / 1000000000)) (hi := (54573041 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4039) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 4039) = 1/(4039 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-802293263 / 250000000) (-3209173047 / 1000000000) (Real.log (4039 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (336516877 / 500000000) ≤ -Real.log (40000 / 78407) ∧
    -Real.log (40000 / 78407) ≤ (134606751 / 200000000) := by
  have h := checkLog_sound (w := (38407 / 118407)) (n := 12)
    (lo := (336516877 / 500000000)) (hi := (134606751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78407 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78407 / 40000) = 1/(40000 / 78407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (336516877 / 500000000) (134606751 / 200000000) (Real.log (78407 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (78407 / 40000) = -Real.log (40000 / 78407) := by
    rw [show ((78407 / 40000) : ℝ) = ((40000 / 78407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (161163021 / 50000000) ≤ -Real.log (1593 / 40000) ∧
    -Real.log (1593 / 40000) ≤ (128930417 / 40000000) := by
  have h := checkLog_sound (w := (907 / 4093)) (n := 12)
    (lo := (4506717 / 10000000)) (hi := (450671701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1593) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2500 / 1593) = 1/(1593 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-128930417 / 40000000) (-161163021 / 50000000) (Real.log (1593 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (672503559 / 1000000000) ≤ -Real.log (31250 / 61223) ∧
    -Real.log (31250 / 61223) ≤ (16812589 / 25000000) := by
  have h := checkLog_sound (w := (29973 / 92473)) (n := 12)
    (lo := (672503559 / 1000000000)) (hi := (16812589 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61223 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61223 / 31250) = 1/(31250 / 61223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (672503559 / 1000000000) (16812589 / 25000000) (Real.log (61223 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61223 / 31250) = -Real.log (31250 / 61223) := by
    rw [show ((61223 / 31250) : ℝ) = ((31250 / 61223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (799376449 / 250000000) ≤ -Real.log (1277 / 31250) ∧
    -Real.log (1277 / 31250) ≤ (3197505801 / 1000000000) := by
  have h := checkLog_sound (w := (5409 / 25841)) (n := 12)
    (lo := (106229269 / 250000000)) (hi := (424917077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10216) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 10216) = 1/(1277 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3197505801 / 1000000000) (-799376449 / 250000000) (Real.log (1277 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (134560117 / 200000000) ≤ -Real.log (500000 / 979859) ∧
    -Real.log (500000 / 979859) ≤ (336400293 / 500000000) := by
  have h := checkLog_sound (w := (479859 / 1479859)) (n := 12)
    (lo := (134560117 / 200000000)) (hi := (336400293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979859 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979859 / 500000) = 1/(500000 / 979859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (134560117 / 200000000) (336400293 / 500000000) (Real.log (979859 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (979859 / 500000) = -Real.log (500000 / 979859) := by
    rw [show ((979859 / 500000) : ℝ) = ((500000 / 979859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3211850557 / 1000000000) ≤ -Real.log (20141 / 500000) ∧
    -Real.log (20141 / 500000) ≤ (1605925281 / 500000000) := by
  have h := checkLog_sound (w := (11109 / 51391)) (n := 12)
    (lo := (439261837 / 1000000000)) (hi := (219630919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20141) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 20141) = 1/(20141 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1605925281 / 500000000) (-3211850557 / 1000000000) (Real.log (20141 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (97047963 / 25000000) ≤ -Real.log (125000000000 / 6064650903689) ∧
    -Real.log (125000000000 / 6064650903689) ≤ (1940959263 / 500000000) := by
  have h := checkLog_sound (w := (2064650903689 / 10064650903689)) (n := 12)
    (lo := (20809131 / 50000000)) (hi := (416182621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6064650903689 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6064650903689 / 4000000000000) = 1/(125000000000 / 6064650903689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (97047963 / 25000000) (1940959263 / 500000000) (Real.log (6064650903689 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6064650903689 / 125000000000) = -Real.log (125000000000 / 6064650903689) := by
    rw [show ((6064650903689 / 125000000000) : ℝ) = ((125000000000 / 6064650903689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (155851767 / 40000000) ≤ -Real.log (500000000000 / 24609855618331) ∧
    -Real.log (500000000000 / 24609855618331) ≤ (3896294181 / 1000000000) := by
  have h := checkLog_sound (w := (8609855618331 / 40609855618331)) (n := 12)
    (lo := (17222331 / 40000000)) (hi := (107639569 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24609855618331 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24609855618331 / 16000000000000) = 1/(500000000000 / 24609855618331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (155851767 / 40000000) (3896294181 / 1000000000) (Real.log (24609855618331 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (24609855618331 / 500000000000) = -Real.log (500000000000 / 24609855618331) := by
    rw [show ((24609855618331 / 500000000000) : ℝ) = ((500000000000 / 24609855618331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (967502339 / 250000000) ≤ -Real.log (250000000000 / 11985708692247) ∧
    -Real.log (250000000000 / 11985708692247) ≤ (1935004681 / 500000000) := by
  have h := checkLog_sound (w := (3985708692247 / 19985708692247)) (n := 12)
    (lo := (25267091 / 62500000)) (hi := (404273457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11985708692247 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(11985708692247 / 8000000000000) = 1/(250000000000 / 11985708692247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (967502339 / 250000000) (1935004681 / 500000000) (Real.log (11985708692247 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11985708692247 / 250000000000) = -Real.log (250000000000 / 11985708692247) := by
    rw [show ((11985708692247 / 250000000000) : ℝ) = ((250000000000 / 11985708692247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1942325571 / 500000000) ≤ -Real.log (500000000000 / 24324983863761) ∧
    -Real.log (500000000000 / 24324983863761) ≤ (971162787 / 250000000) := by
  have h := checkLog_sound (w := (8324983863761 / 40324983863761)) (n := 12)
    (lo := (209457621 / 500000000)) (hi := (418915243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24324983863761 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24324983863761 / 16000000000000) = 1/(500000000000 / 24324983863761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1942325571 / 500000000) (971162787 / 250000000) (Real.log (24324983863761 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (24324983863761 / 500000000000) = -Real.log (500000000000 / 24324983863761) := by
    rw [show ((24324983863761 / 500000000000) : ℝ) = ((500000000000 / 24324983863761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0114

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0115Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0115
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

theorem reflection_log_1_neg : (41749351 / 62500000) ≤ -Real.log (3200 / 6241) ∧
    -Real.log (3200 / 6241) ≤ (667989617 / 1000000000) := by
  have h := checkLog_sound (w := (3041 / 9441)) (n := 12)
    (lo := (41749351 / 62500000)) (hi := (667989617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6241 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6241 / 3200) = 1/(3200 / 6241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (41749351 / 62500000) (667989617 / 1000000000) (Real.log (6241 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6241 / 3200) = -Real.log (3200 / 6241) := by
    rw [show ((6241 / 3200) : ℝ) = ((3200 / 6241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (750500471 / 250000000) ≤ -Real.log (159 / 3200) ∧
    -Real.log (159 / 3200) ≤ (3002001889 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 359)) (n := 12)
    (lo := (57353291 / 250000000)) (hi := (45882633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 159) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 159) = 1/(159 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3002001889 / 1000000000) (-750500471 / 250000000) (Real.log (159 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (133521799 / 200000000) ≤ -Real.log (25600 / 49909) ∧
    -Real.log (25600 / 49909) ≤ (166902249 / 250000000) := by
  have h := checkLog_sound (w := (24309 / 75509)) (n := 12)
    (lo := (133521799 / 200000000)) (hi := (166902249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49909 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49909 / 25600) = 1/(25600 / 49909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (133521799 / 200000000) (166902249 / 250000000) (Real.log (49909 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49909 / 25600) = -Real.log (25600 / 49909) := by
    rw [show ((49909 / 25600) : ℝ) = ((25600 / 49909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2987175237 / 1000000000) ≤ -Real.log (1291 / 25600) ∧
    -Real.log (1291 / 25600) ≤ (1493587621 / 500000000) := by
  have h := checkLog_sound (w := (309 / 2891)) (n := 12)
    (lo := (214586517 / 1000000000)) (hi := (107293259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1291) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1291) = 1/(1291 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1493587621 / 500000000) (-2987175237 / 1000000000) (Real.log (1291 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (642182779 / 1000000000) ≤ -Real.log (1600 / 3041) ∧
    -Real.log (1600 / 3041) ≤ (32109139 / 50000000) := by
  have h := checkLog_sound (w := (1441 / 4641)) (n := 12)
    (lo := (642182779 / 1000000000)) (hi := (32109139 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3041 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3041 / 1600) = 1/(1600 / 3041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (642182779 / 1000000000) (32109139 / 50000000) (Real.log (3041 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3041 / 1600) = -Real.log (1600 / 3041) := by
    rw [show ((3041 / 1600) : ℝ) = ((1600 / 3041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (144303419 / 62500000) ≤ -Real.log (159 / 1600) ∧
    -Real.log (159 / 1600) ≤ (577213677 / 250000000) := by
  have h := checkLog_sound (w := (41 / 359)) (n := 12)
    (lo := (57353291 / 250000000)) (hi := (45882633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 159) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 159) = 1/(159 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-577213677 / 250000000) (-144303419 / 62500000) (Real.log (159 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (641401481 / 1000000000) ≤ -Real.log (12800 / 24309) ∧
    -Real.log (12800 / 24309) ≤ (320700741 / 500000000) := by
  have h := checkLog_sound (w := (11509 / 37109)) (n := 12)
    (lo := (641401481 / 1000000000)) (hi := (320700741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24309 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24309 / 12800) = 1/(12800 / 24309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (641401481 / 1000000000) (320700741 / 500000000) (Real.log (24309 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24309 / 12800) = -Real.log (12800 / 24309) := by
    rw [show ((24309 / 12800) : ℝ) = ((12800 / 24309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2294028057 / 1000000000) ≤ -Real.log (1291 / 12800) ∧
    -Real.log (1291 / 12800) ≤ (2294028061 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 2891)) (n := 12)
    (lo := (214586517 / 1000000000)) (hi := (107293259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1291) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1291) = 1/(1291 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2294028061 / 1000000000) (-2294028057 / 1000000000) (Real.log (1291 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (33622881 / 50000000) ≤ -Real.log (500000 / 979523) ∧
    -Real.log (500000 / 979523) ≤ (672457621 / 1000000000) := by
  have h := checkLog_sound (w := (479523 / 1479523)) (n := 12)
    (lo := (33622881 / 50000000)) (hi := (672457621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979523 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979523 / 500000) = 1/(500000 / 979523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (33622881 / 50000000) (672457621 / 1000000000) (Real.log (979523 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (979523 / 500000) = -Real.log (500000 / 979523) := by
    rw [show ((979523 / 500000) : ℝ) = ((500000 / 979523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3195305791 / 1000000000) ≤ -Real.log (20477 / 500000) ∧
    -Real.log (20477 / 500000) ≤ (798826449 / 250000000) := by
  have h := checkLog_sound (w := (10773 / 51727)) (n := 12)
    (lo := (422717071 / 1000000000)) (hi := (26419817 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20477) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 20477) = 1/(20477 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-798826449 / 250000000) (-3195305791 / 1000000000) (Real.log (20477 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1313957 / 1953125) ≤ -Real.log (1000000 / 1959611) ∧
    -Real.log (1000000 / 1959611) ≤ (134549197 / 200000000) := by
  have h := checkLog_sound (w := (959611 / 2959611)) (n := 12)
    (lo := (1313957 / 1953125)) (hi := (134549197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1959611 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1959611 / 1000000) = 1/(1000000 / 1959611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1313957 / 1953125) (134549197 / 200000000) (Real.log (1959611 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1959611 / 1000000) = -Real.log (1000000 / 1959611) := by
    rw [show ((1959611 / 1000000) : ℝ) = ((1000000 / 1959611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1604598903 / 500000000) ≤ -Real.log (40389 / 1000000) ∧
    -Real.log (40389 / 1000000) ≤ (3209197811 / 1000000000) := by
  have h := checkLog_sound (w := (22111 / 102889)) (n := 12)
    (lo := (218304543 / 500000000)) (hi := (436609087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40389) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 40389) = 1/(40389 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3209197811 / 1000000000) (-1604598903 / 500000000) (Real.log (40389 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (672207467 / 1000000000) ≤ -Real.log (250000 / 489639) ∧
    -Real.log (250000 / 489639) ≤ (168051867 / 250000000) := by
  have h := checkLog_sound (w := (239639 / 739639)) (n := 12)
    (lo := (672207467 / 1000000000)) (hi := (168051867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489639 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489639 / 250000) = 1/(250000 / 489639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (672207467 / 1000000000) (168051867 / 250000000) (Real.log (489639 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (489639 / 250000) = -Real.log (250000 / 489639) := by
    rw [show ((489639 / 250000) : ℝ) = ((250000 / 489639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1591706079 / 500000000) ≤ -Real.log (10361 / 250000) ∧
    -Real.log (10361 / 250000) ≤ (3183412163 / 1000000000) := by
  have h := checkLog_sound (w := (2632 / 12993)) (n := 12)
    (lo := (205411719 / 500000000)) (hi := (410823439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10361) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 10361) = 1/(10361 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3183412163 / 1000000000) (-1591706079 / 500000000) (Real.log (10361 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (67250407 / 100000000) ≤ -Real.log (1000000 / 1959137) ∧
    -Real.log (1000000 / 1959137) ≤ (672504071 / 1000000000) := by
  have h := checkLog_sound (w := (959137 / 2959137)) (n := 12)
    (lo := (67250407 / 100000000)) (hi := (672504071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1959137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1959137 / 1000000) = 1/(1000000 / 1959137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (67250407 / 100000000) (672504071 / 1000000000) (Real.log (1959137 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1959137 / 1000000) = -Real.log (1000000 / 1959137) := by
    rw [show ((1959137 / 1000000) : ℝ) = ((1000000 / 1959137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (799382567 / 250000000) ≤ -Real.log (40863 / 1000000) ∧
    -Real.log (40863 / 1000000) ≤ (3197530273 / 1000000000) := by
  have h := checkLog_sound (w := (21637 / 103363)) (n := 12)
    (lo := (106235387 / 250000000)) (hi := (424941549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40863) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 40863) = 1/(40863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3197530273 / 1000000000) (-799382567 / 250000000) (Real.log (40863 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (386776341 / 100000000) ≤ -Real.log (62500000000 / 2989704912829) ∧
    -Real.log (62500000000 / 2989704912829) ≤ (483470427 / 125000000) := by
  have h := checkLog_sound (w := (989704912829 / 4989704912829)) (n := 12)
    (lo := (40202751 / 100000000)) (hi := (402027511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2989704912829 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2989704912829 / 2000000000000) = 1/(62500000000 / 2989704912829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (386776341 / 100000000) (483470427 / 125000000) (Real.log (2989704912829 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2989704912829 / 62500000000) = -Real.log (62500000000 / 2989704912829) := by
    rw [show ((2989704912829 / 62500000000) : ℝ) = ((62500000000 / 2989704912829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3881943789 / 1000000000) ≤ -Real.log (500000000000 / 24259216618387) ∧
    -Real.log (500000000000 / 24259216618387) ≤ (776388759 / 200000000) := by
  have h := checkLog_sound (w := (8259216618387 / 40259216618387)) (n := 12)
    (lo := (416207889 / 1000000000)) (hi := (41620789 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24259216618387 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24259216618387 / 16000000000000) = 1/(500000000000 / 24259216618387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3881943789 / 1000000000) (776388759 / 200000000) (Real.log (24259216618387 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (24259216618387 / 500000000000) = -Real.log (500000000000 / 24259216618387) := by
    rw [show ((24259216618387 / 500000000000) : ℝ) = ((500000000000 / 24259216618387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (481952453 / 125000000) ≤ -Real.log (12500000000 / 590723627063) ∧
    -Real.log (12500000000 / 590723627063) ≤ (385561963 / 100000000) := by
  have h := checkLog_sound (w := (190723627063 / 990723627063)) (n := 12)
    (lo := (97470931 / 250000000)) (hi := (15595349 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590723627063 / 400000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(590723627063 / 400000000000) = 1/(12500000000 / 590723627063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (481952453 / 125000000) (385561963 / 100000000) (Real.log (590723627063 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (590723627063 / 12500000000) = -Real.log (12500000000 / 590723627063) := by
    rw [show ((590723627063 / 12500000000) : ℝ) = ((12500000000 / 590723627063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1935017169 / 500000000) ≤ -Real.log (500000000000 / 23972016249419) ∧
    -Real.log (500000000000 / 23972016249419) ≤ (483754293 / 125000000) := by
  have h := checkLog_sound (w := (7972016249419 / 39972016249419)) (n := 12)
    (lo := (202149219 / 500000000)) (hi := (404298439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23972016249419 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23972016249419 / 16000000000000) = 1/(500000000000 / 23972016249419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1935017169 / 500000000) (483754293 / 125000000) (Real.log (23972016249419 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (23972016249419 / 500000000000) = -Real.log (500000000000 / 23972016249419) := by
    rw [show ((23972016249419 / 500000000000) : ℝ) = ((500000000000 / 23972016249419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0115

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0116Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0116
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

theorem reflection_log_1_neg : (133521799 / 200000000) ≤ -Real.log (25600 / 49909) ∧
    -Real.log (25600 / 49909) ≤ (166902249 / 250000000) := by
  have h := checkLog_sound (w := (24309 / 75509)) (n := 12)
    (lo := (133521799 / 200000000)) (hi := (166902249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49909 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49909 / 25600) = 1/(25600 / 49909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (133521799 / 200000000) (166902249 / 250000000) (Real.log (49909 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49909 / 25600) = -Real.log (25600 / 49909) := by
    rw [show ((49909 / 25600) : ℝ) = ((25600 / 49909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2987175237 / 1000000000) ≤ -Real.log (1291 / 25600) ∧
    -Real.log (1291 / 25600) ≤ (1493587621 / 500000000) := by
  have h := checkLog_sound (w := (309 / 2891)) (n := 12)
    (lo := (214586517 / 1000000000)) (hi := (107293259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1291) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1291) = 1/(1291 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1493587621 / 500000000) (-2987175237 / 1000000000) (Real.log (1291 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66722823 / 100000000) ≤ -Real.log (2560 / 4989) ∧
    -Real.log (2560 / 4989) ≤ (667228231 / 1000000000) := by
  have h := checkLog_sound (w := (2429 / 7549)) (n := 12)
    (lo := (66722823 / 100000000)) (hi := (667228231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4989 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4989 / 2560) = 1/(2560 / 4989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66722823 / 100000000) (667228231 / 1000000000) (Real.log (4989 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4989 / 2560) = -Real.log (2560 / 4989) := by
    rw [show ((4989 / 2560) : ℝ) = ((2560 / 4989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (743141303 / 250000000) ≤ -Real.log (131 / 2560) ∧
    -Real.log (131 / 2560) ≤ (2972565217 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 291)) (n := 12)
    (lo := (49994123 / 250000000)) (hi := (199976493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 131) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 131) = 1/(131 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2972565217 / 1000000000) (-743141303 / 250000000) (Real.log (131 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (641401481 / 1000000000) ≤ -Real.log (12800 / 24309) ∧
    -Real.log (12800 / 24309) ≤ (320700741 / 500000000) := by
  have h := checkLog_sound (w := (11509 / 37109)) (n := 12)
    (lo := (641401481 / 1000000000)) (hi := (320700741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24309 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24309 / 12800) = 1/(12800 / 24309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (641401481 / 1000000000) (320700741 / 500000000) (Real.log (24309 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24309 / 12800) = -Real.log (12800 / 24309) := by
    rw [show ((24309 / 12800) : ℝ) = ((12800 / 24309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2294028057 / 1000000000) ≤ -Real.log (1291 / 12800) ∧
    -Real.log (1291 / 12800) ≤ (2294028061 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 2891)) (n := 12)
    (lo := (214586517 / 1000000000)) (hi := (107293259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1291) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1291) = 1/(1291 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2294028061 / 1000000000) (-2294028057 / 1000000000) (Real.log (1291 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (160154893 / 250000000) ≤ -Real.log (1280 / 2429) ∧
    -Real.log (1280 / 2429) ≤ (640619573 / 1000000000) := by
  have h := checkLog_sound (w := (1149 / 3709)) (n := 12)
    (lo := (160154893 / 250000000)) (hi := (640619573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2429 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2429 / 1280) = 1/(1280 / 2429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (160154893 / 250000000) (640619573 / 1000000000) (Real.log (2429 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2429 / 1280) = -Real.log (1280 / 2429) := by
    rw [show ((2429 / 1280) : ℝ) = ((1280 / 2429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (142463627 / 62500000) ≤ -Real.log (131 / 1280) ∧
    -Real.log (131 / 1280) ≤ (569854509 / 250000000) := by
  have h := checkLog_sound (w := (29 / 291)) (n := 12)
    (lo := (49994123 / 250000000)) (hi := (199976493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 131) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 131) = 1/(131 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-569854509 / 250000000) (-142463627 / 62500000) (Real.log (131 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (672170193 / 1000000000) ≤ -Real.log (1000000 / 1958483) ∧
    -Real.log (1000000 / 1958483) ≤ (336085097 / 500000000) := by
  have h := checkLog_sound (w := (958483 / 2958483)) (n := 12)
    (lo := (672170193 / 1000000000)) (hi := (336085097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1958483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1958483 / 1000000) = 1/(1000000 / 1958483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (672170193 / 1000000000) (336085097 / 500000000) (Real.log (1958483 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1958483 / 1000000) = -Real.log (1000000 / 1958483) := by
    rw [show ((1958483 / 1000000) : ℝ) = ((1000000 / 1958483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1590826147 / 500000000) ≤ -Real.log (41517 / 1000000) ∧
    -Real.log (41517 / 1000000) ≤ (3181652299 / 1000000000) := by
  have h := checkLog_sound (w := (20983 / 104017)) (n := 12)
    (lo := (204531787 / 500000000)) (hi := (16362543 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41517) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 41517) = 1/(41517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3181652299 / 1000000000) (-1590826147 / 500000000) (Real.log (41517 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67245813 / 100000000) ≤ -Real.log (1000000 / 1959047) ∧
    -Real.log (1000000 / 1959047) ≤ (672458131 / 1000000000) := by
  have h := checkLog_sound (w := (959047 / 2959047)) (n := 12)
    (lo := (67245813 / 100000000)) (hi := (672458131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1959047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1959047 / 1000000) = 1/(1000000 / 1959047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67245813 / 100000000) (672458131 / 1000000000) (Real.log (1959047 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1959047 / 1000000) = -Real.log (1000000 / 1959047) := by
    rw [show ((1959047 / 1000000) : ℝ) = ((1000000 / 1959047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3195330209 / 1000000000) ≤ -Real.log (40953 / 1000000) ∧
    -Real.log (40953 / 1000000) ≤ (1597665107 / 500000000) := by
  have h := checkLog_sound (w := (21547 / 103453)) (n := 12)
    (lo := (422741489 / 1000000000)) (hi := (42274149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40953) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 40953) = 1/(40953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1597665107 / 500000000) (-3195330209 / 1000000000) (Real.log (40953 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (671911797 / 1000000000) ≤ -Real.log (1000000 / 1957977) ∧
    -Real.log (1000000 / 1957977) ≤ (335955899 / 500000000) := by
  have h := checkLog_sound (w := (957977 / 2957977)) (n := 12)
    (lo := (671911797 / 1000000000)) (hi := (335955899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957977 / 1000000) = 1/(1000000 / 1957977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (671911797 / 1000000000) (335955899 / 500000000) (Real.log (1957977 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1957977 / 1000000) = -Real.log (1000000 / 1957977) := by
    rw [show ((1957977 / 1000000) : ℝ) = ((1000000 / 1957977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3169538189 / 1000000000) ≤ -Real.log (42023 / 1000000) ∧
    -Real.log (42023 / 1000000) ≤ (1584769097 / 500000000) := by
  have h := checkLog_sound (w := (20477 / 104523)) (n := 12)
    (lo := (396949469 / 1000000000)) (hi := (39694947 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42023) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 42023) = 1/(42023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1584769097 / 500000000) (-3169538189 / 1000000000) (Real.log (42023 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (672207977 / 1000000000) ≤ -Real.log (1000000 / 1958557) ∧
    -Real.log (1000000 / 1958557) ≤ (336103989 / 500000000) := by
  have h := checkLog_sound (w := (958557 / 2958557)) (n := 12)
    (lo := (672207977 / 1000000000)) (hi := (336103989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1958557 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1958557 / 1000000) = 1/(1000000 / 1958557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (672207977 / 1000000000) (336103989 / 500000000) (Real.log (1958557 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1958557 / 1000000) = -Real.log (1000000 / 1958557) := by
    rw [show ((1958557 / 1000000) : ℝ) = ((1000000 / 1958557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3183436287 / 1000000000) ≤ -Real.log (41443 / 1000000) ∧
    -Real.log (41443 / 1000000) ≤ (795859073 / 250000000) := by
  have h := checkLog_sound (w := (21057 / 103943)) (n := 12)
    (lo := (410847567 / 1000000000)) (hi := (25677973 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41443) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 41443) = 1/(41443 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-795859073 / 250000000) (-3183436287 / 1000000000) (Real.log (41443 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (481727811 / 125000000) ≤ -Real.log (500000000000 / 23586518775441) ∧
    -Real.log (500000000000 / 23586518775441) ≤ (1926911247 / 500000000) := by
  have h := checkLog_sound (w := (7586518775441 / 39586518775441)) (n := 12)
    (lo := (97021647 / 250000000)) (hi := (388086589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23586518775441 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23586518775441 / 16000000000000) = 1/(500000000000 / 23586518775441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (481727811 / 125000000) (1926911247 / 500000000) (Real.log (23586518775441 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (23586518775441 / 500000000000) = -Real.log (500000000000 / 23586518775441) := by
    rw [show ((23586518775441 / 500000000000) : ℝ) = ((500000000000 / 23586518775441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3867788339 / 1000000000) ≤ -Real.log (500000000000 / 23918235538301) ∧
    -Real.log (500000000000 / 23918235538301) ≤ (773557669 / 200000000) := by
  have h := checkLog_sound (w := (7918235538301 / 39918235538301)) (n := 12)
    (lo := (402052439 / 1000000000)) (hi := (10051311 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23918235538301 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23918235538301 / 16000000000000) = 1/(500000000000 / 23918235538301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3867788339 / 1000000000) (773557669 / 200000000) (Real.log (23918235538301 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (23918235538301 / 500000000000) = -Real.log (500000000000 / 23918235538301) := by
    rw [show ((23918235538301 / 500000000000) : ℝ) = ((500000000000 / 23918235538301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1920724993 / 500000000) ≤ -Real.log (25000000000 / 1164824619851) ∧
    -Real.log (25000000000 / 1164824619851) ≤ (480181249 / 125000000) := by
  have h := checkLog_sound (w := (364824619851 / 1964824619851)) (n := 12)
    (lo := (187857043 / 500000000)) (hi := (375714087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164824619851 / 800000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1164824619851 / 800000000000) = 1/(25000000000 / 1164824619851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1920724993 / 500000000) (480181249 / 125000000) (Real.log (1164824619851 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1164824619851 / 25000000000) = -Real.log (25000000000 / 1164824619851) := by
    rw [show ((1164824619851 / 25000000000) : ℝ) = ((25000000000 / 1164824619851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (481955533 / 125000000) ≤ -Real.log (500000000000 / 23629527302561) ∧
    -Real.log (500000000000 / 23629527302561) ≤ (385564427 / 100000000) := by
  have h := checkLog_sound (w := (7629527302561 / 39629527302561)) (n := 12)
    (lo := (97477091 / 250000000)) (hi := (77981673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23629527302561 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23629527302561 / 16000000000000) = 1/(500000000000 / 23629527302561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (481955533 / 125000000) (385564427 / 100000000) (Real.log (23629527302561 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (23629527302561 / 500000000000) = -Real.log (500000000000 / 23629527302561) := by
    rw [show ((23629527302561 / 500000000000) : ℝ) = ((500000000000 / 23629527302561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0116

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0117Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0117
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

theorem reflection_log_1_neg : (66722823 / 100000000) ≤ -Real.log (2560 / 4989) ∧
    -Real.log (2560 / 4989) ≤ (667228231 / 1000000000) := by
  have h := checkLog_sound (w := (2429 / 7549)) (n := 12)
    (lo := (66722823 / 100000000)) (hi := (667228231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4989 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4989 / 2560) = 1/(2560 / 4989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66722823 / 100000000) (667228231 / 1000000000) (Real.log (4989 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4989 / 2560) = -Real.log (2560 / 4989) := by
    rw [show ((4989 / 2560) : ℝ) = ((2560 / 4989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (743141303 / 250000000) ≤ -Real.log (131 / 2560) ∧
    -Real.log (131 / 2560) ≤ (2972565217 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 291)) (n := 12)
    (lo := (49994123 / 250000000)) (hi := (199976493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 131) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 131) = 1/(131 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2972565217 / 1000000000) (-743141303 / 250000000) (Real.log (131 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (16671183 / 25000000) ≤ -Real.log (25600 / 49871) ∧
    -Real.log (25600 / 49871) ≤ (666847321 / 1000000000) := by
  have h := checkLog_sound (w := (24271 / 75471)) (n := 12)
    (lo := (16671183 / 25000000)) (hi := (666847321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49871 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49871 / 25600) = 1/(25600 / 49871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (16671183 / 25000000) (666847321 / 1000000000) (Real.log (49871 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49871 / 25600) = -Real.log (25600 / 49871) := by
    rw [show ((49871 / 25600) : ℝ) = ((25600 / 49871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2958165569 / 1000000000) ≤ -Real.log (1329 / 25600) ∧
    -Real.log (1329 / 25600) ≤ (1479082787 / 500000000) := by
  have h := checkLog_sound (w := (271 / 2929)) (n := 12)
    (lo := (185576849 / 1000000000)) (hi := (3711537 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1329) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1329) = 1/(1329 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1479082787 / 500000000) (-2958165569 / 1000000000) (Real.log (1329 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (160154893 / 250000000) ≤ -Real.log (1280 / 2429) ∧
    -Real.log (1280 / 2429) ≤ (640619573 / 1000000000) := by
  have h := checkLog_sound (w := (1149 / 3709)) (n := 12)
    (lo := (160154893 / 250000000)) (hi := (640619573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2429 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2429 / 1280) = 1/(1280 / 2429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (160154893 / 250000000) (640619573 / 1000000000) (Real.log (2429 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2429 / 1280) = -Real.log (1280 / 2429) := by
    rw [show ((2429 / 1280) : ℝ) = ((1280 / 2429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (142463627 / 62500000) ≤ -Real.log (131 / 1280) ∧
    -Real.log (131 / 1280) ≤ (569854509 / 250000000) := by
  have h := checkLog_sound (w := (29 / 291)) (n := 12)
    (lo := (49994123 / 250000000)) (hi := (199976493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 131) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 131) = 1/(131 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-569854509 / 250000000) (-142463627 / 62500000) (Real.log (131 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (639837051 / 1000000000) ≤ -Real.log (12800 / 24271) ∧
    -Real.log (12800 / 24271) ≤ (159959263 / 250000000) := by
  have h := checkLog_sound (w := (11471 / 37071)) (n := 12)
    (lo := (639837051 / 1000000000)) (hi := (159959263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24271 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24271 / 12800) = 1/(12800 / 24271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (639837051 / 1000000000) (159959263 / 250000000) (Real.log (24271 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24271 / 12800) = -Real.log (12800 / 24271) := by
    rw [show ((24271 / 12800) : ℝ) = ((12800 / 24271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2265018389 / 1000000000) ≤ -Real.log (1329 / 12800) ∧
    -Real.log (1329 / 12800) ≤ (2265018393 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2929)) (n := 12)
    (lo := (185576849 / 1000000000)) (hi := (3711537 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1329) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1329) = 1/(1329 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2265018393 / 1000000000) (-2265018389 / 1000000000) (Real.log (1329 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167970799 / 250000000) ≤ -Real.log (1000000 / 1957921) ∧
    -Real.log (1000000 / 1957921) ≤ (671883197 / 1000000000) := by
  have h := checkLog_sound (w := (957921 / 2957921)) (n := 12)
    (lo := (167970799 / 250000000)) (hi := (671883197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957921 / 1000000) = 1/(1000000 / 1957921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167970799 / 250000000) (671883197 / 1000000000) (Real.log (1957921 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1957921 / 1000000) = -Real.log (1000000 / 1957921) := by
    rw [show ((1957921 / 1000000) : ℝ) = ((1000000 / 1957921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (396025809 / 125000000) ≤ -Real.log (42079 / 1000000) ∧
    -Real.log (42079 / 1000000) ≤ (3168206477 / 1000000000) := by
  have h := checkLog_sound (w := (20421 / 104579)) (n := 12)
    (lo := (49452219 / 125000000)) (hi := (395617753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42079) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 42079) = 1/(42079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3168206477 / 1000000000) (-396025809 / 125000000) (Real.log (42079 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42010669 / 62500000) ≤ -Real.log (250000 / 489621) ∧
    -Real.log (250000 / 489621) ≤ (134434141 / 200000000) := by
  have h := checkLog_sound (w := (239621 / 739621)) (n := 12)
    (lo := (42010669 / 62500000)) (hi := (134434141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489621 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489621 / 250000) = 1/(250000 / 489621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42010669 / 62500000) (134434141 / 200000000) (Real.log (489621 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (489621 / 250000) = -Real.log (250000 / 489621) := by
    rw [show ((489621 / 250000) : ℝ) = ((250000 / 489621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3181676381 / 1000000000) ≤ -Real.log (10379 / 250000) ∧
    -Real.log (10379 / 250000) ≤ (1590838193 / 500000000) := by
  have h := checkLog_sound (w := (2623 / 13002)) (n := 12)
    (lo := (409087661 / 1000000000)) (hi := (204543831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10379) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 10379) = 1/(10379 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1590838193 / 500000000) (-3181676381 / 1000000000) (Real.log (10379 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (16790401 / 25000000) ≤ -Real.log (500000 / 978699) ∧
    -Real.log (500000 / 978699) ≤ (671616041 / 1000000000) := by
  have h := checkLog_sound (w := (478699 / 1478699)) (n := 12)
    (lo := (16790401 / 25000000)) (hi := (671616041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978699 / 500000) = 1/(500000 / 978699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (16790401 / 25000000) (671616041 / 1000000000) (Real.log (978699 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (978699 / 500000) = -Real.log (500000 / 978699) := by
    rw [show ((978699 / 500000) : ℝ) = ((500000 / 978699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (788963519 / 250000000) ≤ -Real.log (21301 / 500000) ∧
    -Real.log (21301 / 500000) ≤ (3155854081 / 1000000000) := by
  have h := checkLog_sound (w := (9949 / 52551)) (n := 12)
    (lo := (95816339 / 250000000)) (hi := (383265357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21301) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 21301) = 1/(21301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3155854081 / 1000000000) (-788963519 / 250000000) (Real.log (21301 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (167978077 / 250000000) ≤ -Real.log (500000 / 978989) ∧
    -Real.log (500000 / 978989) ≤ (671912309 / 1000000000) := by
  have h := checkLog_sound (w := (478989 / 1478989)) (n := 12)
    (lo := (167978077 / 250000000)) (hi := (671912309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978989 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978989 / 500000) = 1/(500000 / 978989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (167978077 / 250000000) (671912309 / 1000000000) (Real.log (978989 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (978989 / 500000) = -Real.log (500000 / 978989) := by
    rw [show ((978989 / 500000) : ℝ) = ((500000 / 978989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1584780993 / 500000000) ≤ -Real.log (21011 / 500000) ∧
    -Real.log (21011 / 500000) ≤ (3169561991 / 1000000000) := by
  have h := checkLog_sound (w := (10239 / 52261)) (n := 12)
    (lo := (198486633 / 500000000)) (hi := (396973267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21011) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 21011) = 1/(21011 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3169561991 / 1000000000) (-1584780993 / 500000000) (Real.log (21011 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (960022417 / 250000000) ≤ -Real.log (250000000000 / 11632411654269) ∧
    -Real.log (250000000000 / 11632411654269) ≤ (1920044837 / 500000000) := by
  have h := checkLog_sound (w := (3632411654269 / 19632411654269)) (n := 12)
    (lo := (46794221 / 125000000)) (hi := (374353769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11632411654269 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(11632411654269 / 8000000000000) = 1/(250000000000 / 11632411654269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (960022417 / 250000000) (1920044837 / 500000000) (Real.log (11632411654269 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11632411654269 / 250000000000) = -Real.log (250000000000 / 11632411654269) := by
    rw [show ((11632411654269 / 250000000000) : ℝ) = ((250000000000 / 11632411654269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (770769417 / 200000000) ≤ -Real.log (500000000000 / 23587098949803) ∧
    -Real.log (500000000000 / 23587098949803) ≤ (3853847091 / 1000000000) := by
  have h := checkLog_sound (w := (7587098949803 / 39587098949803)) (n := 12)
    (lo := (77622237 / 200000000)) (hi := (194055593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23587098949803 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23587098949803 / 16000000000000) = 1/(500000000000 / 23587098949803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (770769417 / 200000000) (3853847091 / 1000000000) (Real.log (23587098949803 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (23587098949803 / 500000000000) = -Real.log (500000000000 / 23587098949803) := by
    rw [show ((23587098949803 / 500000000000) : ℝ) = ((500000000000 / 23587098949803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (765494023 / 200000000) ≤ -Real.log (50000000000 / 2297307638139) ∧
    -Real.log (50000000000 / 2297307638139) ≤ (3827470121 / 1000000000) := by
  have h := checkLog_sound (w := (697307638139 / 3897307638139)) (n := 12)
    (lo := (72346843 / 200000000)) (hi := (45216777 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2297307638139 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2297307638139 / 1600000000000) = 1/(50000000000 / 2297307638139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (765494023 / 200000000) (3827470121 / 1000000000) (Real.log (2297307638139 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2297307638139 / 50000000000) = -Real.log (50000000000 / 2297307638139) := by
    rw [show ((2297307638139 / 50000000000) : ℝ) = ((50000000000 / 2297307638139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3841474293 / 1000000000) ≤ -Real.log (500000000000 / 23297058683547) ∧
    -Real.log (500000000000 / 23297058683547) ≤ (3841474299 / 1000000000) := by
  have h := checkLog_sound (w := (7297058683547 / 39297058683547)) (n := 12)
    (lo := (375738393 / 1000000000)) (hi := (187869197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23297058683547 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23297058683547 / 16000000000000) = 1/(500000000000 / 23297058683547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3841474293 / 1000000000) (3841474299 / 1000000000) (Real.log (23297058683547 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (23297058683547 / 500000000000) = -Real.log (500000000000 / 23297058683547) := by
    rw [show ((23297058683547 / 500000000000) : ℝ) = ((500000000000 / 23297058683547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0117

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0118Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0118
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

theorem reflection_log_1_neg : (16671183 / 25000000) ≤ -Real.log (25600 / 49871) ∧
    -Real.log (25600 / 49871) ≤ (666847321 / 1000000000) := by
  have h := checkLog_sound (w := (24271 / 75471)) (n := 12)
    (lo := (16671183 / 25000000)) (hi := (666847321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49871 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49871 / 25600) = 1/(25600 / 49871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (16671183 / 25000000) (666847321 / 1000000000) (Real.log (49871 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49871 / 25600) = -Real.log (25600 / 49871) := by
    rw [show ((49871 / 25600) : ℝ) = ((25600 / 49871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2958165569 / 1000000000) ≤ -Real.log (1329 / 25600) ∧
    -Real.log (1329 / 25600) ≤ (1479082787 / 500000000) := by
  have h := checkLog_sound (w := (271 / 2929)) (n := 12)
    (lo := (185576849 / 1000000000)) (hi := (3711537 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1329) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1329) = 1/(1329 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1479082787 / 500000000) (-2958165569 / 1000000000) (Real.log (1329 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (83308283 / 125000000) ≤ -Real.log (6400 / 12463) ∧
    -Real.log (6400 / 12463) ≤ (133293253 / 200000000) := by
  have h := checkLog_sound (w := (6063 / 18863)) (n := 12)
    (lo := (83308283 / 125000000)) (hi := (133293253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12463 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12463 / 6400) = 1/(6400 / 12463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (83308283 / 125000000) (133293253 / 200000000) (Real.log (12463 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12463 / 6400) = -Real.log (6400 / 12463) := by
    rw [show ((12463 / 6400) : ℝ) = ((6400 / 12463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (91999073 / 31250000) ≤ -Real.log (337 / 6400) ∧
    -Real.log (337 / 6400) ≤ (2943970341 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 737)) (n := 12)
    (lo := (10711351 / 62500000)) (hi := (171381617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 337) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 337) = 1/(337 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2943970341 / 1000000000) (-91999073 / 31250000) (Real.log (337 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (639837051 / 1000000000) ≤ -Real.log (12800 / 24271) ∧
    -Real.log (12800 / 24271) ≤ (159959263 / 250000000) := by
  have h := checkLog_sound (w := (11471 / 37071)) (n := 12)
    (lo := (639837051 / 1000000000)) (hi := (159959263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24271 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24271 / 12800) = 1/(12800 / 24271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (639837051 / 1000000000) (159959263 / 250000000) (Real.log (24271 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24271 / 12800) = -Real.log (12800 / 24271) := by
    rw [show ((24271 / 12800) : ℝ) = ((12800 / 24271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2265018389 / 1000000000) ≤ -Real.log (1329 / 12800) ∧
    -Real.log (1329 / 12800) ≤ (2265018393 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2929)) (n := 12)
    (lo := (185576849 / 1000000000)) (hi := (3711537 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1329) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1329) = 1/(1329 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2265018393 / 1000000000) (-2265018389 / 1000000000) (Real.log (1329 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (639053917 / 1000000000) ≤ -Real.log (3200 / 6063) ∧
    -Real.log (3200 / 6063) ≤ (319526959 / 500000000) := by
  have h := checkLog_sound (w := (2863 / 9263)) (n := 12)
    (lo := (639053917 / 1000000000)) (hi := (319526959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6063 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6063 / 3200) = 1/(3200 / 6063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (639053917 / 1000000000) (319526959 / 500000000) (Real.log (6063 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6063 / 3200) = -Real.log (3200 / 6063) := by
    rw [show ((6063 / 3200) : ℝ) = ((3200 / 6063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (562705789 / 250000000) ≤ -Real.log (337 / 3200) ∧
    -Real.log (337 / 3200) ≤ (56270579 / 25000000) := by
  have h := checkLog_sound (w := (63 / 737)) (n := 12)
    (lo := (10711351 / 62500000)) (hi := (171381617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 337) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 337) = 1/(337 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-56270579 / 25000000) (-562705789 / 250000000) (Real.log (337 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (335798313 / 500000000) ≤ -Real.log (12500 / 24467) ∧
    -Real.log (12500 / 24467) ≤ (671596627 / 1000000000) := by
  have h := checkLog_sound (w := (11967 / 36967)) (n := 12)
    (lo := (335798313 / 500000000)) (hi := (671596627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24467 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24467 / 12500) = 1/(12500 / 24467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (335798313 / 500000000) (671596627 / 1000000000) (Real.log (24467 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (24467 / 12500) = -Real.log (12500 / 24467) := by
    rw [show ((24467 / 12500) : ℝ) = ((12500 / 24467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (49296289 / 15625000) ≤ -Real.log (533 / 12500) ∧
    -Real.log (533 / 12500) ≤ (3154962501 / 1000000000) := by
  have h := checkLog_sound (w := (993 / 5257)) (n := 12)
    (lo := (23898361 / 62500000)) (hi := (382373777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2132) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2132) = 1/(533 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3154962501 / 1000000000) (-49296289 / 15625000) (Real.log (533 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (335941853 / 500000000) ≤ -Real.log (500000 / 978961) ∧
    -Real.log (500000 / 978961) ≤ (671883707 / 1000000000) := by
  have h := checkLog_sound (w := (478961 / 1478961)) (n := 12)
    (lo := (335941853 / 500000000)) (hi := (671883707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978961 / 500000) = 1/(500000 / 978961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (335941853 / 500000000) (671883707 / 1000000000) (Real.log (978961 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (978961 / 500000) = -Real.log (500000 / 978961) := by
    rw [show ((978961 / 500000) : ℝ) = ((500000 / 978961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3168230237 / 1000000000) ≤ -Real.log (21039 / 500000) ∧
    -Real.log (21039 / 500000) ≤ (1584115121 / 500000000) := by
  have h := checkLog_sound (w := (10211 / 52289)) (n := 12)
    (lo := (395641517 / 1000000000)) (hi := (197820759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21039) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 21039) = 1/(21039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1584115121 / 500000000) (-3168230237 / 1000000000) (Real.log (21039 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (335660353 / 500000000) ≤ -Real.log (50000 / 97841) ∧
    -Real.log (50000 / 97841) ≤ (671320707 / 1000000000) := by
  have h := checkLog_sound (w := (47841 / 147841)) (n := 12)
    (lo := (335660353 / 500000000)) (hi := (671320707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97841 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97841 / 50000) = 1/(50000 / 97841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (335660353 / 500000000) (671320707 / 1000000000) (Real.log (97841 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (97841 / 50000) = -Real.log (50000 / 97841) := by
    rw [show ((97841 / 50000) : ℝ) = ((50000 / 97841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3142377851 / 1000000000) ≤ -Real.log (2159 / 50000) ∧
    -Real.log (2159 / 50000) ≤ (24549827 / 7812500) := by
  have h := checkLog_sound (w := (483 / 2642)) (n := 12)
    (lo := (369789131 / 1000000000)) (hi := (92447283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2159) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2159) = 1/(2159 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-24549827 / 7812500) (-3142377851 / 1000000000) (Real.log (2159 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (671616551 / 1000000000) ≤ -Real.log (1000000 / 1957399) ∧
    -Real.log (1000000 / 1957399) ≤ (83952069 / 125000000) := by
  have h := checkLog_sound (w := (957399 / 2957399)) (n := 12)
    (lo := (671616551 / 1000000000)) (hi := (83952069 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957399 / 1000000) = 1/(1000000 / 1957399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (671616551 / 1000000000) (83952069 / 125000000) (Real.log (1957399 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1957399 / 1000000) = -Real.log (1000000 / 1957399) := by
    rw [show ((1957399 / 1000000) : ℝ) = ((1000000 / 1957399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3155877549 / 1000000000) ≤ -Real.log (42601 / 1000000) ∧
    -Real.log (42601 / 1000000) ≤ (1577938777 / 500000000) := by
  have h := checkLog_sound (w := (19899 / 105101)) (n := 12)
    (lo := (383288829 / 1000000000)) (hi := (38328883 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42601) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 42601) = 1/(42601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1577938777 / 500000000) (-3155877549 / 1000000000) (Real.log (42601 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1913279561 / 500000000) ≤ -Real.log (500000000000 / 22952157598499) ∧
    -Real.log (500000000000 / 22952157598499) ≤ (478319891 / 125000000) := by
  have h := checkLog_sound (w := (6952157598499 / 38952157598499)) (n := 12)
    (lo := (180411611 / 500000000)) (hi := (360823223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22952157598499 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(22952157598499 / 16000000000000) = 1/(500000000000 / 22952157598499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1913279561 / 500000000) (478319891 / 125000000) (Real.log (22952157598499 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (22952157598499 / 500000000000) = -Real.log (500000000000 / 22952157598499) := by
    rw [show ((22952157598499 / 500000000000) : ℝ) = ((500000000000 / 22952157598499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (480014243 / 125000000) ≤ -Real.log (125000000000 / 5816347022197) ∧
    -Real.log (125000000000 / 5816347022197) ≤ (76802279 / 20000000) := by
  have h := checkLog_sound (w := (1816347022197 / 9816347022197)) (n := 12)
    (lo := (93594511 / 250000000)) (hi := (74875609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5816347022197 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5816347022197 / 4000000000000) = 1/(125000000000 / 5816347022197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (480014243 / 125000000) (76802279 / 20000000) (Real.log (5816347022197 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5816347022197 / 125000000000) = -Real.log (125000000000 / 5816347022197) := by
    rw [show ((5816347022197 / 125000000000) : ℝ) = ((125000000000 / 5816347022197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3813698557 / 1000000000) ≤ -Real.log (500000000000 / 22658869847151) ∧
    -Real.log (500000000000 / 22658869847151) ≤ (3813698563 / 1000000000) := by
  have h := checkLog_sound (w := (6658869847151 / 38658869847151)) (n := 12)
    (lo := (347962657 / 1000000000)) (hi := (173981329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22658869847151 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(22658869847151 / 16000000000000) = 1/(500000000000 / 22658869847151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3813698557 / 1000000000) (3813698563 / 1000000000) (Real.log (22658869847151 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (22658869847151 / 500000000000) = -Real.log (500000000000 / 22658869847151) := by
    rw [show ((22658869847151 / 500000000000) : ℝ) = ((500000000000 / 22658869847151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (38274941 / 10000000) ≤ -Real.log (500000000000 / 22973627379639) ∧
    -Real.log (500000000000 / 22973627379639) ≤ (1913747053 / 500000000) := by
  have h := checkLog_sound (w := (6973627379639 / 38973627379639)) (n := 12)
    (lo := (1808791 / 5000000)) (hi := (361758201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22973627379639 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(22973627379639 / 16000000000000) = 1/(500000000000 / 22973627379639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (38274941 / 10000000) (1913747053 / 500000000) (Real.log (22973627379639 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (22973627379639 / 500000000000) = -Real.log (500000000000 / 22973627379639) := by
    rw [show ((22973627379639 / 500000000000) : ℝ) = ((500000000000 / 22973627379639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0118

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0119Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0119
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

theorem reflection_log_1_neg : (83308283 / 125000000) ≤ -Real.log (6400 / 12463) ∧
    -Real.log (6400 / 12463) ≤ (133293253 / 200000000) := by
  have h := checkLog_sound (w := (6063 / 18863)) (n := 12)
    (lo := (83308283 / 125000000)) (hi := (133293253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12463 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12463 / 6400) = 1/(6400 / 12463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (83308283 / 125000000) (133293253 / 200000000) (Real.log (12463 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12463 / 6400) = -Real.log (6400 / 12463) := by
    rw [show ((12463 / 6400) : ℝ) = ((6400 / 12463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (91999073 / 31250000) ≤ -Real.log (337 / 6400) ∧
    -Real.log (337 / 6400) ≤ (2943970341 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 737)) (n := 12)
    (lo := (10711351 / 62500000)) (hi := (171381617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 337) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 337) = 1/(337 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2943970341 / 1000000000) (-91999073 / 31250000) (Real.log (337 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (666085063 / 1000000000) ≤ -Real.log (25600 / 49833) ∧
    -Real.log (25600 / 49833) ≤ (83260633 / 125000000) := by
  have h := checkLog_sound (w := (24233 / 75433)) (n := 12)
    (lo := (666085063 / 1000000000)) (hi := (83260633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49833 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49833 / 25600) = 1/(25600 / 49833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (666085063 / 1000000000) (83260633 / 125000000) (Real.log (49833 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49833 / 25600) = -Real.log (25600 / 49833) := by
    rw [show ((49833 / 25600) : ℝ) = ((25600 / 49833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2929973791 / 1000000000) ≤ -Real.log (1367 / 25600) ∧
    -Real.log (1367 / 25600) ≤ (732493449 / 250000000) := by
  have h := checkLog_sound (w := (233 / 2967)) (n := 12)
    (lo := (157385071 / 1000000000)) (hi := (9836567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1367) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1367) = 1/(1367 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-732493449 / 250000000) (-2929973791 / 1000000000) (Real.log (1367 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (639053917 / 1000000000) ≤ -Real.log (3200 / 6063) ∧
    -Real.log (3200 / 6063) ≤ (319526959 / 500000000) := by
  have h := checkLog_sound (w := (2863 / 9263)) (n := 12)
    (lo := (639053917 / 1000000000)) (hi := (319526959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6063 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6063 / 3200) = 1/(3200 / 6063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (639053917 / 1000000000) (319526959 / 500000000) (Real.log (6063 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6063 / 3200) = -Real.log (3200 / 6063) := by
    rw [show ((6063 / 3200) : ℝ) = ((3200 / 6063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (562705789 / 250000000) ≤ -Real.log (337 / 3200) ∧
    -Real.log (337 / 3200) ≤ (56270579 / 25000000) := by
  have h := checkLog_sound (w := (63 / 737)) (n := 12)
    (lo := (10711351 / 62500000)) (hi := (171381617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 337) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 337) = 1/(337 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-56270579 / 25000000) (-562705789 / 250000000) (Real.log (337 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (638270169 / 1000000000) ≤ -Real.log (12800 / 24233) ∧
    -Real.log (12800 / 24233) ≤ (63827017 / 100000000) := by
  have h := checkLog_sound (w := (11433 / 37033)) (n := 12)
    (lo := (638270169 / 1000000000)) (hi := (63827017 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24233 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24233 / 12800) = 1/(12800 / 24233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (638270169 / 1000000000) (63827017 / 100000000) (Real.log (24233 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24233 / 12800) = -Real.log (12800 / 24233) := by
    rw [show ((24233 / 12800) : ℝ) = ((12800 / 24233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2236826611 / 1000000000) ≤ -Real.log (1367 / 12800) ∧
    -Real.log (1367 / 12800) ≤ (447365323 / 200000000) := by
  have h := checkLog_sound (w := (233 / 2967)) (n := 12)
    (lo := (157385071 / 1000000000)) (hi := (9836567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1367) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1367) = 1/(1367 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-447365323 / 200000000) (-2236826611 / 1000000000) (Real.log (1367 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (134262097 / 200000000) ≤ -Real.log (625 / 1223) ∧
    -Real.log (625 / 1223) ≤ (335655243 / 500000000) := by
  have h := checkLog_sound (w := (299 / 924)) (n := 12)
    (lo := (134262097 / 200000000)) (hi := (335655243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223 / 625) = 1/(625 / 1223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (134262097 / 200000000) (335655243 / 500000000) (Real.log (1223 / 625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1223 / 625) = -Real.log (625 / 1223) := by
    rw [show ((1223 / 625) : ℝ) = ((625 / 1223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3141914781 / 1000000000) ≤ -Real.log (27 / 625) ∧
    -Real.log (27 / 625) ≤ (1570957393 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1057)) (n := 12)
    (lo := (369326061 / 1000000000)) (hi := (184663031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 432) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625 / 432) = 1/(27 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1570957393 / 500000000) (-3141914781 / 1000000000) (Real.log (27 / 625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (671597137 / 1000000000) ≤ -Real.log (1000000 / 1957361) ∧
    -Real.log (1000000 / 1957361) ≤ (335798569 / 500000000) := by
  have h := checkLog_sound (w := (957361 / 2957361)) (n := 12)
    (lo := (671597137 / 1000000000)) (hi := (335798569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957361 / 1000000) = 1/(1000000 / 1957361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (671597137 / 1000000000) (335798569 / 500000000) (Real.log (1957361 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1957361 / 1000000) = -Real.log (1000000 / 1957361) := by
    rw [show ((1957361 / 1000000) : ℝ) = ((1000000 / 1957361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3154985949 / 1000000000) ≤ -Real.log (42639 / 1000000) ∧
    -Real.log (42639 / 1000000) ≤ (1577492977 / 500000000) := by
  have h := checkLog_sound (w := (19861 / 105139)) (n := 12)
    (lo := (382397229 / 1000000000)) (hi := (38239723 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42639) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 42639) = 1/(42639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1577492977 / 500000000) (-3154985949 / 1000000000) (Real.log (42639 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (134205057 / 200000000) ≤ -Real.log (500000 / 978121) ∧
    -Real.log (500000 / 978121) ≤ (335512643 / 500000000) := by
  have h := checkLog_sound (w := (478121 / 1478121)) (n := 12)
    (lo := (134205057 / 200000000)) (hi := (335512643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978121 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978121 / 500000) = 1/(500000 / 978121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (134205057 / 200000000) (335512643 / 500000000) (Real.log (978121 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (978121 / 500000) = -Real.log (500000 / 978121) := by
    rw [show ((978121 / 500000) : ℝ) = ((500000 / 978121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3129080823 / 1000000000) ≤ -Real.log (21879 / 500000) ∧
    -Real.log (21879 / 500000) ≤ (782270207 / 250000000) := by
  have h := checkLog_sound (w := (9371 / 53129)) (n := 12)
    (lo := (356492103 / 1000000000)) (hi := (44561513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21879) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 21879) = 1/(21879 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-782270207 / 250000000) (-3129080823 / 1000000000) (Real.log (21879 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (671321217 / 1000000000) ≤ -Real.log (1000000 / 1956821) ∧
    -Real.log (1000000 / 1956821) ≤ (335660609 / 500000000) := by
  have h := checkLog_sound (w := (956821 / 2956821)) (n := 12)
    (lo := (671321217 / 1000000000)) (hi := (335660609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1956821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1956821 / 1000000) = 1/(1000000 / 1956821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (671321217 / 1000000000) (335660609 / 500000000) (Real.log (1956821 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1956821 / 1000000) = -Real.log (1000000 / 1956821) := by
    rw [show ((1956821 / 1000000) : ℝ) = ((1000000 / 1956821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (314240101 / 100000000) ≤ -Real.log (43179 / 1000000) ∧
    -Real.log (43179 / 1000000) ≤ (628480203 / 200000000) := by
  have h := checkLog_sound (w := (19321 / 105679)) (n := 12)
    (lo := (36981229 / 100000000)) (hi := (369812291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43179) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 43179) = 1/(43179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-628480203 / 200000000) (-314240101 / 100000000) (Real.log (43179 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1906612633 / 500000000) ≤ -Real.log (125000000000 / 5662037037037) ∧
    -Real.log (125000000000 / 5662037037037) ≤ (476653159 / 125000000) := by
  have h := checkLog_sound (w := (1662037037037 / 9662037037037)) (n := 12)
    (lo := (173744683 / 500000000)) (hi := (347489367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5662037037037 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5662037037037 / 4000000000000) = 1/(125000000000 / 5662037037037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1906612633 / 500000000) (476653159 / 125000000) (Real.log (5662037037037 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5662037037037 / 125000000000) = -Real.log (125000000000 / 5662037037037) := by
    rw [show ((5662037037037 / 125000000000) : ℝ) = ((125000000000 / 5662037037037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1913291543 / 500000000) ≤ -Real.log (100000000000 / 4590541523019) ∧
    -Real.log (100000000000 / 4590541523019) ≤ (956645773 / 250000000) := by
  have h := checkLog_sound (w := (1390541523019 / 7790541523019)) (n := 12)
    (lo := (180423593 / 500000000)) (hi := (360847187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4590541523019 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4590541523019 / 3200000000000) = 1/(100000000000 / 4590541523019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1913291543 / 500000000) (956645773 / 250000000) (Real.log (4590541523019 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4590541523019 / 100000000000) = -Real.log (100000000000 / 4590541523019) := by
    rw [show ((4590541523019 / 100000000000) : ℝ) = ((100000000000 / 4590541523019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (950026527 / 250000000) ≤ -Real.log (250000000000 / 11176482014717) ∧
    -Real.log (250000000000 / 11176482014717) ≤ (1900053057 / 500000000) := by
  have h := checkLog_sound (w := (3176482014717 / 19176482014717)) (n := 12)
    (lo := (10449069 / 31250000)) (hi := (334370209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11176482014717 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(11176482014717 / 8000000000000) = 1/(250000000000 / 11176482014717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (950026527 / 250000000) (1900053057 / 500000000) (Real.log (11176482014717 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11176482014717 / 250000000000) = -Real.log (250000000000 / 11176482014717) := by
    rw [show ((11176482014717 / 250000000000) : ℝ) = ((250000000000 / 11176482014717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3813722227 / 1000000000) ≤ -Real.log (250000000000 / 11329703096413) ∧
    -Real.log (250000000000 / 11329703096413) ≤ (3813722233 / 1000000000) := by
  have h := checkLog_sound (w := (3329703096413 / 19329703096413)) (n := 12)
    (lo := (347986327 / 1000000000)) (hi := (43498291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11329703096413 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(11329703096413 / 8000000000000) = 1/(250000000000 / 11329703096413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3813722227 / 1000000000) (3813722233 / 1000000000) (Real.log (11329703096413 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11329703096413 / 250000000000) = -Real.log (250000000000 / 11329703096413) := by
    rw [show ((11329703096413 / 250000000000) : ℝ) = ((250000000000 / 11329703096413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0119

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0120Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0120
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

theorem reflection_log_1_neg : (666085063 / 1000000000) ≤ -Real.log (25600 / 49833) ∧
    -Real.log (25600 / 49833) ≤ (83260633 / 125000000) := by
  have h := checkLog_sound (w := (24233 / 75433)) (n := 12)
    (lo := (666085063 / 1000000000)) (hi := (83260633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49833 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49833 / 25600) = 1/(25600 / 49833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (666085063 / 1000000000) (83260633 / 125000000) (Real.log (49833 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49833 / 25600) = -Real.log (25600 / 49833) := by
    rw [show ((49833 / 25600) : ℝ) = ((25600 / 49833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2929973791 / 1000000000) ≤ -Real.log (1367 / 25600) ∧
    -Real.log (1367 / 25600) ≤ (732493449 / 250000000) := by
  have h := checkLog_sound (w := (233 / 2967)) (n := 12)
    (lo := (157385071 / 1000000000)) (hi := (9836567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1367) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1367) = 1/(1367 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-732493449 / 250000000) (-2929973791 / 1000000000) (Real.log (1367 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (665703717 / 1000000000) ≤ -Real.log (12800 / 24907) ∧
    -Real.log (12800 / 24907) ≤ (332851859 / 500000000) := by
  have h := checkLog_sound (w := (12107 / 37707)) (n := 12)
    (lo := (665703717 / 1000000000)) (hi := (332851859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24907 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24907 / 12800) = 1/(12800 / 24907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (665703717 / 1000000000) (332851859 / 500000000) (Real.log (24907 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24907 / 12800) = -Real.log (12800 / 24907) := by
    rw [show ((24907 / 12800) : ℝ) = ((12800 / 24907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (182260653 / 62500000) ≤ -Real.log (693 / 12800) ∧
    -Real.log (693 / 12800) ≤ (2916170453 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 1493)) (n := 12)
    (lo := (4486929 / 31250000)) (hi := (143581729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 693) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 693) = 1/(693 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2916170453 / 1000000000) (-182260653 / 62500000) (Real.log (693 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (638270169 / 1000000000) ≤ -Real.log (12800 / 24233) ∧
    -Real.log (12800 / 24233) ≤ (63827017 / 100000000) := by
  have h := checkLog_sound (w := (11433 / 37033)) (n := 12)
    (lo := (638270169 / 1000000000)) (hi := (63827017 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24233 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24233 / 12800) = 1/(12800 / 24233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (638270169 / 1000000000) (63827017 / 100000000) (Real.log (24233 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24233 / 12800) = -Real.log (12800 / 24233) := by
    rw [show ((24233 / 12800) : ℝ) = ((12800 / 24233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2236826611 / 1000000000) ≤ -Real.log (1367 / 12800) ∧
    -Real.log (1367 / 12800) ≤ (447365323 / 200000000) := by
  have h := checkLog_sound (w := (233 / 2967)) (n := 12)
    (lo := (157385071 / 1000000000)) (hi := (9836567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1367) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1367) = 1/(1367 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-447365323 / 200000000) (-2236826611 / 1000000000) (Real.log (1367 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (637485807 / 1000000000) ≤ -Real.log (6400 / 12107) ∧
    -Real.log (6400 / 12107) ≤ (39842863 / 62500000) := by
  have h := checkLog_sound (w := (5707 / 18507)) (n := 12)
    (lo := (637485807 / 1000000000)) (hi := (39842863 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12107 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12107 / 6400) = 1/(6400 / 12107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (637485807 / 1000000000) (39842863 / 62500000) (Real.log (12107 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12107 / 6400) = -Real.log (6400 / 12107) := by
    rw [show ((12107 / 6400) : ℝ) = ((6400 / 12107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (555755817 / 250000000) ≤ -Real.log (693 / 6400) ∧
    -Real.log (693 / 6400) ≤ (277877909 / 125000000) := by
  have h := checkLog_sound (w := (107 / 1493)) (n := 12)
    (lo := (4486929 / 31250000)) (hi := (143581729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 693) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 693) = 1/(693 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-277877909 / 125000000) (-555755817 / 250000000) (Real.log (693 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (335512387 / 500000000) ≤ -Real.log (1000000 / 1956241) ∧
    -Real.log (1000000 / 1956241) ≤ (26840991 / 40000000) := by
  have h := checkLog_sound (w := (956241 / 2956241)) (n := 12)
    (lo := (335512387 / 500000000)) (hi := (26840991 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1956241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1956241 / 1000000) = 1/(1000000 / 1956241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (335512387 / 500000000) (26840991 / 40000000) (Real.log (1956241 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1956241 / 1000000) = -Real.log (1000000 / 1956241) := by
    rw [show ((1956241 / 1000000) : ℝ) = ((1000000 / 1956241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (312905797 / 100000000) ≤ -Real.log (43759 / 1000000) ∧
    -Real.log (43759 / 1000000) ≤ (125162319 / 40000000) := by
  have h := checkLog_sound (w := (18741 / 106259)) (n := 12)
    (lo := (1425877 / 4000000)) (hi := (356469251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43759) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 43759) = 1/(43759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-125162319 / 40000000) (-312905797 / 100000000) (Real.log (43759 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (167827749 / 250000000) ≤ -Real.log (1000000 / 1956801) ∧
    -Real.log (1000000 / 1956801) ≤ (671310997 / 1000000000) := by
  have h := checkLog_sound (w := (956801 / 2956801)) (n := 12)
    (lo := (167827749 / 250000000)) (hi := (671310997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1956801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1956801 / 1000000) = 1/(1000000 / 1956801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (167827749 / 250000000) (671310997 / 1000000000) (Real.log (1956801 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1956801 / 1000000) = -Real.log (1000000 / 1956801) := by
    rw [show ((1956801 / 1000000) : ℝ) = ((1000000 / 1956801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3141937929 / 1000000000) ≤ -Real.log (43199 / 1000000) ∧
    -Real.log (43199 / 1000000) ≤ (1570968967 / 500000000) := by
  have h := checkLog_sound (w := (19301 / 105699)) (n := 12)
    (lo := (369349209 / 1000000000)) (hi := (36934921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43199) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 43199) = 1/(43199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1570968967 / 500000000) (-3141937929 / 1000000000) (Real.log (43199 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (670730289 / 1000000000) ≤ -Real.log (200000 / 391133) ∧
    -Real.log (200000 / 391133) ≤ (67073029 / 100000000) := by
  have h := checkLog_sound (w := (191133 / 591133)) (n := 12)
    (lo := (670730289 / 1000000000)) (hi := (67073029 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391133 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391133 / 200000) = 1/(200000 / 391133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (670730289 / 1000000000) (67073029 / 100000000) (Real.log (391133 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (391133 / 200000) = -Real.log (200000 / 391133) := by
    rw [show ((391133 / 200000) : ℝ) = ((200000 / 391133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3115980843 / 1000000000) ≤ -Real.log (8867 / 200000) ∧
    -Real.log (8867 / 200000) ≤ (194748803 / 62500000) := by
  have h := checkLog_sound (w := (3633 / 21367)) (n := 12)
    (lo := (343392123 / 1000000000)) (hi := (85848031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 8867) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 8867) = 1/(8867 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-194748803 / 62500000) (-3115980843 / 1000000000) (Real.log (8867 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (671025797 / 1000000000) ≤ -Real.log (1000000 / 1956243) ∧
    -Real.log (1000000 / 1956243) ≤ (335512899 / 500000000) := by
  have h := checkLog_sound (w := (956243 / 2956243)) (n := 12)
    (lo := (671025797 / 1000000000)) (hi := (335512899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1956243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1956243 / 1000000) = 1/(1000000 / 1956243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (671025797 / 1000000000) (335512899 / 500000000) (Real.log (1956243 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1956243 / 1000000) = -Real.log (1000000 / 1956243) := by
    rw [show ((1956243 / 1000000) : ℝ) = ((1000000 / 1956243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (782275919 / 250000000) ≤ -Real.log (43757 / 1000000) ∧
    -Real.log (43757 / 1000000) ≤ (3129103681 / 1000000000) := by
  have h := checkLog_sound (w := (18743 / 106257)) (n := 12)
    (lo := (89128739 / 250000000)) (hi := (356514957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43757) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 43757) = 1/(43757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3129103681 / 1000000000) (-782275919 / 250000000) (Real.log (43757 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (475010343 / 125000000) ≤ -Real.log (125000000000 / 5588110445851) ∧
    -Real.log (125000000000 / 5588110445851) ≤ (15200331 / 4000000) := by
  have h := checkLog_sound (w := (1588110445851 / 9588110445851)) (n := 12)
    (lo := (83586711 / 250000000)) (hi := (66869369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5588110445851 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5588110445851 / 4000000000000) = 1/(125000000000 / 5588110445851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (475010343 / 125000000) (15200331 / 4000000) (Real.log (5588110445851 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5588110445851 / 125000000000) = -Real.log (125000000000 / 5588110445851) := by
    rw [show ((5588110445851 / 125000000000) : ℝ) = ((125000000000 / 5588110445851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1906624463 / 500000000) ≤ -Real.log (100000000000 / 4529736799463) ∧
    -Real.log (100000000000 / 4529736799463) ≤ (953312233 / 250000000) := by
  have h := checkLog_sound (w := (1329736799463 / 7729736799463)) (n := 12)
    (lo := (173756513 / 500000000)) (hi := (347513027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4529736799463 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4529736799463 / 3200000000000) = 1/(100000000000 / 4529736799463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1906624463 / 500000000) (953312233 / 250000000) (Real.log (4529736799463 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4529736799463 / 100000000000) = -Real.log (100000000000 / 4529736799463) := by
    rw [show ((4529736799463 / 100000000000) : ℝ) = ((100000000000 / 4529736799463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (946677783 / 250000000) ≤ -Real.log (250000000000 / 11027771512349) ∧
    -Real.log (250000000000 / 11027771512349) ≤ (1893355569 / 500000000) := by
  have h := checkLog_sound (w := (3027771512349 / 19027771512349)) (n := 12)
    (lo := (2507619 / 7812500)) (hi := (320975233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11027771512349 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(11027771512349 / 8000000000000) = 1/(250000000000 / 11027771512349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (946677783 / 250000000) (1893355569 / 500000000) (Real.log (11027771512349 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11027771512349 / 250000000000) = -Real.log (250000000000 / 11027771512349) := by
    rw [show ((11027771512349 / 250000000000) : ℝ) = ((250000000000 / 11027771512349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3800129473 / 1000000000) ≤ -Real.log (100000000000 / 4470697259867) ∧
    -Real.log (100000000000 / 4470697259867) ≤ (3800129479 / 1000000000) := by
  have h := checkLog_sound (w := (1270697259867 / 7670697259867)) (n := 12)
    (lo := (334393573 / 1000000000)) (hi := (167196787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4470697259867 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4470697259867 / 3200000000000) = 1/(100000000000 / 4470697259867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3800129473 / 1000000000) (3800129479 / 1000000000) (Real.log (4470697259867 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4470697259867 / 100000000000) = -Real.log (100000000000 / 4470697259867) := by
    rw [show ((4470697259867 / 100000000000) : ℝ) = ((100000000000 / 4470697259867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0120

end


