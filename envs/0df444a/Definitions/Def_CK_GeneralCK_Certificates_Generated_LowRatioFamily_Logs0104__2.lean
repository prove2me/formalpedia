-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0104__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0104__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T20:43:50.875723+00:00
-- url     : https://prove2.me/theorems/c264f0ee-8b8e-4123-b7b9-0e72ee50b6a8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0104 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0105)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0104 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0105)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0104 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0105)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0104 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0105) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0104 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0105).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0104 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6656_neg : (9990829 / 1000000000) ≤ -Real.log (39602356519 / 40000000000) ∧
    -Real.log (39602356519 / 40000000000) ≤ (999083 / 100000000) := by
  have h := checkLog_sound (w := (397643481 / 79602356519)) (n := 12)
    (lo := (9990829 / 1000000000)) (hi := (999083 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39602356519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39602356519) = 1/(39602356519 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6656 : Bounds (-999083 / 100000000) (-9990829 / 1000000000) (Real.log (39602356519 / 40000000000)) := by
  have h := reflection_log_6656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6657_neg : (9940741 / 1000000000) ≤ -Real.log (241725709 / 244140625) ∧
    -Real.log (241725709 / 244140625) ≤ (4970371 / 500000000) := by
  have h := checkLog_sound (w := (1207458 / 242933167)) (n := 12)
    (lo := (9940741 / 1000000000)) (hi := (4970371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 241725709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 241725709) = 1/(241725709 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6657 : Bounds (-4970371 / 500000000) (-9940741 / 1000000000) (Real.log (241725709 / 244140625)) := by
  have h := reflection_log_6657_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6658_neg : (39914353 / 200000000) ≤ -Real.log (800000000 / 976703859) ∧
    -Real.log (800000000 / 976703859) ≤ (99785883 / 500000000) := by
  have h := checkLog_sound (w := (176703859 / 1776703859)) (n := 12)
    (lo := (39914353 / 200000000)) (hi := (99785883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976703859 / 800000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976703859 / 800000000) = 1/(800000000 / 976703859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6658 : Bounds (39914353 / 200000000) (99785883 / 500000000) (Real.log (976703859 / 800000000)) := by
  have h := reflection_log_6658_neg
  have he : Real.log (976703859 / 800000000) = -Real.log (800000000 / 976703859) := by
    rw [show ((976703859 / 800000000) : ℝ) = ((800000000 / 976703859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6659_neg : (200074753 / 1000000000) ≤ -Real.log (500000000000 / 610747032917) ∧
    -Real.log (500000000000 / 610747032917) ≤ (100037377 / 500000000) := by
  have h := checkLog_sound (w := (110747032917 / 1110747032917)) (n := 12)
    (lo := (200074753 / 1000000000)) (hi := (100037377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610747032917 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610747032917 / 500000000000) = 1/(500000000000 / 610747032917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6659 : Bounds (200074753 / 1000000000) (100037377 / 500000000) (Real.log (610747032917 / 500000000000)) := by
  have h := reflection_log_6659_neg
  have he : Real.log (610747032917 / 500000000000) = -Real.log (500000000000 / 610747032917) := by
    rw [show ((610747032917 / 500000000000) : ℝ) = ((500000000000 / 610747032917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6660_neg : (400675727 / 1000000000) ≤ -Real.log (500000000000 / 746416552411) ∧
    -Real.log (500000000000 / 746416552411) ≤ (25042233 / 62500000) := by
  have h := checkLog_sound (w := (246416552411 / 1246416552411)) (n := 12)
    (lo := (400675727 / 1000000000)) (hi := (25042233 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746416552411 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746416552411 / 500000000000) = 1/(500000000000 / 746416552411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6660 : Bounds (400675727 / 1000000000) (25042233 / 62500000) (Real.log (746416552411 / 500000000000)) := by
  have h := reflection_log_6660_neg
  have he : Real.log (746416552411 / 500000000000) = -Real.log (500000000000 / 746416552411) := by
    rw [show ((746416552411 / 500000000000) : ℝ) = ((500000000000 / 746416552411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6661_neg : (200441933 / 500000000) ≤ -Real.log (500000000000 / 746571927201) ∧
    -Real.log (500000000000 / 746571927201) ≤ (400883867 / 1000000000) := by
  have h := checkLog_sound (w := (246571927201 / 1246571927201)) (n := 12)
    (lo := (200441933 / 500000000)) (hi := (400883867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746571927201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746571927201 / 500000000000) = 1/(500000000000 / 746571927201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6661 : Bounds (200441933 / 500000000) (400883867 / 1000000000) (Real.log (746571927201 / 500000000000)) := by
  have h := reflection_log_6661_neg
  have he : Real.log (746571927201 / 500000000000) = -Real.log (500000000000 / 746571927201) := by
    rw [show ((746571927201 / 500000000000) : ℝ) = ((500000000000 / 746571927201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6662_neg : (180570023 / 1000000000) ≤ -Real.log (10000 / 11979) ∧
    -Real.log (10000 / 11979) ≤ (22571253 / 125000000) := by
  have h := checkLog_sound (w := (1979 / 21979)) (n := 12)
    (lo := (180570023 / 1000000000)) (hi := (22571253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11979 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11979 / 10000) = 1/(10000 / 11979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6662 : Bounds (180570023 / 1000000000) (22571253 / 125000000) (Real.log (11979 / 10000)) := by
  have h := reflection_log_6662_neg
  have he : Real.log (11979 / 10000) = -Real.log (10000 / 11979) := by
    rw [show ((11979 / 10000) : ℝ) = ((10000 / 11979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6663_neg : (22052199 / 100000000) ≤ -Real.log (8021 / 10000) ∧
    -Real.log (8021 / 10000) ≤ (220521991 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 18021)) (n := 12)
    (lo := (22052199 / 100000000)) (hi := (220521991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8021) = 1/(8021 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6663 : Bounds (-220521991 / 1000000000) (-22052199 / 100000000) (Real.log (8021 / 10000)) := by
  have h := reflection_log_6663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6664_neg : (4947 / 25000000) ≤ -Real.log (10000000 / 10001979) ∧
    -Real.log (10000000 / 10001979) ≤ (197881 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 20001979)) (n := 12)
    (lo := (4947 / 25000000)) (hi := (197881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001979 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001979 / 10000000) = 1/(10000000 / 10001979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6664 : Bounds (4947 / 25000000) (197881 / 1000000000) (Real.log (10001979 / 10000000)) := by
  have h := reflection_log_6664_neg
  have he : Real.log (10001979 / 10000000) = -Real.log (10000000 / 10001979) := by
    rw [show ((10001979 / 10000000) : ℝ) = ((10000000 / 10001979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6665_neg : (197919 / 1000000000) ≤ -Real.log (9998021 / 10000000) ∧
    -Real.log (9998021 / 10000000) ≤ (1237 / 6250000) := by
  have h := checkLog_sound (w := (1979 / 19998021)) (n := 12)
    (lo := (197919 / 1000000000)) (hi := (1237 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998021) = 1/(9998021 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6665 : Bounds (-1237 / 6250000) (-197919 / 1000000000) (Real.log (9998021 / 10000000)) := by
  have h := reflection_log_6665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6666_neg : (94861897 / 1000000000) ≤ -Real.log (1000000 / 1099507) ∧
    -Real.log (1000000 / 1099507) ≤ (47430949 / 500000000) := by
  have h := checkLog_sound (w := (99507 / 2099507)) (n := 12)
    (lo := (94861897 / 1000000000)) (hi := (47430949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099507 / 1000000) = 1/(1000000 / 1099507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6666 : Bounds (94861897 / 1000000000) (47430949 / 500000000) (Real.log (1099507 / 1000000)) := by
  have h := reflection_log_6666_neg
  have he : Real.log (1099507 / 1000000) = -Real.log (1000000 / 1099507) := by
    rw [show ((1099507 / 1000000) : ℝ) = ((1000000 / 1099507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6667_neg : (104812887 / 1000000000) ≤ -Real.log (900493 / 1000000) ∧
    -Real.log (900493 / 1000000) ≤ (13101611 / 125000000) := by
  have h := checkLog_sound (w := (99507 / 1900493)) (n := 12)
    (lo := (104812887 / 1000000000)) (hi := (13101611 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900493) = 1/(900493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6667 : Bounds (-13101611 / 125000000) (-104812887 / 1000000000) (Real.log (900493 / 1000000)) := by
  have h := reflection_log_6667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6668_neg : (95088337 / 1000000000) ≤ -Real.log (250000 / 274939) ∧
    -Real.log (250000 / 274939) ≤ (47544169 / 500000000) := by
  have h := checkLog_sound (w := (24939 / 524939)) (n := 12)
    (lo := (95088337 / 1000000000)) (hi := (47544169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274939 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274939 / 250000) = 1/(250000 / 274939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6668 : Bounds (95088337 / 1000000000) (47544169 / 500000000) (Real.log (274939 / 250000)) := by
  have h := reflection_log_6668_neg
  have he : Real.log (274939 / 250000) = -Real.log (250000 / 274939) := by
    rw [show ((274939 / 250000) : ℝ) = ((250000 / 274939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6669_neg : (105089441 / 1000000000) ≤ -Real.log (225061 / 250000) ∧
    -Real.log (225061 / 250000) ≤ (52544721 / 500000000) := by
  have h := checkLog_sound (w := (24939 / 475061)) (n := 12)
    (lo := (105089441 / 1000000000)) (hi := (52544721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225061) = 1/(225061 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6669 : Bounds (-52544721 / 500000000) (-105089441 / 1000000000) (Real.log (225061 / 250000)) := by
  have h := reflection_log_6669_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6670_neg : (625069 / 62500000) ≤ -Real.log (61878046279 / 62500000000) ∧
    -Real.log (61878046279 / 62500000000) ≤ (2000221 / 200000000) := by
  have h := checkLog_sound (w := (621953721 / 124378046279)) (n := 12)
    (lo := (625069 / 62500000)) (hi := (2000221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61878046279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61878046279) = 1/(61878046279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6670 : Bounds (-2000221 / 200000000) (-625069 / 62500000) (Real.log (61878046279 / 62500000000)) := by
  have h := reflection_log_6670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6671_neg : (995099 / 100000000) ≤ -Real.log (990098356951 / 1000000000000) ∧
    -Real.log (990098356951 / 1000000000000) ≤ (9950991 / 1000000000) := by
  have h := checkLog_sound (w := (9901643049 / 1990098356951)) (n := 12)
    (lo := (995099 / 100000000)) (hi := (9950991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990098356951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990098356951) = 1/(990098356951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6671 : Bounds (-9950991 / 1000000000) (-995099 / 100000000) (Real.log (990098356951 / 1000000000000)) := by
  have h := reflection_log_6671_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6672_neg : (39934957 / 200000000) ≤ -Real.log (500000000000 / 610502802353) ∧
    -Real.log (500000000000 / 610502802353) ≤ (99837393 / 500000000) := by
  have h := checkLog_sound (w := (110502802353 / 1110502802353)) (n := 12)
    (lo := (39934957 / 200000000)) (hi := (99837393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610502802353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610502802353 / 500000000000) = 1/(500000000000 / 610502802353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6672 : Bounds (39934957 / 200000000) (99837393 / 500000000) (Real.log (610502802353 / 500000000000)) := by
  have h := reflection_log_6672_neg
  have he : Real.log (610502802353 / 500000000000) = -Real.log (500000000000 / 610502802353) := by
    rw [show ((610502802353 / 500000000000) : ℝ) = ((500000000000 / 610502802353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6673_neg : (100088889 / 500000000) ≤ -Real.log (50000000000 / 61080995819) ∧
    -Real.log (50000000000 / 61080995819) ≤ (200177779 / 1000000000) := by
  have h := checkLog_sound (w := (11080995819 / 111080995819)) (n := 12)
    (lo := (100088889 / 500000000)) (hi := (200177779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61080995819 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61080995819 / 50000000000) = 1/(50000000000 / 61080995819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6673 : Bounds (100088889 / 500000000) (200177779 / 1000000000) (Real.log (61080995819 / 50000000000)) := by
  have h := reflection_log_6673_neg
  have he : Real.log (61080995819 / 50000000000) = -Real.log (50000000000 / 61080995819) := by
    rw [show ((61080995819 / 50000000000) : ℝ) = ((50000000000 / 61080995819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6674_neg : (200441933 / 500000000) ≤ -Real.log (625000000 / 933214909) ∧
    -Real.log (625000000 / 933214909) ≤ (400883867 / 1000000000) := by
  have h := checkLog_sound (w := (308214909 / 1558214909)) (n := 12)
    (lo := (200441933 / 500000000)) (hi := (400883867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933214909 / 625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933214909 / 625000000) = 1/(625000000 / 933214909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6674 : Bounds (200441933 / 500000000) (400883867 / 1000000000) (Real.log (933214909 / 625000000)) := by
  have h := reflection_log_6674_neg
  have he : Real.log (933214909 / 625000000) = -Real.log (625000000 / 933214909) := by
    rw [show ((933214909 / 625000000) : ℝ) = ((625000000 / 933214909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6675_neg : (200546007 / 500000000) ≤ -Real.log (500000000000 / 746727340731) ∧
    -Real.log (500000000000 / 746727340731) ≤ (80218403 / 200000000) := by
  have h := checkLog_sound (w := (246727340731 / 1246727340731)) (n := 12)
    (lo := (200546007 / 500000000)) (hi := (80218403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746727340731 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746727340731 / 500000000000) = 1/(500000000000 / 746727340731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6675 : Bounds (200546007 / 500000000) (80218403 / 200000000) (Real.log (746727340731 / 500000000000)) := by
  have h := reflection_log_6675_neg
  have he : Real.log (746727340731 / 500000000000) = -Real.log (500000000000 / 746727340731) := by
    rw [show ((746727340731 / 500000000000) : ℝ) = ((500000000000 / 746727340731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6676_neg : (180653499 / 1000000000) ≤ -Real.log (500 / 599) ∧
    -Real.log (500 / 599) ≤ (361307 / 2000000) := by
  have h := checkLog_sound (w := (99 / 1099)) (n := 12)
    (lo := (180653499 / 1000000000)) (hi := (361307 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599 / 500) = 1/(500 / 599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6676 : Bounds (180653499 / 1000000000) (361307 / 2000000) (Real.log (599 / 500)) := by
  have h := reflection_log_6676_neg
  have he : Real.log (599 / 500) = -Real.log (500 / 599) := by
    rw [show ((599 / 500) : ℝ) = ((500 / 599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6677_neg : (220646671 / 1000000000) ≤ -Real.log (401 / 500) ∧
    -Real.log (401 / 500) ≤ (13790417 / 62500000) := by
  have h := checkLog_sound (w := (99 / 901)) (n := 12)
    (lo := (220646671 / 1000000000)) (hi := (13790417 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 401) = 1/(401 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6677 : Bounds (-13790417 / 62500000) (-220646671 / 1000000000) (Real.log (401 / 500)) := by
  have h := reflection_log_6677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6678_neg : (9899 / 50000000) ≤ -Real.log (500000 / 500099) ∧
    -Real.log (500000 / 500099) ≤ (197981 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 1000099)) (n := 12)
    (lo := (9899 / 50000000)) (hi := (197981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500099 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500099 / 500000) = 1/(500000 / 500099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6678 : Bounds (9899 / 50000000) (197981 / 1000000000) (Real.log (500099 / 500000)) := by
  have h := reflection_log_6678_neg
  have he : Real.log (500099 / 500000) = -Real.log (500000 / 500099) := by
    rw [show ((500099 / 500000) : ℝ) = ((500000 / 500099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6679_neg : (198019 / 1000000000) ≤ -Real.log (499901 / 500000) ∧
    -Real.log (499901 / 500000) ≤ (9901 / 50000000) := by
  have h := checkLog_sound (w := (99 / 999901)) (n := 12)
    (lo := (198019 / 1000000000)) (hi := (9901 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499901) = 1/(499901 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6679 : Bounds (-9901 / 50000000) (-198019 / 1000000000) (Real.log (499901 / 500000)) := by
  have h := reflection_log_6679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6680_neg : (2372707 / 25000000) ≤ -Real.log (500000 / 549779) ∧
    -Real.log (500000 / 549779) ≤ (94908281 / 1000000000) := by
  have h := checkLog_sound (w := (49779 / 1049779)) (n := 12)
    (lo := (2372707 / 25000000)) (hi := (94908281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549779 / 500000) = 1/(500000 / 549779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6680 : Bounds (2372707 / 25000000) (94908281 / 1000000000) (Real.log (549779 / 500000)) := by
  have h := reflection_log_6680_neg
  have he : Real.log (549779 / 500000) = -Real.log (500000 / 549779) := by
    rw [show ((549779 / 500000) : ℝ) = ((500000 / 549779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6681_neg : (4194781 / 40000000) ≤ -Real.log (450221 / 500000) ∧
    -Real.log (450221 / 500000) ≤ (52434763 / 500000000) := by
  have h := checkLog_sound (w := (49779 / 950221)) (n := 12)
    (lo := (4194781 / 40000000)) (hi := (52434763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450221) = 1/(450221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6681 : Bounds (-52434763 / 500000000) (-4194781 / 40000000) (Real.log (450221 / 500000)) := by
  have h := reflection_log_6681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6682_neg : (95134709 / 1000000000) ≤ -Real.log (1000000 / 1099807) ∧
    -Real.log (1000000 / 1099807) ≤ (9513471 / 100000000) := by
  have h := checkLog_sound (w := (99807 / 2099807)) (n := 12)
    (lo := (95134709 / 1000000000)) (hi := (9513471 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099807 / 1000000) = 1/(1000000 / 1099807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6682 : Bounds (95134709 / 1000000000) (9513471 / 100000000) (Real.log (1099807 / 1000000)) := by
  have h := reflection_log_6682_neg
  have he : Real.log (1099807 / 1000000) = -Real.log (1000000 / 1099807) := by
    rw [show ((1099807 / 1000000) : ℝ) = ((1000000 / 1099807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6683_neg : (52573047 / 500000000) ≤ -Real.log (900193 / 1000000) ∧
    -Real.log (900193 / 1000000) ≤ (21029219 / 200000000) := by
  have h := checkLog_sound (w := (99807 / 1900193)) (n := 12)
    (lo := (52573047 / 500000000)) (hi := (21029219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900193) = 1/(900193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6683 : Bounds (-21029219 / 200000000) (-52573047 / 500000000) (Real.log (900193 / 1000000)) := by
  have h := reflection_log_6683_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6684_neg : (1251423 / 125000000) ≤ -Real.log (990038562751 / 1000000000000) ∧
    -Real.log (990038562751 / 1000000000000) ≤ (2002277 / 200000000) := by
  have h := checkLog_sound (w := (9961437249 / 1990038562751)) (n := 12)
    (lo := (1251423 / 125000000)) (hi := (2002277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990038562751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990038562751) = 1/(990038562751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6684 : Bounds (-2002277 / 200000000) (-1251423 / 125000000) (Real.log (990038562751 / 1000000000000)) := by
  have h := reflection_log_6684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6685_neg : (2490311 / 250000000) ≤ -Real.log (247522051159 / 250000000000) ∧
    -Real.log (247522051159 / 250000000000) ≤ (1992249 / 200000000) := by
  have h := checkLog_sound (w := (2477948841 / 497522051159)) (n := 12)
    (lo := (2490311 / 250000000)) (hi := (1992249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247522051159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247522051159) = 1/(247522051159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6685 : Bounds (-1992249 / 200000000) (-2490311 / 250000000) (Real.log (247522051159 / 250000000000)) := by
  have h := reflection_log_6685_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6686_neg : (39955561 / 200000000) ≤ -Real.log (125000000000 / 152641424989) ∧
    -Real.log (125000000000 / 152641424989) ≤ (99888903 / 500000000) := by
  have h := checkLog_sound (w := (27641424989 / 277641424989)) (n := 12)
    (lo := (39955561 / 200000000)) (hi := (99888903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152641424989 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152641424989 / 125000000000) = 1/(125000000000 / 152641424989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6686 : Bounds (39955561 / 200000000) (99888903 / 500000000) (Real.log (152641424989 / 125000000000)) := by
  have h := reflection_log_6686_neg
  have he : Real.log (152641424989 / 125000000000) = -Real.log (125000000000 / 152641424989) := by
    rw [show ((152641424989 / 125000000000) : ℝ) = ((125000000000 / 152641424989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6687_neg : (50070201 / 250000000) ≤ -Real.log (15625000000 / 19089777831) ∧
    -Real.log (15625000000 / 19089777831) ≤ (40056161 / 200000000) := by
  have h := checkLog_sound (w := (3464777831 / 34714777831)) (n := 12)
    (lo := (50070201 / 250000000)) (hi := (40056161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19089777831 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19089777831 / 15625000000) = 1/(15625000000 / 19089777831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6687 : Bounds (50070201 / 250000000) (40056161 / 200000000) (Real.log (19089777831 / 15625000000)) := by
  have h := reflection_log_6687_neg
  have he : Real.log (19089777831 / 15625000000) = -Real.log (15625000000 / 19089777831) := by
    rw [show ((19089777831 / 15625000000) : ℝ) = ((15625000000 / 19089777831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6688_neg : (200546007 / 500000000) ≤ -Real.log (50000000000 / 74672734073) ∧
    -Real.log (50000000000 / 74672734073) ≤ (80218403 / 200000000) := by
  have h := checkLog_sound (w := (24672734073 / 124672734073)) (n := 12)
    (lo := (200546007 / 500000000)) (hi := (80218403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74672734073 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74672734073 / 50000000000) = 1/(50000000000 / 74672734073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6688 : Bounds (200546007 / 500000000) (80218403 / 200000000) (Real.log (74672734073 / 50000000000)) := by
  have h := reflection_log_6688_neg
  have he : Real.log (74672734073 / 50000000000) = -Real.log (50000000000 / 74672734073) := by
    rw [show ((74672734073 / 50000000000) : ℝ) = ((50000000000 / 74672734073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6689_neg : (40130017 / 100000000) ≤ -Real.log (250000000000 / 373441396509) ∧
    -Real.log (250000000000 / 373441396509) ≤ (401300171 / 1000000000) := by
  have h := checkLog_sound (w := (123441396509 / 623441396509)) (n := 12)
    (lo := (40130017 / 100000000)) (hi := (401300171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373441396509 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373441396509 / 250000000000) = 1/(250000000000 / 373441396509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6689 : Bounds (40130017 / 100000000) (401300171 / 1000000000) (Real.log (373441396509 / 250000000000)) := by
  have h := reflection_log_6689_neg
  have he : Real.log (373441396509 / 250000000000) = -Real.log (250000000000 / 373441396509) := by
    rw [show ((373441396509 / 250000000000) : ℝ) = ((250000000000 / 373441396509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6690_neg : (22592121 / 125000000) ≤ -Real.log (10000 / 11981) ∧
    -Real.log (10000 / 11981) ≤ (180736969 / 1000000000) := by
  have h := checkLog_sound (w := (1981 / 21981)) (n := 12)
    (lo := (22592121 / 125000000)) (hi := (180736969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11981 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11981 / 10000) = 1/(10000 / 11981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6690 : Bounds (22592121 / 125000000) (180736969 / 1000000000) (Real.log (11981 / 10000)) := by
  have h := reflection_log_6690_neg
  have he : Real.log (11981 / 10000) = -Real.log (10000 / 11981) := by
    rw [show ((11981 / 10000) : ℝ) = ((10000 / 11981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6691_neg : (220771367 / 1000000000) ≤ -Real.log (8019 / 10000) ∧
    -Real.log (8019 / 10000) ≤ (27596421 / 125000000) := by
  have h := checkLog_sound (w := (1981 / 18019)) (n := 12)
    (lo := (220771367 / 1000000000)) (hi := (27596421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8019) = 1/(8019 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6691 : Bounds (-27596421 / 125000000) (-220771367 / 1000000000) (Real.log (8019 / 10000)) := by
  have h := reflection_log_6691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6692_neg : (619 / 3125000) ≤ -Real.log (10000000 / 10001981) ∧
    -Real.log (10000000 / 10001981) ≤ (198081 / 1000000000) := by
  have h := checkLog_sound (w := (1981 / 20001981)) (n := 12)
    (lo := (619 / 3125000)) (hi := (198081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001981 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001981 / 10000000) = 1/(10000000 / 10001981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6692 : Bounds (619 / 3125000) (198081 / 1000000000) (Real.log (10001981 / 10000000)) := by
  have h := reflection_log_6692_neg
  have he : Real.log (10001981 / 10000000) = -Real.log (10000000 / 10001981) := by
    rw [show ((10001981 / 10000000) : ℝ) = ((10000000 / 10001981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6693_neg : (198119 / 1000000000) ≤ -Real.log (9998019 / 10000000) ∧
    -Real.log (9998019 / 10000000) ≤ (4953 / 25000000) := by
  have h := checkLog_sound (w := (1981 / 19998019)) (n := 12)
    (lo := (198119 / 1000000000)) (hi := (4953 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998019) = 1/(9998019 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6693 : Bounds (-4953 / 25000000) (-198119 / 1000000000) (Real.log (9998019 / 10000000)) := by
  have h := reflection_log_6693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6694_neg : (47477331 / 500000000) ≤ -Real.log (1000000 / 1099609) ∧
    -Real.log (1000000 / 1099609) ≤ (94954663 / 1000000000) := by
  have h := checkLog_sound (w := (99609 / 2099609)) (n := 12)
    (lo := (47477331 / 500000000)) (hi := (94954663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099609 / 1000000) = 1/(1000000 / 1099609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6694 : Bounds (47477331 / 500000000) (94954663 / 1000000000) (Real.log (1099609 / 1000000)) := by
  have h := reflection_log_6694_neg
  have he : Real.log (1099609 / 1000000) = -Real.log (1000000 / 1099609) := by
    rw [show ((1099609 / 1000000) : ℝ) = ((1000000 / 1099609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6695_neg : (20985233 / 200000000) ≤ -Real.log (900391 / 1000000) ∧
    -Real.log (900391 / 1000000) ≤ (52463083 / 500000000) := by
  have h := checkLog_sound (w := (99609 / 1900391)) (n := 12)
    (lo := (20985233 / 200000000)) (hi := (52463083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900391) = 1/(900391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6695 : Bounds (-52463083 / 500000000) (-20985233 / 200000000) (Real.log (900391 / 1000000)) := by
  have h := reflection_log_6695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6696_neg : (2379527 / 25000000) ≤ -Real.log (500000 / 549929) ∧
    -Real.log (500000 / 549929) ≤ (95181081 / 1000000000) := by
  have h := checkLog_sound (w := (49929 / 1049929)) (n := 12)
    (lo := (2379527 / 25000000)) (hi := (95181081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549929 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549929 / 500000) = 1/(500000 / 549929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6696 : Bounds (2379527 / 25000000) (95181081 / 1000000000) (Real.log (549929 / 500000)) := by
  have h := reflection_log_6696_neg
  have he : Real.log (549929 / 500000) = -Real.log (500000 / 549929) := by
    rw [show ((549929 / 500000) : ℝ) = ((500000 / 549929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6697_neg : (420811 / 4000000) ≤ -Real.log (450071 / 500000) ∧
    -Real.log (450071 / 500000) ≤ (105202751 / 1000000000) := by
  have h := checkLog_sound (w := (49929 / 950071)) (n := 12)
    (lo := (420811 / 4000000)) (hi := (105202751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450071) = 1/(450071 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6697 : Bounds (-105202751 / 1000000000) (-420811 / 4000000) (Real.log (450071 / 500000)) := by
  have h := reflection_log_6697_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6698_neg : (10021669 / 1000000000) ≤ -Real.log (247507094959 / 250000000000) ∧
    -Real.log (247507094959 / 250000000000) ≤ (1002167 / 100000000) := by
  have h := checkLog_sound (w := (2492905041 / 497507094959)) (n := 12)
    (lo := (10021669 / 1000000000)) (hi := (1002167 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247507094959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247507094959) = 1/(247507094959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6698 : Bounds (-1002167 / 100000000) (-10021669 / 1000000000) (Real.log (247507094959 / 250000000000)) := by
  have h := reflection_log_6698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6699_neg : (9971503 / 1000000000) ≤ -Real.log (990078047119 / 1000000000000) ∧
    -Real.log (990078047119 / 1000000000000) ≤ (623219 / 62500000) := by
  have h := checkLog_sound (w := (9921952881 / 1990078047119)) (n := 12)
    (lo := (9971503 / 1000000000)) (hi := (623219 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990078047119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990078047119) = 1/(990078047119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6699 : Bounds (-623219 / 62500000) (-9971503 / 1000000000) (Real.log (990078047119 / 1000000000000)) := by
  have h := reflection_log_6699_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6700_neg : (199880827 / 1000000000) ≤ -Real.log (500000000000 / 610628604683) ∧
    -Real.log (500000000000 / 610628604683) ≤ (49970207 / 250000000) := by
  have h := checkLog_sound (w := (110628604683 / 1110628604683)) (n := 12)
    (lo := (199880827 / 1000000000)) (hi := (49970207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610628604683 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610628604683 / 500000000000) = 1/(500000000000 / 610628604683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6700 : Bounds (199880827 / 1000000000) (49970207 / 250000000) (Real.log (610628604683 / 500000000000)) := by
  have h := reflection_log_6700_neg
  have he : Real.log (610628604683 / 500000000000) = -Real.log (500000000000 / 610628604683) := by
    rw [show ((610628604683 / 500000000000) : ℝ) = ((500000000000 / 610628604683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6701_neg : (20038383 / 100000000) ≤ -Real.log (4000000000 / 4887486641) ∧
    -Real.log (4000000000 / 4887486641) ≤ (200383831 / 1000000000) := by
  have h := checkLog_sound (w := (887486641 / 8887486641)) (n := 12)
    (lo := (20038383 / 100000000)) (hi := (200383831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4887486641 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4887486641 / 4000000000) = 1/(4000000000 / 4887486641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6701 : Bounds (20038383 / 100000000) (200383831 / 1000000000) (Real.log (4887486641 / 4000000000)) := by
  have h := reflection_log_6701_neg
  have he : Real.log (4887486641 / 4000000000) = -Real.log (4000000000 / 4887486641) := by
    rw [show ((4887486641 / 4000000000) : ℝ) = ((4000000000 / 4887486641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6702_neg : (40130017 / 100000000) ≤ -Real.log (500000000000 / 746882793017) ∧
    -Real.log (500000000000 / 746882793017) ≤ (401300171 / 1000000000) := by
  have h := checkLog_sound (w := (246882793017 / 1246882793017)) (n := 12)
    (lo := (40130017 / 100000000)) (hi := (401300171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746882793017 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746882793017 / 500000000000) = 1/(500000000000 / 746882793017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6702 : Bounds (40130017 / 100000000) (401300171 / 1000000000) (Real.log (746882793017 / 500000000000)) := by
  have h := reflection_log_6702_neg
  have he : Real.log (746882793017 / 500000000000) = -Real.log (500000000000 / 746882793017) := by
    rw [show ((746882793017 / 500000000000) : ℝ) = ((500000000000 / 746882793017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6703_neg : (80301667 / 200000000) ≤ -Real.log (125000000000 / 186759571019) ∧
    -Real.log (125000000000 / 186759571019) ≤ (25094271 / 62500000) := by
  have h := checkLog_sound (w := (61759571019 / 311759571019)) (n := 12)
    (lo := (80301667 / 200000000)) (hi := (25094271 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186759571019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186759571019 / 125000000000) = 1/(125000000000 / 186759571019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6703 : Bounds (80301667 / 200000000) (25094271 / 62500000) (Real.log (186759571019 / 125000000000)) := by
  have h := reflection_log_6703_neg
  have he : Real.log (186759571019 / 125000000000) = -Real.log (125000000000 / 186759571019) := by
    rw [show ((186759571019 / 125000000000) : ℝ) = ((125000000000 / 186759571019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6704_neg : (18082043 / 100000000) ≤ -Real.log (5000 / 5991) ∧
    -Real.log (5000 / 5991) ≤ (180820431 / 1000000000) := by
  have h := checkLog_sound (w := (991 / 10991)) (n := 12)
    (lo := (18082043 / 100000000)) (hi := (180820431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5991 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5991 / 5000) = 1/(5000 / 5991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6704 : Bounds (18082043 / 100000000) (180820431 / 1000000000) (Real.log (5991 / 5000)) := by
  have h := reflection_log_6704_neg
  have he : Real.log (5991 / 5000) = -Real.log (5000 / 5991) := by
    rw [show ((5991 / 5000) : ℝ) = ((5000 / 5991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6705_neg : (110448039 / 500000000) ≤ -Real.log (4009 / 5000) ∧
    -Real.log (4009 / 5000) ≤ (220896079 / 1000000000) := by
  have h := checkLog_sound (w := (991 / 9009)) (n := 12)
    (lo := (110448039 / 500000000)) (hi := (220896079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4009) = 1/(4009 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6705 : Bounds (-220896079 / 1000000000) (-110448039 / 500000000) (Real.log (4009 / 5000)) := by
  have h := reflection_log_6705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6706_neg : (9909 / 50000000) ≤ -Real.log (5000000 / 5000991) ∧
    -Real.log (5000000 / 5000991) ≤ (198181 / 1000000000) := by
  have h := checkLog_sound (w := (991 / 10000991)) (n := 12)
    (lo := (9909 / 50000000)) (hi := (198181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000991 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000991 / 5000000) = 1/(5000000 / 5000991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6706 : Bounds (9909 / 50000000) (198181 / 1000000000) (Real.log (5000991 / 5000000)) := by
  have h := reflection_log_6706_neg
  have he : Real.log (5000991 / 5000000) = -Real.log (5000000 / 5000991) := by
    rw [show ((5000991 / 5000000) : ℝ) = ((5000000 / 5000991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6707_neg : (198219 / 1000000000) ≤ -Real.log (4999009 / 5000000) ∧
    -Real.log (4999009 / 5000000) ≤ (9911 / 50000000) := by
  have h := checkLog_sound (w := (991 / 9999009)) (n := 12)
    (lo := (198219 / 1000000000)) (hi := (9911 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999009) = 1/(4999009 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6707 : Bounds (-9911 / 50000000) (-198219 / 1000000000) (Real.log (4999009 / 5000000)) := by
  have h := reflection_log_6707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6708_neg : (95001041 / 1000000000) ≤ -Real.log (50000 / 54983) ∧
    -Real.log (50000 / 54983) ≤ (47500521 / 500000000) := by
  have h := checkLog_sound (w := (4983 / 104983)) (n := 12)
    (lo := (95001041 / 1000000000)) (hi := (47500521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54983 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54983 / 50000) = 1/(50000 / 54983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6708 : Bounds (95001041 / 1000000000) (47500521 / 500000000) (Real.log (54983 / 50000)) := by
  have h := reflection_log_6708_neg
  have he : Real.log (54983 / 50000) = -Real.log (50000 / 54983) := by
    rw [show ((54983 / 50000) : ℝ) = ((50000 / 54983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6709_neg : (104982809 / 1000000000) ≤ -Real.log (45017 / 50000) ∧
    -Real.log (45017 / 50000) ≤ (10498281 / 100000000) := by
  have h := checkLog_sound (w := (4983 / 95017)) (n := 12)
    (lo := (104982809 / 1000000000)) (hi := (10498281 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45017) = 1/(45017 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6709 : Bounds (-10498281 / 100000000) (-104982809 / 1000000000) (Real.log (45017 / 50000)) := by
  have h := reflection_log_6709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6710_neg : (95227449 / 1000000000) ≤ -Real.log (1000000 / 1099909) ∧
    -Real.log (1000000 / 1099909) ≤ (1904549 / 20000000) := by
  have h := checkLog_sound (w := (99909 / 2099909)) (n := 12)
    (lo := (95227449 / 1000000000)) (hi := (1904549 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099909 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099909 / 1000000) = 1/(1000000 / 1099909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6710 : Bounds (95227449 / 1000000000) (1904549 / 20000000) (Real.log (1099909 / 1000000)) := by
  have h := reflection_log_6710_neg
  have he : Real.log (1099909 / 1000000) = -Real.log (1000000 / 1099909) := by
    rw [show ((1099909 / 1000000) : ℝ) = ((1000000 / 1099909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6711_neg : (105259409 / 1000000000) ≤ -Real.log (900091 / 1000000) ∧
    -Real.log (900091 / 1000000) ≤ (10525941 / 100000000) := by
  have h := checkLog_sound (w := (99909 / 1900091)) (n := 12)
    (lo := (105259409 / 1000000000)) (hi := (10525941 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900091) = 1/(900091 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6711 : Bounds (-10525941 / 100000000) (-105259409 / 1000000000) (Real.log (900091 / 1000000)) := by
  have h := reflection_log_6711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6712_neg : (250799 / 25000000) ≤ -Real.log (990018191719 / 1000000000000) ∧
    -Real.log (990018191719 / 1000000000000) ≤ (10031961 / 1000000000) := by
  have h := checkLog_sound (w := (9981808281 / 1990018191719)) (n := 12)
    (lo := (250799 / 25000000)) (hi := (10031961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990018191719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990018191719) = 1/(990018191719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6712 : Bounds (-10031961 / 1000000000) (-250799 / 25000000) (Real.log (990018191719 / 1000000000000)) := by
  have h := reflection_log_6712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6713_neg : (1247721 / 125000000) ≤ -Real.log (2475169711 / 2500000000) ∧
    -Real.log (2475169711 / 2500000000) ≤ (9981769 / 1000000000) := by
  have h := checkLog_sound (w := (24830289 / 4975169711)) (n := 12)
    (lo := (1247721 / 125000000)) (hi := (9981769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2475169711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2475169711) = 1/(2475169711 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6713 : Bounds (-9981769 / 1000000000) (-1247721 / 125000000) (Real.log (2475169711 / 2500000000)) := by
  have h := reflection_log_6713_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6714_neg : (3999677 / 20000000) ≤ -Real.log (250000000000 / 305345758269) ∧
    -Real.log (250000000000 / 305345758269) ≤ (199983851 / 1000000000) := by
  have h := checkLog_sound (w := (55345758269 / 555345758269)) (n := 12)
    (lo := (3999677 / 20000000)) (hi := (199983851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305345758269 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305345758269 / 250000000000) = 1/(250000000000 / 305345758269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6714 : Bounds (3999677 / 20000000) (199983851 / 1000000000) (Real.log (305345758269 / 250000000000)) := by
  have h := reflection_log_6714_neg
  have he : Real.log (305345758269 / 250000000000) = -Real.log (250000000000 / 305345758269) := by
    rw [show ((305345758269 / 250000000000) : ℝ) = ((250000000000 / 305345758269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6715_neg : (100243429 / 500000000) ≤ -Real.log (500000000000 / 610998776791) ∧
    -Real.log (500000000000 / 610998776791) ≤ (200486859 / 1000000000) := by
  have h := checkLog_sound (w := (110998776791 / 1110998776791)) (n := 12)
    (lo := (100243429 / 500000000)) (hi := (200486859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610998776791 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610998776791 / 500000000000) = 1/(500000000000 / 610998776791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6715 : Bounds (100243429 / 500000000) (200486859 / 1000000000) (Real.log (610998776791 / 500000000000)) := by
  have h := reflection_log_6715_neg
  have he : Real.log (610998776791 / 500000000000) = -Real.log (500000000000 / 610998776791) := by
    rw [show ((610998776791 / 500000000000) : ℝ) = ((500000000000 / 610998776791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6716_neg : (80301667 / 200000000) ≤ -Real.log (20000000000 / 29881531363) ∧
    -Real.log (20000000000 / 29881531363) ≤ (25094271 / 62500000) := by
  have h := checkLog_sound (w := (9881531363 / 49881531363)) (n := 12)
    (lo := (80301667 / 200000000)) (hi := (25094271 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29881531363 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29881531363 / 20000000000) = 1/(20000000000 / 29881531363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6716 : Bounds (80301667 / 200000000) (25094271 / 62500000) (Real.log (29881531363 / 20000000000)) := by
  have h := reflection_log_6716_neg
  have he : Real.log (29881531363 / 20000000000) = -Real.log (20000000000 / 29881531363) := by
    rw [show ((29881531363 / 20000000000) : ℝ) = ((20000000000 / 29881531363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6717_neg : (401716509 / 1000000000) ≤ -Real.log (500000000000 / 747193813919) ∧
    -Real.log (500000000000 / 747193813919) ≤ (40171651 / 100000000) := by
  have h := checkLog_sound (w := (247193813919 / 1247193813919)) (n := 12)
    (lo := (401716509 / 1000000000)) (hi := (40171651 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747193813919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747193813919 / 500000000000) = 1/(500000000000 / 747193813919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6717 : Bounds (401716509 / 1000000000) (40171651 / 100000000) (Real.log (747193813919 / 500000000000)) := by
  have h := reflection_log_6717_neg
  have he : Real.log (747193813919 / 500000000000) = -Real.log (500000000000 / 747193813919) := by
    rw [show ((747193813919 / 500000000000) : ℝ) = ((500000000000 / 747193813919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6718_neg : (36180777 / 200000000) ≤ -Real.log (10000 / 11983) ∧
    -Real.log (10000 / 11983) ≤ (90451943 / 500000000) := by
  have h := checkLog_sound (w := (1983 / 21983)) (n := 12)
    (lo := (36180777 / 200000000)) (hi := (90451943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11983 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11983 / 10000) = 1/(10000 / 11983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6718 : Bounds (36180777 / 200000000) (90451943 / 500000000) (Real.log (11983 / 10000)) := by
  have h := reflection_log_6718_neg
  have he : Real.log (11983 / 10000) = -Real.log (10000 / 11983) := by
    rw [show ((11983 / 10000) : ℝ) = ((10000 / 11983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6719_neg : (44204161 / 200000000) ≤ -Real.log (8017 / 10000) ∧
    -Real.log (8017 / 10000) ≤ (110510403 / 500000000) := by
  have h := checkLog_sound (w := (1983 / 18017)) (n := 12)
    (lo := (44204161 / 200000000)) (hi := (110510403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8017) = 1/(8017 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6719 : Bounds (-110510403 / 500000000) (-44204161 / 200000000) (Real.log (8017 / 10000)) := by
  have h := reflection_log_6719_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0105 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6720_neg : (4957 / 25000000) ≤ -Real.log (10000000 / 10001983) ∧
    -Real.log (10000000 / 10001983) ≤ (198281 / 1000000000) := by
  have h := checkLog_sound (w := (1983 / 20001983)) (n := 12)
    (lo := (4957 / 25000000)) (hi := (198281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001983 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001983 / 10000000) = 1/(10000000 / 10001983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6720 : Bounds (4957 / 25000000) (198281 / 1000000000) (Real.log (10001983 / 10000000)) := by
  have h := reflection_log_6720_neg
  have he : Real.log (10001983 / 10000000) = -Real.log (10000000 / 10001983) := by
    rw [show ((10001983 / 10000000) : ℝ) = ((10000000 / 10001983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6721_neg : (198319 / 1000000000) ≤ -Real.log (9998017 / 10000000) ∧
    -Real.log (9998017 / 10000000) ≤ (2479 / 12500000) := by
  have h := checkLog_sound (w := (1983 / 19998017)) (n := 12)
    (lo := (198319 / 1000000000)) (hi := (2479 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998017) = 1/(9998017 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6721 : Bounds (-2479 / 12500000) (-198319 / 1000000000) (Real.log (9998017 / 10000000)) := by
  have h := reflection_log_6721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6722_neg : (47523709 / 500000000) ≤ -Real.log (1000000 / 1099711) ∧
    -Real.log (1000000 / 1099711) ≤ (95047419 / 1000000000) := by
  have h := checkLog_sound (w := (99711 / 2099711)) (n := 12)
    (lo := (47523709 / 500000000)) (hi := (95047419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099711 / 1000000) = 1/(1000000 / 1099711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6722 : Bounds (47523709 / 500000000) (95047419 / 1000000000) (Real.log (1099711 / 1000000)) := by
  have h := reflection_log_6722_neg
  have he : Real.log (1099711 / 1000000) = -Real.log (1000000 / 1099711) := by
    rw [show ((1099711 / 1000000) : ℝ) = ((1000000 / 1099711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6723_neg : (3282483 / 31250000) ≤ -Real.log (900289 / 1000000) ∧
    -Real.log (900289 / 1000000) ≤ (105039457 / 1000000000) := by
  have h := checkLog_sound (w := (99711 / 1900289)) (n := 12)
    (lo := (3282483 / 31250000)) (hi := (105039457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900289) = 1/(900289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6723 : Bounds (-105039457 / 1000000000) (-3282483 / 31250000) (Real.log (900289 / 1000000)) := by
  have h := reflection_log_6723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6724_neg : (19054763 / 200000000) ≤ -Real.log (25000 / 27499) ∧
    -Real.log (25000 / 27499) ≤ (11909227 / 125000000) := by
  have h := checkLog_sound (w := (2499 / 52499)) (n := 12)
    (lo := (19054763 / 200000000)) (hi := (11909227 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27499 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27499 / 25000) = 1/(25000 / 27499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6724 : Bounds (19054763 / 200000000) (11909227 / 125000000) (Real.log (27499 / 25000)) := by
  have h := reflection_log_6724_neg
  have he : Real.log (27499 / 25000) = -Real.log (25000 / 27499) := by
    rw [show ((27499 / 25000) : ℝ) = ((25000 / 27499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6725_neg : (13164509 / 125000000) ≤ -Real.log (22501 / 25000) ∧
    -Real.log (22501 / 25000) ≤ (105316073 / 1000000000) := by
  have h := checkLog_sound (w := (2499 / 47501)) (n := 12)
    (lo := (13164509 / 125000000)) (hi := (105316073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22501) = 1/(22501 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6725 : Bounds (-105316073 / 1000000000) (-13164509 / 125000000) (Real.log (22501 / 25000)) := by
  have h := reflection_log_6725_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6726_neg : (627641 / 62500000) ≤ -Real.log (618754999 / 625000000) ∧
    -Real.log (618754999 / 625000000) ≤ (10042257 / 1000000000) := by
  have h := checkLog_sound (w := (6245001 / 1243754999)) (n := 12)
    (lo := (627641 / 62500000)) (hi := (10042257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 618754999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 618754999) = 1/(618754999 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6726 : Bounds (-10042257 / 1000000000) (-627641 / 62500000) (Real.log (618754999 / 625000000)) := by
  have h := reflection_log_6726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6727_neg : (4996019 / 500000000) ≤ -Real.log (990057716479 / 1000000000000) ∧
    -Real.log (990057716479 / 1000000000000) ≤ (9992039 / 1000000000) := by
  have h := checkLog_sound (w := (9942283521 / 1990057716479)) (n := 12)
    (lo := (4996019 / 500000000)) (hi := (9992039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990057716479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990057716479) = 1/(990057716479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6727 : Bounds (-9992039 / 1000000000) (-4996019 / 500000000) (Real.log (990057716479 / 1000000000000)) := by
  have h := reflection_log_6727_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6728_neg : (100043437 / 500000000) ≤ -Real.log (1562500000 / 1908607611) ∧
    -Real.log (1562500000 / 1908607611) ≤ (320139 / 1600000) := by
  have h := checkLog_sound (w := (346107611 / 3471107611)) (n := 12)
    (lo := (100043437 / 500000000)) (hi := (320139 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1908607611 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1908607611 / 1562500000) = 1/(1562500000 / 1908607611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6728 : Bounds (100043437 / 500000000) (320139 / 1600000) (Real.log (1908607611 / 1562500000)) := by
  have h := reflection_log_6728_neg
  have he : Real.log (1908607611 / 1562500000) = -Real.log (1562500000 / 1908607611) := by
    rw [show ((1908607611 / 1562500000) : ℝ) = ((1562500000 / 1908607611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6729_neg : (200589887 / 1000000000) ≤ -Real.log (50000000000 / 61106173059) ∧
    -Real.log (50000000000 / 61106173059) ≤ (3134217 / 15625000) := by
  have h := checkLog_sound (w := (11106173059 / 111106173059)) (n := 12)
    (lo := (200589887 / 1000000000)) (hi := (3134217 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61106173059 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61106173059 / 50000000000) = 1/(50000000000 / 61106173059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6729 : Bounds (200589887 / 1000000000) (3134217 / 15625000) (Real.log (61106173059 / 50000000000)) := by
  have h := reflection_log_6729_neg
  have he : Real.log (61106173059 / 50000000000) = -Real.log (50000000000 / 61106173059) := by
    rw [show ((61106173059 / 50000000000) : ℝ) = ((50000000000 / 61106173059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6730_neg : (401716509 / 1000000000) ≤ -Real.log (250000000000 / 373596906959) ∧
    -Real.log (250000000000 / 373596906959) ≤ (40171651 / 100000000) := by
  have h := checkLog_sound (w := (123596906959 / 623596906959)) (n := 12)
    (lo := (401716509 / 1000000000)) (hi := (40171651 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373596906959 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373596906959 / 250000000000) = 1/(250000000000 / 373596906959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6730 : Bounds (401716509 / 1000000000) (40171651 / 100000000) (Real.log (373596906959 / 250000000000)) := by
  have h := reflection_log_6730_neg
  have he : Real.log (373596906959 / 250000000000) = -Real.log (250000000000 / 373596906959) := by
    rw [show ((373596906959 / 250000000000) : ℝ) = ((250000000000 / 373596906959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6731_neg : (401924691 / 1000000000) ≤ -Real.log (500000000000 / 747349382563) ∧
    -Real.log (500000000000 / 747349382563) ≤ (100481173 / 250000000) := by
  have h := checkLog_sound (w := (247349382563 / 1247349382563)) (n := 12)
    (lo := (401924691 / 1000000000)) (hi := (100481173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747349382563 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747349382563 / 500000000000) = 1/(500000000000 / 747349382563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6731 : Bounds (401924691 / 1000000000) (100481173 / 250000000) (Real.log (747349382563 / 500000000000)) := by
  have h := reflection_log_6731_neg
  have he : Real.log (747349382563 / 500000000000) = -Real.log (500000000000 / 747349382563) := by
    rw [show ((747349382563 / 500000000000) : ℝ) = ((500000000000 / 747349382563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6732_neg : (180987333 / 1000000000) ≤ -Real.log (625 / 749) ∧
    -Real.log (625 / 749) ≤ (90493667 / 500000000) := by
  have h := checkLog_sound (w := (62 / 687)) (n := 12)
    (lo := (180987333 / 1000000000)) (hi := (90493667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749 / 625) = 1/(625 / 749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6732 : Bounds (180987333 / 1000000000) (90493667 / 500000000) (Real.log (749 / 625)) := by
  have h := reflection_log_6732_neg
  have he : Real.log (749 / 625) = -Real.log (625 / 749) := by
    rw [show ((749 / 625) : ℝ) = ((625 / 749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6733_neg : (55286387 / 250000000) ≤ -Real.log (501 / 625) ∧
    -Real.log (501 / 625) ≤ (221145549 / 1000000000) := by
  have h := checkLog_sound (w := (62 / 563)) (n := 12)
    (lo := (55286387 / 250000000)) (hi := (221145549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 501) = 1/(501 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6733 : Bounds (-221145549 / 1000000000) (-55286387 / 250000000) (Real.log (501 / 625)) := by
  have h := reflection_log_6733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6734_neg : (9919 / 50000000) ≤ -Real.log (156250 / 156281) ∧
    -Real.log (156250 / 156281) ≤ (198381 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 312531)) (n := 12)
    (lo := (9919 / 50000000)) (hi := (198381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156281 / 156250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156281 / 156250) = 1/(156250 / 156281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6734 : Bounds (9919 / 50000000) (198381 / 1000000000) (Real.log (156281 / 156250)) := by
  have h := reflection_log_6734_neg
  have he : Real.log (156281 / 156250) = -Real.log (156250 / 156281) := by
    rw [show ((156281 / 156250) : ℝ) = ((156250 / 156281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6735_neg : (198419 / 1000000000) ≤ -Real.log (156219 / 156250) ∧
    -Real.log (156219 / 156250) ≤ (9921 / 50000000) := by
  have h := checkLog_sound (w := (31 / 312469)) (n := 12)
    (lo := (198419 / 1000000000)) (hi := (9921 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250 / 156219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250 / 156219) = 1/(156219 / 156250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6735 : Bounds (-9921 / 50000000) (-198419 / 1000000000) (Real.log (156219 / 156250)) := by
  have h := reflection_log_6735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6736_neg : (2971681 / 31250000) ≤ -Real.log (500000 / 549881) ∧
    -Real.log (500000 / 549881) ≤ (95093793 / 1000000000) := by
  have h := checkLog_sound (w := (49881 / 1049881)) (n := 12)
    (lo := (2971681 / 31250000)) (hi := (95093793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549881 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549881 / 500000) = 1/(500000 / 549881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6736 : Bounds (2971681 / 31250000) (95093793 / 1000000000) (Real.log (549881 / 500000)) := by
  have h := reflection_log_6736_neg
  have he : Real.log (549881 / 500000) = -Real.log (500000 / 549881) := by
    rw [show ((549881 / 500000) : ℝ) = ((500000 / 549881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6737_neg : (52548053 / 500000000) ≤ -Real.log (450119 / 500000) ∧
    -Real.log (450119 / 500000) ≤ (105096107 / 1000000000) := by
  have h := checkLog_sound (w := (49881 / 950119)) (n := 12)
    (lo := (52548053 / 500000000)) (hi := (105096107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450119) = 1/(450119 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6737 : Bounds (-105096107 / 1000000000) (-52548053 / 500000000) (Real.log (450119 / 500000)) := by
  have h := reflection_log_6737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6738_neg : (95320179 / 1000000000) ≤ -Real.log (1000000 / 1100011) ∧
    -Real.log (1000000 / 1100011) ≤ (4766009 / 50000000) := by
  have h := checkLog_sound (w := (100011 / 2100011)) (n := 12)
    (lo := (95320179 / 1000000000)) (hi := (4766009 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100011 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100011 / 1000000) = 1/(1000000 / 1100011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6738 : Bounds (95320179 / 1000000000) (4766009 / 50000000) (Real.log (1100011 / 1000000)) := by
  have h := reflection_log_6738_neg
  have he : Real.log (1100011 / 1000000) = -Real.log (1000000 / 1100011) := by
    rw [show ((1100011 / 1000000) : ℝ) = ((1000000 / 1100011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6739_neg : (105372737 / 1000000000) ≤ -Real.log (899989 / 1000000) ∧
    -Real.log (899989 / 1000000) ≤ (52686369 / 500000000) := by
  have h := checkLog_sound (w := (100011 / 1899989)) (n := 12)
    (lo := (105372737 / 1000000000)) (hi := (52686369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899989) = 1/(899989 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6739 : Bounds (-52686369 / 500000000) (-105372737 / 1000000000) (Real.log (899989 / 1000000)) := by
  have h := reflection_log_6739_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6740_neg : (5026279 / 500000000) ≤ -Real.log (989997799879 / 1000000000000) ∧
    -Real.log (989997799879 / 1000000000000) ≤ (10052559 / 1000000000) := by
  have h := checkLog_sound (w := (10002200121 / 1989997799879)) (n := 12)
    (lo := (5026279 / 500000000)) (hi := (10052559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989997799879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989997799879) = 1/(989997799879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6740 : Bounds (-10052559 / 1000000000) (-5026279 / 500000000) (Real.log (989997799879 / 1000000000000)) := by
  have h := reflection_log_6740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6741_neg : (10002313 / 1000000000) ≤ -Real.log (247511885839 / 250000000000) ∧
    -Real.log (247511885839 / 250000000000) ≤ (5001157 / 500000000) := by
  have h := checkLog_sound (w := (2488114161 / 497511885839)) (n := 12)
    (lo := (10002313 / 1000000000)) (hi := (5001157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247511885839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247511885839) = 1/(247511885839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6741 : Bounds (-5001157 / 500000000) (-10002313 / 1000000000) (Real.log (247511885839 / 250000000000)) := by
  have h := reflection_log_6741_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6742_neg : (100094949 / 500000000) ≤ -Real.log (500000000000 / 610817361631) ∧
    -Real.log (500000000000 / 610817361631) ≤ (200189899 / 1000000000) := by
  have h := checkLog_sound (w := (110817361631 / 1110817361631)) (n := 12)
    (lo := (100094949 / 500000000)) (hi := (200189899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610817361631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610817361631 / 500000000000) = 1/(500000000000 / 610817361631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6742 : Bounds (100094949 / 500000000) (200189899 / 1000000000) (Real.log (610817361631 / 500000000000)) := by
  have h := reflection_log_6742_neg
  have he : Real.log (610817361631 / 500000000000) = -Real.log (500000000000 / 610817361631) := by
    rw [show ((610817361631 / 500000000000) : ℝ) = ((500000000000 / 610817361631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6743_neg : (200692917 / 1000000000) ≤ -Real.log (20000000000 / 24444987661) ∧
    -Real.log (20000000000 / 24444987661) ≤ (100346459 / 500000000) := by
  have h := checkLog_sound (w := (4444987661 / 44444987661)) (n := 12)
    (lo := (200692917 / 1000000000)) (hi := (100346459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24444987661 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24444987661 / 20000000000) = 1/(20000000000 / 24444987661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6743 : Bounds (200692917 / 1000000000) (100346459 / 500000000) (Real.log (24444987661 / 20000000000)) := by
  have h := reflection_log_6743_neg
  have he : Real.log (24444987661 / 20000000000) = -Real.log (20000000000 / 24444987661) := by
    rw [show ((24444987661 / 20000000000) : ℝ) = ((20000000000 / 24444987661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6744_neg : (401924691 / 1000000000) ≤ -Real.log (250000000000 / 373674691281) ∧
    -Real.log (250000000000 / 373674691281) ≤ (100481173 / 250000000) := by
  have h := checkLog_sound (w := (123674691281 / 623674691281)) (n := 12)
    (lo := (401924691 / 1000000000)) (hi := (100481173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373674691281 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373674691281 / 250000000000) = 1/(250000000000 / 373674691281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6744 : Bounds (401924691 / 1000000000) (100481173 / 250000000) (Real.log (373674691281 / 250000000000)) := by
  have h := reflection_log_6744_neg
  have he : Real.log (373674691281 / 250000000000) = -Real.log (250000000000 / 373674691281) := by
    rw [show ((373674691281 / 250000000000) : ℝ) = ((250000000000 / 373674691281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6745_neg : (201066441 / 500000000) ≤ -Real.log (25000000000 / 37375249501) ∧
    -Real.log (25000000000 / 37375249501) ≤ (402132883 / 1000000000) := by
  have h := checkLog_sound (w := (12375249501 / 62375249501)) (n := 12)
    (lo := (201066441 / 500000000)) (hi := (402132883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37375249501 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37375249501 / 25000000000) = 1/(25000000000 / 37375249501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6745 : Bounds (201066441 / 500000000) (402132883 / 1000000000) (Real.log (37375249501 / 25000000000)) := by
  have h := reflection_log_6745_neg
  have he : Real.log (37375249501 / 25000000000) = -Real.log (25000000000 / 37375249501) := by
    rw [show ((37375249501 / 25000000000) : ℝ) = ((25000000000 / 37375249501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6746_neg : (90535387 / 500000000) ≤ -Real.log (2000 / 2397) ∧
    -Real.log (2000 / 2397) ≤ (7242831 / 40000000) := by
  have h := checkLog_sound (w := (397 / 4397)) (n := 12)
    (lo := (90535387 / 500000000)) (hi := (7242831 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2397 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2397 / 2000) = 1/(2000 / 2397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6746 : Bounds (90535387 / 500000000) (7242831 / 40000000) (Real.log (2397 / 2000)) := by
  have h := reflection_log_6746_neg
  have he : Real.log (2397 / 2000) = -Real.log (2000 / 2397) := by
    rw [show ((2397 / 2000) : ℝ) = ((2000 / 2397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6747_neg : (110635153 / 500000000) ≤ -Real.log (1603 / 2000) ∧
    -Real.log (1603 / 2000) ≤ (221270307 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 3603)) (n := 12)
    (lo := (110635153 / 500000000)) (hi := (221270307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1603) = 1/(1603 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6747 : Bounds (-221270307 / 1000000000) (-110635153 / 500000000) (Real.log (1603 / 2000)) := by
  have h := reflection_log_6747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6748_neg : (2481 / 12500000) ≤ -Real.log (2000000 / 2000397) ∧
    -Real.log (2000000 / 2000397) ≤ (198481 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 4000397)) (n := 12)
    (lo := (2481 / 12500000)) (hi := (198481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000397 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000397 / 2000000) = 1/(2000000 / 2000397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6748 : Bounds (2481 / 12500000) (198481 / 1000000000) (Real.log (2000397 / 2000000)) := by
  have h := reflection_log_6748_neg
  have he : Real.log (2000397 / 2000000) = -Real.log (2000000 / 2000397) := by
    rw [show ((2000397 / 2000000) : ℝ) = ((2000000 / 2000397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6749_neg : (198519 / 1000000000) ≤ -Real.log (1999603 / 2000000) ∧
    -Real.log (1999603 / 2000000) ≤ (4963 / 25000000) := by
  have h := checkLog_sound (w := (397 / 3999603)) (n := 12)
    (lo := (198519 / 1000000000)) (hi := (4963 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999603) = 1/(1999603 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6749 : Bounds (-4963 / 25000000) (-198519 / 1000000000) (Real.log (1999603 / 2000000)) := by
  have h := reflection_log_6749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6750_neg : (19028033 / 200000000) ≤ -Real.log (1000000 / 1099813) ∧
    -Real.log (1000000 / 1099813) ≤ (47570083 / 500000000) := by
  have h := checkLog_sound (w := (99813 / 2099813)) (n := 12)
    (lo := (19028033 / 200000000)) (hi := (47570083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099813 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099813 / 1000000) = 1/(1000000 / 1099813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6750 : Bounds (19028033 / 200000000) (47570083 / 500000000) (Real.log (1099813 / 1000000)) := by
  have h := reflection_log_6750_neg
  have he : Real.log (1099813 / 1000000) = -Real.log (1000000 / 1099813) := by
    rw [show ((1099813 / 1000000) : ℝ) = ((1000000 / 1099813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6751_neg : (105152759 / 1000000000) ≤ -Real.log (900187 / 1000000) ∧
    -Real.log (900187 / 1000000) ≤ (2628819 / 25000000) := by
  have h := checkLog_sound (w := (99813 / 1900187)) (n := 12)
    (lo := (105152759 / 1000000000)) (hi := (2628819 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900187) = 1/(900187 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6751 : Bounds (-2628819 / 25000000) (-105152759 / 1000000000) (Real.log (900187 / 1000000)) := by
  have h := reflection_log_6751_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6752_neg : (1907349 / 20000000) ≤ -Real.log (1000000 / 1100063) ∧
    -Real.log (1000000 / 1100063) ≤ (95367451 / 1000000000) := by
  have h := checkLog_sound (w := (100063 / 2100063)) (n := 12)
    (lo := (1907349 / 20000000)) (hi := (95367451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100063 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100063 / 1000000) = 1/(1000000 / 1100063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6752 : Bounds (1907349 / 20000000) (95367451 / 1000000000) (Real.log (1100063 / 1000000)) := by
  have h := reflection_log_6752_neg
  have he : Real.log (1100063 / 1000000) = -Real.log (1000000 / 1100063) := by
    rw [show ((1100063 / 1000000) : ℝ) = ((1000000 / 1100063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6753_neg : (52715259 / 500000000) ≤ -Real.log (899937 / 1000000) ∧
    -Real.log (899937 / 1000000) ≤ (105430519 / 1000000000) := by
  have h := checkLog_sound (w := (100063 / 1899937)) (n := 12)
    (lo := (52715259 / 500000000)) (hi := (105430519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899937) = 1/(899937 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6753 : Bounds (-105430519 / 1000000000) (-52715259 / 500000000) (Real.log (899937 / 1000000)) := by
  have h := reflection_log_6753_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6754_neg : (10063067 / 1000000000) ≤ -Real.log (989987396031 / 1000000000000) ∧
    -Real.log (989987396031 / 1000000000000) ≤ (2515767 / 250000000) := by
  have h := checkLog_sound (w := (10012603969 / 1989987396031)) (n := 12)
    (lo := (10063067 / 1000000000)) (hi := (2515767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989987396031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989987396031) = 1/(989987396031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6754 : Bounds (-2515767 / 250000000) (-10063067 / 1000000000) (Real.log (989987396031 / 1000000000000)) := by
  have h := reflection_log_6754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6755_neg : (5006297 / 500000000) ≤ -Real.log (990037365031 / 1000000000000) ∧
    -Real.log (990037365031 / 1000000000000) ≤ (2002519 / 200000000) := by
  have h := checkLog_sound (w := (9962634969 / 1990037365031)) (n := 12)
    (lo := (5006297 / 500000000)) (hi := (2002519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990037365031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990037365031) = 1/(990037365031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6755 : Bounds (-2002519 / 200000000) (-5006297 / 500000000) (Real.log (990037365031 / 1000000000000)) := by
  have h := reflection_log_6755_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6756_neg : (50073231 / 250000000) ≤ -Real.log (62500000000 / 76360036859) ∧
    -Real.log (62500000000 / 76360036859) ≤ (8011717 / 40000000) := by
  have h := checkLog_sound (w := (13860036859 / 138860036859)) (n := 12)
    (lo := (50073231 / 250000000)) (hi := (8011717 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76360036859 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76360036859 / 62500000000) = 1/(62500000000 / 76360036859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6756 : Bounds (50073231 / 250000000) (8011717 / 40000000) (Real.log (76360036859 / 62500000000)) := by
  have h := reflection_log_6756_neg
  have he : Real.log (76360036859 / 62500000000) = -Real.log (62500000000 / 76360036859) := by
    rw [show ((76360036859 / 62500000000) : ℝ) = ((62500000000 / 76360036859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6757_neg : (12549873 / 62500000) ≤ -Real.log (250000000000 / 305594447167) ∧
    -Real.log (250000000000 / 305594447167) ≤ (200797969 / 1000000000) := by
  have h := checkLog_sound (w := (55594447167 / 555594447167)) (n := 12)
    (lo := (12549873 / 62500000)) (hi := (200797969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305594447167 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305594447167 / 250000000000) = 1/(250000000000 / 305594447167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6757 : Bounds (12549873 / 62500000) (200797969 / 1000000000) (Real.log (305594447167 / 250000000000)) := by
  have h := reflection_log_6757_neg
  have he : Real.log (305594447167 / 250000000000) = -Real.log (250000000000 / 305594447167) := by
    rw [show ((305594447167 / 250000000000) : ℝ) = ((250000000000 / 305594447167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6758_neg : (201066441 / 500000000) ≤ -Real.log (500000000000 / 747504990019) ∧
    -Real.log (500000000000 / 747504990019) ≤ (402132883 / 1000000000) := by
  have h := checkLog_sound (w := (247504990019 / 1247504990019)) (n := 12)
    (lo := (201066441 / 500000000)) (hi := (402132883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747504990019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747504990019 / 500000000000) = 1/(500000000000 / 747504990019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6758 : Bounds (201066441 / 500000000) (402132883 / 1000000000) (Real.log (747504990019 / 500000000000)) := by
  have h := reflection_log_6758_neg
  have he : Real.log (747504990019 / 500000000000) = -Real.log (500000000000 / 747504990019) := by
    rw [show ((747504990019 / 500000000000) : ℝ) = ((500000000000 / 747504990019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6759_neg : (402341081 / 1000000000) ≤ -Real.log (500000000000 / 747660636307) ∧
    -Real.log (500000000000 / 747660636307) ≤ (201170541 / 500000000) := by
  have h := checkLog_sound (w := (247660636307 / 1247660636307)) (n := 12)
    (lo := (402341081 / 1000000000)) (hi := (201170541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747660636307 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747660636307 / 500000000000) = 1/(500000000000 / 747660636307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6759 : Bounds (402341081 / 1000000000) (201170541 / 500000000) (Real.log (747660636307 / 500000000000)) := by
  have h := reflection_log_6759_neg
  have he : Real.log (747660636307 / 500000000000) = -Real.log (500000000000 / 747660636307) := by
    rw [show ((747660636307 / 500000000000) : ℝ) = ((500000000000 / 747660636307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6760_neg : (181154209 / 1000000000) ≤ -Real.log (5000 / 5993) ∧
    -Real.log (5000 / 5993) ≤ (18115421 / 100000000) := by
  have h := checkLog_sound (w := (993 / 10993)) (n := 12)
    (lo := (181154209 / 1000000000)) (hi := (18115421 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5993 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5993 / 5000) = 1/(5000 / 5993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6760 : Bounds (181154209 / 1000000000) (18115421 / 100000000) (Real.log (5993 / 5000)) := by
  have h := reflection_log_6760_neg
  have he : Real.log (5993 / 5000) = -Real.log (5000 / 5993) := by
    rw [show ((5993 / 5000) : ℝ) = ((5000 / 5993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6761_neg : (5534877 / 25000000) ≤ -Real.log (4007 / 5000) ∧
    -Real.log (4007 / 5000) ≤ (221395081 / 1000000000) := by
  have h := checkLog_sound (w := (993 / 9007)) (n := 12)
    (lo := (5534877 / 25000000)) (hi := (221395081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4007) = 1/(4007 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6761 : Bounds (-221395081 / 1000000000) (-5534877 / 25000000) (Real.log (4007 / 5000)) := by
  have h := reflection_log_6761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6762_neg : (9929 / 50000000) ≤ -Real.log (5000000 / 5000993) ∧
    -Real.log (5000000 / 5000993) ≤ (198581 / 1000000000) := by
  have h := checkLog_sound (w := (993 / 10000993)) (n := 12)
    (lo := (9929 / 50000000)) (hi := (198581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000993 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000993 / 5000000) = 1/(5000000 / 5000993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6762 : Bounds (9929 / 50000000) (198581 / 1000000000) (Real.log (5000993 / 5000000)) := by
  have h := reflection_log_6762_neg
  have he : Real.log (5000993 / 5000000) = -Real.log (5000000 / 5000993) := by
    rw [show ((5000993 / 5000000) : ℝ) = ((5000000 / 5000993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6763_neg : (198619 / 1000000000) ≤ -Real.log (4999007 / 5000000) ∧
    -Real.log (4999007 / 5000000) ≤ (9931 / 50000000) := by
  have h := checkLog_sound (w := (993 / 9999007)) (n := 12)
    (lo := (198619 / 1000000000)) (hi := (9931 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999007) = 1/(4999007 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6763 : Bounds (-9931 / 50000000) (-198619 / 1000000000) (Real.log (4999007 / 5000000)) := by
  have h := reflection_log_6763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6764_neg : (19037307 / 200000000) ≤ -Real.log (125000 / 137483) ∧
    -Real.log (125000 / 137483) ≤ (11898317 / 125000000) := by
  have h := checkLog_sound (w := (12483 / 262483)) (n := 12)
    (lo := (19037307 / 200000000)) (hi := (11898317 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137483 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137483 / 125000) = 1/(125000 / 137483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6764 : Bounds (19037307 / 200000000) (11898317 / 125000000) (Real.log (137483 / 125000)) := by
  have h := reflection_log_6764_neg
  have he : Real.log (137483 / 125000) = -Real.log (125000 / 137483) := by
    rw [show ((137483 / 125000) : ℝ) = ((125000 / 137483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6765_neg : (21041883 / 200000000) ≤ -Real.log (112517 / 125000) ∧
    -Real.log (112517 / 125000) ≤ (13151177 / 125000000) := by
  have h := checkLog_sound (w := (12483 / 237517)) (n := 12)
    (lo := (21041883 / 200000000)) (hi := (13151177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112517) = 1/(112517 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6765 : Bounds (-13151177 / 125000000) (-21041883 / 200000000) (Real.log (112517 / 125000)) := by
  have h := reflection_log_6765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6766_neg : (9541381 / 100000000) ≤ -Real.log (500000 / 550057) ∧
    -Real.log (500000 / 550057) ≤ (95413811 / 1000000000) := by
  have h := checkLog_sound (w := (50057 / 1050057)) (n := 12)
    (lo := (9541381 / 100000000)) (hi := (95413811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550057 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550057 / 500000) = 1/(500000 / 550057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6766 : Bounds (9541381 / 100000000) (95413811 / 1000000000) (Real.log (550057 / 500000)) := by
  have h := reflection_log_6766_neg
  have he : Real.log (550057 / 500000) = -Real.log (500000 / 550057) := by
    rw [show ((550057 / 500000) : ℝ) = ((500000 / 550057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6767_neg : (10548719 / 100000000) ≤ -Real.log (449943 / 500000) ∧
    -Real.log (449943 / 500000) ≤ (105487191 / 1000000000) := by
  have h := checkLog_sound (w := (50057 / 949943)) (n := 12)
    (lo := (10548719 / 100000000)) (hi := (105487191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449943) = 1/(449943 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6767 : Bounds (-105487191 / 1000000000) (-10548719 / 100000000) (Real.log (449943 / 500000)) := by
  have h := reflection_log_6767_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6768_neg : (10073379 / 1000000000) ≤ -Real.log (247494296751 / 250000000000) ∧
    -Real.log (247494296751 / 250000000000) ≤ (503669 / 50000000) := by
  have h := checkLog_sound (w := (2505703249 / 497494296751)) (n := 12)
    (lo := (10073379 / 1000000000)) (hi := (503669 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247494296751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247494296751) = 1/(247494296751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6768 : Bounds (-503669 / 50000000) (-10073379 / 1000000000) (Real.log (247494296751 / 250000000000)) := by
  have h := reflection_log_6768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6769_neg : (62643 / 6250000) ≤ -Real.log (15469174711 / 15625000000) ∧
    -Real.log (15469174711 / 15625000000) ≤ (10022881 / 1000000000) := by
  have h := checkLog_sound (w := (155825289 / 31094174711)) (n := 12)
    (lo := (62643 / 6250000)) (hi := (10022881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15469174711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15469174711) = 1/(15469174711 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6769 : Bounds (-10022881 / 1000000000) (-62643 / 6250000) (Real.log (15469174711 / 15625000000)) := by
  have h := reflection_log_6769_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6770_neg : (200395951 / 1000000000) ≤ -Real.log (125000000000 / 152735808811) ∧
    -Real.log (125000000000 / 152735808811) ≤ (12524747 / 62500000) := by
  have h := checkLog_sound (w := (27735808811 / 277735808811)) (n := 12)
    (lo := (200395951 / 1000000000)) (hi := (12524747 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152735808811 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152735808811 / 125000000000) = 1/(125000000000 / 152735808811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6770 : Bounds (200395951 / 1000000000) (12524747 / 62500000) (Real.log (152735808811 / 125000000000)) := by
  have h := reflection_log_6770_neg
  have he : Real.log (152735808811 / 125000000000) = -Real.log (125000000000 / 152735808811) := by
    rw [show ((152735808811 / 125000000000) : ℝ) = ((125000000000 / 152735808811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6771_neg : (200901001 / 1000000000) ≤ -Real.log (250000000000 / 305625934841) ∧
    -Real.log (250000000000 / 305625934841) ≤ (100450501 / 500000000) := by
  have h := checkLog_sound (w := (55625934841 / 555625934841)) (n := 12)
    (lo := (200901001 / 1000000000)) (hi := (100450501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305625934841 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305625934841 / 250000000000) = 1/(250000000000 / 305625934841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6771 : Bounds (200901001 / 1000000000) (100450501 / 500000000) (Real.log (305625934841 / 250000000000)) := by
  have h := reflection_log_6771_neg
  have he : Real.log (305625934841 / 250000000000) = -Real.log (250000000000 / 305625934841) := by
    rw [show ((305625934841 / 250000000000) : ℝ) = ((250000000000 / 305625934841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6772_neg : (402341081 / 1000000000) ≤ -Real.log (250000000000 / 373830318153) ∧
    -Real.log (250000000000 / 373830318153) ≤ (201170541 / 500000000) := by
  have h := checkLog_sound (w := (123830318153 / 623830318153)) (n := 12)
    (lo := (402341081 / 1000000000)) (hi := (201170541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373830318153 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373830318153 / 250000000000) = 1/(250000000000 / 373830318153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6772 : Bounds (402341081 / 1000000000) (201170541 / 500000000) (Real.log (373830318153 / 250000000000)) := by
  have h := reflection_log_6772_neg
  have he : Real.log (373830318153 / 250000000000) = -Real.log (250000000000 / 373830318153) := by
    rw [show ((373830318153 / 250000000000) : ℝ) = ((250000000000 / 373830318153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6773_neg : (402549289 / 1000000000) ≤ -Real.log (250000000000 / 373908160719) ∧
    -Real.log (250000000000 / 373908160719) ≤ (40254929 / 100000000) := by
  have h := checkLog_sound (w := (123908160719 / 623908160719)) (n := 12)
    (lo := (402549289 / 1000000000)) (hi := (40254929 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373908160719 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373908160719 / 250000000000) = 1/(250000000000 / 373908160719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6773 : Bounds (402549289 / 1000000000) (40254929 / 100000000) (Real.log (373908160719 / 250000000000)) := by
  have h := reflection_log_6773_neg
  have he : Real.log (373908160719 / 250000000000) = -Real.log (250000000000 / 373908160719) := by
    rw [show ((373908160719 / 250000000000) : ℝ) = ((250000000000 / 373908160719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6774_neg : (45309409 / 250000000) ≤ -Real.log (10000 / 11987) ∧
    -Real.log (10000 / 11987) ≤ (181237637 / 1000000000) := by
  have h := checkLog_sound (w := (1987 / 21987)) (n := 12)
    (lo := (45309409 / 250000000)) (hi := (181237637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11987 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11987 / 10000) = 1/(10000 / 11987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6774 : Bounds (45309409 / 250000000) (181237637 / 1000000000) (Real.log (11987 / 10000)) := by
  have h := reflection_log_6774_neg
  have he : Real.log (11987 / 10000) = -Real.log (10000 / 11987) := by
    rw [show ((11987 / 10000) : ℝ) = ((10000 / 11987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6775_neg : (22151987 / 100000000) ≤ -Real.log (8013 / 10000) ∧
    -Real.log (8013 / 10000) ≤ (221519871 / 1000000000) := by
  have h := checkLog_sound (w := (1987 / 18013)) (n := 12)
    (lo := (22151987 / 100000000)) (hi := (221519871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8013) = 1/(8013 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6775 : Bounds (-221519871 / 1000000000) (-22151987 / 100000000) (Real.log (8013 / 10000)) := by
  have h := reflection_log_6775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6776_neg : (4967 / 25000000) ≤ -Real.log (10000000 / 10001987) ∧
    -Real.log (10000000 / 10001987) ≤ (198681 / 1000000000) := by
  have h := checkLog_sound (w := (1987 / 20001987)) (n := 12)
    (lo := (4967 / 25000000)) (hi := (198681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001987 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001987 / 10000000) = 1/(10000000 / 10001987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6776 : Bounds (4967 / 25000000) (198681 / 1000000000) (Real.log (10001987 / 10000000)) := by
  have h := reflection_log_6776_neg
  have he : Real.log (10001987 / 10000000) = -Real.log (10000000 / 10001987) := by
    rw [show ((10001987 / 10000000) : ℝ) = ((10000000 / 10001987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6777_neg : (198719 / 1000000000) ≤ -Real.log (9998013 / 10000000) ∧
    -Real.log (9998013 / 10000000) ≤ (621 / 3125000) := by
  have h := checkLog_sound (w := (1987 / 19998013)) (n := 12)
    (lo := (198719 / 1000000000)) (hi := (621 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998013) = 1/(9998013 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6777 : Bounds (-621 / 3125000) (-198719 / 1000000000) (Real.log (9998013 / 10000000)) := by
  have h := reflection_log_6777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6778_neg : (11904113 / 125000000) ≤ -Real.log (200000 / 219983) ∧
    -Real.log (200000 / 219983) ≤ (19046581 / 200000000) := by
  have h := checkLog_sound (w := (19983 / 419983)) (n := 12)
    (lo := (11904113 / 125000000)) (hi := (19046581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219983 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219983 / 200000) = 1/(200000 / 219983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6778 : Bounds (11904113 / 125000000) (19046581 / 200000000) (Real.log (219983 / 200000)) := by
  have h := reflection_log_6778_neg
  have he : Real.log (219983 / 200000) = -Real.log (200000 / 219983) := by
    rw [show ((219983 / 200000) : ℝ) = ((200000 / 219983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6779_neg : (4210643 / 40000000) ≤ -Real.log (180017 / 200000) ∧
    -Real.log (180017 / 200000) ≤ (26316519 / 250000000) := by
  have h := checkLog_sound (w := (19983 / 380017)) (n := 12)
    (lo := (4210643 / 40000000)) (hi := (26316519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180017) = 1/(180017 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6779 : Bounds (-26316519 / 250000000) (-4210643 / 40000000) (Real.log (180017 / 200000)) := by
  have h := reflection_log_6779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6780_neg : (11932521 / 125000000) ≤ -Real.log (200000 / 220033) ∧
    -Real.log (200000 / 220033) ≤ (95460169 / 1000000000) := by
  have h := checkLog_sound (w := (20033 / 420033)) (n := 12)
    (lo := (11932521 / 125000000)) (hi := (95460169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220033 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220033 / 200000) = 1/(200000 / 220033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6780 : Bounds (11932521 / 125000000) (95460169 / 1000000000) (Real.log (220033 / 200000)) := by
  have h := reflection_log_6780_neg
  have he : Real.log (220033 / 200000) = -Real.log (200000 / 220033) := by
    rw [show ((220033 / 200000) : ℝ) = ((200000 / 220033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6781_neg : (21108773 / 200000000) ≤ -Real.log (179967 / 200000) ∧
    -Real.log (179967 / 200000) ≤ (52771933 / 500000000) := by
  have h := checkLog_sound (w := (20033 / 379967)) (n := 12)
    (lo := (21108773 / 200000000)) (hi := (52771933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 179967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 179967) = 1/(179967 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6781 : Bounds (-52771933 / 500000000) (-21108773 / 200000000) (Real.log (179967 / 200000)) := by
  have h := reflection_log_6781_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6782_neg : (10083697 / 1000000000) ≤ -Real.log (39598678911 / 40000000000) ∧
    -Real.log (39598678911 / 40000000000) ≤ (5041849 / 500000000) := by
  have h := checkLog_sound (w := (401321089 / 79598678911)) (n := 12)
    (lo := (10083697 / 1000000000)) (hi := (5041849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39598678911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39598678911) = 1/(39598678911 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6782 : Bounds (-5041849 / 500000000) (-10083697 / 1000000000) (Real.log (39598678911 / 40000000000)) := by
  have h := reflection_log_6782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6783_neg : (10033171 / 1000000000) ≤ -Real.log (39600679711 / 40000000000) ∧
    -Real.log (39600679711 / 40000000000) ≤ (2508293 / 250000000) := by
  have h := checkLog_sound (w := (399320289 / 79600679711)) (n := 12)
    (lo := (10033171 / 1000000000)) (hi := (2508293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39600679711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39600679711) = 1/(39600679711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6783 : Bounds (-2508293 / 250000000) (-10033171 / 1000000000) (Real.log (39600679711 / 40000000000)) := by
  have h := reflection_log_6783_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


