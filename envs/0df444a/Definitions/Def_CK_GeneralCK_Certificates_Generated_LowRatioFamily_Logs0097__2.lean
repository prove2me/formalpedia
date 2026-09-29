-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0097__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0097__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:08:41.602438+00:00
-- url     : https://prove2.me/theorems/d4b6aa12-deb8-4521-8ac3-289ed78ea9c8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0097 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0098)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0097 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0098)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0097 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0098)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0097 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0098) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0097 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0098).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0097 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6208_neg : (386563 / 40000000) ≤ -Real.log (990382471239 / 1000000000000) ∧
    -Real.log (990382471239 / 1000000000000) ≤ (2416019 / 250000000) := by
  have h := checkLog_sound (w := (9617528761 / 1990382471239)) (n := 12)
    (lo := (386563 / 40000000)) (hi := (2416019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990382471239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990382471239) = 1/(990382471239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6208 : Bounds (-2416019 / 250000000) (-386563 / 40000000) (Real.log (990382471239 / 1000000000000)) := by
  have h := reflection_log_6208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6209_neg : (9615617 / 1000000000) ≤ -Real.log (967217251 / 976562500) ∧
    -Real.log (967217251 / 976562500) ≤ (4807809 / 500000000) := by
  have h := checkLog_sound (w := (9345249 / 1943779751)) (n := 12)
    (lo := (9615617 / 1000000000)) (hi := (4807809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 967217251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 967217251) = 1/(967217251 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6209 : Bounds (-4807809 / 500000000) (-9615617 / 1000000000) (Real.log (967217251 / 976562500)) := by
  have h := reflection_log_6209_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6210_neg : (98137847 / 500000000) ≤ -Real.log (250000000000 / 304215585429) ∧
    -Real.log (250000000000 / 304215585429) ≤ (39255139 / 200000000) := by
  have h := checkLog_sound (w := (54215585429 / 554215585429)) (n := 12)
    (lo := (98137847 / 500000000)) (hi := (39255139 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304215585429 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304215585429 / 250000000000) = 1/(250000000000 / 304215585429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6210 : Bounds (98137847 / 500000000) (39255139 / 200000000) (Real.log (304215585429 / 250000000000)) := by
  have h := reflection_log_6210_neg
  have he : Real.log (304215585429 / 250000000000) = -Real.log (250000000000 / 304215585429) := by
    rw [show ((304215585429 / 250000000000) : ℝ) = ((250000000000 / 304215585429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6211_neg : (196770441 / 1000000000) ≤ -Real.log (250000000000 / 304366132221) ∧
    -Real.log (250000000000 / 304366132221) ≤ (98385221 / 500000000) := by
  have h := checkLog_sound (w := (54366132221 / 554366132221)) (n := 12)
    (lo := (196770441 / 1000000000)) (hi := (98385221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304366132221 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304366132221 / 250000000000) = 1/(250000000000 / 304366132221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6211 : Bounds (196770441 / 1000000000) (98385221 / 500000000) (Real.log (304366132221 / 250000000000)) := by
  have h := reflection_log_6211_neg
  have he : Real.log (304366132221 / 250000000000) = -Real.log (250000000000 / 304366132221) := by
    rw [show ((304366132221 / 250000000000) : ℝ) = ((250000000000 / 304366132221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6212_neg : (98504941 / 250000000) ≤ -Real.log (100000000000 / 148292985723) ∧
    -Real.log (100000000000 / 148292985723) ≤ (78803953 / 200000000) := by
  have h := checkLog_sound (w := (48292985723 / 248292985723)) (n := 12)
    (lo := (98504941 / 250000000)) (hi := (78803953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148292985723 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148292985723 / 100000000000) = 1/(100000000000 / 148292985723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6212 : Bounds (98504941 / 250000000) (78803953 / 200000000) (Real.log (148292985723 / 100000000000)) := by
  have h := reflection_log_6212_neg
  have he : Real.log (148292985723 / 100000000000) = -Real.log (100000000000 / 148292985723) := by
    rw [show ((148292985723 / 100000000000) : ℝ) = ((100000000000 / 148292985723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6213_neg : (394227631 / 1000000000) ≤ -Real.log (500000000000 / 741619071269) ∧
    -Real.log (500000000000 / 741619071269) ≤ (24639227 / 62500000) := by
  have h := checkLog_sound (w := (241619071269 / 1241619071269)) (n := 12)
    (lo := (394227631 / 1000000000)) (hi := (24639227 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741619071269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741619071269 / 500000000000) = 1/(500000000000 / 741619071269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6213 : Bounds (394227631 / 1000000000) (24639227 / 62500000) (Real.log (741619071269 / 500000000000)) := by
  have h := reflection_log_6213_neg
  have he : Real.log (741619071269 / 500000000000) = -Real.log (500000000000 / 741619071269) := by
    rw [show ((741619071269 / 500000000000) : ℝ) = ((500000000000 / 741619071269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6214_neg : (177895107 / 1000000000) ≤ -Real.log (10000 / 11947) ∧
    -Real.log (10000 / 11947) ≤ (44473777 / 250000000) := by
  have h := checkLog_sound (w := (1947 / 21947)) (n := 12)
    (lo := (177895107 / 1000000000)) (hi := (44473777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11947 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11947 / 10000) = 1/(10000 / 11947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6214 : Bounds (177895107 / 1000000000) (44473777 / 250000000) (Real.log (11947 / 10000)) := by
  have h := reflection_log_6214_neg
  have he : Real.log (11947 / 10000) = -Real.log (10000 / 11947) := by
    rw [show ((11947 / 10000) : ℝ) = ((10000 / 11947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6215_neg : (541351 / 2500000) ≤ -Real.log (8053 / 10000) ∧
    -Real.log (8053 / 10000) ≤ (216540401 / 1000000000) := by
  have h := checkLog_sound (w := (1947 / 18053)) (n := 12)
    (lo := (541351 / 2500000)) (hi := (216540401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8053) = 1/(8053 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6215 : Bounds (-216540401 / 1000000000) (-541351 / 2500000) (Real.log (8053 / 10000)) := by
  have h := reflection_log_6215_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6216_neg : (194681 / 1000000000) ≤ -Real.log (10000000 / 10001947) ∧
    -Real.log (10000000 / 10001947) ≤ (97341 / 500000000) := by
  have h := checkLog_sound (w := (1947 / 20001947)) (n := 12)
    (lo := (194681 / 1000000000)) (hi := (97341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001947 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001947 / 10000000) = 1/(10000000 / 10001947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6216 : Bounds (194681 / 1000000000) (97341 / 500000000) (Real.log (10001947 / 10000000)) := by
  have h := reflection_log_6216_neg
  have he : Real.log (10001947 / 10000000) = -Real.log (10000000 / 10001947) := by
    rw [show ((10001947 / 10000000) : ℝ) = ((10000000 / 10001947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6217_neg : (97359 / 500000000) ≤ -Real.log (9998053 / 10000000) ∧
    -Real.log (9998053 / 10000000) ≤ (194719 / 1000000000) := by
  have h := checkLog_sound (w := (1947 / 19998053)) (n := 12)
    (lo := (97359 / 500000000)) (hi := (194719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998053) = 1/(9998053 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6217 : Bounds (-194719 / 1000000000) (-97359 / 500000000) (Real.log (9998053 / 10000000)) := by
  have h := reflection_log_6217_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6218_neg : (93376493 / 1000000000) ≤ -Real.log (8000 / 8783) ∧
    -Real.log (8000 / 8783) ≤ (46688247 / 500000000) := by
  have h := checkLog_sound (w := (783 / 16783)) (n := 12)
    (lo := (93376493 / 1000000000)) (hi := (46688247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8783 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8783 / 8000) = 1/(8000 / 8783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6218 : Bounds (93376493 / 1000000000) (46688247 / 500000000) (Real.log (8783 / 8000)) := by
  have h := reflection_log_6218_neg
  have he : Real.log (8783 / 8000) = -Real.log (8000 / 8783) := by
    rw [show ((8783 / 8000) : ℝ) = ((8000 / 8783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6219_neg : (103002187 / 1000000000) ≤ -Real.log (7217 / 8000) ∧
    -Real.log (7217 / 8000) ≤ (25750547 / 250000000) := by
  have h := checkLog_sound (w := (783 / 15217)) (n := 12)
    (lo := (103002187 / 1000000000)) (hi := (25750547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 7217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 7217) = 1/(7217 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6219 : Bounds (-25750547 / 250000000) (-103002187 / 1000000000) (Real.log (7217 / 8000)) := by
  have h := reflection_log_6219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6220_neg : (46799813 / 500000000) ≤ -Real.log (25000 / 27453) ∧
    -Real.log (25000 / 27453) ≤ (93599627 / 1000000000) := by
  have h := checkLog_sound (w := (2453 / 52453)) (n := 12)
    (lo := (46799813 / 500000000)) (hi := (93599627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27453 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27453 / 25000) = 1/(25000 / 27453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6220 : Bounds (46799813 / 500000000) (93599627 / 1000000000) (Real.log (27453 / 25000)) := by
  have h := reflection_log_6220_neg
  have he : Real.log (27453 / 25000) = -Real.log (25000 / 27453) := by
    rw [show ((27453 / 25000) : ℝ) = ((25000 / 27453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6221_neg : (20654761 / 200000000) ≤ -Real.log (22547 / 25000) ∧
    -Real.log (22547 / 25000) ≤ (51636903 / 500000000) := by
  have h := checkLog_sound (w := (2453 / 47547)) (n := 12)
    (lo := (20654761 / 200000000)) (hi := (51636903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22547) = 1/(22547 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6221 : Bounds (-51636903 / 500000000) (-20654761 / 200000000) (Real.log (22547 / 25000)) := by
  have h := reflection_log_6221_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6222_neg : (4837089 / 500000000) ≤ -Real.log (618982791 / 625000000) ∧
    -Real.log (618982791 / 625000000) ≤ (9674179 / 1000000000) := by
  have h := checkLog_sound (w := (6017209 / 1243982791)) (n := 12)
    (lo := (4837089 / 500000000)) (hi := (9674179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 618982791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 618982791) = 1/(618982791 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6222 : Bounds (-9674179 / 1000000000) (-4837089 / 500000000) (Real.log (618982791 / 625000000)) := by
  have h := reflection_log_6222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6223_neg : (4812847 / 500000000) ≤ -Real.log (63386911 / 64000000) ∧
    -Real.log (63386911 / 64000000) ≤ (1925139 / 200000000) := by
  have h := checkLog_sound (w := (613089 / 127386911)) (n := 12)
    (lo := (4812847 / 500000000)) (hi := (1925139 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64000000 / 63386911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64000000 / 63386911) = 1/(63386911 / 64000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6223 : Bounds (-1925139 / 200000000) (-4812847 / 500000000) (Real.log (63386911 / 64000000)) := by
  have h := reflection_log_6223_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6224_neg : (4909467 / 25000000) ≤ -Real.log (500000000000 / 608493834003) ∧
    -Real.log (500000000000 / 608493834003) ≤ (196378681 / 1000000000) := by
  have h := checkLog_sound (w := (108493834003 / 1108493834003)) (n := 12)
    (lo := (4909467 / 25000000)) (hi := (196378681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608493834003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608493834003 / 500000000000) = 1/(500000000000 / 608493834003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6224 : Bounds (4909467 / 25000000) (196378681 / 1000000000) (Real.log (608493834003 / 500000000000)) := by
  have h := reflection_log_6224_neg
  have he : Real.log (608493834003 / 500000000000) = -Real.log (500000000000 / 608493834003) := by
    rw [show ((608493834003 / 500000000000) : ℝ) = ((500000000000 / 608493834003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6225_neg : (24609179 / 125000000) ≤ -Real.log (125000000000 / 152198740409) ∧
    -Real.log (125000000000 / 152198740409) ≤ (196873433 / 1000000000) := by
  have h := checkLog_sound (w := (27198740409 / 277198740409)) (n := 12)
    (lo := (24609179 / 125000000)) (hi := (196873433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152198740409 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152198740409 / 125000000000) = 1/(125000000000 / 152198740409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6225 : Bounds (24609179 / 125000000) (196873433 / 1000000000) (Real.log (152198740409 / 125000000000)) := by
  have h := reflection_log_6225_neg
  have he : Real.log (152198740409 / 125000000000) = -Real.log (125000000000 / 152198740409) := by
    rw [show ((152198740409 / 125000000000) : ℝ) = ((125000000000 / 152198740409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6226_neg : (394227631 / 1000000000) ≤ -Real.log (125000000000 / 185404767817) ∧
    -Real.log (125000000000 / 185404767817) ≤ (24639227 / 62500000) := by
  have h := checkLog_sound (w := (60404767817 / 310404767817)) (n := 12)
    (lo := (394227631 / 1000000000)) (hi := (24639227 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185404767817 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185404767817 / 125000000000) = 1/(125000000000 / 185404767817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6226 : Bounds (394227631 / 1000000000) (24639227 / 62500000) (Real.log (185404767817 / 125000000000)) := by
  have h := reflection_log_6226_neg
  have he : Real.log (185404767817 / 125000000000) = -Real.log (125000000000 / 185404767817) := by
    rw [show ((185404767817 / 125000000000) : ℝ) = ((125000000000 / 185404767817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6227_neg : (98608877 / 250000000) ≤ -Real.log (100000000000 / 148354650441) ∧
    -Real.log (100000000000 / 148354650441) ≤ (394435509 / 1000000000) := by
  have h := checkLog_sound (w := (48354650441 / 248354650441)) (n := 12)
    (lo := (98608877 / 250000000)) (hi := (394435509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148354650441 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148354650441 / 100000000000) = 1/(100000000000 / 148354650441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6227 : Bounds (98608877 / 250000000) (394435509 / 1000000000) (Real.log (148354650441 / 100000000000)) := by
  have h := reflection_log_6227_neg
  have he : Real.log (148354650441 / 100000000000) = -Real.log (100000000000 / 148354650441) := by
    rw [show ((148354650441 / 100000000000) : ℝ) = ((100000000000 / 148354650441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6228_neg : (177978807 / 1000000000) ≤ -Real.log (2500 / 2987) ∧
    -Real.log (2500 / 2987) ≤ (22247351 / 125000000) := by
  have h := checkLog_sound (w := (487 / 5487)) (n := 12)
    (lo := (177978807 / 1000000000)) (hi := (22247351 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2987 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2987 / 2500) = 1/(2500 / 2987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6228 : Bounds (177978807 / 1000000000) (22247351 / 125000000) (Real.log (2987 / 2500)) := by
  have h := reflection_log_6228_neg
  have he : Real.log (2987 / 2500) = -Real.log (2500 / 2987) := by
    rw [show ((2987 / 2500) : ℝ) = ((2500 / 2987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6229_neg : (43332917 / 200000000) ≤ -Real.log (2013 / 2500) ∧
    -Real.log (2013 / 2500) ≤ (108332293 / 500000000) := by
  have h := checkLog_sound (w := (487 / 4513)) (n := 12)
    (lo := (43332917 / 200000000)) (hi := (108332293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2013) = 1/(2013 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6229 : Bounds (-108332293 / 500000000) (-43332917 / 200000000) (Real.log (2013 / 2500)) := by
  have h := reflection_log_6229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6230_neg : (194781 / 1000000000) ≤ -Real.log (2500000 / 2500487) ∧
    -Real.log (2500000 / 2500487) ≤ (97391 / 500000000) := by
  have h := checkLog_sound (w := (487 / 5000487)) (n := 12)
    (lo := (194781 / 1000000000)) (hi := (97391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500487 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500487 / 2500000) = 1/(2500000 / 2500487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6230 : Bounds (194781 / 1000000000) (97391 / 500000000) (Real.log (2500487 / 2500000)) := by
  have h := reflection_log_6230_neg
  have he : Real.log (2500487 / 2500000) = -Real.log (2500000 / 2500487) := by
    rw [show ((2500487 / 2500000) : ℝ) = ((2500000 / 2500487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6231_neg : (97409 / 500000000) ≤ -Real.log (2499513 / 2500000) ∧
    -Real.log (2499513 / 2500000) ≤ (194819 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 4999513)) (n := 12)
    (lo := (97409 / 500000000)) (hi := (194819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499513) = 1/(2499513 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6231 : Bounds (-194819 / 1000000000) (-97409 / 500000000) (Real.log (2499513 / 2500000)) := by
  have h := reflection_log_6231_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6232_neg : (18684589 / 200000000) ≤ -Real.log (500000 / 548963) ∧
    -Real.log (500000 / 548963) ≤ (46711473 / 500000000) := by
  have h := checkLog_sound (w := (48963 / 1048963)) (n := 12)
    (lo := (18684589 / 200000000)) (hi := (46711473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548963 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548963 / 500000) = 1/(500000 / 548963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6232 : Bounds (18684589 / 200000000) (46711473 / 500000000) (Real.log (548963 / 500000)) := by
  have h := reflection_log_6232_neg
  have he : Real.log (548963 / 500000) = -Real.log (500000 / 548963) := by
    rw [show ((548963 / 500000) : ℝ) = ((500000 / 548963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6233_neg : (51529361 / 500000000) ≤ -Real.log (451037 / 500000) ∧
    -Real.log (451037 / 500000) ≤ (103058723 / 1000000000) := by
  have h := checkLog_sound (w := (48963 / 951037)) (n := 12)
    (lo := (51529361 / 500000000)) (hi := (103058723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451037) = 1/(451037 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6233 : Bounds (-103058723 / 1000000000) (-51529361 / 500000000) (Real.log (451037 / 500000)) := by
  have h := reflection_log_6233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6234_neg : (23411517 / 250000000) ≤ -Real.log (1000000 / 1098171) ∧
    -Real.log (1000000 / 1098171) ≤ (93646069 / 1000000000) := by
  have h := checkLog_sound (w := (98171 / 2098171)) (n := 12)
    (lo := (23411517 / 250000000)) (hi := (93646069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098171 / 1000000) = 1/(1000000 / 1098171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6234 : Bounds (23411517 / 250000000) (93646069 / 1000000000) (Real.log (1098171 / 1000000)) := by
  have h := reflection_log_6234_neg
  have he : Real.log (1098171 / 1000000) = -Real.log (1000000 / 1098171) := by
    rw [show ((1098171 / 1000000) : ℝ) = ((1000000 / 1098171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6235_neg : (20666071 / 200000000) ≤ -Real.log (901829 / 1000000) ∧
    -Real.log (901829 / 1000000) ≤ (25832589 / 250000000) := by
  have h := checkLog_sound (w := (98171 / 1901829)) (n := 12)
    (lo := (20666071 / 200000000)) (hi := (25832589 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901829) = 1/(901829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6235 : Bounds (-25832589 / 250000000) (-20666071 / 200000000) (Real.log (901829 / 1000000)) := by
  have h := reflection_log_6235_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6236_neg : (4842143 / 500000000) ≤ -Real.log (990362454759 / 1000000000000) ∧
    -Real.log (990362454759 / 1000000000000) ≤ (9684287 / 1000000000) := by
  have h := checkLog_sound (w := (9637545241 / 1990362454759)) (n := 12)
    (lo := (4842143 / 500000000)) (hi := (9684287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990362454759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990362454759) = 1/(990362454759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6236 : Bounds (-9684287 / 1000000000) (-4842143 / 500000000) (Real.log (990362454759 / 1000000000000)) := by
  have h := reflection_log_6236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6237_neg : (150559 / 15625000) ≤ -Real.log (247602624631 / 250000000000) ∧
    -Real.log (247602624631 / 250000000000) ≤ (9635777 / 1000000000) := by
  have h := checkLog_sound (w := (2397375369 / 497602624631)) (n := 12)
    (lo := (150559 / 15625000)) (hi := (9635777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247602624631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247602624631) = 1/(247602624631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6237 : Bounds (-9635777 / 1000000000) (-150559 / 15625000) (Real.log (247602624631 / 250000000000)) := by
  have h := reflection_log_6237_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6238_neg : (196481667 / 1000000000) ≤ -Real.log (500000000000 / 608556504233) ∧
    -Real.log (500000000000 / 608556504233) ≤ (49120417 / 250000000) := by
  have h := checkLog_sound (w := (108556504233 / 1108556504233)) (n := 12)
    (lo := (196481667 / 1000000000)) (hi := (49120417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608556504233 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608556504233 / 500000000000) = 1/(500000000000 / 608556504233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6238 : Bounds (196481667 / 1000000000) (49120417 / 250000000) (Real.log (608556504233 / 500000000000)) := by
  have h := reflection_log_6238_neg
  have he : Real.log (608556504233 / 500000000000) = -Real.log (500000000000 / 608556504233) := by
    rw [show ((608556504233 / 500000000000) : ℝ) = ((500000000000 / 608556504233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6239_neg : (24622053 / 125000000) ≤ -Real.log (250000000000 / 304428832961) ∧
    -Real.log (250000000000 / 304428832961) ≤ (7879057 / 40000000) := by
  have h := checkLog_sound (w := (54428832961 / 554428832961)) (n := 12)
    (lo := (24622053 / 125000000)) (hi := (7879057 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304428832961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304428832961 / 250000000000) = 1/(250000000000 / 304428832961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6239 : Bounds (24622053 / 125000000) (7879057 / 40000000) (Real.log (304428832961 / 250000000000)) := by
  have h := reflection_log_6239_neg
  have he : Real.log (304428832961 / 250000000000) = -Real.log (250000000000 / 304428832961) := by
    rw [show ((304428832961 / 250000000000) : ℝ) = ((250000000000 / 304428832961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6240_neg : (98608877 / 250000000) ≤ -Real.log (125000000000 / 185443313051) ∧
    -Real.log (125000000000 / 185443313051) ≤ (394435509 / 1000000000) := by
  have h := checkLog_sound (w := (60443313051 / 310443313051)) (n := 12)
    (lo := (98608877 / 250000000)) (hi := (394435509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185443313051 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185443313051 / 125000000000) = 1/(125000000000 / 185443313051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6240 : Bounds (98608877 / 250000000) (394435509 / 1000000000) (Real.log (185443313051 / 125000000000)) := by
  have h := reflection_log_6240_neg
  have he : Real.log (185443313051 / 125000000000) = -Real.log (125000000000 / 185443313051) := by
    rw [show ((185443313051 / 125000000000) : ℝ) = ((125000000000 / 185443313051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6241_neg : (6166303 / 15625000) ≤ -Real.log (125000000000 / 185481867859) ∧
    -Real.log (125000000000 / 185481867859) ≤ (394643393 / 1000000000) := by
  have h := checkLog_sound (w := (60481867859 / 310481867859)) (n := 12)
    (lo := (6166303 / 15625000)) (hi := (394643393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185481867859 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185481867859 / 125000000000) = 1/(125000000000 / 185481867859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6241 : Bounds (6166303 / 15625000) (394643393 / 1000000000) (Real.log (185481867859 / 125000000000)) := by
  have h := reflection_log_6241_neg
  have he : Real.log (185481867859 / 125000000000) = -Real.log (125000000000 / 185481867859) := by
    rw [show ((185481867859 / 125000000000) : ℝ) = ((125000000000 / 185481867859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6242_neg : (178062499 / 1000000000) ≤ -Real.log (10000 / 11949) ∧
    -Real.log (10000 / 11949) ≤ (2849 / 16000) := by
  have h := checkLog_sound (w := (1949 / 21949)) (n := 12)
    (lo := (178062499 / 1000000000)) (hi := (2849 / 16000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11949 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11949 / 10000) = 1/(10000 / 11949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6242 : Bounds (178062499 / 1000000000) (2849 / 16000) (Real.log (11949 / 10000)) := by
  have h := reflection_log_6242_neg
  have he : Real.log (11949 / 10000) = -Real.log (10000 / 11949) := by
    rw [show ((11949 / 10000) : ℝ) = ((10000 / 11949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6243_neg : (43357757 / 200000000) ≤ -Real.log (8051 / 10000) ∧
    -Real.log (8051 / 10000) ≤ (108394393 / 500000000) := by
  have h := checkLog_sound (w := (1949 / 18051)) (n := 12)
    (lo := (43357757 / 200000000)) (hi := (108394393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8051) = 1/(8051 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6243 : Bounds (-108394393 / 500000000) (-43357757 / 200000000) (Real.log (8051 / 10000)) := by
  have h := reflection_log_6243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6244_neg : (194881 / 1000000000) ≤ -Real.log (10000000 / 10001949) ∧
    -Real.log (10000000 / 10001949) ≤ (97441 / 500000000) := by
  have h := checkLog_sound (w := (1949 / 20001949)) (n := 12)
    (lo := (194881 / 1000000000)) (hi := (97441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001949 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001949 / 10000000) = 1/(10000000 / 10001949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6244 : Bounds (194881 / 1000000000) (97441 / 500000000) (Real.log (10001949 / 10000000)) := by
  have h := reflection_log_6244_neg
  have he : Real.log (10001949 / 10000000) = -Real.log (10000000 / 10001949) := by
    rw [show ((10001949 / 10000000) : ℝ) = ((10000000 / 10001949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6245_neg : (97459 / 500000000) ≤ -Real.log (9998051 / 10000000) ∧
    -Real.log (9998051 / 10000000) ≤ (194919 / 1000000000) := by
  have h := checkLog_sound (w := (1949 / 19998051)) (n := 12)
    (lo := (97459 / 500000000)) (hi := (194919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998051) = 1/(9998051 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6245 : Bounds (-194919 / 1000000000) (-97459 / 500000000) (Real.log (9998051 / 10000000)) := by
  have h := reflection_log_6245_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6246_neg : (18693879 / 200000000) ≤ -Real.log (1000000 / 1097977) ∧
    -Real.log (1000000 / 1097977) ≤ (23367349 / 250000000) := by
  have h := checkLog_sound (w := (97977 / 2097977)) (n := 12)
    (lo := (18693879 / 200000000)) (hi := (23367349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097977 / 1000000) = 1/(1000000 / 1097977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6246 : Bounds (18693879 / 200000000) (23367349 / 250000000) (Real.log (1097977 / 1000000)) := by
  have h := reflection_log_6246_neg
  have he : Real.log (1097977 / 1000000) = -Real.log (1000000 / 1097977) := by
    rw [show ((1097977 / 1000000) : ℝ) = ((1000000 / 1097977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6247_neg : (5155763 / 50000000) ≤ -Real.log (902023 / 1000000) ∧
    -Real.log (902023 / 1000000) ≤ (103115261 / 1000000000) := by
  have h := checkLog_sound (w := (97977 / 1902023)) (n := 12)
    (lo := (5155763 / 50000000)) (hi := (103115261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902023) = 1/(902023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6247 : Bounds (-103115261 / 1000000000) (-5155763 / 50000000) (Real.log (902023 / 1000000)) := by
  have h := reflection_log_6247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6248_neg : (23423127 / 250000000) ≤ -Real.log (500000 / 549111) ∧
    -Real.log (500000 / 549111) ≤ (93692509 / 1000000000) := by
  have h := checkLog_sound (w := (49111 / 1049111)) (n := 12)
    (lo := (23423127 / 250000000)) (hi := (93692509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549111 / 500000) = 1/(500000 / 549111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6248 : Bounds (23423127 / 250000000) (93692509 / 1000000000) (Real.log (549111 / 500000)) := by
  have h := reflection_log_6248_neg
  have he : Real.log (549111 / 500000) = -Real.log (500000 / 549111) := by
    rw [show ((549111 / 500000) : ℝ) = ((500000 / 549111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6249_neg : (25846727 / 250000000) ≤ -Real.log (450889 / 500000) ∧
    -Real.log (450889 / 500000) ≤ (103386909 / 1000000000) := by
  have h := checkLog_sound (w := (49111 / 950889)) (n := 12)
    (lo := (25846727 / 250000000)) (hi := (103386909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450889) = 1/(450889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6249 : Bounds (-103386909 / 1000000000) (-25846727 / 250000000) (Real.log (450889 / 500000)) := by
  have h := reflection_log_6249_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6250_neg : (6059 / 625000) ≤ -Real.log (247588109679 / 250000000000) ∧
    -Real.log (247588109679 / 250000000000) ≤ (9694401 / 1000000000) := by
  have h := checkLog_sound (w := (2411890321 / 497588109679)) (n := 12)
    (lo := (6059 / 625000)) (hi := (9694401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247588109679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247588109679) = 1/(247588109679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6250 : Bounds (-9694401 / 1000000000) (-6059 / 625000) (Real.log (247588109679 / 250000000000)) := by
  have h := reflection_log_6250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6251_neg : (1205733 / 125000000) ≤ -Real.log (990400507471 / 1000000000000) ∧
    -Real.log (990400507471 / 1000000000000) ≤ (1929173 / 200000000) := by
  have h := checkLog_sound (w := (9599492529 / 1990400507471)) (n := 12)
    (lo := (1205733 / 125000000)) (hi := (1929173 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990400507471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990400507471) = 1/(990400507471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6251 : Bounds (-1929173 / 200000000) (-1205733 / 125000000) (Real.log (990400507471 / 1000000000000)) := by
  have h := reflection_log_6251_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6252_neg : (12286541 / 62500000) ≤ -Real.log (10000000000 / 12172383631) ∧
    -Real.log (10000000000 / 12172383631) ≤ (196584657 / 1000000000) := by
  have h := checkLog_sound (w := (2172383631 / 22172383631)) (n := 12)
    (lo := (12286541 / 62500000)) (hi := (196584657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12172383631 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12172383631 / 10000000000) = 1/(10000000000 / 12172383631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6252 : Bounds (12286541 / 62500000) (196584657 / 1000000000) (Real.log (12172383631 / 10000000000)) := by
  have h := reflection_log_6252_neg
  have he : Real.log (12172383631 / 10000000000) = -Real.log (10000000000 / 12172383631) := by
    rw [show ((12172383631 / 10000000000) : ℝ) = ((10000000000 / 12172383631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6253_neg : (197079417 / 1000000000) ≤ -Real.log (5000000000 / 6089203773) ∧
    -Real.log (5000000000 / 6089203773) ≤ (98539709 / 500000000) := by
  have h := checkLog_sound (w := (1089203773 / 11089203773)) (n := 12)
    (lo := (197079417 / 1000000000)) (hi := (98539709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6089203773 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6089203773 / 5000000000) = 1/(5000000000 / 6089203773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6253 : Bounds (197079417 / 1000000000) (98539709 / 500000000) (Real.log (6089203773 / 5000000000)) := by
  have h := reflection_log_6253_neg
  have he : Real.log (6089203773 / 5000000000) = -Real.log (5000000000 / 6089203773) := by
    rw [show ((6089203773 / 5000000000) : ℝ) = ((5000000000 / 6089203773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6254_neg : (6166303 / 15625000) ≤ -Real.log (100000000000 / 148385494287) ∧
    -Real.log (100000000000 / 148385494287) ≤ (394643393 / 1000000000) := by
  have h := checkLog_sound (w := (48385494287 / 248385494287)) (n := 12)
    (lo := (6166303 / 15625000)) (hi := (394643393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148385494287 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148385494287 / 100000000000) = 1/(100000000000 / 148385494287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6254 : Bounds (6166303 / 15625000) (394643393 / 1000000000) (Real.log (148385494287 / 100000000000)) := by
  have h := reflection_log_6254_neg
  have he : Real.log (148385494287 / 100000000000) = -Real.log (100000000000 / 148385494287) := by
    rw [show ((148385494287 / 100000000000) : ℝ) = ((100000000000 / 148385494287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6255_neg : (78970257 / 200000000) ≤ -Real.log (250000000000 / 371040864489) ∧
    -Real.log (250000000000 / 371040864489) ≤ (197425643 / 500000000) := by
  have h := checkLog_sound (w := (121040864489 / 621040864489)) (n := 12)
    (lo := (78970257 / 200000000)) (hi := (197425643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371040864489 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371040864489 / 250000000000) = 1/(250000000000 / 371040864489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6255 : Bounds (78970257 / 200000000) (197425643 / 500000000) (Real.log (371040864489 / 250000000000)) := by
  have h := reflection_log_6255_neg
  have he : Real.log (371040864489 / 250000000000) = -Real.log (250000000000 / 371040864489) := by
    rw [show ((371040864489 / 250000000000) : ℝ) = ((250000000000 / 371040864489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6256_neg : (35629237 / 200000000) ≤ -Real.log (200 / 239) ∧
    -Real.log (200 / 239) ≤ (89073093 / 500000000) := by
  have h := checkLog_sound (w := (39 / 439)) (n := 12)
    (lo := (35629237 / 200000000)) (hi := (89073093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239 / 200) = 1/(200 / 239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6256 : Bounds (35629237 / 200000000) (89073093 / 500000000) (Real.log (239 / 200)) := by
  have h := reflection_log_6256_neg
  have he : Real.log (239 / 200) = -Real.log (200 / 239) := by
    rw [show ((239 / 200) : ℝ) = ((200 / 239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6257_neg : (216913001 / 1000000000) ≤ -Real.log (161 / 200) ∧
    -Real.log (161 / 200) ≤ (108456501 / 500000000) := by
  have h := checkLog_sound (w := (39 / 361)) (n := 12)
    (lo := (216913001 / 1000000000)) (hi := (108456501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 161) = 1/(161 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6257 : Bounds (-108456501 / 500000000) (-216913001 / 1000000000) (Real.log (161 / 200)) := by
  have h := reflection_log_6257_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6258_neg : (9749 / 50000000) ≤ -Real.log (200000 / 200039) ∧
    -Real.log (200000 / 200039) ≤ (194981 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 400039)) (n := 12)
    (lo := (9749 / 50000000)) (hi := (194981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200039 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200039 / 200000) = 1/(200000 / 200039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6258 : Bounds (9749 / 50000000) (194981 / 1000000000) (Real.log (200039 / 200000)) := by
  have h := reflection_log_6258_neg
  have he : Real.log (200039 / 200000) = -Real.log (200000 / 200039) := by
    rw [show ((200039 / 200000) : ℝ) = ((200000 / 200039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6259_neg : (195019 / 1000000000) ≤ -Real.log (199961 / 200000) ∧
    -Real.log (199961 / 200000) ≤ (9751 / 50000000) := by
  have h := checkLog_sound (w := (39 / 399961)) (n := 12)
    (lo := (195019 / 1000000000)) (hi := (9751 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199961) = 1/(199961 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6259 : Bounds (-9751 / 50000000) (-195019 / 1000000000) (Real.log (199961 / 200000)) := by
  have h := reflection_log_6259_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6260_neg : (93515843 / 1000000000) ≤ -Real.log (250000 / 274507) ∧
    -Real.log (250000 / 274507) ≤ (23378961 / 250000000) := by
  have h := checkLog_sound (w := (24507 / 524507)) (n := 12)
    (lo := (93515843 / 1000000000)) (hi := (23378961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274507 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274507 / 250000) = 1/(250000 / 274507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6260 : Bounds (93515843 / 1000000000) (23378961 / 250000000) (Real.log (274507 / 250000)) := by
  have h := reflection_log_6260_neg
  have he : Real.log (274507 / 250000) = -Real.log (250000 / 274507) := by
    rw [show ((274507 / 250000) : ℝ) = ((250000 / 274507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6261_neg : (103171801 / 1000000000) ≤ -Real.log (225493 / 250000) ∧
    -Real.log (225493 / 250000) ≤ (51585901 / 500000000) := by
  have h := checkLog_sound (w := (24507 / 475493)) (n := 12)
    (lo := (103171801 / 1000000000)) (hi := (51585901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225493) = 1/(225493 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6261 : Bounds (-51585901 / 500000000) (-103171801 / 1000000000) (Real.log (225493 / 250000)) := by
  have h := reflection_log_6261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6262_neg : (46869473 / 500000000) ≤ -Real.log (1000000 / 1098273) ∧
    -Real.log (1000000 / 1098273) ≤ (93738947 / 1000000000) := by
  have h := checkLog_sound (w := (98273 / 2098273)) (n := 12)
    (lo := (46869473 / 500000000)) (hi := (93738947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098273 / 1000000) = 1/(1000000 / 1098273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6262 : Bounds (46869473 / 500000000) (93738947 / 1000000000) (Real.log (1098273 / 1000000)) := by
  have h := reflection_log_6262_neg
  have he : Real.log (1098273 / 1000000) = -Real.log (1000000 / 1098273) := by
    rw [show ((1098273 / 1000000) : ℝ) = ((1000000 / 1098273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6263_neg : (20688693 / 200000000) ≤ -Real.log (901727 / 1000000) ∧
    -Real.log (901727 / 1000000) ≤ (51721733 / 500000000) := by
  have h := checkLog_sound (w := (98273 / 1901727)) (n := 12)
    (lo := (20688693 / 200000000)) (hi := (51721733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901727) = 1/(901727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6263 : Bounds (-51721733 / 500000000) (-20688693 / 200000000) (Real.log (901727 / 1000000)) := by
  have h := reflection_log_6263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6264_neg : (9704519 / 1000000000) ≤ -Real.log (990342417471 / 1000000000000) ∧
    -Real.log (990342417471 / 1000000000000) ≤ (242613 / 25000000) := by
  have h := checkLog_sound (w := (9657582529 / 1990342417471)) (n := 12)
    (lo := (9704519 / 1000000000)) (hi := (242613 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990342417471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990342417471) = 1/(990342417471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6264 : Bounds (-242613 / 25000000) (-9704519 / 1000000000) (Real.log (990342417471 / 1000000000000)) := by
  have h := reflection_log_6264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6265_neg : (9655957 / 1000000000) ≤ -Real.log (61899406951 / 62500000000) ∧
    -Real.log (61899406951 / 62500000000) ≤ (4827979 / 500000000) := by
  have h := checkLog_sound (w := (600593049 / 124399406951)) (n := 12)
    (lo := (9655957 / 1000000000)) (hi := (4827979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61899406951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61899406951) = 1/(61899406951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6265 : Bounds (-4827979 / 500000000) (-9655957 / 1000000000) (Real.log (61899406951 / 62500000000)) := by
  have h := reflection_log_6265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6266_neg : (39337529 / 200000000) ≤ -Real.log (100000000000 / 121736373191) ∧
    -Real.log (100000000000 / 121736373191) ≤ (98343823 / 500000000) := by
  have h := checkLog_sound (w := (21736373191 / 221736373191)) (n := 12)
    (lo := (39337529 / 200000000)) (hi := (98343823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121736373191 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121736373191 / 100000000000) = 1/(100000000000 / 121736373191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6266 : Bounds (39337529 / 200000000) (98343823 / 500000000) (Real.log (121736373191 / 100000000000)) := by
  have h := reflection_log_6266_neg
  have he : Real.log (121736373191 / 100000000000) = -Real.log (100000000000 / 121736373191) := by
    rw [show ((121736373191 / 100000000000) : ℝ) = ((100000000000 / 121736373191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6267_neg : (197182411 / 1000000000) ≤ -Real.log (500000000000 / 608983095771) ∧
    -Real.log (500000000000 / 608983095771) ≤ (49295603 / 250000000) := by
  have h := checkLog_sound (w := (108983095771 / 1108983095771)) (n := 12)
    (lo := (197182411 / 1000000000)) (hi := (49295603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608983095771 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608983095771 / 500000000000) = 1/(500000000000 / 608983095771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6267 : Bounds (197182411 / 1000000000) (49295603 / 250000000) (Real.log (608983095771 / 500000000000)) := by
  have h := reflection_log_6267_neg
  have he : Real.log (608983095771 / 500000000000) = -Real.log (500000000000 / 608983095771) := by
    rw [show ((608983095771 / 500000000000) : ℝ) = ((500000000000 / 608983095771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6268_neg : (78970257 / 200000000) ≤ -Real.log (500000000000 / 742081728977) ∧
    -Real.log (500000000000 / 742081728977) ≤ (197425643 / 500000000) := by
  have h := checkLog_sound (w := (242081728977 / 1242081728977)) (n := 12)
    (lo := (78970257 / 200000000)) (hi := (197425643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742081728977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742081728977 / 500000000000) = 1/(500000000000 / 742081728977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6268 : Bounds (78970257 / 200000000) (197425643 / 500000000) (Real.log (742081728977 / 500000000000)) := by
  have h := reflection_log_6268_neg
  have he : Real.log (742081728977 / 500000000000) = -Real.log (500000000000 / 742081728977) := by
    rw [show ((742081728977 / 500000000000) : ℝ) = ((500000000000 / 742081728977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6269_neg : (197529593 / 500000000) ≤ -Real.log (100000000000 / 148447204969) ∧
    -Real.log (100000000000 / 148447204969) ≤ (395059187 / 1000000000) := by
  have h := checkLog_sound (w := (48447204969 / 248447204969)) (n := 12)
    (lo := (197529593 / 500000000)) (hi := (395059187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148447204969 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148447204969 / 100000000000) = 1/(100000000000 / 148447204969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6269 : Bounds (197529593 / 500000000) (395059187 / 1000000000) (Real.log (148447204969 / 100000000000)) := by
  have h := reflection_log_6269_neg
  have he : Real.log (148447204969 / 100000000000) = -Real.log (100000000000 / 148447204969) := by
    rw [show ((148447204969 / 100000000000) : ℝ) = ((100000000000 / 148447204969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6270_neg : (178229863 / 1000000000) ≤ -Real.log (10000 / 11951) ∧
    -Real.log (10000 / 11951) ≤ (22278733 / 125000000) := by
  have h := checkLog_sound (w := (1951 / 21951)) (n := 12)
    (lo := (178229863 / 1000000000)) (hi := (22278733 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11951 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11951 / 10000) = 1/(10000 / 11951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6270 : Bounds (178229863 / 1000000000) (22278733 / 125000000) (Real.log (11951 / 10000)) := by
  have h := reflection_log_6270_neg
  have he : Real.log (11951 / 10000) = -Real.log (10000 / 11951) := by
    rw [show ((11951 / 10000) : ℝ) = ((10000 / 11951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6271_neg : (13564827 / 62500000) ≤ -Real.log (8049 / 10000) ∧
    -Real.log (8049 / 10000) ≤ (217037233 / 1000000000) := by
  have h := checkLog_sound (w := (1951 / 18049)) (n := 12)
    (lo := (13564827 / 62500000)) (hi := (217037233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8049) = 1/(8049 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6271 : Bounds (-217037233 / 1000000000) (-13564827 / 62500000) (Real.log (8049 / 10000)) := by
  have h := reflection_log_6271_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0098 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6272_neg : (4877 / 25000000) ≤ -Real.log (10000000 / 10001951) ∧
    -Real.log (10000000 / 10001951) ≤ (195081 / 1000000000) := by
  have h := checkLog_sound (w := (1951 / 20001951)) (n := 12)
    (lo := (4877 / 25000000)) (hi := (195081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001951 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001951 / 10000000) = 1/(10000000 / 10001951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6272 : Bounds (4877 / 25000000) (195081 / 1000000000) (Real.log (10001951 / 10000000)) := by
  have h := reflection_log_6272_neg
  have he : Real.log (10001951 / 10000000) = -Real.log (10000000 / 10001951) := by
    rw [show ((10001951 / 10000000) : ℝ) = ((10000000 / 10001951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6273_neg : (195119 / 1000000000) ≤ -Real.log (9998049 / 10000000) ∧
    -Real.log (9998049 / 10000000) ≤ (2439 / 12500000) := by
  have h := checkLog_sound (w := (1951 / 19998049)) (n := 12)
    (lo := (195119 / 1000000000)) (hi := (2439 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998049) = 1/(9998049 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6273 : Bounds (-2439 / 12500000) (-195119 / 1000000000) (Real.log (9998049 / 10000000)) := by
  have h := reflection_log_6273_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6274_neg : (93562289 / 1000000000) ≤ -Real.log (1000000 / 1098079) ∧
    -Real.log (1000000 / 1098079) ≤ (9356229 / 100000000) := by
  have h := checkLog_sound (w := (98079 / 2098079)) (n := 12)
    (lo := (93562289 / 1000000000)) (hi := (9356229 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098079 / 1000000) = 1/(1000000 / 1098079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6274 : Bounds (93562289 / 1000000000) (9356229 / 100000000) (Real.log (1098079 / 1000000)) := by
  have h := reflection_log_6274_neg
  have he : Real.log (1098079 / 1000000) = -Real.log (1000000 / 1098079) := by
    rw [show ((1098079 / 1000000) : ℝ) = ((1000000 / 1098079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6275_neg : (20645669 / 200000000) ≤ -Real.log (901921 / 1000000) ∧
    -Real.log (901921 / 1000000) ≤ (51614173 / 500000000) := by
  have h := checkLog_sound (w := (98079 / 1901921)) (n := 12)
    (lo := (20645669 / 200000000)) (hi := (51614173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901921) = 1/(901921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6275 : Bounds (-51614173 / 500000000) (-20645669 / 200000000) (Real.log (901921 / 1000000)) := by
  have h := reflection_log_6275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6276_neg : (23446573 / 250000000) ≤ -Real.log (40000 / 43933) ∧
    -Real.log (40000 / 43933) ≤ (93786293 / 1000000000) := by
  have h := checkLog_sound (w := (3933 / 83933)) (n := 12)
    (lo := (23446573 / 250000000)) (hi := (93786293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43933 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43933 / 40000) = 1/(40000 / 43933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6276 : Bounds (23446573 / 250000000) (93786293 / 1000000000) (Real.log (43933 / 40000)) := by
  have h := reflection_log_6276_neg
  have he : Real.log (43933 / 40000) = -Real.log (40000 / 43933) := by
    rw [show ((43933 / 40000) : ℝ) = ((40000 / 43933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6277_neg : (51750567 / 500000000) ≤ -Real.log (36067 / 40000) ∧
    -Real.log (36067 / 40000) ≤ (20700227 / 200000000) := by
  have h := checkLog_sound (w := (3933 / 76067)) (n := 12)
    (lo := (51750567 / 500000000)) (hi := (20700227 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36067) = 1/(36067 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6277 : Bounds (-20700227 / 200000000) (-51750567 / 500000000) (Real.log (36067 / 40000)) := by
  have h := reflection_log_6277_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6278_neg : (4857421 / 500000000) ≤ -Real.log (1584531511 / 1600000000) ∧
    -Real.log (1584531511 / 1600000000) ≤ (9714843 / 1000000000) := by
  have h := checkLog_sound (w := (15468489 / 3184531511)) (n := 12)
    (lo := (4857421 / 500000000)) (hi := (9714843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1584531511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1584531511) = 1/(1584531511 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6278 : Bounds (-9714843 / 1000000000) (-4857421 / 500000000) (Real.log (1584531511 / 1600000000)) := by
  have h := reflection_log_6278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6279_neg : (1208257 / 125000000) ≤ -Real.log (990380509759 / 1000000000000) ∧
    -Real.log (990380509759 / 1000000000000) ≤ (9666057 / 1000000000) := by
  have h := checkLog_sound (w := (9619490241 / 1990380509759)) (n := 12)
    (lo := (1208257 / 125000000)) (hi := (9666057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990380509759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990380509759) = 1/(990380509759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6279 : Bounds (-9666057 / 1000000000) (-1208257 / 125000000) (Real.log (990380509759 / 1000000000000)) := by
  have h := reflection_log_6279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6280_neg : (39358127 / 200000000) ≤ -Real.log (10000000000 / 12174891149) ∧
    -Real.log (10000000000 / 12174891149) ≤ (49197659 / 250000000) := by
  have h := checkLog_sound (w := (2174891149 / 22174891149)) (n := 12)
    (lo := (39358127 / 200000000)) (hi := (49197659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12174891149 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12174891149 / 10000000000) = 1/(10000000000 / 12174891149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6280 : Bounds (39358127 / 200000000) (49197659 / 250000000) (Real.log (12174891149 / 10000000000)) := by
  have h := reflection_log_6280_neg
  have he : Real.log (12174891149 / 10000000000) = -Real.log (10000000000 / 12174891149) := by
    rw [show ((12174891149 / 10000000000) : ℝ) = ((10000000000 / 12174891149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6281_neg : (98643713 / 500000000) ≤ -Real.log (250000000000 / 304523525661) ∧
    -Real.log (250000000000 / 304523525661) ≤ (197287427 / 1000000000) := by
  have h := checkLog_sound (w := (54523525661 / 554523525661)) (n := 12)
    (lo := (98643713 / 500000000)) (hi := (197287427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304523525661 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304523525661 / 250000000000) = 1/(250000000000 / 304523525661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6281 : Bounds (98643713 / 500000000) (197287427 / 1000000000) (Real.log (304523525661 / 250000000000)) := by
  have h := reflection_log_6281_neg
  have he : Real.log (304523525661 / 250000000000) = -Real.log (250000000000 / 304523525661) := by
    rw [show ((304523525661 / 250000000000) : ℝ) = ((250000000000 / 304523525661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6282_neg : (197529593 / 500000000) ≤ -Real.log (125000000000 / 185559006211) ∧
    -Real.log (125000000000 / 185559006211) ≤ (395059187 / 1000000000) := by
  have h := checkLog_sound (w := (60559006211 / 310559006211)) (n := 12)
    (lo := (197529593 / 500000000)) (hi := (395059187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185559006211 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185559006211 / 125000000000) = 1/(125000000000 / 185559006211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6282 : Bounds (197529593 / 500000000) (395059187 / 1000000000) (Real.log (185559006211 / 125000000000)) := by
  have h := reflection_log_6282_neg
  have he : Real.log (185559006211 / 125000000000) = -Real.log (125000000000 / 185559006211) := by
    rw [show ((185559006211 / 125000000000) : ℝ) = ((125000000000 / 185559006211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6283_neg : (49408387 / 125000000) ≤ -Real.log (500000000000 / 742390359051) ∧
    -Real.log (500000000000 / 742390359051) ≤ (395267097 / 1000000000) := by
  have h := checkLog_sound (w := (242390359051 / 1242390359051)) (n := 12)
    (lo := (49408387 / 125000000)) (hi := (395267097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742390359051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742390359051 / 500000000000) = 1/(500000000000 / 742390359051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6283 : Bounds (49408387 / 125000000) (395267097 / 1000000000) (Real.log (742390359051 / 500000000000)) := by
  have h := reflection_log_6283_neg
  have he : Real.log (742390359051 / 500000000000) = -Real.log (500000000000 / 742390359051) := by
    rw [show ((742390359051 / 500000000000) : ℝ) = ((500000000000 / 742390359051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6284_neg : (35662707 / 200000000) ≤ -Real.log (625 / 747) ∧
    -Real.log (625 / 747) ≤ (2786149 / 15625000) := by
  have h := checkLog_sound (w := (61 / 686)) (n := 12)
    (lo := (35662707 / 200000000)) (hi := (2786149 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747 / 625) = 1/(625 / 747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6284 : Bounds (35662707 / 200000000) (2786149 / 15625000) (Real.log (747 / 625)) := by
  have h := reflection_log_6284_neg
  have he : Real.log (747 / 625) = -Real.log (625 / 747) := by
    rw [show ((747 / 625) : ℝ) = ((625 / 747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6285_neg : (217161479 / 1000000000) ≤ -Real.log (503 / 625) ∧
    -Real.log (503 / 625) ≤ (5429037 / 25000000) := by
  have h := checkLog_sound (w := (61 / 564)) (n := 12)
    (lo := (217161479 / 1000000000)) (hi := (5429037 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 503) = 1/(503 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6285 : Bounds (-5429037 / 25000000) (-217161479 / 1000000000) (Real.log (503 / 625)) := by
  have h := reflection_log_6285_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6286_neg : (9759 / 50000000) ≤ -Real.log (312500 / 312561) ∧
    -Real.log (312500 / 312561) ≤ (195181 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 625061)) (n := 12)
    (lo := (9759 / 50000000)) (hi := (195181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312561 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312561 / 312500) = 1/(312500 / 312561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6286 : Bounds (9759 / 50000000) (195181 / 1000000000) (Real.log (312561 / 312500)) := by
  have h := reflection_log_6286_neg
  have he : Real.log (312561 / 312500) = -Real.log (312500 / 312561) := by
    rw [show ((312561 / 312500) : ℝ) = ((312500 / 312561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6287_neg : (195219 / 1000000000) ≤ -Real.log (312439 / 312500) ∧
    -Real.log (312439 / 312500) ≤ (9761 / 50000000) := by
  have h := checkLog_sound (w := (61 / 624939)) (n := 12)
    (lo := (195219 / 1000000000)) (hi := (9761 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312439) = 1/(312439 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6287 : Bounds (-9761 / 50000000) (-195219 / 1000000000) (Real.log (312439 / 312500)) := by
  have h := reflection_log_6287_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6288_neg : (93608733 / 1000000000) ≤ -Real.log (100000 / 109813) ∧
    -Real.log (100000 / 109813) ≤ (46804367 / 500000000) := by
  have h := checkLog_sound (w := (9813 / 209813)) (n := 12)
    (lo := (93608733 / 1000000000)) (hi := (46804367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109813 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109813 / 100000) = 1/(100000 / 109813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6288 : Bounds (93608733 / 1000000000) (46804367 / 500000000) (Real.log (109813 / 100000)) := by
  have h := reflection_log_6288_neg
  have he : Real.log (109813 / 100000) = -Real.log (100000 / 109813) := by
    rw [show ((109813 / 100000) : ℝ) = ((100000 / 109813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6289_neg : (103284893 / 1000000000) ≤ -Real.log (90187 / 100000) ∧
    -Real.log (90187 / 100000) ≤ (51642447 / 500000000) := by
  have h := checkLog_sound (w := (9813 / 190187)) (n := 12)
    (lo := (103284893 / 1000000000)) (hi := (51642447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90187) = 1/(90187 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6289 : Bounds (-51642447 / 500000000) (-103284893 / 1000000000) (Real.log (90187 / 100000)) := by
  have h := reflection_log_6289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6290_neg : (3753309 / 40000000) ≤ -Real.log (125000 / 137297) ∧
    -Real.log (125000 / 137297) ≤ (46916363 / 500000000) := by
  have h := checkLog_sound (w := (12297 / 262297)) (n := 12)
    (lo := (3753309 / 40000000)) (hi := (46916363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137297 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137297 / 125000) = 1/(125000 / 137297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6290 : Bounds (3753309 / 40000000) (46916363 / 500000000) (Real.log (137297 / 125000)) := by
  have h := reflection_log_6290_neg
  have he : Real.log (137297 / 125000) = -Real.log (125000 / 137297) := by
    rw [show ((137297 / 125000) : ℝ) = ((125000 / 137297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6291_neg : (103557697 / 1000000000) ≤ -Real.log (112703 / 125000) ∧
    -Real.log (112703 / 125000) ≤ (51778849 / 500000000) := by
  have h := checkLog_sound (w := (12297 / 237703)) (n := 12)
    (lo := (103557697 / 1000000000)) (hi := (51778849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112703) = 1/(112703 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6291 : Bounds (-51778849 / 500000000) (-103557697 / 1000000000) (Real.log (112703 / 125000)) := by
  have h := reflection_log_6291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6292_neg : (9724971 / 1000000000) ≤ -Real.log (15473783791 / 15625000000) ∧
    -Real.log (15473783791 / 15625000000) ≤ (2431243 / 250000000) := by
  have h := checkLog_sound (w := (151216209 / 31098783791)) (n := 12)
    (lo := (9724971 / 1000000000)) (hi := (2431243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15473783791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15473783791) = 1/(15473783791 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6292 : Bounds (-2431243 / 250000000) (-9724971 / 1000000000) (Real.log (15473783791 / 15625000000)) := by
  have h := reflection_log_6292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6293_neg : (15119 / 1562500) ≤ -Real.log (9903705031 / 10000000000) ∧
    -Real.log (9903705031 / 10000000000) ≤ (9676161 / 1000000000) := by
  have h := checkLog_sound (w := (96294969 / 19903705031)) (n := 12)
    (lo := (15119 / 1562500)) (hi := (9676161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9903705031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9903705031) = 1/(9903705031 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6293 : Bounds (-9676161 / 1000000000) (-15119 / 1562500) (Real.log (9903705031 / 10000000000)) := by
  have h := reflection_log_6293_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6294_neg : (98446813 / 500000000) ≤ -Real.log (250000000000 / 304403628017) ∧
    -Real.log (250000000000 / 304403628017) ≤ (196893627 / 1000000000) := by
  have h := checkLog_sound (w := (54403628017 / 554403628017)) (n := 12)
    (lo := (98446813 / 500000000)) (hi := (196893627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304403628017 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304403628017 / 250000000000) = 1/(250000000000 / 304403628017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6294 : Bounds (98446813 / 500000000) (196893627 / 1000000000) (Real.log (304403628017 / 250000000000)) := by
  have h := reflection_log_6294_neg
  have he : Real.log (304403628017 / 250000000000) = -Real.log (250000000000 / 304403628017) := by
    rw [show ((304403628017 / 250000000000) : ℝ) = ((250000000000 / 304403628017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6295_neg : (98695211 / 500000000) ≤ -Real.log (500000000000 / 609109784123) ∧
    -Real.log (500000000000 / 609109784123) ≤ (197390423 / 1000000000) := by
  have h := checkLog_sound (w := (109109784123 / 1109109784123)) (n := 12)
    (lo := (98695211 / 500000000)) (hi := (197390423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609109784123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609109784123 / 500000000000) = 1/(500000000000 / 609109784123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6295 : Bounds (98695211 / 500000000) (197390423 / 1000000000) (Real.log (609109784123 / 500000000000)) := by
  have h := reflection_log_6295_neg
  have he : Real.log (609109784123 / 500000000000) = -Real.log (500000000000 / 609109784123) := by
    rw [show ((609109784123 / 500000000000) : ℝ) = ((500000000000 / 609109784123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6296_neg : (49408387 / 125000000) ≤ -Real.log (10000000000 / 14847807181) ∧
    -Real.log (10000000000 / 14847807181) ≤ (395267097 / 1000000000) := by
  have h := checkLog_sound (w := (4847807181 / 24847807181)) (n := 12)
    (lo := (49408387 / 125000000)) (hi := (395267097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14847807181 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14847807181 / 10000000000) = 1/(10000000000 / 14847807181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6296 : Bounds (49408387 / 125000000) (395267097 / 1000000000) (Real.log (14847807181 / 10000000000)) := by
  have h := reflection_log_6296_neg
  have he : Real.log (14847807181 / 10000000000) = -Real.log (10000000000 / 14847807181) := by
    rw [show ((14847807181 / 10000000000) : ℝ) = ((10000000000 / 14847807181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6297_neg : (79095003 / 200000000) ≤ -Real.log (500000000000 / 742544731611) ∧
    -Real.log (500000000000 / 742544731611) ≤ (49434377 / 125000000) := by
  have h := checkLog_sound (w := (242544731611 / 1242544731611)) (n := 12)
    (lo := (79095003 / 200000000)) (hi := (49434377 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742544731611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742544731611 / 500000000000) = 1/(500000000000 / 742544731611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6297 : Bounds (79095003 / 200000000) (49434377 / 125000000) (Real.log (742544731611 / 500000000000)) := by
  have h := reflection_log_6297_neg
  have he : Real.log (742544731611 / 500000000000) = -Real.log (500000000000 / 742544731611) := by
    rw [show ((742544731611 / 500000000000) : ℝ) = ((500000000000 / 742544731611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6298_neg : (178397199 / 1000000000) ≤ -Real.log (10000 / 11953) ∧
    -Real.log (10000 / 11953) ≤ (445993 / 2500000) := by
  have h := checkLog_sound (w := (1953 / 21953)) (n := 12)
    (lo := (178397199 / 1000000000)) (hi := (445993 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11953 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11953 / 10000) = 1/(10000 / 11953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6298 : Bounds (178397199 / 1000000000) (445993 / 2500000) (Real.log (11953 / 10000)) := by
  have h := reflection_log_6298_neg
  have he : Real.log (11953 / 10000) = -Real.log (10000 / 11953) := by
    rw [show ((11953 / 10000) : ℝ) = ((10000 / 11953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6299_neg : (217285741 / 1000000000) ≤ -Real.log (8047 / 10000) ∧
    -Real.log (8047 / 10000) ≤ (108642871 / 500000000) := by
  have h := checkLog_sound (w := (1953 / 18047)) (n := 12)
    (lo := (217285741 / 1000000000)) (hi := (108642871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8047) = 1/(8047 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6299 : Bounds (-108642871 / 500000000) (-217285741 / 1000000000) (Real.log (8047 / 10000)) := by
  have h := reflection_log_6299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6300_neg : (2441 / 12500000) ≤ -Real.log (10000000 / 10001953) ∧
    -Real.log (10000000 / 10001953) ≤ (195281 / 1000000000) := by
  have h := checkLog_sound (w := (1953 / 20001953)) (n := 12)
    (lo := (2441 / 12500000)) (hi := (195281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001953 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001953 / 10000000) = 1/(10000000 / 10001953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6300 : Bounds (2441 / 12500000) (195281 / 1000000000) (Real.log (10001953 / 10000000)) := by
  have h := reflection_log_6300_neg
  have he : Real.log (10001953 / 10000000) = -Real.log (10000000 / 10001953) := by
    rw [show ((10001953 / 10000000) : ℝ) = ((10000000 / 10001953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6301_neg : (195319 / 1000000000) ≤ -Real.log (9998047 / 10000000) ∧
    -Real.log (9998047 / 10000000) ≤ (4883 / 25000000) := by
  have h := checkLog_sound (w := (1953 / 19998047)) (n := 12)
    (lo := (195319 / 1000000000)) (hi := (4883 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998047) = 1/(9998047 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6301 : Bounds (-4883 / 25000000) (-195319 / 1000000000) (Real.log (9998047 / 10000000)) := by
  have h := reflection_log_6301_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6302_neg : (46827587 / 500000000) ≤ -Real.log (1000000 / 1098181) ∧
    -Real.log (1000000 / 1098181) ≤ (3746207 / 40000000) := by
  have h := checkLog_sound (w := (98181 / 2098181)) (n := 12)
    (lo := (46827587 / 500000000)) (hi := (3746207 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098181 / 1000000) = 1/(1000000 / 1098181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6302 : Bounds (46827587 / 500000000) (3746207 / 40000000) (Real.log (1098181 / 1000000)) := by
  have h := reflection_log_6302_neg
  have he : Real.log (1098181 / 1000000) = -Real.log (1000000 / 1098181) := by
    rw [show ((1098181 / 1000000) : ℝ) = ((1000000 / 1098181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6303_neg : (25835361 / 250000000) ≤ -Real.log (901819 / 1000000) ∧
    -Real.log (901819 / 1000000) ≤ (20668289 / 200000000) := by
  have h := checkLog_sound (w := (98181 / 1901819)) (n := 12)
    (lo := (25835361 / 250000000)) (hi := (20668289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901819) = 1/(901819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6303 : Bounds (-20668289 / 200000000) (-25835361 / 250000000) (Real.log (901819 / 1000000)) := by
  have h := reflection_log_6303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6304_neg : (23469789 / 250000000) ≤ -Real.log (1000000 / 1098427) ∧
    -Real.log (1000000 / 1098427) ≤ (93879157 / 1000000000) := by
  have h := checkLog_sound (w := (98427 / 2098427)) (n := 12)
    (lo := (23469789 / 250000000)) (hi := (93879157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098427 / 1000000) = 1/(1000000 / 1098427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6304 : Bounds (23469789 / 250000000) (93879157 / 1000000000) (Real.log (1098427 / 1000000)) := by
  have h := reflection_log_6304_neg
  have he : Real.log (1098427 / 1000000) = -Real.log (1000000 / 1098427) := by
    rw [show ((1098427 / 1000000) : ℝ) = ((1000000 / 1098427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6305_neg : (103614263 / 1000000000) ≤ -Real.log (901573 / 1000000) ∧
    -Real.log (901573 / 1000000) ≤ (12951783 / 125000000) := by
  have h := checkLog_sound (w := (98427 / 1901573)) (n := 12)
    (lo := (103614263 / 1000000000)) (hi := (12951783 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901573) = 1/(901573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6305 : Bounds (-12951783 / 125000000) (-103614263 / 1000000000) (Real.log (901573 / 1000000)) := by
  have h := reflection_log_6305_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6306_neg : (9735107 / 1000000000) ≤ -Real.log (990312125671 / 1000000000000) ∧
    -Real.log (990312125671 / 1000000000000) ≤ (2433777 / 250000000) := by
  have h := checkLog_sound (w := (9687874329 / 1990312125671)) (n := 12)
    (lo := (9735107 / 1000000000)) (hi := (2433777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990312125671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990312125671) = 1/(990312125671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6306 : Bounds (-2433777 / 250000000) (-9735107 / 1000000000) (Real.log (990312125671 / 1000000000000)) := by
  have h := reflection_log_6306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6307_neg : (9686269 / 1000000000) ≤ -Real.log (990360491239 / 1000000000000) ∧
    -Real.log (990360491239 / 1000000000000) ≤ (968627 / 100000000) := by
  have h := checkLog_sound (w := (9639508761 / 1990360491239)) (n := 12)
    (lo := (9686269 / 1000000000)) (hi := (968627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990360491239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990360491239) = 1/(990360491239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6307 : Bounds (-968627 / 100000000) (-9686269 / 1000000000) (Real.log (990360491239 / 1000000000000)) := by
  have h := reflection_log_6307_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6308_neg : (98498309 / 500000000) ≤ -Real.log (50000000000 / 60886996171) ∧
    -Real.log (50000000000 / 60886996171) ≤ (196996619 / 1000000000) := by
  have h := checkLog_sound (w := (10886996171 / 110886996171)) (n := 12)
    (lo := (98498309 / 500000000)) (hi := (196996619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60886996171 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60886996171 / 50000000000) = 1/(50000000000 / 60886996171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6308 : Bounds (98498309 / 500000000) (196996619 / 1000000000) (Real.log (60886996171 / 50000000000)) := by
  have h := reflection_log_6308_neg
  have he : Real.log (60886996171 / 50000000000) = -Real.log (50000000000 / 60886996171) := by
    rw [show ((60886996171 / 50000000000) : ℝ) = ((50000000000 / 60886996171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6309_neg : (197493419 / 1000000000) ≤ -Real.log (250000000000 / 304586262011) ∧
    -Real.log (250000000000 / 304586262011) ≤ (9874671 / 50000000) := by
  have h := checkLog_sound (w := (54586262011 / 554586262011)) (n := 12)
    (lo := (197493419 / 1000000000)) (hi := (9874671 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304586262011 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304586262011 / 250000000000) = 1/(250000000000 / 304586262011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6309 : Bounds (197493419 / 1000000000) (9874671 / 50000000) (Real.log (304586262011 / 250000000000)) := by
  have h := reflection_log_6309_neg
  have he : Real.log (304586262011 / 250000000000) = -Real.log (250000000000 / 304586262011) := by
    rw [show ((304586262011 / 250000000000) : ℝ) = ((250000000000 / 304586262011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6310_neg : (79095003 / 200000000) ≤ -Real.log (50000000000 / 74254473161) ∧
    -Real.log (50000000000 / 74254473161) ≤ (49434377 / 125000000) := by
  have h := checkLog_sound (w := (24254473161 / 124254473161)) (n := 12)
    (lo := (79095003 / 200000000)) (hi := (49434377 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74254473161 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74254473161 / 50000000000) = 1/(50000000000 / 74254473161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6310 : Bounds (79095003 / 200000000) (49434377 / 125000000) (Real.log (74254473161 / 50000000000)) := by
  have h := reflection_log_6310_neg
  have he : Real.log (74254473161 / 50000000000) = -Real.log (50000000000 / 74254473161) := by
    rw [show ((74254473161 / 50000000000) : ℝ) = ((50000000000 / 74254473161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6311_neg : (395682941 / 1000000000) ≤ -Real.log (250000000000 / 371349571269) ∧
    -Real.log (250000000000 / 371349571269) ≤ (197841471 / 500000000) := by
  have h := checkLog_sound (w := (121349571269 / 621349571269)) (n := 12)
    (lo := (395682941 / 1000000000)) (hi := (197841471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371349571269 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371349571269 / 250000000000) = 1/(250000000000 / 371349571269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6311 : Bounds (395682941 / 1000000000) (197841471 / 500000000) (Real.log (371349571269 / 250000000000)) := by
  have h := reflection_log_6311_neg
  have he : Real.log (371349571269 / 250000000000) = -Real.log (250000000000 / 371349571269) := by
    rw [show ((371349571269 / 250000000000) : ℝ) = ((250000000000 / 371349571269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6312_neg : (178480857 / 1000000000) ≤ -Real.log (5000 / 5977) ∧
    -Real.log (5000 / 5977) ≤ (89240429 / 500000000) := by
  have h := checkLog_sound (w := (977 / 10977)) (n := 12)
    (lo := (178480857 / 1000000000)) (hi := (89240429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5977 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5977 / 5000) = 1/(5000 / 5977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6312 : Bounds (178480857 / 1000000000) (89240429 / 500000000) (Real.log (5977 / 5000)) := by
  have h := reflection_log_6312_neg
  have he : Real.log (5977 / 5000) = -Real.log (5000 / 5977) := by
    rw [show ((5977 / 5000) : ℝ) = ((5000 / 5977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6313_neg : (217410019 / 1000000000) ≤ -Real.log (4023 / 5000) ∧
    -Real.log (4023 / 5000) ≤ (10870501 / 50000000) := by
  have h := checkLog_sound (w := (977 / 9023)) (n := 12)
    (lo := (217410019 / 1000000000)) (hi := (10870501 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4023) = 1/(4023 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6313 : Bounds (-10870501 / 50000000) (-217410019 / 1000000000) (Real.log (4023 / 5000)) := by
  have h := reflection_log_6313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6314_neg : (9769 / 50000000) ≤ -Real.log (5000000 / 5000977) ∧
    -Real.log (5000000 / 5000977) ≤ (195381 / 1000000000) := by
  have h := checkLog_sound (w := (977 / 10000977)) (n := 12)
    (lo := (9769 / 50000000)) (hi := (195381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000977 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000977 / 5000000) = 1/(5000000 / 5000977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6314 : Bounds (9769 / 50000000) (195381 / 1000000000) (Real.log (5000977 / 5000000)) := by
  have h := reflection_log_6314_neg
  have he : Real.log (5000977 / 5000000) = -Real.log (5000000 / 5000977) := by
    rw [show ((5000977 / 5000000) : ℝ) = ((5000000 / 5000977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6315_neg : (195419 / 1000000000) ≤ -Real.log (4999023 / 5000000) ∧
    -Real.log (4999023 / 5000000) ≤ (9771 / 50000000) := by
  have h := checkLog_sound (w := (977 / 9999023)) (n := 12)
    (lo := (195419 / 1000000000)) (hi := (9771 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999023) = 1/(4999023 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6315 : Bounds (-9771 / 50000000) (-195419 / 1000000000) (Real.log (4999023 / 5000000)) := by
  have h := reflection_log_6315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6316_neg : (46850807 / 500000000) ≤ -Real.log (125000 / 137279) ∧
    -Real.log (125000 / 137279) ≤ (18740323 / 200000000) := by
  have h := checkLog_sound (w := (12279 / 262279)) (n := 12)
    (lo := (46850807 / 500000000)) (hi := (18740323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137279 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137279 / 125000) = 1/(125000 / 137279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6316 : Bounds (46850807 / 500000000) (18740323 / 200000000) (Real.log (137279 / 125000)) := by
  have h := reflection_log_6316_neg
  have he : Real.log (137279 / 125000) = -Real.log (125000 / 137279) := by
    rw [show ((137279 / 125000) : ℝ) = ((125000 / 137279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6317_neg : (51698999 / 500000000) ≤ -Real.log (112721 / 125000) ∧
    -Real.log (112721 / 125000) ≤ (103397999 / 1000000000) := by
  have h := checkLog_sound (w := (12279 / 237721)) (n := 12)
    (lo := (51698999 / 500000000)) (hi := (103397999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112721) = 1/(112721 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6317 : Bounds (-103397999 / 1000000000) (-51698999 / 500000000) (Real.log (112721 / 125000)) := by
  have h := reflection_log_6317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6318_neg : (18785117 / 200000000) ≤ -Real.log (500000 / 549239) ∧
    -Real.log (500000 / 549239) ≤ (46962793 / 500000000) := by
  have h := checkLog_sound (w := (49239 / 1049239)) (n := 12)
    (lo := (18785117 / 200000000)) (hi := (46962793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549239 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549239 / 500000) = 1/(500000 / 549239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6318 : Bounds (18785117 / 200000000) (46962793 / 500000000) (Real.log (549239 / 500000)) := by
  have h := reflection_log_6318_neg
  have he : Real.log (549239 / 500000) = -Real.log (500000 / 549239) := by
    rw [show ((549239 / 500000) : ℝ) = ((500000 / 549239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6319_neg : (6479427 / 62500000) ≤ -Real.log (450761 / 500000) ∧
    -Real.log (450761 / 500000) ≤ (103670833 / 1000000000) := by
  have h := checkLog_sound (w := (49239 / 950761)) (n := 12)
    (lo := (6479427 / 62500000)) (hi := (103670833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450761) = 1/(450761 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6319 : Bounds (-103670833 / 1000000000) (-6479427 / 62500000) (Real.log (450761 / 500000)) := by
  have h := reflection_log_6319_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6320_neg : (9745247 / 1000000000) ≤ -Real.log (247575520879 / 250000000000) ∧
    -Real.log (247575520879 / 250000000000) ≤ (304539 / 31250000) := by
  have h := checkLog_sound (w := (2424479121 / 497575520879)) (n := 12)
    (lo := (9745247 / 1000000000)) (hi := (304539 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247575520879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247575520879) = 1/(247575520879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6320 : Bounds (-304539 / 31250000) (-9745247 / 1000000000) (Real.log (247575520879 / 250000000000)) := by
  have h := reflection_log_6320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6321_neg : (75753 / 7812500) ≤ -Real.log (15474226159 / 15625000000) ∧
    -Real.log (15474226159 / 15625000000) ≤ (1939277 / 200000000) := by
  have h := checkLog_sound (w := (150773841 / 31099226159)) (n := 12)
    (lo := (75753 / 7812500)) (hi := (1939277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15474226159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15474226159) = 1/(15474226159 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6321 : Bounds (-1939277 / 200000000) (-75753 / 7812500) (Real.log (15474226159 / 15625000000)) := by
  have h := reflection_log_6321_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6322_neg : (49274903 / 250000000) ≤ -Real.log (500000000000 / 608932674479) ∧
    -Real.log (500000000000 / 608932674479) ≤ (197099613 / 1000000000) := by
  have h := checkLog_sound (w := (108932674479 / 1108932674479)) (n := 12)
    (lo := (49274903 / 250000000)) (hi := (197099613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608932674479 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608932674479 / 500000000000) = 1/(500000000000 / 608932674479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6322 : Bounds (49274903 / 250000000) (197099613 / 1000000000) (Real.log (608932674479 / 500000000000)) := by
  have h := reflection_log_6322_neg
  have he : Real.log (608932674479 / 500000000000) = -Real.log (500000000000 / 608932674479) := by
    rw [show ((608932674479 / 500000000000) : ℝ) = ((500000000000 / 608932674479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6323_neg : (98798209 / 500000000) ≤ -Real.log (25000000000 / 30461763551) ∧
    -Real.log (25000000000 / 30461763551) ≤ (197596419 / 1000000000) := by
  have h := checkLog_sound (w := (5461763551 / 55461763551)) (n := 12)
    (lo := (98798209 / 500000000)) (hi := (197596419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30461763551 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30461763551 / 25000000000) = 1/(25000000000 / 30461763551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6323 : Bounds (98798209 / 500000000) (197596419 / 1000000000) (Real.log (30461763551 / 25000000000)) := by
  have h := reflection_log_6323_neg
  have he : Real.log (30461763551 / 25000000000) = -Real.log (25000000000 / 30461763551) := by
    rw [show ((30461763551 / 25000000000) : ℝ) = ((25000000000 / 30461763551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6324_neg : (395682941 / 1000000000) ≤ -Real.log (500000000000 / 742699142537) ∧
    -Real.log (500000000000 / 742699142537) ≤ (197841471 / 500000000) := by
  have h := checkLog_sound (w := (242699142537 / 1242699142537)) (n := 12)
    (lo := (395682941 / 1000000000)) (hi := (197841471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742699142537 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742699142537 / 500000000000) = 1/(500000000000 / 742699142537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6324 : Bounds (395682941 / 1000000000) (197841471 / 500000000) (Real.log (742699142537 / 500000000000)) := by
  have h := reflection_log_6324_neg
  have he : Real.log (742699142537 / 500000000000) = -Real.log (500000000000 / 742699142537) := by
    rw [show ((742699142537 / 500000000000) : ℝ) = ((500000000000 / 742699142537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6325_neg : (98972719 / 250000000) ≤ -Real.log (500000000000 / 742853591847) ∧
    -Real.log (500000000000 / 742853591847) ≤ (395890877 / 1000000000) := by
  have h := checkLog_sound (w := (242853591847 / 1242853591847)) (n := 12)
    (lo := (98972719 / 250000000)) (hi := (395890877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742853591847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742853591847 / 500000000000) = 1/(500000000000 / 742853591847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6325 : Bounds (98972719 / 250000000) (395890877 / 1000000000) (Real.log (742853591847 / 500000000000)) := by
  have h := reflection_log_6325_neg
  have he : Real.log (742853591847 / 500000000000) = -Real.log (500000000000 / 742853591847) := by
    rw [show ((742853591847 / 500000000000) : ℝ) = ((500000000000 / 742853591847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6326_neg : (178564507 / 1000000000) ≤ -Real.log (2000 / 2391) ∧
    -Real.log (2000 / 2391) ≤ (44641127 / 250000000) := by
  have h := checkLog_sound (w := (391 / 4391)) (n := 12)
    (lo := (178564507 / 1000000000)) (hi := (44641127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2391 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2391 / 2000) = 1/(2000 / 2391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6326 : Bounds (178564507 / 1000000000) (44641127 / 250000000) (Real.log (2391 / 2000)) := by
  have h := reflection_log_6326_neg
  have he : Real.log (2391 / 2000) = -Real.log (2000 / 2391) := by
    rw [show ((2391 / 2000) : ℝ) = ((2000 / 2391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6327_neg : (27191789 / 125000000) ≤ -Real.log (1609 / 2000) ∧
    -Real.log (1609 / 2000) ≤ (217534313 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 3609)) (n := 12)
    (lo := (27191789 / 125000000)) (hi := (217534313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1609) = 1/(1609 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6327 : Bounds (-217534313 / 1000000000) (-27191789 / 125000000) (Real.log (1609 / 2000)) := by
  have h := reflection_log_6327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6328_neg : (4887 / 25000000) ≤ -Real.log (2000000 / 2000391) ∧
    -Real.log (2000000 / 2000391) ≤ (195481 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 4000391)) (n := 12)
    (lo := (4887 / 25000000)) (hi := (195481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000391 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000391 / 2000000) = 1/(2000000 / 2000391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6328 : Bounds (4887 / 25000000) (195481 / 1000000000) (Real.log (2000391 / 2000000)) := by
  have h := reflection_log_6328_neg
  have he : Real.log (2000391 / 2000000) = -Real.log (2000000 / 2000391) := by
    rw [show ((2000391 / 2000000) : ℝ) = ((2000000 / 2000391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6329_neg : (195519 / 1000000000) ≤ -Real.log (1999609 / 2000000) ∧
    -Real.log (1999609 / 2000000) ≤ (611 / 3125000) := by
  have h := checkLog_sound (w := (391 / 3999609)) (n := 12)
    (lo := (195519 / 1000000000)) (hi := (611 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999609) = 1/(1999609 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6329 : Bounds (-611 / 3125000) (-195519 / 1000000000) (Real.log (1999609 / 2000000)) := by
  have h := reflection_log_6329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6330_neg : (93748051 / 1000000000) ≤ -Real.log (1000000 / 1098283) ∧
    -Real.log (1000000 / 1098283) ≤ (23437013 / 250000000) := by
  have h := checkLog_sound (w := (98283 / 2098283)) (n := 12)
    (lo := (93748051 / 1000000000)) (hi := (23437013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098283 / 1000000) = 1/(1000000 / 1098283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6330 : Bounds (93748051 / 1000000000) (23437013 / 250000000) (Real.log (1098283 / 1000000)) := by
  have h := reflection_log_6330_neg
  have he : Real.log (1098283 / 1000000) = -Real.log (1000000 / 1098283) := by
    rw [show ((1098283 / 1000000) : ℝ) = ((1000000 / 1098283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6331_neg : (20690911 / 200000000) ≤ -Real.log (901717 / 1000000) ∧
    -Real.log (901717 / 1000000) ≤ (25863639 / 250000000) := by
  have h := checkLog_sound (w := (98283 / 1901717)) (n := 12)
    (lo := (20690911 / 200000000)) (hi := (25863639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901717) = 1/(901717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6331 : Bounds (-25863639 / 250000000) (-20690911 / 200000000) (Real.log (901717 / 1000000)) := by
  have h := reflection_log_6331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6332_neg : (23493003 / 250000000) ≤ -Real.log (1000000 / 1098529) ∧
    -Real.log (1000000 / 1098529) ≤ (93972013 / 1000000000) := by
  have h := checkLog_sound (w := (98529 / 2098529)) (n := 12)
    (lo := (23493003 / 250000000)) (hi := (93972013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098529 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098529 / 1000000) = 1/(1000000 / 1098529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6332 : Bounds (23493003 / 250000000) (93972013 / 1000000000) (Real.log (1098529 / 1000000)) := by
  have h := reflection_log_6332_neg
  have he : Real.log (1098529 / 1000000) = -Real.log (1000000 / 1098529) := by
    rw [show ((1098529 / 1000000) : ℝ) = ((1000000 / 1098529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6333_neg : (20745481 / 200000000) ≤ -Real.log (901471 / 1000000) ∧
    -Real.log (901471 / 1000000) ≤ (51863703 / 500000000) := by
  have h := checkLog_sound (w := (98529 / 1901471)) (n := 12)
    (lo := (20745481 / 200000000)) (hi := (51863703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901471) = 1/(901471 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6333 : Bounds (-51863703 / 500000000) (-20745481 / 200000000) (Real.log (901471 / 1000000)) := by
  have h := reflection_log_6333_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6334_neg : (9755393 / 1000000000) ≤ -Real.log (990292036159 / 1000000000000) ∧
    -Real.log (990292036159 / 1000000000000) ≤ (4877697 / 500000000) := by
  have h := checkLog_sound (w := (9707963841 / 1990292036159)) (n := 12)
    (lo := (9755393 / 1000000000)) (hi := (4877697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990292036159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990292036159) = 1/(990292036159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6334 : Bounds (-4877697 / 500000000) (-9755393 / 1000000000) (Real.log (990292036159 / 1000000000000)) := by
  have h := reflection_log_6334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6335_neg : (1213313 / 125000000) ≤ -Real.log (990340451911 / 1000000000000) ∧
    -Real.log (990340451911 / 1000000000000) ≤ (1941301 / 200000000) := by
  have h := checkLog_sound (w := (9659548089 / 1990340451911)) (n := 12)
    (lo := (1213313 / 125000000)) (hi := (1941301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990340451911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990340451911) = 1/(990340451911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6335 : Bounds (-1941301 / 200000000) (-1213313 / 125000000) (Real.log (990340451911 / 1000000000000)) := by
  have h := reflection_log_6335_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


