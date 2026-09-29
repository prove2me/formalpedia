-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0247
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0247
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:34:12.753698+00:00
-- url     : https://prove2.me/theorems/f0eeaea6-66db-4618-8f0a-5327fd93bdc0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0247` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0247` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0247` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0247 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0247.lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0247 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15808_neg : (7417980717 / 1000000000) ≤ -Real.log (250000000000 / 416416666666667) ∧
    -Real.log (250000000000 / 416416666666667) ≤ (927247591 / 125000000) := by
  have h := checkLog_sound (w := (160416666666667 / 672416666666667)) (n := 12)
    (lo := (486508917 / 1000000000)) (hi := (243254459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416416666666667 / 256000000000000) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(416416666666667 / 256000000000000) = 1/(250000000000 / 416416666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15808 : Bounds (7417980717 / 1000000000) (927247591 / 125000000) (Real.log (416416666666667 / 250000000000)) := by
  have h := reflection_log_15808_neg
  have he : Real.log (416416666666667 / 250000000000) = -Real.log (250000000000 / 416416666666667) := by
    rw [show ((416416666666667 / 250000000000) : ℝ) = ((250000000000 / 416416666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15809_neg : (138529411 / 200000000) ≤ -Real.log (1000 / 1999) ∧
    -Real.log (1000 / 1999) ≤ (43290441 / 62500000) := by
  have h := checkLog_sound (w := (999 / 2999)) (n := 12)
    (lo := (138529411 / 200000000)) (hi := (43290441 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1999 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1999 / 1000) = 1/(1000 / 1999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15809 : Bounds (138529411 / 200000000) (43290441 / 62500000) (Real.log (1999 / 1000)) := by
  have h := reflection_log_15809_neg
  have he : Real.log (1999 / 1000) = -Real.log (1000 / 1999) := by
    rw [show ((1999 / 1000) : ℝ) = ((1000 / 1999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15810_neg : (6907755273 / 1000000000) ≤ -Real.log (1 / 1000) ∧
    -Real.log (1 / 1000) ≤ (6907755283 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(125 / 64) = 1/(1 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15810 : Bounds (-6907755283 / 1000000000) (-6907755273 / 1000000000) (Real.log (1 / 1000)) := by
  have h := reflection_log_15810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15811_neg : (998501 / 1000000000) ≤ -Real.log (1000000 / 1000999) ∧
    -Real.log (1000000 / 1000999) ≤ (499251 / 500000000) := by
  have h := checkLog_sound (w := (999 / 2000999)) (n := 12)
    (lo := (998501 / 1000000000)) (hi := (499251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000999 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000999 / 1000000) = 1/(1000000 / 1000999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15811 : Bounds (998501 / 1000000000) (499251 / 500000000) (Real.log (1000999 / 1000000)) := by
  have h := reflection_log_15811_neg
  have he : Real.log (1000999 / 1000000) = -Real.log (1000000 / 1000999) := by
    rw [show ((1000999 / 1000000) : ℝ) = ((1000000 / 1000999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15812_neg : (999499 / 1000000000) ≤ -Real.log (999001 / 1000000) ∧
    -Real.log (999001 / 1000000) ≤ (1999 / 2000000) := by
  have h := checkLog_sound (w := (999 / 1999001)) (n := 12)
    (lo := (999499 / 1000000000)) (hi := (1999 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999001) = 1/(999001 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15812 : Bounds (-1999 / 2000000) (-999499 / 1000000000) (Real.log (999001 / 1000000)) := by
  have h := reflection_log_15812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15813_neg : (252205547 / 500000000) ≤ -Real.log (100000 / 165601) ∧
    -Real.log (100000 / 165601) ≤ (100882219 / 200000000) := by
  have h := checkLog_sound (w := (65601 / 265601)) (n := 12)
    (lo := (252205547 / 500000000)) (hi := (100882219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165601 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165601 / 100000) = 1/(100000 / 165601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15813 : Bounds (252205547 / 500000000) (100882219 / 200000000) (Real.log (165601 / 100000)) := by
  have h := reflection_log_15813_neg
  have he : Real.log (165601 / 100000) = -Real.log (100000 / 165601) := by
    rw [show ((165601 / 100000) : ℝ) = ((100000 / 165601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15814_neg : (1067142691 / 1000000000) ≤ -Real.log (34399 / 100000) ∧
    -Real.log (34399 / 100000) ≤ (1067142693 / 1000000000) := by
  have h := checkLog_sound (w := (15601 / 84399)) (n := 12)
    (lo := (373995511 / 1000000000)) (hi := (46749439 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 34399) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 34399) = 1/(34399 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15814 : Bounds (-1067142693 / 1000000000) (-1067142691 / 1000000000) (Real.log (34399 / 100000)) := by
  have h := reflection_log_15814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15815_neg : (252511309 / 500000000) ≤ -Real.log (1000000 / 1657023) ∧
    -Real.log (1000000 / 1657023) ≤ (505022619 / 1000000000) := by
  have h := checkLog_sound (w := (657023 / 2657023)) (n := 12)
    (lo := (252511309 / 500000000)) (hi := (505022619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1657023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1657023 / 1000000) = 1/(1000000 / 1657023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15815 : Bounds (252511309 / 500000000) (505022619 / 1000000000) (Real.log (1657023 / 1000000)) := by
  have h := reflection_log_15815_neg
  have he : Real.log (1657023 / 1000000) = -Real.log (1000000 / 1657023) := by
    rw [show ((1657023 / 1000000) : ℝ) = ((1000000 / 1657023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15816_neg : (66880743 / 62500000) ≤ -Real.log (342977 / 1000000) ∧
    -Real.log (342977 / 1000000) ≤ (107009189 / 100000000) := by
  have h := checkLog_sound (w := (157023 / 842977)) (n := 12)
    (lo := (94236177 / 250000000)) (hi := (376944709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342977) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 342977) = 1/(342977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15816 : Bounds (-107009189 / 100000000) (-66880743 / 62500000) (Real.log (342977 / 1000000)) := by
  have h := reflection_log_15816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15817_neg : (56506927 / 100000000) ≤ -Real.log (568320777471 / 1000000000000) ∧
    -Real.log (568320777471 / 1000000000000) ≤ (565069271 / 1000000000) := by
  have h := checkLog_sound (w := (431679222529 / 1568320777471)) (n := 12)
    (lo := (56506927 / 100000000)) (hi := (565069271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 568320777471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 568320777471) = 1/(568320777471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15817 : Bounds (-565069271 / 1000000000) (-56506927 / 100000000) (Real.log (568320777471 / 1000000000000)) := by
  have h := reflection_log_15817_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15818_neg : (562731597 / 1000000000) ≤ -Real.log (5696508799 / 10000000000) ∧
    -Real.log (5696508799 / 10000000000) ≤ (281365799 / 500000000) := by
  have h := checkLog_sound (w := (4303491201 / 15696508799)) (n := 12)
    (lo := (562731597 / 1000000000)) (hi := (281365799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5696508799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5696508799) = 1/(5696508799 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15818 : Bounds (-281365799 / 500000000) (-562731597 / 1000000000) (Real.log (5696508799 / 10000000000)) := by
  have h := reflection_log_15818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15819_neg : (314310757 / 200000000) ≤ -Real.log (25000000000 / 120353062589) ∧
    -Real.log (25000000000 / 120353062589) ≤ (392888447 / 250000000) := by
  have h := checkLog_sound (w := (20353062589 / 220353062589)) (n := 12)
    (lo := (7410377 / 40000000)) (hi := (92629713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120353062589 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(120353062589 / 100000000000) = 1/(25000000000 / 120353062589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15819 : Bounds (314310757 / 200000000) (392888447 / 250000000) (Real.log (120353062589 / 25000000000)) := by
  have h := reflection_log_15819_neg
  have he : Real.log (120353062589 / 25000000000) = -Real.log (25000000000 / 120353062589) := by
    rw [show ((120353062589 / 25000000000) : ℝ) = ((25000000000 / 120353062589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15820_neg : (1575114507 / 1000000000) ≤ -Real.log (500000000000 / 2415647404929) ∧
    -Real.log (500000000000 / 2415647404929) ≤ (157511451 / 100000000) := by
  have h := checkLog_sound (w := (415647404929 / 4415647404929)) (n := 12)
    (lo := (188820147 / 1000000000)) (hi := (47205037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2415647404929 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2415647404929 / 2000000000000) = 1/(500000000000 / 2415647404929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15820 : Bounds (1575114507 / 1000000000) (157511451 / 100000000) (Real.log (2415647404929 / 500000000000)) := by
  have h := reflection_log_15820_neg
  have he : Real.log (2415647404929 / 500000000000) = -Real.log (500000000000 / 2415647404929) := by
    rw [show ((2415647404929 / 500000000000) : ℝ) = ((500000000000 / 2415647404929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15821_neg : (7417980717 / 1000000000) ≤ -Real.log (500000000000 / 832833333333333) ∧
    -Real.log (500000000000 / 832833333333333) ≤ (927247591 / 125000000) := by
  have h := checkLog_sound (w := (320833333333333 / 1344833333333333)) (n := 12)
    (lo := (486508917 / 1000000000)) (hi := (243254459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832833333333333 / 512000000000000) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(832833333333333 / 512000000000000) = 1/(500000000000 / 832833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15821 : Bounds (7417980717 / 1000000000) (927247591 / 125000000) (Real.log (832833333333333 / 500000000000)) := by
  have h := reflection_log_15821_neg
  have he : Real.log (832833333333333 / 500000000000) = -Real.log (500000000000 / 832833333333333) := by
    rw [show ((832833333333333 / 500000000000) : ℝ) = ((500000000000 / 832833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15822_neg : (950050291 / 125000000) ≤ -Real.log (1 / 1999) ∧
    -Real.log (1 / 1999) ≤ (7600402339 / 1000000000) := by
  have h := checkLog_sound (w := (975 / 3023)) (n := 12)
    (lo := (20904079 / 31250000)) (hi := (668930529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1999 / 1024) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(1999 / 1024) = 1/(1 / 1999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15822 : Bounds (950050291 / 125000000) (7600402339 / 1000000000) (Real.log (1999 / 1)) := by
  have h := reflection_log_15822_neg
  have he : Real.log (1999 / 1) = -Real.log (1 / 1999) := by
    rw [show ((1999 / 1) : ℝ) = ((1 / 1999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


