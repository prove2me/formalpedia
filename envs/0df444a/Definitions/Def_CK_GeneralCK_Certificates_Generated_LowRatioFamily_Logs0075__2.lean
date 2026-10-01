-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0075__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0075__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:14:09.391359+00:00
-- url     : https://prove2.me/theorems/04c2f2b4-e6cb-4509-904b-24c1bbc3e766
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0075 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0076)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0075 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0076)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0075 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0076)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0075 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0076) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0075 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0076).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0075 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4800_neg : (42351291 / 250000000) ≤ -Real.log (5000 / 5923) ∧
    -Real.log (5000 / 5923) ≤ (33881033 / 200000000) := by
  have h := checkLog_sound (w := (923 / 10923)) (n := 12)
    (lo := (42351291 / 250000000)) (hi := (33881033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5923 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5923 / 5000) = 1/(5000 / 5923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4800 : Bounds (42351291 / 250000000) (33881033 / 200000000) (Real.log (5923 / 5000)) := by
  have h := reflection_log_4800_neg
  have he : Real.log (5923 / 5000) = -Real.log (5000 / 5923) := by
    rw [show ((5923 / 5000) : ℝ) = ((5000 / 5923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4801_neg : (25509561 / 125000000) ≤ -Real.log (4077 / 5000) ∧
    -Real.log (4077 / 5000) ≤ (204076489 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 9077)) (n := 12)
    (lo := (25509561 / 125000000)) (hi := (204076489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4077) = 1/(4077 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4801 : Bounds (-204076489 / 1000000000) (-25509561 / 125000000) (Real.log (4077 / 5000)) := by
  have h := reflection_log_4801_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4802_neg : (92291 / 500000000) ≤ -Real.log (5000000 / 5000923) ∧
    -Real.log (5000000 / 5000923) ≤ (184583 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 10000923)) (n := 12)
    (lo := (92291 / 500000000)) (hi := (184583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000923 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000923 / 5000000) = 1/(5000000 / 5000923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4802 : Bounds (92291 / 500000000) (184583 / 1000000000) (Real.log (5000923 / 5000000)) := by
  have h := reflection_log_4802_neg
  have he : Real.log (5000923 / 5000000) = -Real.log (5000000 / 5000923) := by
    rw [show ((5000923 / 5000000) : ℝ) = ((5000000 / 5000923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4803_neg : (184617 / 1000000000) ≤ -Real.log (4999077 / 5000000) ∧
    -Real.log (4999077 / 5000000) ≤ (92309 / 500000000) := by
  have h := checkLog_sound (w := (923 / 9999077)) (n := 12)
    (lo := (184617 / 1000000000)) (hi := (92309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999077) = 1/(4999077 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4803 : Bounds (-92309 / 500000000) (-184617 / 1000000000) (Real.log (4999077 / 5000000)) := by
  have h := reflection_log_4803_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4804_neg : (5542447 / 62500000) ≤ -Real.log (100000 / 109273) ∧
    -Real.log (100000 / 109273) ≤ (88679153 / 1000000000) := by
  have h := checkLog_sound (w := (9273 / 209273)) (n := 12)
    (lo := (5542447 / 62500000)) (hi := (88679153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109273 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109273 / 100000) = 1/(100000 / 109273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4804 : Bounds (5542447 / 62500000) (88679153 / 1000000000) (Real.log (109273 / 100000)) := by
  have h := reflection_log_4804_neg
  have he : Real.log (109273 / 100000) = -Real.log (100000 / 109273) := by
    rw [show ((109273 / 100000) : ℝ) = ((100000 / 109273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4805_neg : (24328797 / 250000000) ≤ -Real.log (90727 / 100000) ∧
    -Real.log (90727 / 100000) ≤ (97315189 / 1000000000) := by
  have h := checkLog_sound (w := (9273 / 190727)) (n := 12)
    (lo := (24328797 / 250000000)) (hi := (97315189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90727) = 1/(90727 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4805 : Bounds (-97315189 / 1000000000) (-24328797 / 250000000) (Real.log (90727 / 100000)) := by
  have h := reflection_log_4805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4806_neg : (44447093 / 500000000) ≤ -Real.log (200000 / 218593) ∧
    -Real.log (200000 / 218593) ≤ (88894187 / 1000000000) := by
  have h := checkLog_sound (w := (18593 / 418593)) (n := 12)
    (lo := (44447093 / 500000000)) (hi := (88894187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218593 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218593 / 200000) = 1/(200000 / 218593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4806 : Bounds (44447093 / 500000000) (88894187 / 1000000000) (Real.log (218593 / 200000)) := by
  have h := reflection_log_4806_neg
  have he : Real.log (218593 / 200000) = -Real.log (200000 / 218593) := by
    rw [show ((218593 / 200000) : ℝ) = ((200000 / 218593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4807_neg : (609839 / 6250000) ≤ -Real.log (181407 / 200000) ∧
    -Real.log (181407 / 200000) ≤ (97574241 / 1000000000) := by
  have h := checkLog_sound (w := (18593 / 381407)) (n := 12)
    (lo := (609839 / 6250000)) (hi := (97574241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181407) = 1/(181407 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4807 : Bounds (-97574241 / 1000000000) (-609839 / 6250000) (Real.log (181407 / 200000)) := by
  have h := reflection_log_4807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4808_neg : (4340027 / 500000000) ≤ -Real.log (39654300351 / 40000000000) ∧
    -Real.log (39654300351 / 40000000000) ≤ (1736011 / 200000000) := by
  have h := checkLog_sound (w := (345699649 / 79654300351)) (n := 12)
    (lo := (4340027 / 500000000)) (hi := (1736011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39654300351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39654300351) = 1/(39654300351 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4808 : Bounds (-1736011 / 200000000) (-4340027 / 500000000) (Real.log (39654300351 / 40000000000)) := by
  have h := reflection_log_4808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4809_neg : (2159009 / 250000000) ≤ -Real.log (9914011471 / 10000000000) ∧
    -Real.log (9914011471 / 10000000000) ≤ (8636037 / 1000000000) := by
  have h := checkLog_sound (w := (85988529 / 19914011471)) (n := 12)
    (lo := (2159009 / 250000000)) (hi := (8636037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9914011471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9914011471) = 1/(9914011471 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4809 : Bounds (-8636037 / 1000000000) (-2159009 / 250000000) (Real.log (9914011471 / 10000000000)) := by
  have h := reflection_log_4809_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4810_neg : (9299717 / 50000000) ≤ -Real.log (500000000000 / 602207722067) ∧
    -Real.log (500000000000 / 602207722067) ≤ (185994341 / 1000000000) := by
  have h := checkLog_sound (w := (102207722067 / 1102207722067)) (n := 12)
    (lo := (9299717 / 50000000)) (hi := (185994341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602207722067 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602207722067 / 500000000000) = 1/(500000000000 / 602207722067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4810 : Bounds (9299717 / 50000000) (185994341 / 1000000000) (Real.log (602207722067 / 500000000000)) := by
  have h := reflection_log_4810_neg
  have he : Real.log (602207722067 / 500000000000) = -Real.log (500000000000 / 602207722067) := by
    rw [show ((602207722067 / 500000000000) : ℝ) = ((500000000000 / 602207722067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4811_neg : (186468427 / 1000000000) ≤ -Real.log (500000000000 / 602493288573) ∧
    -Real.log (500000000000 / 602493288573) ≤ (46617107 / 250000000) := by
  have h := checkLog_sound (w := (102493288573 / 1102493288573)) (n := 12)
    (lo := (186468427 / 1000000000)) (hi := (46617107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602493288573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602493288573 / 500000000000) = 1/(500000000000 / 602493288573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4811 : Bounds (186468427 / 1000000000) (46617107 / 250000000) (Real.log (602493288573 / 500000000000)) := by
  have h := reflection_log_4811_neg
  have he : Real.log (602493288573 / 500000000000) = -Real.log (500000000000 / 602493288573) := by
    rw [show ((602493288573 / 500000000000) : ℝ) = ((500000000000 / 602493288573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4812_neg : (373274601 / 1000000000) ≤ -Real.log (500000000000 / 726241569589) ∧
    -Real.log (500000000000 / 726241569589) ≤ (186637301 / 500000000) := by
  have h := checkLog_sound (w := (226241569589 / 1226241569589)) (n := 12)
    (lo := (373274601 / 1000000000)) (hi := (186637301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726241569589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726241569589 / 500000000000) = 1/(500000000000 / 726241569589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4812 : Bounds (373274601 / 1000000000) (186637301 / 500000000) (Real.log (726241569589 / 500000000000)) := by
  have h := reflection_log_4812_neg
  have he : Real.log (726241569589 / 500000000000) = -Real.log (500000000000 / 726241569589) := by
    rw [show ((726241569589 / 500000000000) : ℝ) = ((500000000000 / 726241569589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4813_neg : (373481653 / 1000000000) ≤ -Real.log (500000000000 / 726391954869) ∧
    -Real.log (500000000000 / 726391954869) ≤ (186740827 / 500000000) := by
  have h := checkLog_sound (w := (226391954869 / 1226391954869)) (n := 12)
    (lo := (373481653 / 1000000000)) (hi := (186740827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726391954869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726391954869 / 500000000000) = 1/(500000000000 / 726391954869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4813 : Bounds (373481653 / 1000000000) (186740827 / 500000000) (Real.log (726391954869 / 500000000000)) := by
  have h := reflection_log_4813_neg
  have he : Real.log (726391954869 / 500000000000) = -Real.log (500000000000 / 726391954869) := by
    rw [show ((726391954869 / 500000000000) : ℝ) = ((500000000000 / 726391954869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4814_neg : (169489577 / 1000000000) ≤ -Real.log (10000 / 11847) ∧
    -Real.log (10000 / 11847) ≤ (84744789 / 500000000) := by
  have h := checkLog_sound (w := (1847 / 21847)) (n := 12)
    (lo := (169489577 / 1000000000)) (hi := (84744789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11847 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11847 / 10000) = 1/(10000 / 11847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4814 : Bounds (169489577 / 1000000000) (84744789 / 500000000) (Real.log (11847 / 10000)) := by
  have h := reflection_log_4814_neg
  have he : Real.log (11847 / 10000) = -Real.log (10000 / 11847) := by
    rw [show ((11847 / 10000) : ℝ) = ((10000 / 11847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4815_neg : (40839827 / 200000000) ≤ -Real.log (8153 / 10000) ∧
    -Real.log (8153 / 10000) ≤ (6381223 / 31250000) := by
  have h := checkLog_sound (w := (1847 / 18153)) (n := 12)
    (lo := (40839827 / 200000000)) (hi := (6381223 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8153) = 1/(8153 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4815 : Bounds (-6381223 / 31250000) (-40839827 / 200000000) (Real.log (8153 / 10000)) := by
  have h := reflection_log_4815_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4816_neg : (92341 / 500000000) ≤ -Real.log (10000000 / 10001847) ∧
    -Real.log (10000000 / 10001847) ≤ (184683 / 1000000000) := by
  have h := checkLog_sound (w := (1847 / 20001847)) (n := 12)
    (lo := (92341 / 500000000)) (hi := (184683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001847 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001847 / 10000000) = 1/(10000000 / 10001847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4816 : Bounds (92341 / 500000000) (184683 / 1000000000) (Real.log (10001847 / 10000000)) := by
  have h := reflection_log_4816_neg
  have he : Real.log (10001847 / 10000000) = -Real.log (10000000 / 10001847) := by
    rw [show ((10001847 / 10000000) : ℝ) = ((10000000 / 10001847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4817_neg : (184717 / 1000000000) ≤ -Real.log (9998153 / 10000000) ∧
    -Real.log (9998153 / 10000000) ≤ (92359 / 500000000) := by
  have h := checkLog_sound (w := (1847 / 19998153)) (n := 12)
    (lo := (184717 / 1000000000)) (hi := (92359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998153) = 1/(9998153 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4817 : Bounds (-92359 / 500000000) (-184717 / 1000000000) (Real.log (9998153 / 10000000)) := by
  have h := reflection_log_4817_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4818_neg : (88725823 / 1000000000) ≤ -Real.log (1000000 / 1092781) ∧
    -Real.log (1000000 / 1092781) ≤ (1386341 / 15625000) := by
  have h := checkLog_sound (w := (92781 / 2092781)) (n := 12)
    (lo := (88725823 / 1000000000)) (hi := (1386341 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092781 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092781 / 1000000) = 1/(1000000 / 1092781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4818 : Bounds (88725823 / 1000000000) (1386341 / 15625000) (Real.log (1092781 / 1000000)) := by
  have h := reflection_log_4818_neg
  have he : Real.log (1092781 / 1000000) = -Real.log (1000000 / 1092781) := by
    rw [show ((1092781 / 1000000) : ℝ) = ((1000000 / 1092781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4819_neg : (48685701 / 500000000) ≤ -Real.log (907219 / 1000000) ∧
    -Real.log (907219 / 1000000) ≤ (97371403 / 1000000000) := by
  have h := checkLog_sound (w := (92781 / 1907219)) (n := 12)
    (lo := (48685701 / 500000000)) (hi := (97371403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907219) = 1/(907219 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4819 : Bounds (-97371403 / 1000000000) (-48685701 / 500000000) (Real.log (907219 / 1000000)) := by
  have h := reflection_log_4819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4820_neg : (88940847 / 1000000000) ≤ -Real.log (125000 / 136627) ∧
    -Real.log (125000 / 136627) ≤ (5558803 / 62500000) := by
  have h := checkLog_sound (w := (11627 / 261627)) (n := 12)
    (lo := (88940847 / 1000000000)) (hi := (5558803 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136627 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136627 / 125000) = 1/(125000 / 136627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4820 : Bounds (88940847 / 1000000000) (5558803 / 62500000) (Real.log (136627 / 125000)) := by
  have h := reflection_log_4820_neg
  have he : Real.log (136627 / 125000) = -Real.log (125000 / 136627) := by
    rw [show ((136627 / 125000) : ℝ) = ((125000 / 136627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4821_neg : (97630469 / 1000000000) ≤ -Real.log (113373 / 125000) ∧
    -Real.log (113373 / 125000) ≤ (9763047 / 100000000) := by
  have h := checkLog_sound (w := (11627 / 238373)) (n := 12)
    (lo := (97630469 / 1000000000)) (hi := (9763047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113373) = 1/(113373 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4821 : Bounds (-9763047 / 100000000) (-97630469 / 1000000000) (Real.log (113373 / 125000)) := by
  have h := reflection_log_4821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4822_neg : (8689621 / 1000000000) ≤ -Real.log (15489812871 / 15625000000) ∧
    -Real.log (15489812871 / 15625000000) ≤ (4344811 / 500000000) := by
  have h := checkLog_sound (w := (135187129 / 31114812871)) (n := 12)
    (lo := (8689621 / 1000000000)) (hi := (4344811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15489812871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15489812871) = 1/(15489812871 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4822 : Bounds (-4344811 / 500000000) (-8689621 / 1000000000) (Real.log (15489812871 / 15625000000)) := by
  have h := reflection_log_4822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4823_neg : (8645579 / 1000000000) ≤ -Real.log (991391686039 / 1000000000000) ∧
    -Real.log (991391686039 / 1000000000000) ≤ (432279 / 50000000) := by
  have h := checkLog_sound (w := (8608313961 / 1991391686039)) (n := 12)
    (lo := (8645579 / 1000000000)) (hi := (432279 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991391686039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991391686039) = 1/(991391686039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4823 : Bounds (-432279 / 50000000) (-8645579 / 1000000000) (Real.log (991391686039 / 1000000000000)) := by
  have h := reflection_log_4823_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4824_neg : (7443889 / 40000000) ≤ -Real.log (100000000000 / 120453936701) ∧
    -Real.log (100000000000 / 120453936701) ≤ (93048613 / 500000000) := by
  have h := checkLog_sound (w := (20453936701 / 220453936701)) (n := 12)
    (lo := (7443889 / 40000000)) (hi := (93048613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120453936701 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120453936701 / 100000000000) = 1/(100000000000 / 120453936701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4824 : Bounds (7443889 / 40000000) (93048613 / 500000000) (Real.log (120453936701 / 100000000000)) := by
  have h := reflection_log_4824_neg
  have he : Real.log (120453936701 / 100000000000) = -Real.log (100000000000 / 120453936701) := by
    rw [show ((120453936701 / 100000000000) : ℝ) = ((100000000000 / 120453936701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4825_neg : (186571317 / 1000000000) ≤ -Real.log (250000000000 / 301277641061) ∧
    -Real.log (250000000000 / 301277641061) ≤ (93285659 / 500000000) := by
  have h := checkLog_sound (w := (51277641061 / 551277641061)) (n := 12)
    (lo := (186571317 / 1000000000)) (hi := (93285659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301277641061 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301277641061 / 250000000000) = 1/(250000000000 / 301277641061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4825 : Bounds (186571317 / 1000000000) (93285659 / 500000000) (Real.log (301277641061 / 250000000000)) := by
  have h := reflection_log_4825_neg
  have he : Real.log (301277641061 / 250000000000) = -Real.log (250000000000 / 301277641061) := by
    rw [show ((301277641061 / 250000000000) : ℝ) = ((250000000000 / 301277641061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4826_neg : (373481653 / 1000000000) ≤ -Real.log (125000000000 / 181597988717) ∧
    -Real.log (125000000000 / 181597988717) ≤ (186740827 / 500000000) := by
  have h := checkLog_sound (w := (56597988717 / 306597988717)) (n := 12)
    (lo := (373481653 / 1000000000)) (hi := (186740827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181597988717 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181597988717 / 125000000000) = 1/(125000000000 / 181597988717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4826 : Bounds (373481653 / 1000000000) (186740827 / 500000000) (Real.log (181597988717 / 125000000000)) := by
  have h := reflection_log_4826_neg
  have he : Real.log (181597988717 / 125000000000) = -Real.log (125000000000 / 181597988717) := by
    rw [show ((181597988717 / 125000000000) : ℝ) = ((125000000000 / 181597988717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4827_neg : (373688713 / 1000000000) ≤ -Real.log (6250000000 / 9081779713) ∧
    -Real.log (6250000000 / 9081779713) ≤ (186844357 / 500000000) := by
  have h := checkLog_sound (w := (2831779713 / 15331779713)) (n := 12)
    (lo := (373688713 / 1000000000)) (hi := (186844357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9081779713 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9081779713 / 6250000000) = 1/(6250000000 / 9081779713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4827 : Bounds (373688713 / 1000000000) (186844357 / 500000000) (Real.log (9081779713 / 6250000000)) := by
  have h := reflection_log_4827_neg
  have he : Real.log (9081779713 / 6250000000) = -Real.log (6250000000 / 9081779713) := by
    rw [show ((9081779713 / 6250000000) : ℝ) = ((6250000000 / 9081779713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4828_neg : (169573983 / 1000000000) ≤ -Real.log (1250 / 1481) ∧
    -Real.log (1250 / 1481) ≤ (5299187 / 31250000) := by
  have h := checkLog_sound (w := (231 / 2731)) (n := 12)
    (lo := (169573983 / 1000000000)) (hi := (5299187 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1481 / 1250) = 1/(1250 / 1481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4828 : Bounds (169573983 / 1000000000) (5299187 / 31250000) (Real.log (1481 / 1250)) := by
  have h := reflection_log_4828_neg
  have he : Real.log (1481 / 1250) = -Real.log (1250 / 1481) := by
    rw [show ((1481 / 1250) : ℝ) = ((1250 / 1481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4829_neg : (204321797 / 1000000000) ≤ -Real.log (1019 / 1250) ∧
    -Real.log (1019 / 1250) ≤ (102160899 / 500000000) := by
  have h := checkLog_sound (w := (231 / 2269)) (n := 12)
    (lo := (204321797 / 1000000000)) (hi := (102160899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1019) = 1/(1019 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4829 : Bounds (-102160899 / 500000000) (-204321797 / 1000000000) (Real.log (1019 / 1250)) := by
  have h := reflection_log_4829_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4830_neg : (92391 / 500000000) ≤ -Real.log (1250000 / 1250231) ∧
    -Real.log (1250000 / 1250231) ≤ (184783 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 2500231)) (n := 12)
    (lo := (92391 / 500000000)) (hi := (184783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250231 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250231 / 1250000) = 1/(1250000 / 1250231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4830 : Bounds (92391 / 500000000) (184783 / 1000000000) (Real.log (1250231 / 1250000)) := by
  have h := reflection_log_4830_neg
  have he : Real.log (1250231 / 1250000) = -Real.log (1250000 / 1250231) := by
    rw [show ((1250231 / 1250000) : ℝ) = ((1250000 / 1250231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4831_neg : (184817 / 1000000000) ≤ -Real.log (1249769 / 1250000) ∧
    -Real.log (1249769 / 1250000) ≤ (92409 / 500000000) := by
  have h := checkLog_sound (w := (231 / 2499769)) (n := 12)
    (lo := (184817 / 1000000000)) (hi := (92409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249769) = 1/(1249769 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4831 : Bounds (-92409 / 500000000) (-184817 / 1000000000) (Real.log (1249769 / 1250000)) := by
  have h := reflection_log_4831_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4832_neg : (88772491 / 1000000000) ≤ -Real.log (31250 / 34151) ∧
    -Real.log (31250 / 34151) ≤ (22193123 / 250000000) := by
  have h := checkLog_sound (w := (2901 / 65401)) (n := 12)
    (lo := (88772491 / 1000000000)) (hi := (22193123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34151 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34151 / 31250) = 1/(31250 / 34151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4832 : Bounds (88772491 / 1000000000) (22193123 / 250000000) (Real.log (34151 / 31250)) := by
  have h := reflection_log_4832_neg
  have he : Real.log (34151 / 31250) = -Real.log (31250 / 34151) := by
    rw [show ((34151 / 31250) : ℝ) = ((31250 / 34151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4833_neg : (97427619 / 1000000000) ≤ -Real.log (28349 / 31250) ∧
    -Real.log (28349 / 31250) ≤ (4871381 / 50000000) := by
  have h := checkLog_sound (w := (2901 / 59599)) (n := 12)
    (lo := (97427619 / 1000000000)) (hi := (4871381 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28349) = 1/(28349 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4833 : Bounds (-4871381 / 50000000) (-97427619 / 1000000000) (Real.log (28349 / 31250)) := by
  have h := reflection_log_4833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4834_neg : (44493753 / 500000000) ≤ -Real.log (1000000 / 1093067) ∧
    -Real.log (1000000 / 1093067) ≤ (88987507 / 1000000000) := by
  have h := checkLog_sound (w := (93067 / 2093067)) (n := 12)
    (lo := (44493753 / 500000000)) (hi := (88987507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093067 / 1000000) = 1/(1000000 / 1093067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4834 : Bounds (44493753 / 500000000) (88987507 / 1000000000) (Real.log (1093067 / 1000000)) := by
  have h := reflection_log_4834_neg
  have he : Real.log (1093067 / 1000000) = -Real.log (1000000 / 1093067) := by
    rw [show ((1093067 / 1000000) : ℝ) = ((1000000 / 1093067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4835_neg : (97686701 / 1000000000) ≤ -Real.log (906933 / 1000000) ∧
    -Real.log (906933 / 1000000) ≤ (48843351 / 500000000) := by
  have h := checkLog_sound (w := (93067 / 1906933)) (n := 12)
    (lo := (97686701 / 1000000000)) (hi := (48843351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906933) = 1/(906933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4835 : Bounds (-48843351 / 500000000) (-97686701 / 1000000000) (Real.log (906933 / 1000000)) := by
  have h := reflection_log_4835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4836_neg : (1739839 / 200000000) ≤ -Real.log (991338533511 / 1000000000000) ∧
    -Real.log (991338533511 / 1000000000000) ≤ (2174799 / 250000000) := by
  have h := checkLog_sound (w := (8661466489 / 1991338533511)) (n := 12)
    (lo := (1739839 / 200000000)) (hi := (2174799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991338533511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991338533511) = 1/(991338533511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4836 : Bounds (-2174799 / 250000000) (-1739839 / 200000000) (Real.log (991338533511 / 1000000000000)) := by
  have h := reflection_log_4836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4837_neg : (1081891 / 125000000) ≤ -Real.log (968146699 / 976562500) ∧
    -Real.log (968146699 / 976562500) ≤ (8655129 / 1000000000) := by
  have h := checkLog_sound (w := (8415801 / 1944709199)) (n := 12)
    (lo := (1081891 / 125000000)) (hi := (8655129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 968146699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 968146699) = 1/(968146699 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4837 : Bounds (-8655129 / 1000000000) (-1081891 / 125000000) (Real.log (968146699 / 976562500)) := by
  have h := reflection_log_4837_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4838_neg : (186200111 / 1000000000) ≤ -Real.log (50000000000 / 60233165191) ∧
    -Real.log (50000000000 / 60233165191) ≤ (11637507 / 62500000) := by
  have h := checkLog_sound (w := (10233165191 / 110233165191)) (n := 12)
    (lo := (186200111 / 1000000000)) (hi := (11637507 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60233165191 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60233165191 / 50000000000) = 1/(50000000000 / 60233165191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4838 : Bounds (186200111 / 1000000000) (11637507 / 62500000) (Real.log (60233165191 / 50000000000)) := by
  have h := reflection_log_4838_neg
  have he : Real.log (60233165191 / 50000000000) = -Real.log (50000000000 / 60233165191) := by
    rw [show ((60233165191 / 50000000000) : ℝ) = ((50000000000 / 60233165191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4839_neg : (186674207 / 1000000000) ≤ -Real.log (125000000000 / 150654320661) ∧
    -Real.log (125000000000 / 150654320661) ≤ (5833569 / 31250000) := by
  have h := checkLog_sound (w := (25654320661 / 275654320661)) (n := 12)
    (lo := (186674207 / 1000000000)) (hi := (5833569 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150654320661 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150654320661 / 125000000000) = 1/(125000000000 / 150654320661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4839 : Bounds (186674207 / 1000000000) (5833569 / 31250000) (Real.log (150654320661 / 125000000000)) := by
  have h := reflection_log_4839_neg
  have he : Real.log (150654320661 / 125000000000) = -Real.log (125000000000 / 150654320661) := by
    rw [show ((150654320661 / 125000000000) : ℝ) = ((125000000000 / 150654320661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4840_neg : (373688713 / 1000000000) ≤ -Real.log (500000000000 / 726542377039) ∧
    -Real.log (500000000000 / 726542377039) ≤ (186844357 / 500000000) := by
  have h := checkLog_sound (w := (226542377039 / 1226542377039)) (n := 12)
    (lo := (373688713 / 1000000000)) (hi := (186844357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726542377039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726542377039 / 500000000000) = 1/(500000000000 / 726542377039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4840 : Bounds (373688713 / 1000000000) (186844357 / 500000000) (Real.log (726542377039 / 500000000000)) := by
  have h := reflection_log_4840_neg
  have he : Real.log (726542377039 / 500000000000) = -Real.log (500000000000 / 726542377039) := by
    rw [show ((726542377039 / 500000000000) : ℝ) = ((500000000000 / 726542377039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4841_neg : (373895781 / 1000000000) ≤ -Real.log (250000000000 / 363346418057) ∧
    -Real.log (250000000000 / 363346418057) ≤ (186947891 / 500000000) := by
  have h := checkLog_sound (w := (113346418057 / 613346418057)) (n := 12)
    (lo := (373895781 / 1000000000)) (hi := (186947891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363346418057 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363346418057 / 250000000000) = 1/(250000000000 / 363346418057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4841 : Bounds (373895781 / 1000000000) (186947891 / 500000000) (Real.log (363346418057 / 250000000000)) := by
  have h := reflection_log_4841_neg
  have he : Real.log (363346418057 / 250000000000) = -Real.log (250000000000 / 363346418057) := by
    rw [show ((363346418057 / 250000000000) : ℝ) = ((250000000000 / 363346418057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4842_neg : (84829191 / 500000000) ≤ -Real.log (10000 / 11849) ∧
    -Real.log (10000 / 11849) ≤ (169658383 / 1000000000) := by
  have h := checkLog_sound (w := (1849 / 21849)) (n := 12)
    (lo := (84829191 / 500000000)) (hi := (169658383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11849 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11849 / 10000) = 1/(10000 / 11849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4842 : Bounds (84829191 / 500000000) (169658383 / 1000000000) (Real.log (11849 / 10000)) := by
  have h := reflection_log_4842_neg
  have he : Real.log (11849 / 10000) = -Real.log (10000 / 11849) := by
    rw [show ((11849 / 10000) : ℝ) = ((10000 / 11849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4843_neg : (204444473 / 1000000000) ≤ -Real.log (8151 / 10000) ∧
    -Real.log (8151 / 10000) ≤ (102222237 / 500000000) := by
  have h := checkLog_sound (w := (1849 / 18151)) (n := 12)
    (lo := (204444473 / 1000000000)) (hi := (102222237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8151) = 1/(8151 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4843 : Bounds (-102222237 / 500000000) (-204444473 / 1000000000) (Real.log (8151 / 10000)) := by
  have h := reflection_log_4843_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4844_neg : (92441 / 500000000) ≤ -Real.log (10000000 / 10001849) ∧
    -Real.log (10000000 / 10001849) ≤ (184883 / 1000000000) := by
  have h := checkLog_sound (w := (1849 / 20001849)) (n := 12)
    (lo := (92441 / 500000000)) (hi := (184883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001849 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001849 / 10000000) = 1/(10000000 / 10001849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4844 : Bounds (92441 / 500000000) (184883 / 1000000000) (Real.log (10001849 / 10000000)) := by
  have h := reflection_log_4844_neg
  have he : Real.log (10001849 / 10000000) = -Real.log (10000000 / 10001849) := by
    rw [show ((10001849 / 10000000) : ℝ) = ((10000000 / 10001849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4845_neg : (184917 / 1000000000) ≤ -Real.log (9998151 / 10000000) ∧
    -Real.log (9998151 / 10000000) ≤ (92459 / 500000000) := by
  have h := checkLog_sound (w := (1849 / 19998151)) (n := 12)
    (lo := (184917 / 1000000000)) (hi := (92459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998151) = 1/(9998151 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4845 : Bounds (-92459 / 500000000) (-184917 / 1000000000) (Real.log (9998151 / 10000000)) := by
  have h := reflection_log_4845_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4846_neg : (88818243 / 1000000000) ≤ -Real.log (500000 / 546441) ∧
    -Real.log (500000 / 546441) ≤ (22204561 / 250000000) := by
  have h := checkLog_sound (w := (46441 / 1046441)) (n := 12)
    (lo := (88818243 / 1000000000)) (hi := (22204561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546441 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546441 / 500000) = 1/(500000 / 546441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4846 : Bounds (88818243 / 1000000000) (22204561 / 250000000) (Real.log (546441 / 500000)) := by
  have h := reflection_log_4846_neg
  have he : Real.log (546441 / 500000) = -Real.log (500000 / 546441) := by
    rw [show ((546441 / 500000) : ℝ) = ((500000 / 546441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4847_neg : (48741369 / 500000000) ≤ -Real.log (453559 / 500000) ∧
    -Real.log (453559 / 500000) ≤ (97482739 / 1000000000) := by
  have h := checkLog_sound (w := (46441 / 953559)) (n := 12)
    (lo := (48741369 / 500000000)) (hi := (97482739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453559) = 1/(453559 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4847 : Bounds (-97482739 / 1000000000) (-48741369 / 500000000) (Real.log (453559 / 500000)) := by
  have h := reflection_log_4847_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4848_neg : (89034163 / 1000000000) ≤ -Real.log (500000 / 546559) ∧
    -Real.log (500000 / 546559) ≤ (22258541 / 250000000) := by
  have h := checkLog_sound (w := (46559 / 1046559)) (n := 12)
    (lo := (89034163 / 1000000000)) (hi := (22258541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546559 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546559 / 500000) = 1/(500000 / 546559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4848 : Bounds (89034163 / 1000000000) (22258541 / 250000000) (Real.log (546559 / 500000)) := by
  have h := reflection_log_4848_neg
  have he : Real.log (546559 / 500000) = -Real.log (500000 / 546559) := by
    rw [show ((546559 / 500000) : ℝ) = ((500000 / 546559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4849_neg : (12217867 / 125000000) ≤ -Real.log (453441 / 500000) ∧
    -Real.log (453441 / 500000) ≤ (97742937 / 1000000000) := by
  have h := checkLog_sound (w := (46559 / 953441)) (n := 12)
    (lo := (12217867 / 125000000)) (hi := (97742937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453441) = 1/(453441 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4849 : Bounds (-97742937 / 1000000000) (-12217867 / 125000000) (Real.log (453441 / 500000)) := by
  have h := reflection_log_4849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4850_neg : (8708773 / 1000000000) ≤ -Real.log (247832259519 / 250000000000) ∧
    -Real.log (247832259519 / 250000000000) ≤ (4354387 / 500000000) := by
  have h := checkLog_sound (w := (2167740481 / 497832259519)) (n := 12)
    (lo := (8708773 / 1000000000)) (hi := (4354387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247832259519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247832259519) = 1/(247832259519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4850 : Bounds (-4354387 / 500000000) (-8708773 / 1000000000) (Real.log (247832259519 / 250000000000)) := by
  have h := reflection_log_4850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4851_neg : (4332247 / 500000000) ≤ -Real.log (247843233519 / 250000000000) ∧
    -Real.log (247843233519 / 250000000000) ≤ (1732899 / 200000000) := by
  have h := checkLog_sound (w := (2156766481 / 497843233519)) (n := 12)
    (lo := (4332247 / 500000000)) (hi := (1732899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247843233519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247843233519) = 1/(247843233519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4851 : Bounds (-1732899 / 200000000) (-4332247 / 500000000) (Real.log (247843233519 / 250000000000)) := by
  have h := reflection_log_4851_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4852_neg : (186300981 / 1000000000) ≤ -Real.log (125000000000 / 150598103003) ∧
    -Real.log (125000000000 / 150598103003) ≤ (93150491 / 500000000) := by
  have h := checkLog_sound (w := (25598103003 / 275598103003)) (n := 12)
    (lo := (186300981 / 1000000000)) (hi := (93150491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150598103003 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150598103003 / 125000000000) = 1/(125000000000 / 150598103003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4852 : Bounds (186300981 / 1000000000) (93150491 / 500000000) (Real.log (150598103003 / 125000000000)) := by
  have h := reflection_log_4852_neg
  have he : Real.log (150598103003 / 125000000000) = -Real.log (125000000000 / 150598103003) := by
    rw [show ((150598103003 / 125000000000) : ℝ) = ((125000000000 / 150598103003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4853_neg : (186777099 / 1000000000) ≤ -Real.log (25000000000 / 30133964507) ∧
    -Real.log (25000000000 / 30133964507) ≤ (1867771 / 10000000) := by
  have h := checkLog_sound (w := (5133964507 / 55133964507)) (n := 12)
    (lo := (186777099 / 1000000000)) (hi := (1867771 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30133964507 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30133964507 / 25000000000) = 1/(25000000000 / 30133964507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4853 : Bounds (186777099 / 1000000000) (1867771 / 10000000) (Real.log (30133964507 / 25000000000)) := by
  have h := reflection_log_4853_neg
  have he : Real.log (30133964507 / 25000000000) = -Real.log (25000000000 / 30133964507) := by
    rw [show ((30133964507 / 25000000000) : ℝ) = ((25000000000 / 30133964507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4854_neg : (373895781 / 1000000000) ≤ -Real.log (500000000000 / 726692836113) ∧
    -Real.log (500000000000 / 726692836113) ≤ (186947891 / 500000000) := by
  have h := checkLog_sound (w := (226692836113 / 1226692836113)) (n := 12)
    (lo := (373895781 / 1000000000)) (hi := (186947891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726692836113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726692836113 / 500000000000) = 1/(500000000000 / 726692836113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4854 : Bounds (373895781 / 1000000000) (186947891 / 500000000) (Real.log (726692836113 / 500000000000)) := by
  have h := reflection_log_4854_neg
  have he : Real.log (726692836113 / 500000000000) = -Real.log (500000000000 / 726692836113) := by
    rw [show ((726692836113 / 500000000000) : ℝ) = ((500000000000 / 726692836113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4855_neg : (46762857 / 125000000) ≤ -Real.log (500000000000 / 726843332107) ∧
    -Real.log (500000000000 / 726843332107) ≤ (374102857 / 1000000000) := by
  have h := checkLog_sound (w := (226843332107 / 1226843332107)) (n := 12)
    (lo := (46762857 / 125000000)) (hi := (374102857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726843332107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726843332107 / 500000000000) = 1/(500000000000 / 726843332107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4855 : Bounds (46762857 / 125000000) (374102857 / 1000000000) (Real.log (726843332107 / 500000000000)) := by
  have h := reflection_log_4855_neg
  have he : Real.log (726843332107 / 500000000000) = -Real.log (500000000000 / 726843332107) := by
    rw [show ((726843332107 / 500000000000) : ℝ) = ((500000000000 / 726843332107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4856_neg : (84871387 / 500000000) ≤ -Real.log (200 / 237) ∧
    -Real.log (200 / 237) ≤ (6789711 / 40000000) := by
  have h := checkLog_sound (w := (37 / 437)) (n := 12)
    (lo := (84871387 / 500000000)) (hi := (6789711 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237 / 200) = 1/(200 / 237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4856 : Bounds (84871387 / 500000000) (6789711 / 40000000) (Real.log (237 / 200)) := by
  have h := reflection_log_4856_neg
  have he : Real.log (237 / 200) = -Real.log (200 / 237) := by
    rw [show ((237 / 200) : ℝ) = ((200 / 237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4857_neg : (40913433 / 200000000) ≤ -Real.log (163 / 200) ∧
    -Real.log (163 / 200) ≤ (102283583 / 500000000) := by
  have h := checkLog_sound (w := (37 / 363)) (n := 12)
    (lo := (40913433 / 200000000)) (hi := (102283583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 163) = 1/(163 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4857 : Bounds (-102283583 / 500000000) (-40913433 / 200000000) (Real.log (163 / 200)) := by
  have h := reflection_log_4857_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4858_neg : (92491 / 500000000) ≤ -Real.log (200000 / 200037) ∧
    -Real.log (200000 / 200037) ≤ (184983 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 400037)) (n := 12)
    (lo := (92491 / 500000000)) (hi := (184983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200037 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200037 / 200000) = 1/(200000 / 200037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4858 : Bounds (92491 / 500000000) (184983 / 1000000000) (Real.log (200037 / 200000)) := by
  have h := reflection_log_4858_neg
  have he : Real.log (200037 / 200000) = -Real.log (200000 / 200037) := by
    rw [show ((200037 / 200000) : ℝ) = ((200000 / 200037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4859_neg : (185017 / 1000000000) ≤ -Real.log (199963 / 200000) ∧
    -Real.log (199963 / 200000) ≤ (92509 / 500000000) := by
  have h := checkLog_sound (w := (37 / 399963)) (n := 12)
    (lo := (185017 / 1000000000)) (hi := (92509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199963) = 1/(199963 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4859 : Bounds (-92509 / 500000000) (-185017 / 1000000000) (Real.log (199963 / 200000)) := by
  have h := reflection_log_4859_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4860_neg : (22216227 / 250000000) ≤ -Real.log (1000000 / 1092933) ∧
    -Real.log (1000000 / 1092933) ≤ (88864909 / 1000000000) := by
  have h := checkLog_sound (w := (92933 / 2092933)) (n := 12)
    (lo := (22216227 / 250000000)) (hi := (88864909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092933 / 1000000) = 1/(1000000 / 1092933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4860 : Bounds (22216227 / 250000000) (88864909 / 1000000000) (Real.log (1092933 / 1000000)) := by
  have h := reflection_log_4860_neg
  have he : Real.log (1092933 / 1000000) = -Real.log (1000000 / 1092933) := by
    rw [show ((1092933 / 1000000) : ℝ) = ((1000000 / 1092933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4861_neg : (97538961 / 1000000000) ≤ -Real.log (907067 / 1000000) ∧
    -Real.log (907067 / 1000000) ≤ (48769481 / 500000000) := by
  have h := checkLog_sound (w := (92933 / 1907067)) (n := 12)
    (lo := (97538961 / 1000000000)) (hi := (48769481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907067) = 1/(907067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4861 : Bounds (-48769481 / 500000000) (-97538961 / 1000000000) (Real.log (907067 / 1000000)) := by
  have h := reflection_log_4861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4862_neg : (89080817 / 1000000000) ≤ -Real.log (1000000 / 1093169) ∧
    -Real.log (1000000 / 1093169) ≤ (44540409 / 500000000) := by
  have h := checkLog_sound (w := (93169 / 2093169)) (n := 12)
    (lo := (89080817 / 1000000000)) (hi := (44540409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093169 / 1000000) = 1/(1000000 / 1093169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4862 : Bounds (89080817 / 1000000000) (44540409 / 500000000) (Real.log (1093169 / 1000000)) := by
  have h := reflection_log_4862_neg
  have he : Real.log (1093169 / 1000000) = -Real.log (1000000 / 1093169) := by
    rw [show ((1093169 / 1000000) : ℝ) = ((1000000 / 1093169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4863_neg : (48899587 / 500000000) ≤ -Real.log (906831 / 1000000) ∧
    -Real.log (906831 / 1000000) ≤ (3911967 / 40000000) := by
  have h := checkLog_sound (w := (93169 / 1906831)) (n := 12)
    (lo := (48899587 / 500000000)) (hi := (3911967 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906831) = 1/(906831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4863 : Bounds (-3911967 / 40000000) (-48899587 / 500000000) (Real.log (906831 / 1000000)) := by
  have h := reflection_log_4863_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0076 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4864_neg : (8718357 / 1000000000) ≤ -Real.log (991319537439 / 1000000000000) ∧
    -Real.log (991319537439 / 1000000000000) ≤ (4359179 / 500000000) := by
  have h := checkLog_sound (w := (8680462561 / 1991319537439)) (n := 12)
    (lo := (8718357 / 1000000000)) (hi := (4359179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991319537439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991319537439) = 1/(991319537439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4864 : Bounds (-4359179 / 500000000) (-8718357 / 1000000000) (Real.log (991319537439 / 1000000000000)) := by
  have h := reflection_log_4864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4865_neg : (8674053 / 1000000000) ≤ -Real.log (991363457511 / 1000000000000) ∧
    -Real.log (991363457511 / 1000000000000) ≤ (4337027 / 500000000) := by
  have h := checkLog_sound (w := (8636542489 / 1991363457511)) (n := 12)
    (lo := (8674053 / 1000000000)) (hi := (4337027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991363457511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991363457511) = 1/(991363457511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4865 : Bounds (-4337027 / 500000000) (-8674053 / 1000000000) (Real.log (991363457511 / 1000000000000)) := by
  have h := reflection_log_4865_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4866_neg : (186403869 / 1000000000) ≤ -Real.log (500000000000 / 602454394217) ∧
    -Real.log (500000000000 / 602454394217) ≤ (18640387 / 100000000) := by
  have h := checkLog_sound (w := (102454394217 / 1102454394217)) (n := 12)
    (lo := (186403869 / 1000000000)) (hi := (18640387 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602454394217 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602454394217 / 500000000000) = 1/(500000000000 / 602454394217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4866 : Bounds (186403869 / 1000000000) (18640387 / 100000000) (Real.log (602454394217 / 500000000000)) := by
  have h := reflection_log_4866_neg
  have he : Real.log (602454394217 / 500000000000) = -Real.log (500000000000 / 602454394217) := by
    rw [show ((602454394217 / 500000000000) : ℝ) = ((500000000000 / 602454394217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4867_neg : (23359999 / 125000000) ≤ -Real.log (50000000000 / 60274130461) ∧
    -Real.log (50000000000 / 60274130461) ≤ (186879993 / 1000000000) := by
  have h := checkLog_sound (w := (10274130461 / 110274130461)) (n := 12)
    (lo := (23359999 / 125000000)) (hi := (186879993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60274130461 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60274130461 / 50000000000) = 1/(50000000000 / 60274130461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4867 : Bounds (23359999 / 125000000) (186879993 / 1000000000) (Real.log (60274130461 / 50000000000)) := by
  have h := reflection_log_4867_neg
  have he : Real.log (60274130461 / 50000000000) = -Real.log (50000000000 / 60274130461) := by
    rw [show ((60274130461 / 50000000000) : ℝ) = ((50000000000 / 60274130461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4868_neg : (46762857 / 125000000) ≤ -Real.log (250000000000 / 363421666053) ∧
    -Real.log (250000000000 / 363421666053) ≤ (374102857 / 1000000000) := by
  have h := checkLog_sound (w := (113421666053 / 613421666053)) (n := 12)
    (lo := (46762857 / 125000000)) (hi := (374102857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363421666053 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363421666053 / 250000000000) = 1/(250000000000 / 363421666053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4868 : Bounds (46762857 / 125000000) (374102857 / 1000000000) (Real.log (363421666053 / 250000000000)) := by
  have h := reflection_log_4868_neg
  have he : Real.log (363421666053 / 250000000000) = -Real.log (250000000000 / 363421666053) := by
    rw [show ((363421666053 / 250000000000) : ℝ) = ((250000000000 / 363421666053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4869_neg : (18715497 / 50000000) ≤ -Real.log (500000000000 / 726993865031) ∧
    -Real.log (500000000000 / 726993865031) ≤ (374309941 / 1000000000) := by
  have h := checkLog_sound (w := (226993865031 / 1226993865031)) (n := 12)
    (lo := (18715497 / 50000000)) (hi := (374309941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726993865031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726993865031 / 500000000000) = 1/(500000000000 / 726993865031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4869 : Bounds (18715497 / 50000000) (374309941 / 1000000000) (Real.log (726993865031 / 500000000000)) := by
  have h := reflection_log_4869_neg
  have he : Real.log (726993865031 / 500000000000) = -Real.log (500000000000 / 726993865031) := by
    rw [show ((726993865031 / 500000000000) : ℝ) = ((500000000000 / 726993865031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4870_neg : (169827159 / 1000000000) ≤ -Real.log (10000 / 11851) ∧
    -Real.log (10000 / 11851) ≤ (4245679 / 25000000) := by
  have h := checkLog_sound (w := (1851 / 21851)) (n := 12)
    (lo := (169827159 / 1000000000)) (hi := (4245679 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11851 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11851 / 10000) = 1/(10000 / 11851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4870 : Bounds (169827159 / 1000000000) (4245679 / 25000000) (Real.log (11851 / 10000)) := by
  have h := reflection_log_4870_neg
  have he : Real.log (11851 / 10000) = -Real.log (10000 / 11851) := by
    rw [show ((11851 / 10000) : ℝ) = ((10000 / 11851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4871_neg : (12793117 / 62500000) ≤ -Real.log (8149 / 10000) ∧
    -Real.log (8149 / 10000) ≤ (204689873 / 1000000000) := by
  have h := checkLog_sound (w := (1851 / 18149)) (n := 12)
    (lo := (12793117 / 62500000)) (hi := (204689873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8149) = 1/(8149 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4871 : Bounds (-204689873 / 1000000000) (-12793117 / 62500000) (Real.log (8149 / 10000)) := by
  have h := reflection_log_4871_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4872_neg : (92541 / 500000000) ≤ -Real.log (10000000 / 10001851) ∧
    -Real.log (10000000 / 10001851) ≤ (185083 / 1000000000) := by
  have h := checkLog_sound (w := (1851 / 20001851)) (n := 12)
    (lo := (92541 / 500000000)) (hi := (185083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001851 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001851 / 10000000) = 1/(10000000 / 10001851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4872 : Bounds (92541 / 500000000) (185083 / 1000000000) (Real.log (10001851 / 10000000)) := by
  have h := reflection_log_4872_neg
  have he : Real.log (10001851 / 10000000) = -Real.log (10000000 / 10001851) := by
    rw [show ((10001851 / 10000000) : ℝ) = ((10000000 / 10001851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4873_neg : (185117 / 1000000000) ≤ -Real.log (9998149 / 10000000) ∧
    -Real.log (9998149 / 10000000) ≤ (92559 / 500000000) := by
  have h := checkLog_sound (w := (1851 / 19998149)) (n := 12)
    (lo := (185117 / 1000000000)) (hi := (92559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998149) = 1/(9998149 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4873 : Bounds (-92559 / 500000000) (-185117 / 1000000000) (Real.log (9998149 / 10000000)) := by
  have h := reflection_log_4873_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4874_neg : (8891157 / 100000000) ≤ -Real.log (125000 / 136623) ∧
    -Real.log (125000 / 136623) ≤ (88911571 / 1000000000) := by
  have h := checkLog_sound (w := (11623 / 261623)) (n := 12)
    (lo := (8891157 / 100000000)) (hi := (88911571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136623 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136623 / 125000) = 1/(125000 / 136623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4874 : Bounds (8891157 / 100000000) (88911571 / 1000000000) (Real.log (136623 / 125000)) := by
  have h := reflection_log_4874_neg
  have he : Real.log (136623 / 125000) = -Real.log (125000 / 136623) := by
    rw [show ((136623 / 125000) : ℝ) = ((125000 / 136623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4875_neg : (24398797 / 250000000) ≤ -Real.log (113377 / 125000) ∧
    -Real.log (113377 / 125000) ≤ (97595189 / 1000000000) := by
  have h := checkLog_sound (w := (11623 / 238377)) (n := 12)
    (lo := (24398797 / 250000000)) (hi := (97595189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113377) = 1/(113377 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4875 : Bounds (-97595189 / 1000000000) (-24398797 / 250000000) (Real.log (113377 / 125000)) := by
  have h := reflection_log_4875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4876_neg : (89127469 / 1000000000) ≤ -Real.log (50000 / 54661) ∧
    -Real.log (50000 / 54661) ≤ (8912747 / 100000000) := by
  have h := checkLog_sound (w := (4661 / 104661)) (n := 12)
    (lo := (89127469 / 1000000000)) (hi := (8912747 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54661 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54661 / 50000) = 1/(50000 / 54661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4876 : Bounds (89127469 / 1000000000) (8912747 / 100000000) (Real.log (54661 / 50000)) := by
  have h := reflection_log_4876_neg
  have he : Real.log (54661 / 50000) = -Real.log (50000 / 54661) := by
    rw [show ((54661 / 50000) : ℝ) = ((50000 / 54661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4877_neg : (12231927 / 125000000) ≤ -Real.log (45339 / 50000) ∧
    -Real.log (45339 / 50000) ≤ (97855417 / 1000000000) := by
  have h := checkLog_sound (w := (4661 / 95339)) (n := 12)
    (lo := (12231927 / 125000000)) (hi := (97855417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45339) = 1/(45339 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4877 : Bounds (-97855417 / 1000000000) (-12231927 / 125000000) (Real.log (45339 / 50000)) := by
  have h := reflection_log_4877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4878_neg : (4363973 / 500000000) ≤ -Real.log (2478275079 / 2500000000) ∧
    -Real.log (2478275079 / 2500000000) ≤ (8727947 / 1000000000) := by
  have h := checkLog_sound (w := (21724921 / 4978275079)) (n := 12)
    (lo := (4363973 / 500000000)) (hi := (8727947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2478275079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2478275079) = 1/(2478275079 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4878 : Bounds (-8727947 / 1000000000) (-4363973 / 500000000) (Real.log (2478275079 / 2500000000)) := by
  have h := reflection_log_4878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4879_neg : (8683617 / 1000000000) ≤ -Real.log (15489905871 / 15625000000) ∧
    -Real.log (15489905871 / 15625000000) ≤ (4341809 / 500000000) := by
  have h := checkLog_sound (w := (135094129 / 31114905871)) (n := 12)
    (lo := (8683617 / 1000000000)) (hi := (4341809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15489905871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15489905871) = 1/(15489905871 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4879 : Bounds (-4341809 / 500000000) (-8683617 / 1000000000) (Real.log (15489905871 / 15625000000)) := by
  have h := reflection_log_4879_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4880_neg : (93253379 / 500000000) ≤ -Real.log (500000000000 / 602516383393) ∧
    -Real.log (500000000000 / 602516383393) ≤ (186506759 / 1000000000) := by
  have h := checkLog_sound (w := (102516383393 / 1102516383393)) (n := 12)
    (lo := (93253379 / 500000000)) (hi := (186506759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602516383393 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602516383393 / 500000000000) = 1/(500000000000 / 602516383393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4880 : Bounds (93253379 / 500000000) (186506759 / 1000000000) (Real.log (602516383393 / 500000000000)) := by
  have h := reflection_log_4880_neg
  have he : Real.log (602516383393 / 500000000000) = -Real.log (500000000000 / 602516383393) := by
    rw [show ((602516383393 / 500000000000) : ℝ) = ((500000000000 / 602516383393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4881_neg : (37396577 / 200000000) ≤ -Real.log (100000000000 / 120560665211) ∧
    -Real.log (100000000000 / 120560665211) ≤ (93491443 / 500000000) := by
  have h := checkLog_sound (w := (20560665211 / 220560665211)) (n := 12)
    (lo := (37396577 / 200000000)) (hi := (93491443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120560665211 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120560665211 / 100000000000) = 1/(100000000000 / 120560665211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4881 : Bounds (37396577 / 200000000) (93491443 / 500000000) (Real.log (120560665211 / 100000000000)) := by
  have h := reflection_log_4881_neg
  have he : Real.log (120560665211 / 100000000000) = -Real.log (100000000000 / 120560665211) := by
    rw [show ((120560665211 / 100000000000) : ℝ) = ((100000000000 / 120560665211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4882_neg : (18715497 / 50000000) ≤ -Real.log (50000000000 / 72699386503) ∧
    -Real.log (50000000000 / 72699386503) ≤ (374309941 / 1000000000) := by
  have h := checkLog_sound (w := (22699386503 / 122699386503)) (n := 12)
    (lo := (18715497 / 50000000)) (hi := (374309941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72699386503 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72699386503 / 50000000000) = 1/(50000000000 / 72699386503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4882 : Bounds (18715497 / 50000000) (374309941 / 1000000000) (Real.log (72699386503 / 50000000000)) := by
  have h := reflection_log_4882_neg
  have he : Real.log (72699386503 / 50000000000) = -Real.log (50000000000 / 72699386503) := by
    rw [show ((72699386503 / 50000000000) : ℝ) = ((50000000000 / 72699386503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4883_neg : (374517031 / 1000000000) ≤ -Real.log (5000000000 / 7271444349) ∧
    -Real.log (5000000000 / 7271444349) ≤ (46814629 / 125000000) := by
  have h := checkLog_sound (w := (2271444349 / 12271444349)) (n := 12)
    (lo := (374517031 / 1000000000)) (hi := (46814629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7271444349 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7271444349 / 5000000000) = 1/(5000000000 / 7271444349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4883 : Bounds (374517031 / 1000000000) (46814629 / 125000000) (Real.log (7271444349 / 5000000000)) := by
  have h := reflection_log_4883_neg
  have he : Real.log (7271444349 / 5000000000) = -Real.log (5000000000 / 7271444349) := by
    rw [show ((7271444349 / 5000000000) : ℝ) = ((5000000000 / 7271444349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4884_neg : (10619471 / 62500000) ≤ -Real.log (2500 / 2963) ∧
    -Real.log (2500 / 2963) ≤ (169911537 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 5463)) (n := 12)
    (lo := (10619471 / 62500000)) (hi := (169911537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2963 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2963 / 2500) = 1/(2500 / 2963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4884 : Bounds (10619471 / 62500000) (169911537 / 1000000000) (Real.log (2963 / 2500)) := by
  have h := reflection_log_4884_neg
  have he : Real.log (2963 / 2500) = -Real.log (2500 / 2963) := by
    rw [show ((2963 / 2500) : ℝ) = ((2500 / 2963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4885_neg : (102406297 / 500000000) ≤ -Real.log (2037 / 2500) ∧
    -Real.log (2037 / 2500) ≤ (40962519 / 200000000) := by
  have h := checkLog_sound (w := (463 / 4537)) (n := 12)
    (lo := (102406297 / 500000000)) (hi := (40962519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2037) = 1/(2037 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4885 : Bounds (-40962519 / 200000000) (-102406297 / 500000000) (Real.log (2037 / 2500)) := by
  have h := reflection_log_4885_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4886_neg : (92591 / 500000000) ≤ -Real.log (2500000 / 2500463) ∧
    -Real.log (2500000 / 2500463) ≤ (185183 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 5000463)) (n := 12)
    (lo := (92591 / 500000000)) (hi := (185183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500463 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500463 / 2500000) = 1/(2500000 / 2500463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4886 : Bounds (92591 / 500000000) (185183 / 1000000000) (Real.log (2500463 / 2500000)) := by
  have h := reflection_log_4886_neg
  have he : Real.log (2500463 / 2500000) = -Real.log (2500000 / 2500463) := by
    rw [show ((2500463 / 2500000) : ℝ) = ((2500000 / 2500463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4887_neg : (185217 / 1000000000) ≤ -Real.log (2499537 / 2500000) ∧
    -Real.log (2499537 / 2500000) ≤ (92609 / 500000000) := by
  have h := checkLog_sound (w := (463 / 4999537)) (n := 12)
    (lo := (185217 / 1000000000)) (hi := (92609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499537) = 1/(2499537 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4887 : Bounds (-92609 / 500000000) (-185217 / 1000000000) (Real.log (2499537 / 2500000)) := by
  have h := reflection_log_4887_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4888_neg : (8895823 / 100000000) ≤ -Real.log (200000 / 218607) ∧
    -Real.log (200000 / 218607) ≤ (88958231 / 1000000000) := by
  have h := checkLog_sound (w := (18607 / 418607)) (n := 12)
    (lo := (8895823 / 100000000)) (hi := (88958231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218607 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218607 / 200000) = 1/(200000 / 218607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4888 : Bounds (8895823 / 100000000) (88958231 / 1000000000) (Real.log (218607 / 200000)) := by
  have h := reflection_log_4888_neg
  have he : Real.log (218607 / 200000) = -Real.log (200000 / 218607) := by
    rw [show ((218607 / 200000) : ℝ) = ((200000 / 218607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4889_neg : (48825709 / 500000000) ≤ -Real.log (181393 / 200000) ∧
    -Real.log (181393 / 200000) ≤ (97651419 / 1000000000) := by
  have h := checkLog_sound (w := (18607 / 381393)) (n := 12)
    (lo := (48825709 / 500000000)) (hi := (97651419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181393) = 1/(181393 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4889 : Bounds (-97651419 / 1000000000) (-48825709 / 500000000) (Real.log (181393 / 200000)) := by
  have h := reflection_log_4889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4890_neg : (89174119 / 1000000000) ≤ -Real.log (1000000 / 1093271) ∧
    -Real.log (1000000 / 1093271) ≤ (2229353 / 25000000) := by
  have h := checkLog_sound (w := (93271 / 2093271)) (n := 12)
    (lo := (89174119 / 1000000000)) (hi := (2229353 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093271 / 1000000) = 1/(1000000 / 1093271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4890 : Bounds (89174119 / 1000000000) (2229353 / 25000000) (Real.log (1093271 / 1000000)) := by
  have h := reflection_log_4890_neg
  have he : Real.log (1093271 / 1000000) = -Real.log (1000000 / 1093271) := by
    rw [show ((1093271 / 1000000) : ℝ) = ((1000000 / 1093271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4891_neg : (4895583 / 50000000) ≤ -Real.log (906729 / 1000000) ∧
    -Real.log (906729 / 1000000) ≤ (97911661 / 1000000000) := by
  have h := checkLog_sound (w := (93271 / 1906729)) (n := 12)
    (lo := (4895583 / 50000000)) (hi := (97911661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906729) = 1/(906729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4891 : Bounds (-97911661 / 1000000000) (-4895583 / 50000000) (Real.log (906729 / 1000000)) := by
  have h := reflection_log_4891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4892_neg : (436877 / 50000000) ≤ -Real.log (991300520559 / 1000000000000) ∧
    -Real.log (991300520559 / 1000000000000) ≤ (8737541 / 1000000000) := by
  have h := checkLog_sound (w := (8699479441 / 1991300520559)) (n := 12)
    (lo := (436877 / 50000000)) (hi := (8737541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991300520559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991300520559) = 1/(991300520559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4892 : Bounds (-8737541 / 1000000000) (-436877 / 50000000) (Real.log (991300520559 / 1000000000000)) := by
  have h := reflection_log_4892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4893_neg : (8693187 / 1000000000) ≤ -Real.log (39653779551 / 40000000000) ∧
    -Real.log (39653779551 / 40000000000) ≤ (2173297 / 250000000) := by
  have h := checkLog_sound (w := (346220449 / 79653779551)) (n := 12)
    (lo := (8693187 / 1000000000)) (hi := (2173297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39653779551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39653779551) = 1/(39653779551 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4893 : Bounds (-2173297 / 250000000) (-8693187 / 1000000000) (Real.log (39653779551 / 40000000000)) := by
  have h := reflection_log_4893_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4894_neg : (186609649 / 1000000000) ≤ -Real.log (25000000000 / 30128918977) ∧
    -Real.log (25000000000 / 30128918977) ≤ (3732193 / 20000000) := by
  have h := checkLog_sound (w := (5128918977 / 55128918977)) (n := 12)
    (lo := (186609649 / 1000000000)) (hi := (3732193 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30128918977 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30128918977 / 25000000000) = 1/(25000000000 / 30128918977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4894 : Bounds (186609649 / 1000000000) (3732193 / 20000000) (Real.log (30128918977 / 25000000000)) := by
  have h := reflection_log_4894_neg
  have he : Real.log (30128918977 / 25000000000) = -Real.log (25000000000 / 30128918977) := by
    rw [show ((30128918977 / 25000000000) : ℝ) = ((25000000000 / 30128918977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4895_neg : (9354289 / 50000000) ≤ -Real.log (250000000000 / 301432677239) ∧
    -Real.log (250000000000 / 301432677239) ≤ (187085781 / 1000000000) := by
  have h := checkLog_sound (w := (51432677239 / 551432677239)) (n := 12)
    (lo := (9354289 / 50000000)) (hi := (187085781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301432677239 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301432677239 / 250000000000) = 1/(250000000000 / 301432677239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4895 : Bounds (9354289 / 50000000) (187085781 / 1000000000) (Real.log (301432677239 / 250000000000)) := by
  have h := reflection_log_4895_neg
  have he : Real.log (301432677239 / 250000000000) = -Real.log (250000000000 / 301432677239) := by
    rw [show ((301432677239 / 250000000000) : ℝ) = ((250000000000 / 301432677239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4896_neg : (374517031 / 1000000000) ≤ -Real.log (500000000000 / 727144434899) ∧
    -Real.log (500000000000 / 727144434899) ≤ (46814629 / 125000000) := by
  have h := checkLog_sound (w := (227144434899 / 1227144434899)) (n := 12)
    (lo := (374517031 / 1000000000)) (hi := (46814629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727144434899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727144434899 / 500000000000) = 1/(500000000000 / 727144434899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4896 : Bounds (374517031 / 1000000000) (46814629 / 125000000) (Real.log (727144434899 / 500000000000)) := by
  have h := reflection_log_4896_neg
  have he : Real.log (727144434899 / 500000000000) = -Real.log (500000000000 / 727144434899) := by
    rw [show ((727144434899 / 500000000000) : ℝ) = ((500000000000 / 727144434899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4897_neg : (374724131 / 1000000000) ≤ -Real.log (500000000000 / 727295041729) ∧
    -Real.log (500000000000 / 727295041729) ≤ (93681033 / 250000000) := by
  have h := checkLog_sound (w := (227295041729 / 1227295041729)) (n := 12)
    (lo := (374724131 / 1000000000)) (hi := (93681033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727295041729 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727295041729 / 500000000000) = 1/(500000000000 / 727295041729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4897 : Bounds (374724131 / 1000000000) (93681033 / 250000000) (Real.log (727295041729 / 500000000000)) := by
  have h := reflection_log_4897_neg
  have he : Real.log (727295041729 / 500000000000) = -Real.log (500000000000 / 727295041729) := by
    rw [show ((727295041729 / 500000000000) : ℝ) = ((500000000000 / 727295041729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4898_neg : (169995907 / 1000000000) ≤ -Real.log (10000 / 11853) ∧
    -Real.log (10000 / 11853) ≤ (42498977 / 250000000) := by
  have h := checkLog_sound (w := (1853 / 21853)) (n := 12)
    (lo := (169995907 / 1000000000)) (hi := (42498977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11853 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11853 / 10000) = 1/(10000 / 11853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4898 : Bounds (169995907 / 1000000000) (42498977 / 250000000) (Real.log (11853 / 10000)) := by
  have h := reflection_log_4898_neg
  have he : Real.log (11853 / 10000) = -Real.log (10000 / 11853) := by
    rw [show ((11853 / 10000) : ℝ) = ((10000 / 11853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4899_neg : (204935331 / 1000000000) ≤ -Real.log (8147 / 10000) ∧
    -Real.log (8147 / 10000) ≤ (51233833 / 250000000) := by
  have h := checkLog_sound (w := (1853 / 18147)) (n := 12)
    (lo := (204935331 / 1000000000)) (hi := (51233833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8147) = 1/(8147 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4899 : Bounds (-51233833 / 250000000) (-204935331 / 1000000000) (Real.log (8147 / 10000)) := by
  have h := reflection_log_4899_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4900_neg : (92641 / 500000000) ≤ -Real.log (10000000 / 10001853) ∧
    -Real.log (10000000 / 10001853) ≤ (185283 / 1000000000) := by
  have h := checkLog_sound (w := (1853 / 20001853)) (n := 12)
    (lo := (92641 / 500000000)) (hi := (185283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001853 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001853 / 10000000) = 1/(10000000 / 10001853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4900 : Bounds (92641 / 500000000) (185283 / 1000000000) (Real.log (10001853 / 10000000)) := by
  have h := reflection_log_4900_neg
  have he : Real.log (10001853 / 10000000) = -Real.log (10000000 / 10001853) := by
    rw [show ((10001853 / 10000000) : ℝ) = ((10000000 / 10001853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4901_neg : (185317 / 1000000000) ≤ -Real.log (9998147 / 10000000) ∧
    -Real.log (9998147 / 10000000) ≤ (92659 / 500000000) := by
  have h := checkLog_sound (w := (1853 / 19998147)) (n := 12)
    (lo := (185317 / 1000000000)) (hi := (92659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998147) = 1/(9998147 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4901 : Bounds (-92659 / 500000000) (-185317 / 1000000000) (Real.log (9998147 / 10000000)) := by
  have h := reflection_log_4901_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4902_neg : (11125611 / 125000000) ≤ -Real.log (500000 / 546543) ∧
    -Real.log (500000 / 546543) ≤ (89004889 / 1000000000) := by
  have h := checkLog_sound (w := (46543 / 1046543)) (n := 12)
    (lo := (11125611 / 125000000)) (hi := (89004889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546543 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546543 / 500000) = 1/(500000 / 546543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4902 : Bounds (11125611 / 125000000) (89004889 / 1000000000) (Real.log (546543 / 500000)) := by
  have h := reflection_log_4902_neg
  have he : Real.log (546543 / 500000) = -Real.log (500000 / 546543) := by
    rw [show ((546543 / 500000) : ℝ) = ((500000 / 546543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4903_neg : (97707651 / 1000000000) ≤ -Real.log (453457 / 500000) ∧
    -Real.log (453457 / 500000) ≤ (24426913 / 250000000) := by
  have h := checkLog_sound (w := (46543 / 953457)) (n := 12)
    (lo := (97707651 / 1000000000)) (hi := (24426913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453457) = 1/(453457 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4903 : Bounds (-24426913 / 250000000) (-97707651 / 1000000000) (Real.log (453457 / 500000)) := by
  have h := reflection_log_4903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4904_neg : (89220767 / 1000000000) ≤ -Real.log (500000 / 546661) ∧
    -Real.log (500000 / 546661) ≤ (2788149 / 31250000) := by
  have h := checkLog_sound (w := (46661 / 1046661)) (n := 12)
    (lo := (89220767 / 1000000000)) (hi := (2788149 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546661 / 500000) = 1/(500000 / 546661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4904 : Bounds (89220767 / 1000000000) (2788149 / 31250000) (Real.log (546661 / 500000)) := by
  have h := reflection_log_4904_neg
  have he : Real.log (546661 / 500000) = -Real.log (500000 / 546661) := by
    rw [show ((546661 / 500000) : ℝ) = ((500000 / 546661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4905_neg : (24491977 / 250000000) ≤ -Real.log (453339 / 500000) ∧
    -Real.log (453339 / 500000) ≤ (97967909 / 1000000000) := by
  have h := checkLog_sound (w := (46661 / 953339)) (n := 12)
    (lo := (24491977 / 250000000)) (hi := (97967909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453339) = 1/(453339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4905 : Bounds (-97967909 / 1000000000) (-24491977 / 250000000) (Real.log (453339 / 500000)) := by
  have h := reflection_log_4905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4906_neg : (437357 / 50000000) ≤ -Real.log (247822751079 / 250000000000) ∧
    -Real.log (247822751079 / 250000000000) ≤ (8747141 / 1000000000) := by
  have h := checkLog_sound (w := (2177248921 / 497822751079)) (n := 12)
    (lo := (437357 / 50000000)) (hi := (8747141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247822751079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247822751079) = 1/(247822751079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4906 : Bounds (-8747141 / 1000000000) (-437357 / 50000000) (Real.log (247822751079 / 250000000000)) := by
  have h := reflection_log_4906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4907_neg : (4351381 / 500000000) ≤ -Real.log (247833749151 / 250000000000) ∧
    -Real.log (247833749151 / 250000000000) ≤ (8702763 / 1000000000) := by
  have h := checkLog_sound (w := (2166250849 / 497833749151)) (n := 12)
    (lo := (4351381 / 500000000)) (hi := (8702763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247833749151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247833749151) = 1/(247833749151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4907 : Bounds (-8702763 / 1000000000) (-4351381 / 500000000) (Real.log (247833749151 / 250000000000)) := by
  have h := reflection_log_4907_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4908_neg : (9335627 / 50000000) ≤ -Real.log (25000000000 / 30132019133) ∧
    -Real.log (25000000000 / 30132019133) ≤ (186712541 / 1000000000) := by
  have h := checkLog_sound (w := (5132019133 / 55132019133)) (n := 12)
    (lo := (9335627 / 50000000)) (hi := (186712541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30132019133 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30132019133 / 25000000000) = 1/(25000000000 / 30132019133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4908 : Bounds (9335627 / 50000000) (186712541 / 1000000000) (Real.log (30132019133 / 25000000000)) := by
  have h := reflection_log_4908_neg
  have he : Real.log (30132019133 / 25000000000) = -Real.log (25000000000 / 30132019133) := by
    rw [show ((30132019133 / 25000000000) : ℝ) = ((25000000000 / 30132019133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4909_neg : (46797169 / 250000000) ≤ -Real.log (500000000000 / 602927389879) ∧
    -Real.log (500000000000 / 602927389879) ≤ (187188677 / 1000000000) := by
  have h := checkLog_sound (w := (102927389879 / 1102927389879)) (n := 12)
    (lo := (46797169 / 250000000)) (hi := (187188677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602927389879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602927389879 / 500000000000) = 1/(500000000000 / 602927389879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4909 : Bounds (46797169 / 250000000) (187188677 / 1000000000) (Real.log (602927389879 / 500000000000)) := by
  have h := reflection_log_4909_neg
  have he : Real.log (602927389879 / 500000000000) = -Real.log (500000000000 / 602927389879) := by
    rw [show ((602927389879 / 500000000000) : ℝ) = ((500000000000 / 602927389879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4910_neg : (374724131 / 1000000000) ≤ -Real.log (7812500000 / 11363985027) ∧
    -Real.log (7812500000 / 11363985027) ≤ (93681033 / 250000000) := by
  have h := checkLog_sound (w := (3551485027 / 19176485027)) (n := 12)
    (lo := (374724131 / 1000000000)) (hi := (93681033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11363985027 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11363985027 / 7812500000) = 1/(7812500000 / 11363985027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4910 : Bounds (374724131 / 1000000000) (93681033 / 250000000) (Real.log (11363985027 / 7812500000)) := by
  have h := reflection_log_4910_neg
  have he : Real.log (11363985027 / 7812500000) = -Real.log (7812500000 / 11363985027) := by
    rw [show ((11363985027 / 7812500000) : ℝ) = ((7812500000 / 11363985027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4911_neg : (187465619 / 500000000) ≤ -Real.log (500000000000 / 727445685529) ∧
    -Real.log (500000000000 / 727445685529) ≤ (374931239 / 1000000000) := by
  have h := checkLog_sound (w := (227445685529 / 1227445685529)) (n := 12)
    (lo := (187465619 / 500000000)) (hi := (374931239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727445685529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727445685529 / 500000000000) = 1/(500000000000 / 727445685529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4911 : Bounds (187465619 / 500000000) (374931239 / 1000000000) (Real.log (727445685529 / 500000000000)) := by
  have h := reflection_log_4911_neg
  have he : Real.log (727445685529 / 500000000000) = -Real.log (500000000000 / 727445685529) := by
    rw [show ((727445685529 / 500000000000) : ℝ) = ((500000000000 / 727445685529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4912_neg : (17008027 / 100000000) ≤ -Real.log (5000 / 5927) ∧
    -Real.log (5000 / 5927) ≤ (170080271 / 1000000000) := by
  have h := checkLog_sound (w := (927 / 10927)) (n := 12)
    (lo := (17008027 / 100000000)) (hi := (170080271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5927 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5927 / 5000) = 1/(5000 / 5927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4912 : Bounds (17008027 / 100000000) (170080271 / 1000000000) (Real.log (5927 / 5000)) := by
  have h := reflection_log_4912_neg
  have he : Real.log (5927 / 5000) = -Real.log (5000 / 5927) := by
    rw [show ((5927 / 5000) : ℝ) = ((5000 / 5927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4913_neg : (205058083 / 1000000000) ≤ -Real.log (4073 / 5000) ∧
    -Real.log (4073 / 5000) ≤ (51264521 / 250000000) := by
  have h := checkLog_sound (w := (927 / 9073)) (n := 12)
    (lo := (205058083 / 1000000000)) (hi := (51264521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4073) = 1/(4073 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4913 : Bounds (-51264521 / 250000000) (-205058083 / 1000000000) (Real.log (4073 / 5000)) := by
  have h := reflection_log_4913_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4914_neg : (92691 / 500000000) ≤ -Real.log (5000000 / 5000927) ∧
    -Real.log (5000000 / 5000927) ≤ (185383 / 1000000000) := by
  have h := checkLog_sound (w := (927 / 10000927)) (n := 12)
    (lo := (92691 / 500000000)) (hi := (185383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000927 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000927 / 5000000) = 1/(5000000 / 5000927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4914 : Bounds (92691 / 500000000) (185383 / 1000000000) (Real.log (5000927 / 5000000)) := by
  have h := reflection_log_4914_neg
  have he : Real.log (5000927 / 5000000) = -Real.log (5000000 / 5000927) := by
    rw [show ((5000927 / 5000000) : ℝ) = ((5000000 / 5000927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4915_neg : (185417 / 1000000000) ≤ -Real.log (4999073 / 5000000) ∧
    -Real.log (4999073 / 5000000) ≤ (92709 / 500000000) := by
  have h := checkLog_sound (w := (927 / 9999073)) (n := 12)
    (lo := (185417 / 1000000000)) (hi := (92709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999073) = 1/(4999073 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4915 : Bounds (-92709 / 500000000) (-185417 / 1000000000) (Real.log (4999073 / 5000000)) := by
  have h := reflection_log_4915_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4916_neg : (11131443 / 125000000) ≤ -Real.log (1000000 / 1093137) ∧
    -Real.log (1000000 / 1093137) ≤ (17810309 / 200000000) := by
  have h := checkLog_sound (w := (93137 / 2093137)) (n := 12)
    (lo := (11131443 / 125000000)) (hi := (17810309 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093137 / 1000000) = 1/(1000000 / 1093137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4916 : Bounds (11131443 / 125000000) (17810309 / 200000000) (Real.log (1093137 / 1000000)) := by
  have h := reflection_log_4916_neg
  have he : Real.log (1093137 / 1000000) = -Real.log (1000000 / 1093137) := by
    rw [show ((1093137 / 1000000) : ℝ) = ((1000000 / 1093137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4917_neg : (97763887 / 1000000000) ≤ -Real.log (906863 / 1000000) ∧
    -Real.log (906863 / 1000000) ≤ (6110243 / 62500000) := by
  have h := checkLog_sound (w := (93137 / 1906863)) (n := 12)
    (lo := (97763887 / 1000000000)) (hi := (6110243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906863) = 1/(906863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4917 : Bounds (-6110243 / 62500000) (-97763887 / 1000000000) (Real.log (906863 / 1000000)) := by
  have h := reflection_log_4917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4918_neg : (89267413 / 1000000000) ≤ -Real.log (1000000 / 1093373) ∧
    -Real.log (1000000 / 1093373) ≤ (44633707 / 500000000) := by
  have h := checkLog_sound (w := (93373 / 2093373)) (n := 12)
    (lo := (89267413 / 1000000000)) (hi := (44633707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093373 / 1000000) = 1/(1000000 / 1093373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4918 : Bounds (89267413 / 1000000000) (44633707 / 500000000) (Real.log (1093373 / 1000000)) := by
  have h := reflection_log_4918_neg
  have he : Real.log (1093373 / 1000000) = -Real.log (1000000 / 1093373) := by
    rw [show ((1093373 / 1000000) : ℝ) = ((1000000 / 1093373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4919_neg : (98024159 / 1000000000) ≤ -Real.log (906627 / 1000000) ∧
    -Real.log (906627 / 1000000) ≤ (612651 / 6250000) := by
  have h := checkLog_sound (w := (93373 / 1906627)) (n := 12)
    (lo := (98024159 / 1000000000)) (hi := (612651 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906627) = 1/(906627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4919 : Bounds (-612651 / 6250000) (-98024159 / 1000000000) (Real.log (906627 / 1000000)) := by
  have h := reflection_log_4919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4920_neg : (1751349 / 200000000) ≤ -Real.log (991281482871 / 1000000000000) ∧
    -Real.log (991281482871 / 1000000000000) ≤ (4378373 / 500000000) := by
  have h := checkLog_sound (w := (8718517129 / 1991281482871)) (n := 12)
    (lo := (1751349 / 200000000)) (hi := (4378373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991281482871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991281482871) = 1/(991281482871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4920 : Bounds (-4378373 / 500000000) (-1751349 / 200000000) (Real.log (991281482871 / 1000000000000)) := by
  have h := reflection_log_4920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4921_neg : (8712343 / 1000000000) ≤ -Real.log (991325499231 / 1000000000000) ∧
    -Real.log (991325499231 / 1000000000000) ≤ (1089043 / 125000000) := by
  have h := checkLog_sound (w := (8674500769 / 1991325499231)) (n := 12)
    (lo := (8712343 / 1000000000)) (hi := (1089043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991325499231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991325499231) = 1/(991325499231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4921 : Bounds (-1089043 / 125000000) (-8712343 / 1000000000) (Real.log (991325499231 / 1000000000000)) := by
  have h := reflection_log_4921_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4922_neg : (23351929 / 125000000) ≤ -Real.log (500000000000 / 602702392753) ∧
    -Real.log (500000000000 / 602702392753) ≤ (186815433 / 1000000000) := by
  have h := checkLog_sound (w := (102702392753 / 1102702392753)) (n := 12)
    (lo := (23351929 / 125000000)) (hi := (186815433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602702392753 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602702392753 / 500000000000) = 1/(500000000000 / 602702392753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4922 : Bounds (23351929 / 125000000) (186815433 / 1000000000) (Real.log (602702392753 / 500000000000)) := by
  have h := reflection_log_4922_neg
  have he : Real.log (602702392753 / 500000000000) = -Real.log (500000000000 / 602702392753) := by
    rw [show ((602702392753 / 500000000000) : ℝ) = ((500000000000 / 602702392753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4923_neg : (46822893 / 250000000) ≤ -Real.log (500000000000 / 602989432259) ∧
    -Real.log (500000000000 / 602989432259) ≤ (187291573 / 1000000000) := by
  have h := checkLog_sound (w := (102989432259 / 1102989432259)) (n := 12)
    (lo := (46822893 / 250000000)) (hi := (187291573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602989432259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602989432259 / 500000000000) = 1/(500000000000 / 602989432259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4923 : Bounds (46822893 / 250000000) (187291573 / 1000000000) (Real.log (602989432259 / 500000000000)) := by
  have h := reflection_log_4923_neg
  have he : Real.log (602989432259 / 500000000000) = -Real.log (500000000000 / 602989432259) := by
    rw [show ((602989432259 / 500000000000) : ℝ) = ((500000000000 / 602989432259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4924_neg : (187465619 / 500000000) ≤ -Real.log (62500000000 / 90930710691) ∧
    -Real.log (62500000000 / 90930710691) ≤ (374931239 / 1000000000) := by
  have h := checkLog_sound (w := (28430710691 / 153430710691)) (n := 12)
    (lo := (187465619 / 500000000)) (hi := (374931239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90930710691 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90930710691 / 62500000000) = 1/(62500000000 / 90930710691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4924 : Bounds (187465619 / 500000000) (374931239 / 1000000000) (Real.log (90930710691 / 62500000000)) := by
  have h := reflection_log_4924_neg
  have he : Real.log (90930710691 / 62500000000) = -Real.log (62500000000 / 90930710691) := by
    rw [show ((90930710691 / 62500000000) : ℝ) = ((62500000000 / 90930710691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4925_neg : (187569177 / 500000000) ≤ -Real.log (100000000000 / 145519273263) ∧
    -Real.log (100000000000 / 145519273263) ≤ (75027671 / 200000000) := by
  have h := checkLog_sound (w := (45519273263 / 245519273263)) (n := 12)
    (lo := (187569177 / 500000000)) (hi := (75027671 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145519273263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145519273263 / 100000000000) = 1/(100000000000 / 145519273263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4925 : Bounds (187569177 / 500000000) (75027671 / 200000000) (Real.log (145519273263 / 100000000000)) := by
  have h := reflection_log_4925_neg
  have he : Real.log (145519273263 / 100000000000) = -Real.log (100000000000 / 145519273263) := by
    rw [show ((145519273263 / 100000000000) : ℝ) = ((100000000000 / 145519273263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4926_neg : (85082313 / 500000000) ≤ -Real.log (2000 / 2371) ∧
    -Real.log (2000 / 2371) ≤ (170164627 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 4371)) (n := 12)
    (lo := (85082313 / 500000000)) (hi := (170164627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2371 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2371 / 2000) = 1/(2000 / 2371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4926 : Bounds (85082313 / 500000000) (170164627 / 1000000000) (Real.log (2371 / 2000)) := by
  have h := reflection_log_4926_neg
  have he : Real.log (2371 / 2000) = -Real.log (2000 / 2371) := by
    rw [show ((2371 / 2000) : ℝ) = ((2000 / 2371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4927_neg : (4103617 / 20000000) ≤ -Real.log (1629 / 2000) ∧
    -Real.log (1629 / 2000) ≤ (205180851 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 3629)) (n := 12)
    (lo := (4103617 / 20000000)) (hi := (205180851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1629) = 1/(1629 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4927 : Bounds (-205180851 / 1000000000) (-4103617 / 20000000) (Real.log (1629 / 2000)) := by
  have h := reflection_log_4927_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


