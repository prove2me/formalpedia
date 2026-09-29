-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0022__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0022__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:11:11.407873+00:00
-- url     : https://prove2.me/theorems/23114b06-cdc9-49d2-89af-fae054c28512
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0022 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0023, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0022 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0023, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0024)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0022 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0023, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0024)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0022 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0023, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0024) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0022 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0023, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0024).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0022 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1408_neg : (648401 / 100000000) ≤ -Real.log (993536965551 / 1000000000000) ∧
    -Real.log (993536965551 / 1000000000000) ≤ (6484011 / 1000000000) := by
  have h := checkLog_sound (w := (6463034449 / 1993536965551)) (n := 12)
    (lo := (648401 / 100000000)) (hi := (6484011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993536965551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993536965551) = 1/(993536965551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1408 : Bounds (-6484011 / 1000000000) (-648401 / 100000000) (Real.log (993536965551 / 1000000000000)) := by
  have h := reflection_log_1408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1409_neg : (161133737 / 1000000000) ≤ -Real.log (500000000000 / 587421039639) ∧
    -Real.log (500000000000 / 587421039639) ≤ (80566869 / 500000000) := by
  have h := checkLog_sound (w := (87421039639 / 1087421039639)) (n := 12)
    (lo := (161133737 / 1000000000)) (hi := (80566869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587421039639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587421039639 / 500000000000) = 1/(500000000000 / 587421039639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1409 : Bounds (161133737 / 1000000000) (80566869 / 500000000) (Real.log (587421039639 / 500000000000)) := by
  have h := reflection_log_1409_neg
  have he : Real.log (587421039639 / 500000000000) = -Real.log (500000000000 / 587421039639) := by
    rw [show ((587421039639 / 500000000000) : ℝ) = ((500000000000 / 587421039639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1410_neg : (161560503 / 1000000000) ≤ -Real.log (500000000000 / 587671784163) ∧
    -Real.log (500000000000 / 587671784163) ≤ (20195063 / 125000000) := by
  have h := checkLog_sound (w := (87671784163 / 1087671784163)) (n := 12)
    (lo := (161560503 / 1000000000)) (hi := (20195063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587671784163 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587671784163 / 500000000000) = 1/(500000000000 / 587671784163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1410 : Bounds (161560503 / 1000000000) (20195063 / 125000000) (Real.log (587671784163 / 500000000000)) := by
  have h := reflection_log_1410_neg
  have he : Real.log (587671784163 / 500000000000) = -Real.log (500000000000 / 587671784163) := by
    rw [show ((587671784163 / 500000000000) : ℝ) = ((500000000000 / 587671784163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1411_neg : (161591957 / 500000000) ≤ -Real.log (500000000000 / 690759704691) ∧
    -Real.log (500000000000 / 690759704691) ≤ (64636783 / 200000000) := by
  have h := checkLog_sound (w := (190759704691 / 1190759704691)) (n := 12)
    (lo := (161591957 / 500000000)) (hi := (64636783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690759704691 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690759704691 / 500000000000) = 1/(500000000000 / 690759704691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1411 : Bounds (161591957 / 500000000) (64636783 / 200000000) (Real.log (690759704691 / 500000000000)) := by
  have h := reflection_log_1411_neg
  have he : Real.log (690759704691 / 500000000000) = -Real.log (500000000000 / 690759704691) := by
    rw [show ((690759704691 / 500000000000) : ℝ) = ((500000000000 / 690759704691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1412_neg : (161694593 / 500000000) ≤ -Real.log (100000000000 / 138180302489) ∧
    -Real.log (100000000000 / 138180302489) ≤ (323389187 / 1000000000) := by
  have h := checkLog_sound (w := (38180302489 / 238180302489)) (n := 12)
    (lo := (161694593 / 500000000)) (hi := (323389187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138180302489 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138180302489 / 100000000000) = 1/(100000000000 / 138180302489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1412 : Bounds (161694593 / 500000000) (323389187 / 1000000000) (Real.log (138180302489 / 100000000000)) := by
  have h := reflection_log_1412_neg
  have he : Real.log (138180302489 / 100000000000) = -Real.log (100000000000 / 138180302489) := by
    rw [show ((138180302489 / 100000000000) : ℝ) = ((100000000000 / 138180302489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1413_neg : (148764773 / 1000000000) ≤ -Real.log (2500 / 2901) ∧
    -Real.log (2500 / 2901) ≤ (74382387 / 500000000) := by
  have h := checkLog_sound (w := (401 / 5401)) (n := 12)
    (lo := (148764773 / 1000000000)) (hi := (74382387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2901 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2901 / 2500) = 1/(2500 / 2901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1413 : Bounds (148764773 / 1000000000) (74382387 / 500000000) (Real.log (2901 / 2500)) := by
  have h := reflection_log_1413_neg
  have he : Real.log (2901 / 2500) = -Real.log (2500 / 2901) := by
    rw [show ((2901 / 2500) : ℝ) = ((2500 / 2901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1414_neg : (174829691 / 1000000000) ≤ -Real.log (2099 / 2500) ∧
    -Real.log (2099 / 2500) ≤ (43707423 / 250000000) := by
  have h := checkLog_sound (w := (401 / 4599)) (n := 12)
    (lo := (174829691 / 1000000000)) (hi := (43707423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2099) = 1/(2099 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1414 : Bounds (-43707423 / 250000000) (-174829691 / 1000000000) (Real.log (2099 / 2500)) := by
  have h := reflection_log_1414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1415_neg : (160387 / 1000000000) ≤ -Real.log (2500000 / 2500401) ∧
    -Real.log (2500000 / 2500401) ≤ (40097 / 250000000) := by
  have h := checkLog_sound (w := (401 / 5000401)) (n := 12)
    (lo := (160387 / 1000000000)) (hi := (40097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500401 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500401 / 2500000) = 1/(2500000 / 2500401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1415 : Bounds (160387 / 1000000000) (40097 / 250000000) (Real.log (2500401 / 2500000)) := by
  have h := reflection_log_1415_neg
  have he : Real.log (2500401 / 2500000) = -Real.log (2500000 / 2500401) := by
    rw [show ((2500401 / 2500000) : ℝ) = ((2500000 / 2500401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1416_neg : (40103 / 250000000) ≤ -Real.log (2499599 / 2500000) ∧
    -Real.log (2499599 / 2500000) ≤ (160413 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 4999599)) (n := 12)
    (lo := (40103 / 250000000)) (hi := (160413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499599) = 1/(2499599 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1416 : Bounds (-160413 / 1000000000) (-40103 / 250000000) (Real.log (2499599 / 2500000)) := by
  have h := reflection_log_1416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1417_neg : (77372067 / 1000000000) ≤ -Real.log (250000 / 270111) ∧
    -Real.log (250000 / 270111) ≤ (19343017 / 250000000) := by
  have h := checkLog_sound (w := (20111 / 520111)) (n := 12)
    (lo := (77372067 / 1000000000)) (hi := (19343017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270111 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270111 / 250000) = 1/(250000 / 270111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1417 : Bounds (77372067 / 1000000000) (19343017 / 250000000) (Real.log (270111 / 250000)) := by
  have h := reflection_log_1417_neg
  have he : Real.log (270111 / 250000) = -Real.log (250000 / 270111) := by
    rw [show ((270111 / 250000) : ℝ) = ((250000 / 270111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1418_neg : (41932167 / 500000000) ≤ -Real.log (229889 / 250000) ∧
    -Real.log (229889 / 250000) ≤ (16772867 / 200000000) := by
  have h := checkLog_sound (w := (20111 / 479889)) (n := 12)
    (lo := (41932167 / 500000000)) (hi := (16772867 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229889) = 1/(229889 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1418 : Bounds (-16772867 / 200000000) (-41932167 / 500000000) (Real.log (229889 / 250000)) := by
  have h := reflection_log_1418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1419_neg : (38783669 / 500000000) ≤ -Real.log (200000 / 216131) ∧
    -Real.log (200000 / 216131) ≤ (77567339 / 1000000000) := by
  have h := checkLog_sound (w := (16131 / 416131)) (n := 12)
    (lo := (38783669 / 500000000)) (hi := (77567339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216131 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216131 / 200000) = 1/(200000 / 216131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1419 : Bounds (38783669 / 500000000) (77567339 / 1000000000) (Real.log (216131 / 200000)) := by
  have h := reflection_log_1419_neg
  have he : Real.log (216131 / 200000) = -Real.log (200000 / 216131) := by
    rw [show ((216131 / 200000) : ℝ) = ((200000 / 216131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1420_neg : (84093819 / 1000000000) ≤ -Real.log (183869 / 200000) ∧
    -Real.log (183869 / 200000) ≤ (4204691 / 50000000) := by
  have h := checkLog_sound (w := (16131 / 383869)) (n := 12)
    (lo := (84093819 / 1000000000)) (hi := (4204691 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183869) = 1/(183869 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1420 : Bounds (-4204691 / 50000000) (-84093819 / 1000000000) (Real.log (183869 / 200000)) := by
  have h := reflection_log_1420_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1421_neg : (81581 / 12500000) ≤ -Real.log (39739790839 / 40000000000) ∧
    -Real.log (39739790839 / 40000000000) ≤ (6526481 / 1000000000) := by
  have h := checkLog_sound (w := (260209161 / 79739790839)) (n := 12)
    (lo := (81581 / 12500000)) (hi := (6526481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39739790839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39739790839) = 1/(39739790839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1421 : Bounds (-6526481 / 1000000000) (-81581 / 12500000) (Real.log (39739790839 / 40000000000)) := by
  have h := reflection_log_1421_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1422_neg : (3246133 / 500000000) ≤ -Real.log (62095547679 / 62500000000) ∧
    -Real.log (62095547679 / 62500000000) ≤ (6492267 / 1000000000) := by
  have h := checkLog_sound (w := (404452321 / 124595547679)) (n := 12)
    (lo := (3246133 / 500000000)) (hi := (6492267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62095547679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62095547679) = 1/(62095547679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1422 : Bounds (-6492267 / 1000000000) (-3246133 / 500000000) (Real.log (62095547679 / 62500000000)) := by
  have h := reflection_log_1422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1423_neg : (161236401 / 1000000000) ≤ -Real.log (250000000000 / 293740674847) ∧
    -Real.log (250000000000 / 293740674847) ≤ (80618201 / 500000000) := by
  have h := checkLog_sound (w := (43740674847 / 543740674847)) (n := 12)
    (lo := (161236401 / 1000000000)) (hi := (80618201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293740674847 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293740674847 / 250000000000) = 1/(250000000000 / 293740674847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1423 : Bounds (161236401 / 1000000000) (80618201 / 500000000) (Real.log (293740674847 / 250000000000)) := by
  have h := reflection_log_1423_neg
  have he : Real.log (293740674847 / 250000000000) = -Real.log (250000000000 / 293740674847) := by
    rw [show ((293740674847 / 250000000000) : ℝ) = ((250000000000 / 293740674847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1424_neg : (161661157 / 1000000000) ≤ -Real.log (4000000000 / 4701847511) ∧
    -Real.log (4000000000 / 4701847511) ≤ (80830579 / 500000000) := by
  have h := checkLog_sound (w := (701847511 / 8701847511)) (n := 12)
    (lo := (161661157 / 1000000000)) (hi := (80830579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4701847511 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4701847511 / 4000000000) = 1/(4000000000 / 4701847511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1424 : Bounds (161661157 / 1000000000) (80830579 / 500000000) (Real.log (4701847511 / 4000000000)) := by
  have h := reflection_log_1424_neg
  have he : Real.log (4701847511 / 4000000000) = -Real.log (4000000000 / 4701847511) := by
    rw [show ((4701847511 / 4000000000) : ℝ) = ((4000000000 / 4701847511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1425_neg : (161694593 / 500000000) ≤ -Real.log (125000000000 / 172725378111) ∧
    -Real.log (125000000000 / 172725378111) ≤ (323389187 / 1000000000) := by
  have h := checkLog_sound (w := (47725378111 / 297725378111)) (n := 12)
    (lo := (161694593 / 500000000)) (hi := (323389187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172725378111 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172725378111 / 125000000000) = 1/(125000000000 / 172725378111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1425 : Bounds (161694593 / 500000000) (323389187 / 1000000000) (Real.log (172725378111 / 125000000000)) := by
  have h := reflection_log_1425_neg
  have he : Real.log (172725378111 / 125000000000) = -Real.log (125000000000 / 172725378111) := by
    rw [show ((172725378111 / 125000000000) : ℝ) = ((125000000000 / 172725378111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1426_neg : (10112327 / 31250000) ≤ -Real.log (500000000000 / 691043353979) ∧
    -Real.log (500000000000 / 691043353979) ≤ (64718893 / 200000000) := by
  have h := checkLog_sound (w := (191043353979 / 1191043353979)) (n := 12)
    (lo := (10112327 / 31250000)) (hi := (64718893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691043353979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691043353979 / 500000000000) = 1/(500000000000 / 691043353979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1426 : Bounds (10112327 / 31250000) (64718893 / 200000000) (Real.log (691043353979 / 500000000000)) := by
  have h := reflection_log_1426_neg
  have he : Real.log (691043353979 / 500000000000) = -Real.log (500000000000 / 691043353979) := by
    rw [show ((691043353979 / 500000000000) : ℝ) = ((500000000000 / 691043353979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1427_neg : (74425473 / 500000000) ≤ -Real.log (2000 / 2321) ∧
    -Real.log (2000 / 2321) ≤ (148850947 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 4321)) (n := 12)
    (lo := (74425473 / 500000000)) (hi := (148850947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2321 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2321 / 2000) = 1/(2000 / 2321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1427 : Bounds (74425473 / 500000000) (148850947 / 1000000000) (Real.log (2321 / 2000)) := by
  have h := reflection_log_1427_neg
  have he : Real.log (2321 / 2000) = -Real.log (2000 / 2321) := by
    rw [show ((2321 / 2000) : ℝ) = ((2000 / 2321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1428_neg : (87474401 / 500000000) ≤ -Real.log (1679 / 2000) ∧
    -Real.log (1679 / 2000) ≤ (174948803 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 3679)) (n := 12)
    (lo := (87474401 / 500000000)) (hi := (174948803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1679) = 1/(1679 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1428 : Bounds (-174948803 / 1000000000) (-87474401 / 500000000) (Real.log (1679 / 2000)) := by
  have h := reflection_log_1428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1429_neg : (160487 / 1000000000) ≤ -Real.log (2000000 / 2000321) ∧
    -Real.log (2000000 / 2000321) ≤ (20061 / 125000000) := by
  have h := checkLog_sound (w := (321 / 4000321)) (n := 12)
    (lo := (160487 / 1000000000)) (hi := (20061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000321 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000321 / 2000000) = 1/(2000000 / 2000321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1429 : Bounds (160487 / 1000000000) (20061 / 125000000) (Real.log (2000321 / 2000000)) := by
  have h := reflection_log_1429_neg
  have he : Real.log (2000321 / 2000000) = -Real.log (2000000 / 2000321) := by
    rw [show ((2000321 / 2000000) : ℝ) = ((2000000 / 2000321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1430_neg : (627 / 3906250) ≤ -Real.log (1999679 / 2000000) ∧
    -Real.log (1999679 / 2000000) ≤ (160513 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 3999679)) (n := 12)
    (lo := (627 / 3906250)) (hi := (160513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999679) = 1/(1999679 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1430 : Bounds (-160513 / 1000000000) (-627 / 3906250) (Real.log (1999679 / 2000000)) := by
  have h := reflection_log_1430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1431_neg : (77419269 / 1000000000) ≤ -Real.log (200000 / 216099) ∧
    -Real.log (200000 / 216099) ≤ (7741927 / 100000000) := by
  have h := checkLog_sound (w := (16099 / 416099)) (n := 12)
    (lo := (77419269 / 1000000000)) (hi := (7741927 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216099 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216099 / 200000) = 1/(200000 / 216099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1431 : Bounds (77419269 / 1000000000) (7741927 / 100000000) (Real.log (216099 / 200000)) := by
  have h := reflection_log_1431_neg
  have he : Real.log (216099 / 200000) = -Real.log (200000 / 216099) := by
    rw [show ((216099 / 200000) : ℝ) = ((200000 / 216099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1432_neg : (83919797 / 1000000000) ≤ -Real.log (183901 / 200000) ∧
    -Real.log (183901 / 200000) ≤ (41959899 / 500000000) := by
  have h := checkLog_sound (w := (16099 / 383901)) (n := 12)
    (lo := (83919797 / 1000000000)) (hi := (41959899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183901) = 1/(183901 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1432 : Bounds (-41959899 / 500000000) (-83919797 / 1000000000) (Real.log (183901 / 200000)) := by
  have h := reflection_log_1432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1433_neg : (77614531 / 1000000000) ≤ -Real.log (500000 / 540353) ∧
    -Real.log (500000 / 540353) ≤ (19403633 / 250000000) := by
  have h := checkLog_sound (w := (40353 / 1040353)) (n := 12)
    (lo := (77614531 / 1000000000)) (hi := (19403633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540353 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540353 / 500000) = 1/(500000 / 540353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1433 : Bounds (77614531 / 1000000000) (19403633 / 250000000) (Real.log (540353 / 500000)) := by
  have h := reflection_log_1433_neg
  have he : Real.log (540353 / 500000) = -Real.log (500000 / 540353) := by
    rw [show ((540353 / 500000) : ℝ) = ((500000 / 540353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1434_neg : (42074647 / 500000000) ≤ -Real.log (459647 / 500000) ∧
    -Real.log (459647 / 500000) ≤ (16829859 / 200000000) := by
  have h := checkLog_sound (w := (40353 / 959647)) (n := 12)
    (lo := (42074647 / 500000000)) (hi := (16829859 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459647) = 1/(459647 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1434 : Bounds (-16829859 / 200000000) (-42074647 / 500000000) (Real.log (459647 / 500000)) := by
  have h := reflection_log_1434_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1435_neg : (6534763 / 1000000000) ≤ -Real.log (248371635391 / 250000000000) ∧
    -Real.log (248371635391 / 250000000000) ≤ (1633691 / 250000000) := by
  have h := checkLog_sound (w := (1628364609 / 498371635391)) (n := 12)
    (lo := (6534763 / 1000000000)) (hi := (1633691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248371635391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248371635391) = 1/(248371635391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1435 : Bounds (-1633691 / 250000000) (-6534763 / 1000000000) (Real.log (248371635391 / 250000000000)) := by
  have h := reflection_log_1435_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1436_neg : (6500527 / 1000000000) ≤ -Real.log (39740822199 / 40000000000) ∧
    -Real.log (39740822199 / 40000000000) ≤ (406283 / 62500000) := by
  have h := checkLog_sound (w := (259177801 / 79740822199)) (n := 12)
    (lo := (6500527 / 1000000000)) (hi := (406283 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39740822199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39740822199) = 1/(39740822199 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1436 : Bounds (-406283 / 62500000) (-6500527 / 1000000000) (Real.log (39740822199 / 40000000000)) := by
  have h := reflection_log_1436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1437_neg : (80669533 / 500000000) ≤ -Real.log (12500000000 / 14688541661) ∧
    -Real.log (12500000000 / 14688541661) ≤ (161339067 / 1000000000) := by
  have h := checkLog_sound (w := (2188541661 / 27188541661)) (n := 12)
    (lo := (80669533 / 500000000)) (hi := (161339067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14688541661 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14688541661 / 12500000000) = 1/(12500000000 / 14688541661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1437 : Bounds (80669533 / 500000000) (161339067 / 1000000000) (Real.log (14688541661 / 12500000000)) := by
  have h := reflection_log_1437_neg
  have he : Real.log (14688541661 / 12500000000) = -Real.log (12500000000 / 14688541661) := by
    rw [show ((14688541661 / 12500000000) : ℝ) = ((12500000000 / 14688541661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1438_neg : (80881913 / 500000000) ≤ -Real.log (500000000000 / 587791283311) ∧
    -Real.log (500000000000 / 587791283311) ≤ (161763827 / 1000000000) := by
  have h := checkLog_sound (w := (87791283311 / 1087791283311)) (n := 12)
    (lo := (80881913 / 500000000)) (hi := (161763827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587791283311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587791283311 / 500000000000) = 1/(500000000000 / 587791283311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1438 : Bounds (80881913 / 500000000) (161763827 / 1000000000) (Real.log (587791283311 / 500000000000)) := by
  have h := reflection_log_1438_neg
  have he : Real.log (587791283311 / 500000000000) = -Real.log (500000000000 / 587791283311) := by
    rw [show ((587791283311 / 500000000000) : ℝ) = ((500000000000 / 587791283311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1439_neg : (10112327 / 31250000) ≤ -Real.log (250000000000 / 345521676989) ∧
    -Real.log (250000000000 / 345521676989) ≤ (64718893 / 200000000) := by
  have h := checkLog_sound (w := (95521676989 / 595521676989)) (n := 12)
    (lo := (10112327 / 31250000)) (hi := (64718893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345521676989 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345521676989 / 250000000000) = 1/(250000000000 / 345521676989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1439 : Bounds (10112327 / 31250000) (64718893 / 200000000) (Real.log (345521676989 / 250000000000)) := by
  have h := reflection_log_1439_neg
  have he : Real.log (345521676989 / 250000000000) = -Real.log (250000000000 / 345521676989) := by
    rw [show ((345521676989 / 250000000000) : ℝ) = ((250000000000 / 345521676989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1440_neg : (323799749 / 1000000000) ≤ -Real.log (62500000000 / 86398153663) ∧
    -Real.log (62500000000 / 86398153663) ≤ (1295199 / 4000000) := by
  have h := checkLog_sound (w := (23898153663 / 148898153663)) (n := 12)
    (lo := (323799749 / 1000000000)) (hi := (1295199 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86398153663 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86398153663 / 62500000000) = 1/(62500000000 / 86398153663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1440 : Bounds (323799749 / 1000000000) (1295199 / 4000000) (Real.log (86398153663 / 62500000000)) := by
  have h := reflection_log_1440_neg
  have he : Real.log (86398153663 / 62500000000) = -Real.log (62500000000 / 86398153663) := by
    rw [show ((86398153663 / 62500000000) : ℝ) = ((62500000000 / 86398153663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1441_neg : (18617139 / 125000000) ≤ -Real.log (5000 / 5803) ∧
    -Real.log (5000 / 5803) ≤ (148937113 / 1000000000) := by
  have h := checkLog_sound (w := (803 / 10803)) (n := 12)
    (lo := (18617139 / 125000000)) (hi := (148937113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5803 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5803 / 5000) = 1/(5000 / 5803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1441 : Bounds (18617139 / 125000000) (148937113 / 1000000000) (Real.log (5803 / 5000)) := by
  have h := reflection_log_1441_neg
  have he : Real.log (5803 / 5000) = -Real.log (5000 / 5803) := by
    rw [show ((5803 / 5000) : ℝ) = ((5000 / 5803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1442_neg : (21883491 / 125000000) ≤ -Real.log (4197 / 5000) ∧
    -Real.log (4197 / 5000) ≤ (175067929 / 1000000000) := by
  have h := checkLog_sound (w := (803 / 9197)) (n := 12)
    (lo := (21883491 / 125000000)) (hi := (175067929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4197) = 1/(4197 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1442 : Bounds (-175067929 / 1000000000) (-21883491 / 125000000) (Real.log (4197 / 5000)) := by
  have h := reflection_log_1442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1443_neg : (160587 / 1000000000) ≤ -Real.log (5000000 / 5000803) ∧
    -Real.log (5000000 / 5000803) ≤ (40147 / 250000000) := by
  have h := checkLog_sound (w := (803 / 10000803)) (n := 12)
    (lo := (160587 / 1000000000)) (hi := (40147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000803 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000803 / 5000000) = 1/(5000000 / 5000803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1443 : Bounds (160587 / 1000000000) (40147 / 250000000) (Real.log (5000803 / 5000000)) := by
  have h := reflection_log_1443_neg
  have he : Real.log (5000803 / 5000000) = -Real.log (5000000 / 5000803) := by
    rw [show ((5000803 / 5000000) : ℝ) = ((5000000 / 5000803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1444_neg : (40153 / 250000000) ≤ -Real.log (4999197 / 5000000) ∧
    -Real.log (4999197 / 5000000) ≤ (160613 / 1000000000) := by
  have h := checkLog_sound (w := (803 / 9999197)) (n := 12)
    (lo := (40153 / 250000000)) (hi := (160613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999197) = 1/(4999197 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1444 : Bounds (-160613 / 1000000000) (-40153 / 250000000) (Real.log (4999197 / 5000000)) := by
  have h := reflection_log_1444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1445_neg : (77465543 / 1000000000) ≤ -Real.log (200000 / 216109) ∧
    -Real.log (200000 / 216109) ≤ (9683193 / 125000000) := by
  have h := checkLog_sound (w := (16109 / 416109)) (n := 12)
    (lo := (77465543 / 1000000000)) (hi := (9683193 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216109 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216109 / 200000) = 1/(200000 / 216109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1445 : Bounds (77465543 / 1000000000) (9683193 / 125000000) (Real.log (216109 / 200000)) := by
  have h := reflection_log_1445_neg
  have he : Real.log (216109 / 200000) = -Real.log (200000 / 216109) := by
    rw [show ((216109 / 200000) : ℝ) = ((200000 / 216109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1446_neg : (3358967 / 40000000) ≤ -Real.log (183891 / 200000) ∧
    -Real.log (183891 / 200000) ≤ (2624193 / 31250000) := by
  have h := checkLog_sound (w := (16109 / 383891)) (n := 12)
    (lo := (3358967 / 40000000)) (hi := (2624193 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183891) = 1/(183891 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1446 : Bounds (-2624193 / 31250000) (-3358967 / 40000000) (Real.log (183891 / 200000)) := by
  have h := reflection_log_1446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1447_neg : (77661721 / 1000000000) ≤ -Real.log (1000000 / 1080757) ∧
    -Real.log (1000000 / 1080757) ≤ (38830861 / 500000000) := by
  have h := checkLog_sound (w := (80757 / 2080757)) (n := 12)
    (lo := (77661721 / 1000000000)) (hi := (38830861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080757 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080757 / 1000000) = 1/(1000000 / 1080757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1447 : Bounds (77661721 / 1000000000) (38830861 / 500000000) (Real.log (1080757 / 1000000)) := by
  have h := reflection_log_1447_neg
  have he : Real.log (1080757 / 1000000) = -Real.log (1000000 / 1080757) := by
    rw [show ((1080757 / 1000000) : ℝ) = ((1000000 / 1080757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1448_neg : (84204773 / 1000000000) ≤ -Real.log (919243 / 1000000) ∧
    -Real.log (919243 / 1000000) ≤ (42102387 / 500000000) := by
  have h := checkLog_sound (w := (80757 / 1919243)) (n := 12)
    (lo := (84204773 / 1000000000)) (hi := (42102387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919243) = 1/(919243 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1448 : Bounds (-42102387 / 500000000) (-84204773 / 1000000000) (Real.log (919243 / 1000000)) := by
  have h := reflection_log_1448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1449_neg : (1635763 / 250000000) ≤ -Real.log (993478306951 / 1000000000000) ∧
    -Real.log (993478306951 / 1000000000000) ≤ (6543053 / 1000000000) := by
  have h := checkLog_sound (w := (6521693049 / 1993478306951)) (n := 12)
    (lo := (1635763 / 250000000)) (hi := (6543053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993478306951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993478306951) = 1/(993478306951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1449 : Bounds (-6543053 / 1000000000) (-1635763 / 250000000) (Real.log (993478306951 / 1000000000000)) := by
  have h := reflection_log_1449_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1450_neg : (813579 / 125000000) ≤ -Real.log (39740500119 / 40000000000) ∧
    -Real.log (39740500119 / 40000000000) ≤ (6508633 / 1000000000) := by
  have h := checkLog_sound (w := (259499881 / 79740500119)) (n := 12)
    (lo := (813579 / 125000000)) (hi := (6508633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39740500119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39740500119) = 1/(39740500119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1450 : Bounds (-6508633 / 1000000000) (-813579 / 125000000) (Real.log (39740500119 / 40000000000)) := by
  have h := reflection_log_1450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1451_neg : (161439719 / 1000000000) ≤ -Real.log (500000000000 / 587600806999) ∧
    -Real.log (500000000000 / 587600806999) ≤ (4035993 / 25000000) := by
  have h := checkLog_sound (w := (87600806999 / 1087600806999)) (n := 12)
    (lo := (161439719 / 1000000000)) (hi := (4035993 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587600806999 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587600806999 / 500000000000) = 1/(500000000000 / 587600806999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1451 : Bounds (161439719 / 1000000000) (4035993 / 25000000) (Real.log (587600806999 / 500000000000)) := by
  have h := reflection_log_1451_neg
  have he : Real.log (587600806999 / 500000000000) = -Real.log (500000000000 / 587600806999) := by
    rw [show ((587600806999 / 500000000000) : ℝ) = ((500000000000 / 587600806999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1452_neg : (32373299 / 200000000) ≤ -Real.log (500000000000 / 587851634443) ∧
    -Real.log (500000000000 / 587851634443) ≤ (632291 / 3906250) := by
  have h := checkLog_sound (w := (87851634443 / 1087851634443)) (n := 12)
    (lo := (32373299 / 200000000)) (hi := (632291 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587851634443 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587851634443 / 500000000000) = 1/(500000000000 / 587851634443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1452 : Bounds (32373299 / 200000000) (632291 / 3906250) (Real.log (587851634443 / 500000000000)) := by
  have h := reflection_log_1452_neg
  have he : Real.log (587851634443 / 500000000000) = -Real.log (500000000000 / 587851634443) := by
    rw [show ((587851634443 / 500000000000) : ℝ) = ((500000000000 / 587851634443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1453_neg : (323799749 / 1000000000) ≤ -Real.log (500000000000 / 691185229303) ∧
    -Real.log (500000000000 / 691185229303) ≤ (1295199 / 4000000) := by
  have h := checkLog_sound (w := (191185229303 / 1191185229303)) (n := 12)
    (lo := (323799749 / 1000000000)) (hi := (1295199 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691185229303 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691185229303 / 500000000000) = 1/(500000000000 / 691185229303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1453 : Bounds (323799749 / 1000000000) (1295199 / 4000000) (Real.log (691185229303 / 500000000000)) := by
  have h := reflection_log_1453_neg
  have he : Real.log (691185229303 / 500000000000) = -Real.log (500000000000 / 691185229303) := by
    rw [show ((691185229303 / 500000000000) : ℝ) = ((500000000000 / 691185229303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1454_neg : (4050063 / 12500000) ≤ -Real.log (500000000000 / 691327138433) ∧
    -Real.log (500000000000 / 691327138433) ≤ (324005041 / 1000000000) := by
  have h := checkLog_sound (w := (191327138433 / 1191327138433)) (n := 12)
    (lo := (4050063 / 12500000)) (hi := (324005041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691327138433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691327138433 / 500000000000) = 1/(500000000000 / 691327138433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1454 : Bounds (4050063 / 12500000) (324005041 / 1000000000) (Real.log (691327138433 / 500000000000)) := by
  have h := reflection_log_1454_neg
  have he : Real.log (691327138433 / 500000000000) = -Real.log (500000000000 / 691327138433) := by
    rw [show ((691327138433 / 500000000000) : ℝ) = ((500000000000 / 691327138433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1455_neg : (149023271 / 1000000000) ≤ -Real.log (10000 / 11607) ∧
    -Real.log (10000 / 11607) ≤ (18627909 / 125000000) := by
  have h := checkLog_sound (w := (1607 / 21607)) (n := 12)
    (lo := (149023271 / 1000000000)) (hi := (18627909 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11607 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11607 / 10000) = 1/(10000 / 11607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1455 : Bounds (149023271 / 1000000000) (18627909 / 125000000) (Real.log (11607 / 10000)) := by
  have h := reflection_log_1455_neg
  have he : Real.log (11607 / 10000) = -Real.log (10000 / 11607) := by
    rw [show ((11607 / 10000) : ℝ) = ((10000 / 11607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1456_neg : (175187067 / 1000000000) ≤ -Real.log (8393 / 10000) ∧
    -Real.log (8393 / 10000) ≤ (43796767 / 250000000) := by
  have h := checkLog_sound (w := (1607 / 18393)) (n := 12)
    (lo := (175187067 / 1000000000)) (hi := (43796767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8393) = 1/(8393 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1456 : Bounds (-43796767 / 250000000) (-175187067 / 1000000000) (Real.log (8393 / 10000)) := by
  have h := reflection_log_1456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1457_neg : (160687 / 1000000000) ≤ -Real.log (10000000 / 10001607) ∧
    -Real.log (10000000 / 10001607) ≤ (10043 / 62500000) := by
  have h := checkLog_sound (w := (1607 / 20001607)) (n := 12)
    (lo := (160687 / 1000000000)) (hi := (10043 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001607 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001607 / 10000000) = 1/(10000000 / 10001607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1457 : Bounds (160687 / 1000000000) (10043 / 62500000) (Real.log (10001607 / 10000000)) := by
  have h := reflection_log_1457_neg
  have he : Real.log (10001607 / 10000000) = -Real.log (10000000 / 10001607) := by
    rw [show ((10001607 / 10000000) : ℝ) = ((10000000 / 10001607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1458_neg : (20089 / 125000000) ≤ -Real.log (9998393 / 10000000) ∧
    -Real.log (9998393 / 10000000) ≤ (160713 / 1000000000) := by
  have h := checkLog_sound (w := (1607 / 19998393)) (n := 12)
    (lo := (20089 / 125000000)) (hi := (160713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998393) = 1/(9998393 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1458 : Bounds (-160713 / 1000000000) (-20089 / 125000000) (Real.log (9998393 / 10000000)) := by
  have h := reflection_log_1458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1459_neg : (3875637 / 50000000) ≤ -Real.log (250000 / 270149) ∧
    -Real.log (250000 / 270149) ≤ (77512741 / 1000000000) := by
  have h := checkLog_sound (w := (20149 / 520149)) (n := 12)
    (lo := (3875637 / 50000000)) (hi := (77512741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270149 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270149 / 250000) = 1/(250000 / 270149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1459 : Bounds (3875637 / 50000000) (77512741 / 1000000000) (Real.log (270149 / 250000)) := by
  have h := reflection_log_1459_neg
  have he : Real.log (270149 / 250000) = -Real.log (250000 / 270149) := by
    rw [show ((270149 / 250000) : ℝ) = ((250000 / 270149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1460_neg : (21007411 / 250000000) ≤ -Real.log (229851 / 250000) ∧
    -Real.log (229851 / 250000) ≤ (16805929 / 200000000) := by
  have h := checkLog_sound (w := (20149 / 479851)) (n := 12)
    (lo := (21007411 / 250000000)) (hi := (16805929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229851) = 1/(229851 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1460 : Bounds (-16805929 / 200000000) (-21007411 / 250000000) (Real.log (229851 / 250000)) := by
  have h := reflection_log_1460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1461_neg : (77708909 / 1000000000) ≤ -Real.log (125000 / 135101) ∧
    -Real.log (125000 / 135101) ≤ (7770891 / 100000000) := by
  have h := checkLog_sound (w := (10101 / 260101)) (n := 12)
    (lo := (77708909 / 1000000000)) (hi := (7770891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135101 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135101 / 125000) = 1/(125000 / 135101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1461 : Bounds (77708909 / 1000000000) (7770891 / 100000000) (Real.log (135101 / 125000)) := by
  have h := reflection_log_1461_neg
  have he : Real.log (135101 / 125000) = -Real.log (125000 / 135101) := by
    rw [show ((135101 / 125000) : ℝ) = ((125000 / 135101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1462_neg : (16852051 / 200000000) ≤ -Real.log (114899 / 125000) ∧
    -Real.log (114899 / 125000) ≤ (2633133 / 31250000) := by
  have h := checkLog_sound (w := (10101 / 239899)) (n := 12)
    (lo := (16852051 / 200000000)) (hi := (2633133 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114899) = 1/(114899 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1462 : Bounds (-2633133 / 31250000) (-16852051 / 200000000) (Real.log (114899 / 125000)) := by
  have h := reflection_log_1462_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1463_neg : (3275673 / 500000000) ≤ -Real.log (15522969799 / 15625000000) ∧
    -Real.log (15522969799 / 15625000000) ≤ (6551347 / 1000000000) := by
  have h := checkLog_sound (w := (102030201 / 31147969799)) (n := 12)
    (lo := (3275673 / 500000000)) (hi := (6551347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15522969799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15522969799) = 1/(15522969799 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1463 : Bounds (-6551347 / 1000000000) (-3275673 / 500000000) (Real.log (15522969799 / 15625000000)) := by
  have h := reflection_log_1463_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1464_neg : (814613 / 125000000) ≤ -Real.log (62094017799 / 62500000000) ∧
    -Real.log (62094017799 / 62500000000) ≤ (1303381 / 200000000) := by
  have h := checkLog_sound (w := (405982201 / 124594017799)) (n := 12)
    (lo := (814613 / 125000000)) (hi := (1303381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62094017799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62094017799) = 1/(62094017799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1464 : Bounds (-1303381 / 200000000) (-814613 / 125000000) (Real.log (62094017799 / 62500000000)) := by
  have h := reflection_log_1464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1465_neg : (32308477 / 200000000) ≤ -Real.log (500000000000 / 587661136997) ∧
    -Real.log (500000000000 / 587661136997) ≤ (80771193 / 500000000) := by
  have h := checkLog_sound (w := (87661136997 / 1087661136997)) (n := 12)
    (lo := (32308477 / 200000000)) (hi := (80771193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587661136997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587661136997 / 500000000000) = 1/(500000000000 / 587661136997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1465 : Bounds (32308477 / 200000000) (80771193 / 500000000) (Real.log (587661136997 / 500000000000)) := by
  have h := reflection_log_1465_neg
  have he : Real.log (587661136997 / 500000000000) = -Real.log (500000000000 / 587661136997) := by
    rw [show ((587661136997 / 500000000000) : ℝ) = ((500000000000 / 587661136997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1466_neg : (32393833 / 200000000) ≤ -Real.log (31250000000 / 36744499517) ∧
    -Real.log (31250000000 / 36744499517) ≤ (80984583 / 500000000) := by
  have h := checkLog_sound (w := (5494499517 / 67994499517)) (n := 12)
    (lo := (32393833 / 200000000)) (hi := (80984583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36744499517 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36744499517 / 31250000000) = 1/(31250000000 / 36744499517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1466 : Bounds (32393833 / 200000000) (80984583 / 500000000) (Real.log (36744499517 / 31250000000)) := by
  have h := reflection_log_1466_neg
  have he : Real.log (36744499517 / 31250000000) = -Real.log (31250000000 / 36744499517) := by
    rw [show ((36744499517 / 31250000000) : ℝ) = ((31250000000 / 36744499517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1467_neg : (4050063 / 12500000) ≤ -Real.log (3906250000 / 5400993269) ∧
    -Real.log (3906250000 / 5400993269) ≤ (324005041 / 1000000000) := by
  have h := checkLog_sound (w := (1494743269 / 9307243269)) (n := 12)
    (lo := (4050063 / 12500000)) (hi := (324005041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5400993269 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5400993269 / 3906250000) = 1/(3906250000 / 5400993269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1467 : Bounds (4050063 / 12500000) (324005041 / 1000000000) (Real.log (5400993269 / 3906250000)) := by
  have h := reflection_log_1467_neg
  have he : Real.log (5400993269 / 3906250000) = -Real.log (3906250000 / 5400993269) := by
    rw [show ((5400993269 / 3906250000) : ℝ) = ((3906250000 / 5400993269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1468_neg : (324210339 / 1000000000) ≤ -Real.log (250000000000 / 345734540689) ∧
    -Real.log (250000000000 / 345734540689) ≤ (16210517 / 50000000) := by
  have h := checkLog_sound (w := (95734540689 / 595734540689)) (n := 12)
    (lo := (324210339 / 1000000000)) (hi := (16210517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345734540689 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345734540689 / 250000000000) = 1/(250000000000 / 345734540689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1468 : Bounds (324210339 / 1000000000) (16210517 / 50000000) (Real.log (345734540689 / 250000000000)) := by
  have h := reflection_log_1468_neg
  have he : Real.log (345734540689 / 250000000000) = -Real.log (250000000000 / 345734540689) := by
    rw [show ((345734540689 / 250000000000) : ℝ) = ((250000000000 / 345734540689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1469_neg : (74554711 / 500000000) ≤ -Real.log (1250 / 1451) ∧
    -Real.log (1250 / 1451) ≤ (149109423 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 2701)) (n := 12)
    (lo := (74554711 / 500000000)) (hi := (149109423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 1250) = 1/(1250 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1469 : Bounds (74554711 / 500000000) (149109423 / 1000000000) (Real.log (1451 / 1250)) := by
  have h := reflection_log_1469_neg
  have he : Real.log (1451 / 1250) = -Real.log (1250 / 1451) := by
    rw [show ((1451 / 1250) : ℝ) = ((1250 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1470_neg : (175306221 / 1000000000) ≤ -Real.log (1049 / 1250) ∧
    -Real.log (1049 / 1250) ≤ (87653111 / 500000000) := by
  have h := checkLog_sound (w := (201 / 2299)) (n := 12)
    (lo := (175306221 / 1000000000)) (hi := (87653111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1049) = 1/(1049 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1470 : Bounds (-87653111 / 500000000) (-175306221 / 1000000000) (Real.log (1049 / 1250)) := by
  have h := reflection_log_1470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1471_neg : (160787 / 1000000000) ≤ -Real.log (1250000 / 1250201) ∧
    -Real.log (1250000 / 1250201) ≤ (40197 / 250000000) := by
  have h := checkLog_sound (w := (201 / 2500201)) (n := 12)
    (lo := (160787 / 1000000000)) (hi := (40197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250201 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250201 / 1250000) = 1/(1250000 / 1250201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1471 : Bounds (160787 / 1000000000) (40197 / 250000000) (Real.log (1250201 / 1250000)) := by
  have h := reflection_log_1471_neg
  have he : Real.log (1250201 / 1250000) = -Real.log (1250000 / 1250201) := by
    rw [show ((1250201 / 1250000) : ℝ) = ((1250000 / 1250201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0023 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1472_neg : (40203 / 250000000) ≤ -Real.log (1249799 / 1250000) ∧
    -Real.log (1249799 / 1250000) ≤ (160813 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 2499799)) (n := 12)
    (lo := (40203 / 250000000)) (hi := (160813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249799) = 1/(1249799 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1472 : Bounds (-160813 / 1000000000) (-40203 / 250000000) (Real.log (1249799 / 1250000)) := by
  have h := reflection_log_1472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1473_neg : (15511987 / 200000000) ≤ -Real.log (1000000 / 1080647) ∧
    -Real.log (1000000 / 1080647) ≤ (605937 / 7812500) := by
  have h := checkLog_sound (w := (80647 / 2080647)) (n := 12)
    (lo := (15511987 / 200000000)) (hi := (605937 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080647 / 1000000) = 1/(1000000 / 1080647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1473 : Bounds (15511987 / 200000000) (605937 / 7812500) (Real.log (1080647 / 1000000)) := by
  have h := reflection_log_1473_neg
  have he : Real.log (1080647 / 1000000) = -Real.log (1000000 / 1080647) := by
    rw [show ((1080647 / 1000000) : ℝ) = ((1000000 / 1080647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1474_neg : (84085117 / 1000000000) ≤ -Real.log (919353 / 1000000) ∧
    -Real.log (919353 / 1000000) ≤ (42042559 / 500000000) := by
  have h := checkLog_sound (w := (80647 / 1919353)) (n := 12)
    (lo := (84085117 / 1000000000)) (hi := (42042559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919353) = 1/(919353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1474 : Bounds (-42042559 / 500000000) (-84085117 / 1000000000) (Real.log (919353 / 1000000)) := by
  have h := reflection_log_1474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1475_neg : (7775517 / 100000000) ≤ -Real.log (500000 / 540429) ∧
    -Real.log (500000 / 540429) ≤ (77755171 / 1000000000) := by
  have h := checkLog_sound (w := (40429 / 1040429)) (n := 12)
    (lo := (7775517 / 100000000)) (hi := (77755171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540429 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540429 / 500000) = 1/(500000 / 540429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1475 : Bounds (7775517 / 100000000) (77755171 / 1000000000) (Real.log (540429 / 500000)) := by
  have h := reflection_log_1475_neg
  have he : Real.log (540429 / 500000) = -Real.log (500000 / 540429) := by
    rw [show ((540429 / 500000) : ℝ) = ((500000 / 540429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1476_neg : (21078663 / 250000000) ≤ -Real.log (459571 / 500000) ∧
    -Real.log (459571 / 500000) ≤ (84314653 / 1000000000) := by
  have h := checkLog_sound (w := (40429 / 959571)) (n := 12)
    (lo := (21078663 / 250000000)) (hi := (84314653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459571) = 1/(459571 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1476 : Bounds (-84314653 / 1000000000) (-21078663 / 250000000) (Real.log (459571 / 500000)) := by
  have h := reflection_log_1476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1477_neg : (3279741 / 500000000) ≤ -Real.log (248365495959 / 250000000000) ∧
    -Real.log (248365495959 / 250000000000) ≤ (6559483 / 1000000000) := by
  have h := checkLog_sound (w := (1634504041 / 498365495959)) (n := 12)
    (lo := (3279741 / 500000000)) (hi := (6559483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248365495959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248365495959) = 1/(248365495959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1477 : Bounds (-6559483 / 1000000000) (-3279741 / 500000000) (Real.log (248365495959 / 250000000000)) := by
  have h := reflection_log_1477_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1478_neg : (6525181 / 1000000000) ≤ -Real.log (993496061391 / 1000000000000) ∧
    -Real.log (993496061391 / 1000000000000) ≤ (3262591 / 500000000) := by
  have h := checkLog_sound (w := (6503938609 / 1993496061391)) (n := 12)
    (lo := (6525181 / 1000000000)) (hi := (3262591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993496061391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993496061391) = 1/(993496061391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1478 : Bounds (-3262591 / 500000000) (-6525181 / 1000000000) (Real.log (993496061391 / 1000000000000)) := by
  have h := reflection_log_1478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1479_neg : (161645053 / 1000000000) ≤ -Real.log (62500000000 / 73465184211) ∧
    -Real.log (62500000000 / 73465184211) ≤ (80822527 / 500000000) := by
  have h := checkLog_sound (w := (10965184211 / 135965184211)) (n := 12)
    (lo := (161645053 / 1000000000)) (hi := (80822527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73465184211 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73465184211 / 62500000000) = 1/(62500000000 / 73465184211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1479 : Bounds (161645053 / 1000000000) (80822527 / 500000000) (Real.log (73465184211 / 62500000000)) := by
  have h := reflection_log_1479_neg
  have he : Real.log (73465184211 / 62500000000) = -Real.log (62500000000 / 73465184211) := by
    rw [show ((73465184211 / 62500000000) : ℝ) = ((62500000000 / 73465184211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1480_neg : (81034911 / 500000000) ≤ -Real.log (125000000000 / 146992793279) ∧
    -Real.log (125000000000 / 146992793279) ≤ (162069823 / 1000000000) := by
  have h := checkLog_sound (w := (21992793279 / 271992793279)) (n := 12)
    (lo := (81034911 / 500000000)) (hi := (162069823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146992793279 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146992793279 / 125000000000) = 1/(125000000000 / 146992793279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1480 : Bounds (81034911 / 500000000) (162069823 / 1000000000) (Real.log (146992793279 / 125000000000)) := by
  have h := reflection_log_1480_neg
  have he : Real.log (146992793279 / 125000000000) = -Real.log (125000000000 / 146992793279) := by
    rw [show ((146992793279 / 125000000000) : ℝ) = ((125000000000 / 146992793279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1481_neg : (324210339 / 1000000000) ≤ -Real.log (500000000000 / 691469081377) ∧
    -Real.log (500000000000 / 691469081377) ≤ (16210517 / 50000000) := by
  have h := checkLog_sound (w := (191469081377 / 1191469081377)) (n := 12)
    (lo := (324210339 / 1000000000)) (hi := (16210517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691469081377 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691469081377 / 500000000000) = 1/(500000000000 / 691469081377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1481 : Bounds (324210339 / 1000000000) (16210517 / 50000000) (Real.log (691469081377 / 500000000000)) := by
  have h := reflection_log_1481_neg
  have he : Real.log (691469081377 / 500000000000) = -Real.log (500000000000 / 691469081377) := by
    rw [show ((691469081377 / 500000000000) : ℝ) = ((500000000000 / 691469081377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1482_neg : (81103911 / 250000000) ≤ -Real.log (500000000000 / 691611058151) ∧
    -Real.log (500000000000 / 691611058151) ≤ (64883129 / 200000000) := by
  have h := checkLog_sound (w := (191611058151 / 1191611058151)) (n := 12)
    (lo := (81103911 / 250000000)) (hi := (64883129 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691611058151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691611058151 / 500000000000) = 1/(500000000000 / 691611058151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1482 : Bounds (81103911 / 250000000) (64883129 / 200000000) (Real.log (691611058151 / 500000000000)) := by
  have h := reflection_log_1482_neg
  have he : Real.log (691611058151 / 500000000000) = -Real.log (500000000000 / 691611058151) := by
    rw [show ((691611058151 / 500000000000) : ℝ) = ((500000000000 / 691611058151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1483_neg : (74597783 / 500000000) ≤ -Real.log (10000 / 11609) ∧
    -Real.log (10000 / 11609) ≤ (149195567 / 1000000000) := by
  have h := checkLog_sound (w := (1609 / 21609)) (n := 12)
    (lo := (74597783 / 500000000)) (hi := (149195567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11609 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11609 / 10000) = 1/(10000 / 11609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1483 : Bounds (74597783 / 500000000) (149195567 / 1000000000) (Real.log (11609 / 10000)) := by
  have h := reflection_log_1483_neg
  have he : Real.log (11609 / 10000) = -Real.log (10000 / 11609) := by
    rw [show ((11609 / 10000) : ℝ) = ((10000 / 11609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1484_neg : (17542539 / 100000000) ≤ -Real.log (8391 / 10000) ∧
    -Real.log (8391 / 10000) ≤ (175425391 / 1000000000) := by
  have h := checkLog_sound (w := (1609 / 18391)) (n := 12)
    (lo := (17542539 / 100000000)) (hi := (175425391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8391) = 1/(8391 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1484 : Bounds (-175425391 / 1000000000) (-17542539 / 100000000) (Real.log (8391 / 10000)) := by
  have h := reflection_log_1484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1485_neg : (160887 / 1000000000) ≤ -Real.log (10000000 / 10001609) ∧
    -Real.log (10000000 / 10001609) ≤ (20111 / 125000000) := by
  have h := checkLog_sound (w := (1609 / 20001609)) (n := 12)
    (lo := (160887 / 1000000000)) (hi := (20111 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001609 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001609 / 10000000) = 1/(10000000 / 10001609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1485 : Bounds (160887 / 1000000000) (20111 / 125000000) (Real.log (10001609 / 10000000)) := by
  have h := reflection_log_1485_neg
  have he : Real.log (10001609 / 10000000) = -Real.log (10000000 / 10001609) := by
    rw [show ((10001609 / 10000000) : ℝ) = ((10000000 / 10001609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1486_neg : (10057 / 62500000) ≤ -Real.log (9998391 / 10000000) ∧
    -Real.log (9998391 / 10000000) ≤ (160913 / 1000000000) := by
  have h := checkLog_sound (w := (1609 / 19998391)) (n := 12)
    (lo := (10057 / 62500000)) (hi := (160913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998391) = 1/(9998391 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1486 : Bounds (-160913 / 1000000000) (-10057 / 62500000) (Real.log (9998391 / 10000000)) := by
  have h := reflection_log_1486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1487_neg : (77606203 / 1000000000) ≤ -Real.log (1000000 / 1080697) ∧
    -Real.log (1000000 / 1080697) ≤ (19401551 / 250000000) := by
  have h := checkLog_sound (w := (80697 / 2080697)) (n := 12)
    (lo := (77606203 / 1000000000)) (hi := (19401551 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080697 / 1000000) = 1/(1000000 / 1080697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1487 : Bounds (77606203 / 1000000000) (19401551 / 250000000) (Real.log (1080697 / 1000000)) := by
  have h := reflection_log_1487_neg
  have he : Real.log (1080697 / 1000000) = -Real.log (1000000 / 1080697) := by
    rw [show ((1080697 / 1000000) : ℝ) = ((1000000 / 1080697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1488_neg : (5258719 / 62500000) ≤ -Real.log (919303 / 1000000) ∧
    -Real.log (919303 / 1000000) ≤ (16827901 / 200000000) := by
  have h := checkLog_sound (w := (80697 / 1919303)) (n := 12)
    (lo := (5258719 / 62500000)) (hi := (16827901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919303) = 1/(919303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1488 : Bounds (-16827901 / 200000000) (-5258719 / 62500000) (Real.log (919303 / 1000000)) := by
  have h := reflection_log_1488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1489_neg : (77802353 / 1000000000) ≤ -Real.log (1000000 / 1080909) ∧
    -Real.log (1000000 / 1080909) ≤ (38901177 / 500000000) := by
  have h := checkLog_sound (w := (80909 / 2080909)) (n := 12)
    (lo := (77802353 / 1000000000)) (hi := (38901177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080909 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080909 / 1000000) = 1/(1000000 / 1080909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1489 : Bounds (77802353 / 1000000000) (38901177 / 500000000) (Real.log (1080909 / 1000000)) := by
  have h := reflection_log_1489_neg
  have he : Real.log (1080909 / 1000000) = -Real.log (1000000 / 1080909) := by
    rw [show ((1080909 / 1000000) : ℝ) = ((1000000 / 1080909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1490_neg : (4218507 / 50000000) ≤ -Real.log (919091 / 1000000) ∧
    -Real.log (919091 / 1000000) ≤ (84370141 / 1000000000) := by
  have h := checkLog_sound (w := (80909 / 1919091)) (n := 12)
    (lo := (4218507 / 50000000)) (hi := (84370141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919091) = 1/(919091 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1490 : Bounds (-84370141 / 1000000000) (-4218507 / 50000000) (Real.log (919091 / 1000000)) := by
  have h := reflection_log_1490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1491_neg : (6567787 / 1000000000) ≤ -Real.log (993453733719 / 1000000000000) ∧
    -Real.log (993453733719 / 1000000000000) ≤ (1641947 / 250000000) := by
  have h := checkLog_sound (w := (6546266281 / 1993453733719)) (n := 12)
    (lo := (6567787 / 1000000000)) (hi := (1641947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993453733719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993453733719) = 1/(993453733719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1491 : Bounds (-1641947 / 250000000) (-6567787 / 1000000000) (Real.log (993453733719 / 1000000000000)) := by
  have h := reflection_log_1491_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1492_neg : (6533301 / 1000000000) ≤ -Real.log (993487994191 / 1000000000000) ∧
    -Real.log (993487994191 / 1000000000000) ≤ (3266651 / 500000000) := by
  have h := checkLog_sound (w := (6512005809 / 1993487994191)) (n := 12)
    (lo := (6533301 / 1000000000)) (hi := (3266651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993487994191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993487994191) = 1/(993487994191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1492 : Bounds (-3266651 / 500000000) (-6533301 / 1000000000) (Real.log (993487994191 / 1000000000000)) := by
  have h := reflection_log_1492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1493_neg : (40436427 / 250000000) ≤ -Real.log (250000000000 / 293890316903) ∧
    -Real.log (250000000000 / 293890316903) ≤ (161745709 / 1000000000) := by
  have h := checkLog_sound (w := (43890316903 / 543890316903)) (n := 12)
    (lo := (40436427 / 250000000)) (hi := (161745709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293890316903 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293890316903 / 250000000000) = 1/(250000000000 / 293890316903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1493 : Bounds (40436427 / 250000000) (161745709 / 1000000000) (Real.log (293890316903 / 250000000000)) := by
  have h := reflection_log_1493_neg
  have he : Real.log (293890316903 / 250000000000) = -Real.log (250000000000 / 293890316903) := by
    rw [show ((293890316903 / 250000000000) : ℝ) = ((250000000000 / 293890316903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1494_neg : (81086247 / 500000000) ≤ -Real.log (500000000000 / 588031544211) ∧
    -Real.log (500000000000 / 588031544211) ≤ (32434499 / 200000000) := by
  have h := checkLog_sound (w := (88031544211 / 1088031544211)) (n := 12)
    (lo := (81086247 / 500000000)) (hi := (32434499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588031544211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588031544211 / 500000000000) = 1/(500000000000 / 588031544211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1494 : Bounds (81086247 / 500000000) (32434499 / 200000000) (Real.log (588031544211 / 500000000000)) := by
  have h := reflection_log_1494_neg
  have he : Real.log (588031544211 / 500000000000) = -Real.log (500000000000 / 588031544211) := by
    rw [show ((588031544211 / 500000000000) : ℝ) = ((500000000000 / 588031544211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1495_neg : (81103911 / 250000000) ≤ -Real.log (10000000000 / 13832221163) ∧
    -Real.log (10000000000 / 13832221163) ≤ (64883129 / 200000000) := by
  have h := checkLog_sound (w := (3832221163 / 23832221163)) (n := 12)
    (lo := (81103911 / 250000000)) (hi := (64883129 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13832221163 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13832221163 / 10000000000) = 1/(10000000000 / 13832221163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1495 : Bounds (81103911 / 250000000) (64883129 / 200000000) (Real.log (13832221163 / 10000000000)) := by
  have h := reflection_log_1495_neg
  have he : Real.log (13832221163 / 10000000000) = -Real.log (10000000000 / 13832221163) := by
    rw [show ((13832221163 / 10000000000) : ℝ) = ((10000000000 / 13832221163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1496_neg : (81155239 / 250000000) ≤ -Real.log (100000000000 / 138350613753) ∧
    -Real.log (100000000000 / 138350613753) ≤ (324620957 / 1000000000) := by
  have h := checkLog_sound (w := (38350613753 / 238350613753)) (n := 12)
    (lo := (81155239 / 250000000)) (hi := (324620957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138350613753 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138350613753 / 100000000000) = 1/(100000000000 / 138350613753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1496 : Bounds (81155239 / 250000000) (324620957 / 1000000000) (Real.log (138350613753 / 100000000000)) := by
  have h := reflection_log_1496_neg
  have he : Real.log (138350613753 / 100000000000) = -Real.log (100000000000 / 138350613753) := by
    rw [show ((138350613753 / 100000000000) : ℝ) = ((100000000000 / 138350613753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1497_neg : (74640851 / 500000000) ≤ -Real.log (1000 / 1161) ∧
    -Real.log (1000 / 1161) ≤ (149281703 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 2161)) (n := 12)
    (lo := (74640851 / 500000000)) (hi := (149281703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161 / 1000) = 1/(1000 / 1161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1497 : Bounds (74640851 / 500000000) (149281703 / 1000000000) (Real.log (1161 / 1000)) := by
  have h := reflection_log_1497_neg
  have he : Real.log (1161 / 1000) = -Real.log (1000 / 1161) := by
    rw [show ((1161 / 1000) : ℝ) = ((1000 / 1161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1498_neg : (43886143 / 250000000) ≤ -Real.log (839 / 1000) ∧
    -Real.log (839 / 1000) ≤ (175544573 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1839)) (n := 12)
    (lo := (43886143 / 250000000)) (hi := (175544573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 839) = 1/(839 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1498 : Bounds (-175544573 / 1000000000) (-43886143 / 250000000) (Real.log (839 / 1000)) := by
  have h := reflection_log_1498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1499_neg : (160987 / 1000000000) ≤ -Real.log (1000000 / 1000161) ∧
    -Real.log (1000000 / 1000161) ≤ (40247 / 250000000) := by
  have h := checkLog_sound (w := (161 / 2000161)) (n := 12)
    (lo := (160987 / 1000000000)) (hi := (40247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000161 / 1000000) = 1/(1000000 / 1000161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1499 : Bounds (160987 / 1000000000) (40247 / 250000000) (Real.log (1000161 / 1000000)) := by
  have h := reflection_log_1499_neg
  have he : Real.log (1000161 / 1000000) = -Real.log (1000000 / 1000161) := by
    rw [show ((1000161 / 1000000) : ℝ) = ((1000000 / 1000161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1500_neg : (40253 / 250000000) ≤ -Real.log (999839 / 1000000) ∧
    -Real.log (999839 / 1000000) ≤ (161013 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1999839)) (n := 12)
    (lo := (40253 / 250000000)) (hi := (161013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999839) = 1/(999839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1500 : Bounds (-161013 / 1000000000) (-40253 / 250000000) (Real.log (999839 / 1000000)) := by
  have h := reflection_log_1500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1501_neg : (77653393 / 1000000000) ≤ -Real.log (250000 / 270187) ∧
    -Real.log (250000 / 270187) ≤ (38826697 / 500000000) := by
  have h := checkLog_sound (w := (20187 / 520187)) (n := 12)
    (lo := (77653393 / 1000000000)) (hi := (38826697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270187 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270187 / 250000) = 1/(250000 / 270187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1501 : Bounds (77653393 / 1000000000) (38826697 / 500000000) (Real.log (270187 / 250000)) := by
  have h := reflection_log_1501_neg
  have he : Real.log (270187 / 250000) = -Real.log (250000 / 270187) := by
    rw [show ((270187 / 250000) : ℝ) = ((250000 / 270187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1502_neg : (84194983 / 1000000000) ≤ -Real.log (229813 / 250000) ∧
    -Real.log (229813 / 250000) ≤ (10524373 / 125000000) := by
  have h := checkLog_sound (w := (20187 / 479813)) (n := 12)
    (lo := (84194983 / 1000000000)) (hi := (10524373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229813) = 1/(229813 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1502 : Bounds (-10524373 / 125000000) (-84194983 / 1000000000) (Real.log (229813 / 250000)) := by
  have h := reflection_log_1502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1503_neg : (15569907 / 200000000) ≤ -Real.log (3125 / 3378) ∧
    -Real.log (3125 / 3378) ≤ (1216399 / 15625000) := by
  have h := checkLog_sound (w := (253 / 6503)) (n := 12)
    (lo := (15569907 / 200000000)) (hi := (1216399 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3378 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3378 / 3125) = 1/(3125 / 3378) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1503 : Bounds (15569907 / 200000000) (1216399 / 15625000) (Real.log (3378 / 3125)) := by
  have h := reflection_log_1503_neg
  have he : Real.log (3378 / 3125) = -Real.log (3125 / 3378) := by
    rw [show ((3378 / 3125) : ℝ) = ((3125 / 3378) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1504_neg : (2638301 / 31250000) ≤ -Real.log (2872 / 3125) ∧
    -Real.log (2872 / 3125) ≤ (84425633 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 5997)) (n := 12)
    (lo := (2638301 / 31250000)) (hi := (84425633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2872) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2872) = 1/(2872 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1504 : Bounds (-84425633 / 1000000000) (-2638301 / 31250000) (Real.log (2872 / 3125)) := by
  have h := reflection_log_1504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1505_neg : (205503 / 31250000) ≤ -Real.log (9701616 / 9765625) ∧
    -Real.log (9701616 / 9765625) ≤ (6576097 / 1000000000) := by
  have h := checkLog_sound (w := (64009 / 19467241)) (n := 12)
    (lo := (205503 / 31250000)) (hi := (6576097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9701616) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9701616) = 1/(9701616 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1505 : Bounds (-6576097 / 1000000000) (-205503 / 31250000) (Real.log (9701616 / 9765625)) := by
  have h := reflection_log_1505_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1506_neg : (6541589 / 1000000000) ≤ -Real.log (62092485031 / 62500000000) ∧
    -Real.log (62092485031 / 62500000000) ≤ (654159 / 100000000) := by
  have h := checkLog_sound (w := (407514969 / 124592485031)) (n := 12)
    (lo := (6541589 / 1000000000)) (hi := (654159 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62092485031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62092485031) = 1/(62092485031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1506 : Bounds (-654159 / 100000000) (-6541589 / 1000000000) (Real.log (62092485031 / 62500000000)) := by
  have h := reflection_log_1506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1507_neg : (161848377 / 1000000000) ≤ -Real.log (125000000000 / 146960245939) ∧
    -Real.log (125000000000 / 146960245939) ≤ (80924189 / 500000000) := by
  have h := checkLog_sound (w := (21960245939 / 271960245939)) (n := 12)
    (lo := (161848377 / 1000000000)) (hi := (80924189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146960245939 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146960245939 / 125000000000) = 1/(125000000000 / 146960245939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1507 : Bounds (161848377 / 1000000000) (80924189 / 500000000) (Real.log (146960245939 / 125000000000)) := by
  have h := reflection_log_1507_neg
  have he : Real.log (146960245939 / 125000000000) = -Real.log (125000000000 / 146960245939) := by
    rw [show ((146960245939 / 125000000000) : ℝ) = ((125000000000 / 146960245939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1508_neg : (162275167 / 1000000000) ≤ -Real.log (250000000000 / 294045961003) ∧
    -Real.log (250000000000 / 294045961003) ≤ (5071099 / 31250000) := by
  have h := checkLog_sound (w := (44045961003 / 544045961003)) (n := 12)
    (lo := (162275167 / 1000000000)) (hi := (5071099 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294045961003 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294045961003 / 250000000000) = 1/(250000000000 / 294045961003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1508 : Bounds (162275167 / 1000000000) (5071099 / 31250000) (Real.log (294045961003 / 250000000000)) := by
  have h := reflection_log_1508_neg
  have he : Real.log (294045961003 / 250000000000) = -Real.log (250000000000 / 294045961003) := by
    rw [show ((294045961003 / 250000000000) : ℝ) = ((250000000000 / 294045961003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1509_neg : (81155239 / 250000000) ≤ -Real.log (125000000000 / 172938267191) ∧
    -Real.log (125000000000 / 172938267191) ≤ (324620957 / 1000000000) := by
  have h := checkLog_sound (w := (47938267191 / 297938267191)) (n := 12)
    (lo := (81155239 / 250000000)) (hi := (324620957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172938267191 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172938267191 / 125000000000) = 1/(125000000000 / 172938267191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1509 : Bounds (81155239 / 250000000) (324620957 / 1000000000) (Real.log (172938267191 / 125000000000)) := by
  have h := reflection_log_1509_neg
  have he : Real.log (172938267191 / 125000000000) = -Real.log (125000000000 / 172938267191) := by
    rw [show ((172938267191 / 125000000000) : ℝ) = ((125000000000 / 172938267191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1510_neg : (12993051 / 40000000) ≤ -Real.log (500000000000 / 691895113231) ∧
    -Real.log (500000000000 / 691895113231) ≤ (81206569 / 250000000) := by
  have h := checkLog_sound (w := (191895113231 / 1191895113231)) (n := 12)
    (lo := (12993051 / 40000000)) (hi := (81206569 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691895113231 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691895113231 / 500000000000) = 1/(500000000000 / 691895113231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1510 : Bounds (12993051 / 40000000) (81206569 / 250000000) (Real.log (691895113231 / 500000000000)) := by
  have h := reflection_log_1510_neg
  have he : Real.log (691895113231 / 500000000000) = -Real.log (500000000000 / 691895113231) := by
    rw [show ((691895113231 / 500000000000) : ℝ) = ((500000000000 / 691895113231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1511_neg : (149367831 / 1000000000) ≤ -Real.log (10000 / 11611) ∧
    -Real.log (10000 / 11611) ≤ (18670979 / 125000000) := by
  have h := checkLog_sound (w := (1611 / 21611)) (n := 12)
    (lo := (149367831 / 1000000000)) (hi := (18670979 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11611 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11611 / 10000) = 1/(10000 / 11611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1511 : Bounds (149367831 / 1000000000) (18670979 / 125000000) (Real.log (11611 / 10000)) := by
  have h := reflection_log_1511_neg
  have he : Real.log (11611 / 10000) = -Real.log (10000 / 11611) := by
    rw [show ((11611 / 10000) : ℝ) = ((10000 / 11611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1512_neg : (175663769 / 1000000000) ≤ -Real.log (8389 / 10000) ∧
    -Real.log (8389 / 10000) ≤ (17566377 / 100000000) := by
  have h := checkLog_sound (w := (1611 / 18389)) (n := 12)
    (lo := (175663769 / 1000000000)) (hi := (17566377 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8389) = 1/(8389 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1512 : Bounds (-17566377 / 100000000) (-175663769 / 1000000000) (Real.log (8389 / 10000)) := by
  have h := reflection_log_1512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1513_neg : (161087 / 1000000000) ≤ -Real.log (10000000 / 10001611) ∧
    -Real.log (10000000 / 10001611) ≤ (2517 / 15625000) := by
  have h := checkLog_sound (w := (1611 / 20001611)) (n := 12)
    (lo := (161087 / 1000000000)) (hi := (2517 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001611 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001611 / 10000000) = 1/(10000000 / 10001611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1513 : Bounds (161087 / 1000000000) (2517 / 15625000) (Real.log (10001611 / 10000000)) := by
  have h := reflection_log_1513_neg
  have he : Real.log (10001611 / 10000000) = -Real.log (10000000 / 10001611) := by
    rw [show ((10001611 / 10000000) : ℝ) = ((10000000 / 10001611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1514_neg : (20139 / 125000000) ≤ -Real.log (9998389 / 10000000) ∧
    -Real.log (9998389 / 10000000) ≤ (161113 / 1000000000) := by
  have h := checkLog_sound (w := (1611 / 19998389)) (n := 12)
    (lo := (20139 / 125000000)) (hi := (161113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998389) = 1/(9998389 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1514 : Bounds (-161113 / 1000000000) (-20139 / 125000000) (Real.log (9998389 / 10000000)) := by
  have h := reflection_log_1514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1515_neg : (38850291 / 500000000) ≤ -Real.log (1000000 / 1080799) ∧
    -Real.log (1000000 / 1080799) ≤ (77700583 / 1000000000) := by
  have h := checkLog_sound (w := (80799 / 2080799)) (n := 12)
    (lo := (38850291 / 500000000)) (hi := (77700583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080799 / 1000000) = 1/(1000000 / 1080799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1515 : Bounds (38850291 / 500000000) (77700583 / 1000000000) (Real.log (1080799 / 1000000)) := by
  have h := reflection_log_1515_neg
  have he : Real.log (1080799 / 1000000) = -Real.log (1000000 / 1080799) := by
    rw [show ((1080799 / 1000000) : ℝ) = ((1000000 / 1080799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1516_neg : (2632827 / 31250000) ≤ -Real.log (919201 / 1000000) ∧
    -Real.log (919201 / 1000000) ≤ (16850093 / 200000000) := by
  have h := checkLog_sound (w := (80799 / 1919201)) (n := 12)
    (lo := (2632827 / 31250000)) (hi := (16850093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919201) = 1/(919201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1516 : Bounds (-16850093 / 200000000) (-2632827 / 31250000) (Real.log (919201 / 1000000)) := by
  have h := reflection_log_1516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1517_neg : (38948357 / 500000000) ≤ -Real.log (1000000 / 1081011) ∧
    -Real.log (1000000 / 1081011) ≤ (15579343 / 200000000) := by
  have h := checkLog_sound (w := (81011 / 2081011)) (n := 12)
    (lo := (38948357 / 500000000)) (hi := (15579343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081011 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081011 / 1000000) = 1/(1000000 / 1081011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1517 : Bounds (38948357 / 500000000) (15579343 / 200000000) (Real.log (1081011 / 1000000)) := by
  have h := reflection_log_1517_neg
  have he : Real.log (1081011 / 1000000) = -Real.log (1000000 / 1081011) := by
    rw [show ((1081011 / 1000000) : ℝ) = ((1000000 / 1081011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1518_neg : (42240563 / 500000000) ≤ -Real.log (918989 / 1000000) ∧
    -Real.log (918989 / 1000000) ≤ (84481127 / 1000000000) := by
  have h := checkLog_sound (w := (81011 / 1918989)) (n := 12)
    (lo := (42240563 / 500000000)) (hi := (84481127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918989) = 1/(918989 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1518 : Bounds (-84481127 / 1000000000) (-42240563 / 500000000) (Real.log (918989 / 1000000)) := by
  have h := reflection_log_1518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1519_neg : (6584411 / 1000000000) ≤ -Real.log (993437217879 / 1000000000000) ∧
    -Real.log (993437217879 / 1000000000000) ≤ (1646103 / 250000000) := by
  have h := checkLog_sound (w := (6562782121 / 1993437217879)) (n := 12)
    (lo := (6584411 / 1000000000)) (hi := (1646103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993437217879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993437217879) = 1/(993437217879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1519 : Bounds (-1646103 / 250000000) (-6584411 / 1000000000) (Real.log (993437217879 / 1000000000000)) := by
  have h := reflection_log_1519_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1520_neg : (3274941 / 500000000) ≤ -Real.log (993471521599 / 1000000000000) ∧
    -Real.log (993471521599 / 1000000000000) ≤ (6549883 / 1000000000) := by
  have h := checkLog_sound (w := (6528478401 / 1993471521599)) (n := 12)
    (lo := (3274941 / 500000000)) (hi := (6549883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993471521599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993471521599) = 1/(993471521599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1520 : Bounds (-6549883 / 1000000000) (-3274941 / 500000000) (Real.log (993471521599 / 1000000000000)) := by
  have h := reflection_log_1520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1521_neg : (80975523 / 500000000) ≤ -Real.log (500000000000 / 587901340403) ∧
    -Real.log (500000000000 / 587901340403) ≤ (161951047 / 1000000000) := by
  have h := checkLog_sound (w := (87901340403 / 1087901340403)) (n := 12)
    (lo := (80975523 / 500000000)) (hi := (161951047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587901340403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587901340403 / 500000000000) = 1/(500000000000 / 587901340403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1521 : Bounds (80975523 / 500000000) (161951047 / 1000000000) (Real.log (587901340403 / 500000000000)) := by
  have h := reflection_log_1521_neg
  have he : Real.log (587901340403 / 500000000000) = -Real.log (500000000000 / 587901340403) := by
    rw [show ((587901340403 / 500000000000) : ℝ) = ((500000000000 / 587901340403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1522_neg : (2029723 / 12500000) ≤ -Real.log (500000000000 / 588152306503) ∧
    -Real.log (500000000000 / 588152306503) ≤ (162377841 / 1000000000) := by
  have h := checkLog_sound (w := (88152306503 / 1088152306503)) (n := 12)
    (lo := (2029723 / 12500000)) (hi := (162377841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588152306503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588152306503 / 500000000000) = 1/(500000000000 / 588152306503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1522 : Bounds (2029723 / 12500000) (162377841 / 1000000000) (Real.log (588152306503 / 500000000000)) := by
  have h := reflection_log_1522_neg
  have he : Real.log (588152306503 / 500000000000) = -Real.log (500000000000 / 588152306503) := by
    rw [show ((588152306503 / 500000000000) : ℝ) = ((500000000000 / 588152306503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1523_neg : (12993051 / 40000000) ≤ -Real.log (50000000000 / 69189511323) ∧
    -Real.log (50000000000 / 69189511323) ≤ (81206569 / 250000000) := by
  have h := checkLog_sound (w := (19189511323 / 119189511323)) (n := 12)
    (lo := (12993051 / 40000000)) (hi := (81206569 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69189511323 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69189511323 / 50000000000) = 1/(50000000000 / 69189511323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1523 : Bounds (12993051 / 40000000) (81206569 / 250000000) (Real.log (69189511323 / 50000000000)) := by
  have h := reflection_log_1523_neg
  have he : Real.log (69189511323 / 50000000000) = -Real.log (50000000000 / 69189511323) := by
    rw [show ((69189511323 / 50000000000) : ℝ) = ((50000000000 / 69189511323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1524_neg : (812579 / 2500000) ≤ -Real.log (500000000000 / 692037191561) ∧
    -Real.log (500000000000 / 692037191561) ≤ (325031601 / 1000000000) := by
  have h := checkLog_sound (w := (192037191561 / 1192037191561)) (n := 12)
    (lo := (812579 / 2500000)) (hi := (325031601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692037191561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692037191561 / 500000000000) = 1/(500000000000 / 692037191561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1524 : Bounds (812579 / 2500000) (325031601 / 1000000000) (Real.log (692037191561 / 500000000000)) := by
  have h := reflection_log_1524_neg
  have he : Real.log (692037191561 / 500000000000) = -Real.log (500000000000 / 692037191561) := by
    rw [show ((692037191561 / 500000000000) : ℝ) = ((500000000000 / 692037191561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1525_neg : (149453953 / 1000000000) ≤ -Real.log (2500 / 2903) ∧
    -Real.log (2500 / 2903) ≤ (74726977 / 500000000) := by
  have h := checkLog_sound (w := (403 / 5403)) (n := 12)
    (lo := (149453953 / 1000000000)) (hi := (74726977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2903 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2903 / 2500) = 1/(2500 / 2903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1525 : Bounds (149453953 / 1000000000) (74726977 / 500000000) (Real.log (2903 / 2500)) := by
  have h := reflection_log_1525_neg
  have he : Real.log (2903 / 2500) = -Real.log (2500 / 2903) := by
    rw [show ((2903 / 2500) : ℝ) = ((2500 / 2903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1526_neg : (175782979 / 1000000000) ≤ -Real.log (2097 / 2500) ∧
    -Real.log (2097 / 2500) ≤ (8789149 / 50000000) := by
  have h := checkLog_sound (w := (403 / 4597)) (n := 12)
    (lo := (175782979 / 1000000000)) (hi := (8789149 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2097) = 1/(2097 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1526 : Bounds (-8789149 / 50000000) (-175782979 / 1000000000) (Real.log (2097 / 2500)) := by
  have h := reflection_log_1526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1527_neg : (161187 / 1000000000) ≤ -Real.log (2500000 / 2500403) ∧
    -Real.log (2500000 / 2500403) ≤ (40297 / 250000000) := by
  have h := checkLog_sound (w := (403 / 5000403)) (n := 12)
    (lo := (161187 / 1000000000)) (hi := (40297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500403 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500403 / 2500000) = 1/(2500000 / 2500403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1527 : Bounds (161187 / 1000000000) (40297 / 250000000) (Real.log (2500403 / 2500000)) := by
  have h := reflection_log_1527_neg
  have he : Real.log (2500403 / 2500000) = -Real.log (2500000 / 2500403) := by
    rw [show ((2500403 / 2500000) : ℝ) = ((2500000 / 2500403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1528_neg : (40303 / 250000000) ≤ -Real.log (2499597 / 2500000) ∧
    -Real.log (2499597 / 2500000) ≤ (161213 / 1000000000) := by
  have h := checkLog_sound (w := (403 / 4999597)) (n := 12)
    (lo := (40303 / 250000000)) (hi := (161213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499597) = 1/(2499597 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1528 : Bounds (-161213 / 1000000000) (-40303 / 250000000) (Real.log (2499597 / 2500000)) := by
  have h := reflection_log_1528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1529_neg : (77746843 / 1000000000) ≤ -Real.log (1000000 / 1080849) ∧
    -Real.log (1000000 / 1080849) ≤ (19436711 / 250000000) := by
  have h := checkLog_sound (w := (80849 / 2080849)) (n := 12)
    (lo := (77746843 / 1000000000)) (hi := (19436711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080849 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080849 / 1000000) = 1/(1000000 / 1080849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1529 : Bounds (77746843 / 1000000000) (19436711 / 250000000) (Real.log (1080849 / 1000000)) := by
  have h := reflection_log_1529_neg
  have he : Real.log (1080849 / 1000000) = -Real.log (1000000 / 1080849) := by
    rw [show ((1080849 / 1000000) : ℝ) = ((1000000 / 1080849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1530_neg : (84304861 / 1000000000) ≤ -Real.log (919151 / 1000000) ∧
    -Real.log (919151 / 1000000) ≤ (42152431 / 500000000) := by
  have h := checkLog_sound (w := (80849 / 1919151)) (n := 12)
    (lo := (84304861 / 1000000000)) (hi := (42152431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919151) = 1/(919151 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1530 : Bounds (-42152431 / 500000000) (-84304861 / 1000000000) (Real.log (919151 / 1000000)) := by
  have h := reflection_log_1530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1531_neg : (38971483 / 500000000) ≤ -Real.log (1000000 / 1081061) ∧
    -Real.log (1000000 / 1081061) ≤ (77942967 / 1000000000) := by
  have h := checkLog_sound (w := (81061 / 2081061)) (n := 12)
    (lo := (38971483 / 500000000)) (hi := (77942967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081061 / 1000000) = 1/(1000000 / 1081061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1531 : Bounds (38971483 / 500000000) (77942967 / 1000000000) (Real.log (1081061 / 1000000)) := by
  have h := reflection_log_1531_neg
  have he : Real.log (1081061 / 1000000) = -Real.log (1000000 / 1081061) := by
    rw [show ((1081061 / 1000000) : ℝ) = ((1000000 / 1081061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1532_neg : (16907107 / 200000000) ≤ -Real.log (918939 / 1000000) ∧
    -Real.log (918939 / 1000000) ≤ (5283471 / 62500000) := by
  have h := checkLog_sound (w := (81061 / 1918939)) (n := 12)
    (lo := (16907107 / 200000000)) (hi := (5283471 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918939) = 1/(918939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1532 : Bounds (-5283471 / 62500000) (-16907107 / 200000000) (Real.log (918939 / 1000000)) := by
  have h := reflection_log_1532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1533_neg : (6592569 / 1000000000) ≤ -Real.log (993429114279 / 1000000000000) ∧
    -Real.log (993429114279 / 1000000000000) ≤ (659257 / 100000000) := by
  have h := checkLog_sound (w := (6570885721 / 1993429114279)) (n := 12)
    (lo := (6592569 / 1000000000)) (hi := (659257 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993429114279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993429114279) = 1/(993429114279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1533 : Bounds (-659257 / 100000000) (-6592569 / 1000000000) (Real.log (993429114279 / 1000000000000)) := by
  have h := reflection_log_1533_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1534_neg : (6558017 / 1000000000) ≤ -Real.log (993463439199 / 1000000000000) ∧
    -Real.log (993463439199 / 1000000000000) ≤ (3279009 / 500000000) := by
  have h := checkLog_sound (w := (6536560801 / 1993463439199)) (n := 12)
    (lo := (6558017 / 1000000000)) (hi := (3279009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993463439199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993463439199) = 1/(993463439199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1534 : Bounds (-3279009 / 500000000) (-6558017 / 1000000000) (Real.log (993463439199 / 1000000000000)) := by
  have h := reflection_log_1534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1535_neg : (20256463 / 125000000) ≤ -Real.log (62500000000 / 73495065011) ∧
    -Real.log (62500000000 / 73495065011) ≤ (32410341 / 200000000) := by
  have h := checkLog_sound (w := (10995065011 / 135995065011)) (n := 12)
    (lo := (20256463 / 125000000)) (hi := (32410341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73495065011 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73495065011 / 62500000000) = 1/(62500000000 / 73495065011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1535 : Bounds (20256463 / 125000000) (32410341 / 200000000) (Real.log (73495065011 / 62500000000)) := by
  have h := reflection_log_1535_neg
  have he : Real.log (73495065011 / 62500000000) = -Real.log (62500000000 / 73495065011) := by
    rw [show ((73495065011 / 62500000000) : ℝ) = ((62500000000 / 73495065011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0024 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1536_neg : (162478501 / 1000000000) ≤ -Real.log (62500000000 / 73526439187) ∧
    -Real.log (62500000000 / 73526439187) ≤ (81239251 / 500000000) := by
  have h := checkLog_sound (w := (11026439187 / 136026439187)) (n := 12)
    (lo := (162478501 / 1000000000)) (hi := (81239251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73526439187 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73526439187 / 62500000000) = 1/(62500000000 / 73526439187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1536 : Bounds (162478501 / 1000000000) (81239251 / 500000000) (Real.log (73526439187 / 62500000000)) := by
  have h := reflection_log_1536_neg
  have he : Real.log (73526439187 / 62500000000) = -Real.log (62500000000 / 73526439187) := by
    rw [show ((73526439187 / 62500000000) : ℝ) = ((62500000000 / 73526439187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1537_neg : (812579 / 2500000) ≤ -Real.log (12500000000 / 17300929789) ∧
    -Real.log (12500000000 / 17300929789) ≤ (325031601 / 1000000000) := by
  have h := checkLog_sound (w := (4800929789 / 29800929789)) (n := 12)
    (lo := (812579 / 2500000)) (hi := (325031601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17300929789 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17300929789 / 12500000000) = 1/(12500000000 / 17300929789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1537 : Bounds (812579 / 2500000) (325031601 / 1000000000) (Real.log (17300929789 / 12500000000)) := by
  have h := reflection_log_1537_neg
  have he : Real.log (17300929789 / 12500000000) = -Real.log (12500000000 / 17300929789) := by
    rw [show ((17300929789 / 12500000000) : ℝ) = ((12500000000 / 17300929789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1538_neg : (325236933 / 1000000000) ≤ -Real.log (62500000000 / 86522412971) ∧
    -Real.log (62500000000 / 86522412971) ≤ (162618467 / 500000000) := by
  have h := checkLog_sound (w := (24022412971 / 149022412971)) (n := 12)
    (lo := (325236933 / 1000000000)) (hi := (162618467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86522412971 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86522412971 / 62500000000) = 1/(62500000000 / 86522412971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1538 : Bounds (325236933 / 1000000000) (162618467 / 500000000) (Real.log (86522412971 / 62500000000)) := by
  have h := reflection_log_1538_neg
  have he : Real.log (86522412971 / 62500000000) = -Real.log (62500000000 / 86522412971) := by
    rw [show ((86522412971 / 62500000000) : ℝ) = ((62500000000 / 86522412971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1539_neg : (149540067 / 1000000000) ≤ -Real.log (10000 / 11613) ∧
    -Real.log (10000 / 11613) ≤ (37385017 / 250000000) := by
  have h := checkLog_sound (w := (1613 / 21613)) (n := 12)
    (lo := (149540067 / 1000000000)) (hi := (37385017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11613 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11613 / 10000) = 1/(10000 / 11613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1539 : Bounds (149540067 / 1000000000) (37385017 / 250000000) (Real.log (11613 / 10000)) := by
  have h := reflection_log_1539_neg
  have he : Real.log (11613 / 10000) = -Real.log (10000 / 11613) := by
    rw [show ((11613 / 10000) : ℝ) = ((10000 / 11613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1540_neg : (43975551 / 250000000) ≤ -Real.log (8387 / 10000) ∧
    -Real.log (8387 / 10000) ≤ (35180441 / 200000000) := by
  have h := checkLog_sound (w := (1613 / 18387)) (n := 12)
    (lo := (43975551 / 250000000)) (hi := (35180441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8387) = 1/(8387 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1540 : Bounds (-35180441 / 200000000) (-43975551 / 250000000) (Real.log (8387 / 10000)) := by
  have h := reflection_log_1540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1541_neg : (80643 / 500000000) ≤ -Real.log (10000000 / 10001613) ∧
    -Real.log (10000000 / 10001613) ≤ (161287 / 1000000000) := by
  have h := checkLog_sound (w := (1613 / 20001613)) (n := 12)
    (lo := (80643 / 500000000)) (hi := (161287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001613 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001613 / 10000000) = 1/(10000000 / 10001613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1541 : Bounds (80643 / 500000000) (161287 / 1000000000) (Real.log (10001613 / 10000000)) := by
  have h := reflection_log_1541_neg
  have he : Real.log (10001613 / 10000000) = -Real.log (10000000 / 10001613) := by
    rw [show ((10001613 / 10000000) : ℝ) = ((10000000 / 10001613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1542_neg : (161313 / 1000000000) ≤ -Real.log (9998387 / 10000000) ∧
    -Real.log (9998387 / 10000000) ≤ (80657 / 500000000) := by
  have h := checkLog_sound (w := (1613 / 19998387)) (n := 12)
    (lo := (161313 / 1000000000)) (hi := (80657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998387) = 1/(9998387 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1542 : Bounds (-80657 / 500000000) (-161313 / 1000000000) (Real.log (9998387 / 10000000)) := by
  have h := reflection_log_1542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1543_neg : (77794027 / 1000000000) ≤ -Real.log (10000 / 10809) ∧
    -Real.log (10000 / 10809) ≤ (19448507 / 250000000) := by
  have h := checkLog_sound (w := (809 / 20809)) (n := 12)
    (lo := (77794027 / 1000000000)) (hi := (19448507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10809 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10809 / 10000) = 1/(10000 / 10809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1543 : Bounds (77794027 / 1000000000) (19448507 / 250000000) (Real.log (10809 / 10000)) := by
  have h := reflection_log_1543_neg
  have he : Real.log (10809 / 10000) = -Real.log (10000 / 10809) := by
    rw [show ((10809 / 10000) : ℝ) = ((10000 / 10809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1544_neg : (21090087 / 250000000) ≤ -Real.log (9191 / 10000) ∧
    -Real.log (9191 / 10000) ≤ (84360349 / 1000000000) := by
  have h := checkLog_sound (w := (809 / 19191)) (n := 12)
    (lo := (21090087 / 250000000)) (hi := (84360349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 9191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 9191) = 1/(9191 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1544 : Bounds (-84360349 / 1000000000) (-21090087 / 250000000) (Real.log (9191 / 10000)) := by
  have h := reflection_log_1544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1545_neg : (77990141 / 1000000000) ≤ -Real.log (125000 / 135139) ∧
    -Real.log (125000 / 135139) ≤ (38995071 / 500000000) := by
  have h := checkLog_sound (w := (10139 / 260139)) (n := 12)
    (lo := (77990141 / 1000000000)) (hi := (38995071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135139 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135139 / 125000) = 1/(125000 / 135139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1545 : Bounds (77990141 / 1000000000) (38995071 / 500000000) (Real.log (135139 / 125000)) := by
  have h := reflection_log_1545_neg
  have he : Real.log (135139 / 125000) = -Real.log (125000 / 135139) := by
    rw [show ((135139 / 125000) : ℝ) = ((125000 / 135139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1546_neg : (16918207 / 200000000) ≤ -Real.log (114861 / 125000) ∧
    -Real.log (114861 / 125000) ≤ (21147759 / 250000000) := by
  have h := checkLog_sound (w := (10139 / 239861)) (n := 12)
    (lo := (16918207 / 200000000)) (hi := (21147759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114861) = 1/(114861 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1546 : Bounds (-21147759 / 250000000) (-16918207 / 200000000) (Real.log (114861 / 125000)) := by
  have h := reflection_log_1546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1547_neg : (3300447 / 500000000) ≤ -Real.log (15522200679 / 15625000000) ∧
    -Real.log (15522200679 / 15625000000) ≤ (1320179 / 200000000) := by
  have h := checkLog_sound (w := (102799321 / 31147200679)) (n := 12)
    (lo := (3300447 / 500000000)) (hi := (1320179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15522200679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15522200679) = 1/(15522200679 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1547 : Bounds (-1320179 / 200000000) (-3300447 / 500000000) (Real.log (15522200679 / 15625000000)) := by
  have h := reflection_log_1547_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1548_neg : (6566321 / 1000000000) ≤ -Real.log (99345519 / 100000000) ∧
    -Real.log (99345519 / 100000000) ≤ (3283161 / 500000000) := by
  have h := checkLog_sound (w := (654481 / 199345519)) (n := 12)
    (lo := (6566321 / 1000000000)) (hi := (3283161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 99345519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 99345519) = 1/(99345519 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1548 : Bounds (-3283161 / 500000000) (-6566321 / 1000000000) (Real.log (99345519 / 100000000)) := by
  have h := reflection_log_1548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1549_neg : (20269297 / 125000000) ≤ -Real.log (500000000000 / 588020890001) ∧
    -Real.log (500000000000 / 588020890001) ≤ (162154377 / 1000000000) := by
  have h := checkLog_sound (w := (88020890001 / 1088020890001)) (n := 12)
    (lo := (20269297 / 125000000)) (hi := (162154377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588020890001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588020890001 / 500000000000) = 1/(500000000000 / 588020890001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1549 : Bounds (20269297 / 125000000) (162154377 / 1000000000) (Real.log (588020890001 / 500000000000)) := by
  have h := reflection_log_1549_neg
  have he : Real.log (588020890001 / 500000000000) = -Real.log (500000000000 / 588020890001) := by
    rw [show ((588020890001 / 500000000000) : ℝ) = ((500000000000 / 588020890001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1550_neg : (20322647 / 125000000) ≤ -Real.log (500000000000 / 588271911267) ∧
    -Real.log (500000000000 / 588271911267) ≤ (162581177 / 1000000000) := by
  have h := checkLog_sound (w := (88271911267 / 1088271911267)) (n := 12)
    (lo := (20322647 / 125000000)) (hi := (162581177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588271911267 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588271911267 / 500000000000) = 1/(500000000000 / 588271911267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1550 : Bounds (20322647 / 125000000) (162581177 / 1000000000) (Real.log (588271911267 / 500000000000)) := by
  have h := reflection_log_1550_neg
  have he : Real.log (588271911267 / 500000000000) = -Real.log (500000000000 / 588271911267) := by
    rw [show ((588271911267 / 500000000000) : ℝ) = ((500000000000 / 588271911267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1551_neg : (325236933 / 1000000000) ≤ -Real.log (500000000000 / 692179303767) ∧
    -Real.log (500000000000 / 692179303767) ≤ (162618467 / 500000000) := by
  have h := checkLog_sound (w := (192179303767 / 1192179303767)) (n := 12)
    (lo := (325236933 / 1000000000)) (hi := (162618467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692179303767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692179303767 / 500000000000) = 1/(500000000000 / 692179303767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1551 : Bounds (325236933 / 1000000000) (162618467 / 500000000) (Real.log (692179303767 / 500000000000)) := by
  have h := reflection_log_1551_neg
  have he : Real.log (692179303767 / 500000000000) = -Real.log (500000000000 / 692179303767) := by
    rw [show ((692179303767 / 500000000000) : ℝ) = ((500000000000 / 692179303767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1552_neg : (10170071 / 31250000) ≤ -Real.log (500000000000 / 692321449863) ∧
    -Real.log (500000000000 / 692321449863) ≤ (325442273 / 1000000000) := by
  have h := checkLog_sound (w := (192321449863 / 1192321449863)) (n := 12)
    (lo := (10170071 / 31250000)) (hi := (325442273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692321449863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692321449863 / 500000000000) = 1/(500000000000 / 692321449863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1552 : Bounds (10170071 / 31250000) (325442273 / 1000000000) (Real.log (692321449863 / 500000000000)) := by
  have h := reflection_log_1552_neg
  have he : Real.log (692321449863 / 500000000000) = -Real.log (500000000000 / 692321449863) := by
    rw [show ((692321449863 / 500000000000) : ℝ) = ((500000000000 / 692321449863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1553_neg : (149626173 / 1000000000) ≤ -Real.log (5000 / 5807) ∧
    -Real.log (5000 / 5807) ≤ (74813087 / 500000000) := by
  have h := checkLog_sound (w := (807 / 10807)) (n := 12)
    (lo := (149626173 / 1000000000)) (hi := (74813087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5807 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5807 / 5000) = 1/(5000 / 5807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1553 : Bounds (149626173 / 1000000000) (74813087 / 500000000) (Real.log (5807 / 5000)) := by
  have h := reflection_log_1553_neg
  have he : Real.log (5807 / 5000) = -Real.log (5000 / 5807) := by
    rw [show ((5807 / 5000) : ℝ) = ((5000 / 5807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1554_neg : (44005361 / 250000000) ≤ -Real.log (4193 / 5000) ∧
    -Real.log (4193 / 5000) ≤ (35204289 / 200000000) := by
  have h := checkLog_sound (w := (807 / 9193)) (n := 12)
    (lo := (44005361 / 250000000)) (hi := (35204289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4193) = 1/(4193 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1554 : Bounds (-35204289 / 200000000) (-44005361 / 250000000) (Real.log (4193 / 5000)) := by
  have h := reflection_log_1554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1555_neg : (80693 / 500000000) ≤ -Real.log (5000000 / 5000807) ∧
    -Real.log (5000000 / 5000807) ≤ (161387 / 1000000000) := by
  have h := checkLog_sound (w := (807 / 10000807)) (n := 12)
    (lo := (80693 / 500000000)) (hi := (161387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000807 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000807 / 5000000) = 1/(5000000 / 5000807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1555 : Bounds (80693 / 500000000) (161387 / 1000000000) (Real.log (5000807 / 5000000)) := by
  have h := reflection_log_1555_neg
  have he : Real.log (5000807 / 5000000) = -Real.log (5000000 / 5000807) := by
    rw [show ((5000807 / 5000000) : ℝ) = ((5000000 / 5000807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1556_neg : (161413 / 1000000000) ≤ -Real.log (4999193 / 5000000) ∧
    -Real.log (4999193 / 5000000) ≤ (80707 / 500000000) := by
  have h := checkLog_sound (w := (807 / 9999193)) (n := 12)
    (lo := (161413 / 1000000000)) (hi := (80707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999193) = 1/(4999193 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1556 : Bounds (-80707 / 500000000) (-161413 / 1000000000) (Real.log (4999193 / 5000000)) := by
  have h := reflection_log_1556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1557_neg : (77841209 / 1000000000) ≤ -Real.log (1000000 / 1080951) ∧
    -Real.log (1000000 / 1080951) ≤ (7784121 / 100000000) := by
  have h := checkLog_sound (w := (80951 / 2080951)) (n := 12)
    (lo := (77841209 / 1000000000)) (hi := (7784121 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080951 / 1000000) = 1/(1000000 / 1080951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1557 : Bounds (77841209 / 1000000000) (7784121 / 100000000) (Real.log (1080951 / 1000000)) := by
  have h := reflection_log_1557_neg
  have he : Real.log (1080951 / 1000000) = -Real.log (1000000 / 1080951) := by
    rw [show ((1080951 / 1000000) : ℝ) = ((1000000 / 1080951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1558_neg : (84415839 / 1000000000) ≤ -Real.log (919049 / 1000000) ∧
    -Real.log (919049 / 1000000) ≤ (527599 / 6250000) := by
  have h := checkLog_sound (w := (80951 / 1919049)) (n := 12)
    (lo := (84415839 / 1000000000)) (hi := (527599 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919049) = 1/(919049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1558 : Bounds (-527599 / 6250000) (-84415839 / 1000000000) (Real.log (919049 / 1000000)) := by
  have h := reflection_log_1558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1559_neg : (78037313 / 1000000000) ≤ -Real.log (1000000 / 1081163) ∧
    -Real.log (1000000 / 1081163) ≤ (39018657 / 500000000) := by
  have h := checkLog_sound (w := (81163 / 2081163)) (n := 12)
    (lo := (78037313 / 1000000000)) (hi := (39018657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081163 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081163 / 1000000) = 1/(1000000 / 1081163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1559 : Bounds (78037313 / 1000000000) (39018657 / 500000000) (Real.log (1081163 / 1000000)) := by
  have h := reflection_log_1559_neg
  have he : Real.log (1081163 / 1000000) = -Real.log (1000000 / 1081163) := by
    rw [show ((1081163 / 1000000) : ℝ) = ((1000000 / 1081163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1560_neg : (84646539 / 1000000000) ≤ -Real.log (918837 / 1000000) ∧
    -Real.log (918837 / 1000000) ≤ (4232327 / 50000000) := by
  have h := checkLog_sound (w := (81163 / 1918837)) (n := 12)
    (lo := (84646539 / 1000000000)) (hi := (4232327 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918837) = 1/(918837 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1560 : Bounds (-4232327 / 50000000) (-84646539 / 1000000000) (Real.log (918837 / 1000000)) := by
  have h := reflection_log_1560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1561_neg : (264369 / 40000000) ≤ -Real.log (993412567431 / 1000000000000) ∧
    -Real.log (993412567431 / 1000000000000) ≤ (3304613 / 500000000) := by
  have h := checkLog_sound (w := (6587432569 / 1993412567431)) (n := 12)
    (lo := (264369 / 40000000)) (hi := (3304613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993412567431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993412567431) = 1/(993412567431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1561 : Bounds (-3304613 / 500000000) (-264369 / 40000000) (Real.log (993412567431 / 1000000000000)) := by
  have h := reflection_log_1561_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1562_neg : (6574629 / 1000000000) ≤ -Real.log (993446935599 / 1000000000000) ∧
    -Real.log (993446935599 / 1000000000000) ≤ (657463 / 100000000) := by
  have h := checkLog_sound (w := (6553064401 / 1993446935599)) (n := 12)
    (lo := (6574629 / 1000000000)) (hi := (657463 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993446935599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993446935599) = 1/(993446935599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1562 : Bounds (-657463 / 100000000) (-6574629 / 1000000000) (Real.log (993446935599 / 1000000000000)) := by
  have h := reflection_log_1562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1563_neg : (20282131 / 125000000) ≤ -Real.log (500000000000 / 588081266613) ∧
    -Real.log (500000000000 / 588081266613) ≤ (162257049 / 1000000000) := by
  have h := checkLog_sound (w := (88081266613 / 1088081266613)) (n := 12)
    (lo := (20282131 / 125000000)) (hi := (162257049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588081266613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588081266613 / 500000000000) = 1/(500000000000 / 588081266613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1563 : Bounds (20282131 / 125000000) (162257049 / 1000000000) (Real.log (588081266613 / 500000000000)) := by
  have h := reflection_log_1563_neg
  have he : Real.log (588081266613 / 500000000000) = -Real.log (500000000000 / 588081266613) := by
    rw [show ((588081266613 / 500000000000) : ℝ) = ((500000000000 / 588081266613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1564_neg : (40670963 / 250000000) ≤ -Real.log (500000000000 / 588332315743) ∧
    -Real.log (500000000000 / 588332315743) ≤ (162683853 / 1000000000) := by
  have h := checkLog_sound (w := (88332315743 / 1088332315743)) (n := 12)
    (lo := (40670963 / 250000000)) (hi := (162683853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588332315743 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588332315743 / 500000000000) = 1/(500000000000 / 588332315743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1564 : Bounds (40670963 / 250000000) (162683853 / 1000000000) (Real.log (588332315743 / 500000000000)) := by
  have h := reflection_log_1564_neg
  have he : Real.log (588332315743 / 500000000000) = -Real.log (500000000000 / 588332315743) := by
    rw [show ((588332315743 / 500000000000) : ℝ) = ((500000000000 / 588332315743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1565_neg : (10170071 / 31250000) ≤ -Real.log (250000000000 / 346160724931) ∧
    -Real.log (250000000000 / 346160724931) ≤ (325442273 / 1000000000) := by
  have h := checkLog_sound (w := (96160724931 / 596160724931)) (n := 12)
    (lo := (10170071 / 31250000)) (hi := (325442273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346160724931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346160724931 / 250000000000) = 1/(250000000000 / 346160724931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1565 : Bounds (10170071 / 31250000) (325442273 / 1000000000) (Real.log (346160724931 / 250000000000)) := by
  have h := reflection_log_1565_neg
  have he : Real.log (346160724931 / 250000000000) = -Real.log (250000000000 / 346160724931) := by
    rw [show ((346160724931 / 250000000000) : ℝ) = ((250000000000 / 346160724931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1566_neg : (162823809 / 500000000) ≤ -Real.log (25000000000 / 34623181493) ∧
    -Real.log (25000000000 / 34623181493) ≤ (325647619 / 1000000000) := by
  have h := checkLog_sound (w := (9623181493 / 59623181493)) (n := 12)
    (lo := (162823809 / 500000000)) (hi := (325647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34623181493 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34623181493 / 25000000000) = 1/(25000000000 / 34623181493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1566 : Bounds (162823809 / 500000000) (325647619 / 1000000000) (Real.log (34623181493 / 25000000000)) := by
  have h := reflection_log_1566_neg
  have he : Real.log (34623181493 / 25000000000) = -Real.log (25000000000 / 34623181493) := by
    rw [show ((34623181493 / 25000000000) : ℝ) = ((25000000000 / 34623181493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1567_neg : (149712273 / 1000000000) ≤ -Real.log (2000 / 2323) ∧
    -Real.log (2000 / 2323) ≤ (74856137 / 500000000) := by
  have h := checkLog_sound (w := (323 / 4323)) (n := 12)
    (lo := (149712273 / 1000000000)) (hi := (74856137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2323 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2323 / 2000) = 1/(2000 / 2323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1567 : Bounds (149712273 / 1000000000) (74856137 / 500000000) (Real.log (2323 / 2000)) := by
  have h := reflection_log_1567_neg
  have he : Real.log (2323 / 2000) = -Real.log (2000 / 2323) := by
    rw [show ((2323 / 2000) : ℝ) = ((2000 / 2323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1568_neg : (176140697 / 1000000000) ≤ -Real.log (1677 / 2000) ∧
    -Real.log (1677 / 2000) ≤ (88070349 / 500000000) := by
  have h := checkLog_sound (w := (323 / 3677)) (n := 12)
    (lo := (176140697 / 1000000000)) (hi := (88070349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1677) = 1/(1677 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1568 : Bounds (-88070349 / 500000000) (-176140697 / 1000000000) (Real.log (1677 / 2000)) := by
  have h := reflection_log_1568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1569_neg : (80743 / 500000000) ≤ -Real.log (2000000 / 2000323) ∧
    -Real.log (2000000 / 2000323) ≤ (161487 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 4000323)) (n := 12)
    (lo := (80743 / 500000000)) (hi := (161487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000323 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000323 / 2000000) = 1/(2000000 / 2000323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1569 : Bounds (80743 / 500000000) (161487 / 1000000000) (Real.log (2000323 / 2000000)) := by
  have h := reflection_log_1569_neg
  have he : Real.log (2000323 / 2000000) = -Real.log (2000000 / 2000323) := by
    rw [show ((2000323 / 2000000) : ℝ) = ((2000000 / 2000323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1570_neg : (161513 / 1000000000) ≤ -Real.log (1999677 / 2000000) ∧
    -Real.log (1999677 / 2000000) ≤ (80757 / 500000000) := by
  have h := checkLog_sound (w := (323 / 3999677)) (n := 12)
    (lo := (161513 / 1000000000)) (hi := (80757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999677) = 1/(1999677 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1570 : Bounds (-80757 / 500000000) (-161513 / 1000000000) (Real.log (1999677 / 2000000)) := by
  have h := reflection_log_1570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1571_neg : (77887463 / 1000000000) ≤ -Real.log (1000000 / 1081001) ∧
    -Real.log (1000000 / 1081001) ≤ (9735933 / 125000000) := by
  have h := checkLog_sound (w := (81001 / 2081001)) (n := 12)
    (lo := (77887463 / 1000000000)) (hi := (9735933 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081001 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081001 / 1000000) = 1/(1000000 / 1081001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1571 : Bounds (77887463 / 1000000000) (9735933 / 125000000) (Real.log (1081001 / 1000000)) := by
  have h := reflection_log_1571_neg
  have he : Real.log (1081001 / 1000000) = -Real.log (1000000 / 1081001) := by
    rw [show ((1081001 / 1000000) : ℝ) = ((1000000 / 1081001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1572_neg : (21117561 / 250000000) ≤ -Real.log (918999 / 1000000) ∧
    -Real.log (918999 / 1000000) ≤ (16894049 / 200000000) := by
  have h := checkLog_sound (w := (81001 / 1918999)) (n := 12)
    (lo := (21117561 / 250000000)) (hi := (16894049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918999) = 1/(918999 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1572 : Bounds (-16894049 / 200000000) (-21117561 / 250000000) (Real.log (918999 / 1000000)) := by
  have h := reflection_log_1572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1573_neg : (78084483 / 1000000000) ≤ -Real.log (500000 / 540607) ∧
    -Real.log (500000 / 540607) ≤ (19521121 / 250000000) := by
  have h := checkLog_sound (w := (40607 / 1040607)) (n := 12)
    (lo := (78084483 / 1000000000)) (hi := (19521121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540607 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540607 / 500000) = 1/(500000 / 540607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1573 : Bounds (78084483 / 1000000000) (19521121 / 250000000) (Real.log (540607 / 500000)) := by
  have h := reflection_log_1573_neg
  have he : Real.log (540607 / 500000) = -Real.log (500000 / 540607) := by
    rw [show ((540607 / 500000) : ℝ) = ((500000 / 540607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1574_neg : (16940409 / 200000000) ≤ -Real.log (459393 / 500000) ∧
    -Real.log (459393 / 500000) ≤ (42351023 / 500000000) := by
  have h := checkLog_sound (w := (40607 / 959393)) (n := 12)
    (lo := (16940409 / 200000000)) (hi := (42351023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459393) = 1/(459393 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1574 : Bounds (-42351023 / 500000000) (-16940409 / 200000000) (Real.log (459393 / 500000)) := by
  have h := reflection_log_1574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1575_neg : (6617561 / 1000000000) ≤ -Real.log (248351071551 / 250000000000) ∧
    -Real.log (248351071551 / 250000000000) ≤ (3308781 / 500000000) := by
  have h := checkLog_sound (w := (1648928449 / 498351071551)) (n := 12)
    (lo := (6617561 / 1000000000)) (hi := (3308781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248351071551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248351071551) = 1/(248351071551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1575 : Bounds (-3308781 / 500000000) (-6617561 / 1000000000) (Real.log (248351071551 / 250000000000)) := by
  have h := reflection_log_1575_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1576_neg : (6582781 / 1000000000) ≤ -Real.log (993438837999 / 1000000000000) ∧
    -Real.log (993438837999 / 1000000000000) ≤ (3291391 / 500000000) := by
  have h := checkLog_sound (w := (6561162001 / 1993438837999)) (n := 12)
    (lo := (6582781 / 1000000000)) (hi := (3291391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993438837999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993438837999) = 1/(993438837999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1576 : Bounds (-3291391 / 500000000) (-6582781 / 1000000000) (Real.log (993438837999 / 1000000000000)) := by
  have h := reflection_log_1576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1577_neg : (40589427 / 250000000) ≤ -Real.log (125000000000 / 147035116469) ∧
    -Real.log (125000000000 / 147035116469) ≤ (162357709 / 1000000000) := by
  have h := checkLog_sound (w := (22035116469 / 272035116469)) (n := 12)
    (lo := (40589427 / 250000000)) (hi := (162357709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147035116469 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147035116469 / 125000000000) = 1/(125000000000 / 147035116469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1577 : Bounds (40589427 / 250000000) (162357709 / 1000000000) (Real.log (147035116469 / 125000000000)) := by
  have h := reflection_log_1577_neg
  have he : Real.log (147035116469 / 125000000000) = -Real.log (125000000000 / 147035116469) := by
    rw [show ((147035116469 / 125000000000) : ℝ) = ((125000000000 / 147035116469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1578_neg : (162786529 / 1000000000) ≤ -Real.log (20000000000 / 23535709077) ∧
    -Real.log (20000000000 / 23535709077) ≤ (16278653 / 100000000) := by
  have h := checkLog_sound (w := (3535709077 / 43535709077)) (n := 12)
    (lo := (162786529 / 1000000000)) (hi := (16278653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23535709077 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23535709077 / 20000000000) = 1/(20000000000 / 23535709077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1578 : Bounds (162786529 / 1000000000) (16278653 / 100000000) (Real.log (23535709077 / 20000000000)) := by
  have h := reflection_log_1578_neg
  have he : Real.log (23535709077 / 20000000000) = -Real.log (20000000000 / 23535709077) := by
    rw [show ((23535709077 / 20000000000) : ℝ) = ((20000000000 / 23535709077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1579_neg : (162823809 / 500000000) ≤ -Real.log (500000000000 / 692463629859) ∧
    -Real.log (500000000000 / 692463629859) ≤ (325647619 / 1000000000) := by
  have h := checkLog_sound (w := (192463629859 / 1192463629859)) (n := 12)
    (lo := (162823809 / 500000000)) (hi := (325647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692463629859 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692463629859 / 500000000000) = 1/(500000000000 / 692463629859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1579 : Bounds (162823809 / 500000000) (325647619 / 1000000000) (Real.log (692463629859 / 500000000000)) := by
  have h := reflection_log_1579_neg
  have he : Real.log (692463629859 / 500000000000) = -Real.log (500000000000 / 692463629859) := by
    rw [show ((692463629859 / 500000000000) : ℝ) = ((500000000000 / 692463629859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1580_neg : (32585297 / 100000000) ≤ -Real.log (500000000000 / 692605843769) ∧
    -Real.log (500000000000 / 692605843769) ≤ (325852971 / 1000000000) := by
  have h := checkLog_sound (w := (192605843769 / 1192605843769)) (n := 12)
    (lo := (32585297 / 100000000)) (hi := (325852971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692605843769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692605843769 / 500000000000) = 1/(500000000000 / 692605843769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1580 : Bounds (32585297 / 100000000) (325852971 / 1000000000) (Real.log (692605843769 / 500000000000)) := by
  have h := reflection_log_1580_neg
  have he : Real.log (692605843769 / 500000000000) = -Real.log (500000000000 / 692605843769) := by
    rw [show ((692605843769 / 500000000000) : ℝ) = ((500000000000 / 692605843769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1581_neg : (29959673 / 200000000) ≤ -Real.log (625 / 726) ∧
    -Real.log (625 / 726) ≤ (74899183 / 500000000) := by
  have h := checkLog_sound (w := (101 / 1351)) (n := 12)
    (lo := (29959673 / 200000000)) (hi := (74899183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726 / 625) = 1/(625 / 726) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1581 : Bounds (29959673 / 200000000) (74899183 / 500000000) (Real.log (726 / 625)) := by
  have h := reflection_log_1581_neg
  have he : Real.log (726 / 625) = -Real.log (625 / 726) := by
    rw [show ((726 / 625) : ℝ) = ((625 / 726) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1582_neg : (35251993 / 200000000) ≤ -Real.log (524 / 625) ∧
    -Real.log (524 / 625) ≤ (88129983 / 500000000) := by
  have h := checkLog_sound (w := (101 / 1149)) (n := 12)
    (lo := (35251993 / 200000000)) (hi := (88129983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 524) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 524) = 1/(524 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1582 : Bounds (-88129983 / 500000000) (-35251993 / 200000000) (Real.log (524 / 625)) := by
  have h := reflection_log_1582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1583_neg : (80793 / 500000000) ≤ -Real.log (625000 / 625101) ∧
    -Real.log (625000 / 625101) ≤ (161587 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 1250101)) (n := 12)
    (lo := (80793 / 500000000)) (hi := (161587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625101 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625101 / 625000) = 1/(625000 / 625101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1583 : Bounds (80793 / 500000000) (161587 / 1000000000) (Real.log (625101 / 625000)) := by
  have h := reflection_log_1583_neg
  have he : Real.log (625101 / 625000) = -Real.log (625000 / 625101) := by
    rw [show ((625101 / 625000) : ℝ) = ((625000 / 625101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1584_neg : (161613 / 1000000000) ≤ -Real.log (624899 / 625000) ∧
    -Real.log (624899 / 625000) ≤ (80807 / 500000000) := by
  have h := checkLog_sound (w := (101 / 1249899)) (n := 12)
    (lo := (161613 / 1000000000)) (hi := (80807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624899) = 1/(624899 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1584 : Bounds (-80807 / 500000000) (-161613 / 1000000000) (Real.log (624899 / 625000)) := by
  have h := reflection_log_1584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1585_neg : (77934641 / 1000000000) ≤ -Real.log (250000 / 270263) ∧
    -Real.log (250000 / 270263) ≤ (38967321 / 500000000) := by
  have h := checkLog_sound (w := (20263 / 520263)) (n := 12)
    (lo := (77934641 / 1000000000)) (hi := (38967321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270263 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270263 / 250000) = 1/(250000 / 270263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1585 : Bounds (77934641 / 1000000000) (38967321 / 500000000) (Real.log (270263 / 250000)) := by
  have h := reflection_log_1585_neg
  have he : Real.log (270263 / 250000) = -Real.log (250000 / 270263) := by
    rw [show ((270263 / 250000) : ℝ) = ((250000 / 270263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1586_neg : (84525741 / 1000000000) ≤ -Real.log (229737 / 250000) ∧
    -Real.log (229737 / 250000) ≤ (42262871 / 500000000) := by
  have h := checkLog_sound (w := (20263 / 479737)) (n := 12)
    (lo := (84525741 / 1000000000)) (hi := (42262871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229737) = 1/(229737 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1586 : Bounds (-42262871 / 500000000) (-84525741 / 1000000000) (Real.log (229737 / 250000)) := by
  have h := reflection_log_1586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1587_neg : (78130727 / 1000000000) ≤ -Real.log (62500 / 67579) ∧
    -Real.log (62500 / 67579) ≤ (9766341 / 125000000) := by
  have h := checkLog_sound (w := (5079 / 130079)) (n := 12)
    (lo := (78130727 / 1000000000)) (hi := (9766341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67579 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67579 / 62500) = 1/(62500 / 67579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1587 : Bounds (78130727 / 1000000000) (9766341 / 125000000) (Real.log (67579 / 62500)) := by
  have h := reflection_log_1587_neg
  have he : Real.log (67579 / 62500) = -Real.log (62500 / 67579) := by
    rw [show ((67579 / 62500) : ℝ) = ((62500 / 67579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1588_neg : (42378233 / 500000000) ≤ -Real.log (57421 / 62500) ∧
    -Real.log (57421 / 62500) ≤ (84756467 / 1000000000) := by
  have h := checkLog_sound (w := (5079 / 119921)) (n := 12)
    (lo := (42378233 / 500000000)) (hi := (84756467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57421) = 1/(57421 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1588 : Bounds (-84756467 / 1000000000) (-42378233 / 500000000) (Real.log (57421 / 62500)) := by
  have h := reflection_log_1588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1589_neg : (6625739 / 1000000000) ≤ -Real.log (3880453759 / 3906250000) ∧
    -Real.log (3880453759 / 3906250000) ≤ (331287 / 50000000) := by
  have h := checkLog_sound (w := (25796241 / 7786703759)) (n := 12)
    (lo := (6625739 / 1000000000)) (hi := (331287 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3880453759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3880453759) = 1/(3880453759 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1589 : Bounds (-331287 / 50000000) (-6625739 / 1000000000) (Real.log (3880453759 / 3906250000)) := by
  have h := reflection_log_1589_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1590_neg : (65911 / 10000000) ≤ -Real.log (62089410831 / 62500000000) ∧
    -Real.log (62089410831 / 62500000000) ≤ (6591101 / 1000000000) := by
  have h := checkLog_sound (w := (410589169 / 124589410831)) (n := 12)
    (lo := (65911 / 10000000)) (hi := (6591101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62089410831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62089410831) = 1/(62089410831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1590 : Bounds (-6591101 / 1000000000) (-65911 / 10000000) (Real.log (62089410831 / 62500000000)) := by
  have h := reflection_log_1590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1591_neg : (81230191 / 500000000) ≤ -Real.log (500000000000 / 588200855761) ∧
    -Real.log (500000000000 / 588200855761) ≤ (162460383 / 1000000000) := by
  have h := checkLog_sound (w := (88200855761 / 1088200855761)) (n := 12)
    (lo := (81230191 / 500000000)) (hi := (162460383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588200855761 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588200855761 / 500000000000) = 1/(500000000000 / 588200855761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1591 : Bounds (81230191 / 500000000) (162460383 / 1000000000) (Real.log (588200855761 / 500000000000)) := by
  have h := reflection_log_1591_neg
  have he : Real.log (588200855761 / 500000000000) = -Real.log (500000000000 / 588200855761) := by
    rw [show ((588200855761 / 500000000000) : ℝ) = ((500000000000 / 588200855761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1592_neg : (162887193 / 1000000000) ≤ -Real.log (100000000000 / 117690392017) ∧
    -Real.log (100000000000 / 117690392017) ≤ (81443597 / 500000000) := by
  have h := checkLog_sound (w := (17690392017 / 217690392017)) (n := 12)
    (lo := (162887193 / 1000000000)) (hi := (81443597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117690392017 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117690392017 / 100000000000) = 1/(100000000000 / 117690392017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1592 : Bounds (162887193 / 1000000000) (81443597 / 500000000) (Real.log (117690392017 / 100000000000)) := by
  have h := reflection_log_1592_neg
  have he : Real.log (117690392017 / 100000000000) = -Real.log (100000000000 / 117690392017) := by
    rw [show ((117690392017 / 100000000000) : ℝ) = ((100000000000 / 117690392017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1593_neg : (32585297 / 100000000) ≤ -Real.log (62500000000 / 86575730471) ∧
    -Real.log (62500000000 / 86575730471) ≤ (325852971 / 1000000000) := by
  have h := checkLog_sound (w := (24075730471 / 149075730471)) (n := 12)
    (lo := (32585297 / 100000000)) (hi := (325852971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86575730471 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86575730471 / 62500000000) = 1/(62500000000 / 86575730471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1593 : Bounds (32585297 / 100000000) (325852971 / 1000000000) (Real.log (86575730471 / 62500000000)) := by
  have h := reflection_log_1593_neg
  have he : Real.log (86575730471 / 62500000000) = -Real.log (62500000000 / 86575730471) := by
    rw [show ((86575730471 / 62500000000) : ℝ) = ((62500000000 / 86575730471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1594_neg : (32605833 / 100000000) ≤ -Real.log (125000000000 / 173187022901) ∧
    -Real.log (125000000000 / 173187022901) ≤ (326058331 / 1000000000) := by
  have h := checkLog_sound (w := (48187022901 / 298187022901)) (n := 12)
    (lo := (32605833 / 100000000)) (hi := (326058331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173187022901 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173187022901 / 125000000000) = 1/(125000000000 / 173187022901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1594 : Bounds (32605833 / 100000000) (326058331 / 1000000000) (Real.log (173187022901 / 125000000000)) := by
  have h := reflection_log_1594_neg
  have he : Real.log (173187022901 / 125000000000) = -Real.log (125000000000 / 173187022901) := by
    rw [show ((173187022901 / 125000000000) : ℝ) = ((125000000000 / 173187022901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1595_neg : (149884449 / 1000000000) ≤ -Real.log (10000 / 11617) ∧
    -Real.log (10000 / 11617) ≤ (2997689 / 20000000) := by
  have h := checkLog_sound (w := (1617 / 21617)) (n := 12)
    (lo := (149884449 / 1000000000)) (hi := (2997689 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11617 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11617 / 10000) = 1/(10000 / 11617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1595 : Bounds (149884449 / 1000000000) (2997689 / 20000000) (Real.log (11617 / 10000)) := by
  have h := reflection_log_1595_neg
  have he : Real.log (11617 / 10000) = -Real.log (10000 / 11617) := by
    rw [show ((11617 / 10000) : ℝ) = ((10000 / 11617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1596_neg : (176379247 / 1000000000) ≤ -Real.log (8383 / 10000) ∧
    -Real.log (8383 / 10000) ≤ (11023703 / 62500000) := by
  have h := checkLog_sound (w := (1617 / 18383)) (n := 12)
    (lo := (176379247 / 1000000000)) (hi := (11023703 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8383) = 1/(8383 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1596 : Bounds (-11023703 / 62500000) (-176379247 / 1000000000) (Real.log (8383 / 10000)) := by
  have h := reflection_log_1596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1597_neg : (80843 / 500000000) ≤ -Real.log (10000000 / 10001617) ∧
    -Real.log (10000000 / 10001617) ≤ (161687 / 1000000000) := by
  have h := checkLog_sound (w := (1617 / 20001617)) (n := 12)
    (lo := (80843 / 500000000)) (hi := (161687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001617 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001617 / 10000000) = 1/(10000000 / 10001617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1597 : Bounds (80843 / 500000000) (161687 / 1000000000) (Real.log (10001617 / 10000000)) := by
  have h := reflection_log_1597_neg
  have he : Real.log (10001617 / 10000000) = -Real.log (10000000 / 10001617) := by
    rw [show ((10001617 / 10000000) : ℝ) = ((10000000 / 10001617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1598_neg : (161713 / 1000000000) ≤ -Real.log (9998383 / 10000000) ∧
    -Real.log (9998383 / 10000000) ≤ (80857 / 500000000) := by
  have h := checkLog_sound (w := (1617 / 19998383)) (n := 12)
    (lo := (161713 / 1000000000)) (hi := (80857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998383) = 1/(9998383 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1598 : Bounds (-80857 / 500000000) (-161713 / 1000000000) (Real.log (9998383 / 10000000)) := by
  have h := reflection_log_1598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1599_neg : (9747727 / 125000000) ≤ -Real.log (1000000 / 1081103) ∧
    -Real.log (1000000 / 1081103) ≤ (77981817 / 1000000000) := by
  have h := checkLog_sound (w := (81103 / 2081103)) (n := 12)
    (lo := (9747727 / 125000000)) (hi := (77981817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081103 / 1000000) = 1/(1000000 / 1081103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1599 : Bounds (9747727 / 125000000) (77981817 / 1000000000) (Real.log (1081103 / 1000000)) := by
  have h := reflection_log_1599_neg
  have he : Real.log (1081103 / 1000000) = -Real.log (1000000 / 1081103) := by
    rw [show ((1081103 / 1000000) : ℝ) = ((1000000 / 1081103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


