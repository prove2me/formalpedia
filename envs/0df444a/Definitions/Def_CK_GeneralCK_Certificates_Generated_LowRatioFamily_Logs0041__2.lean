-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0041__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0041__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:06:35.987703+00:00
-- url     : https://prove2.me/theorems/55f45fc0-1acb-41a2-933b-6517d08a9a51
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0041 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0042)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0041 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0042)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0041 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0042)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0041 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0042) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0041 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0042).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0041 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2624_neg : (1777127 / 20000000) ≤ -Real.log (914977 / 1000000) ∧
    -Real.log (914977 / 1000000) ≤ (88856351 / 1000000000) := by
  have h := checkLog_sound (w := (85023 / 1914977)) (n := 12)
    (lo := (1777127 / 20000000)) (hi := (88856351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914977) = 1/(914977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2624 : Bounds (-88856351 / 1000000000) (-1777127 / 20000000) (Real.log (914977 / 1000000)) := by
  have h := reflection_log_2624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2625_neg : (1451033 / 200000000) ≤ -Real.log (992771089471 / 1000000000000) ∧
    -Real.log (992771089471 / 1000000000000) ≤ (3627583 / 500000000) := by
  have h := checkLog_sound (w := (7228910529 / 1992771089471)) (n := 12)
    (lo := (1451033 / 200000000)) (hi := (3627583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992771089471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992771089471) = 1/(992771089471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2625 : Bounds (-3627583 / 500000000) (-1451033 / 200000000) (Real.log (992771089471 / 1000000000000)) := by
  have h := reflection_log_2625_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2626_neg : (7217703 / 1000000000) ≤ -Real.log (62050517599 / 62500000000) ∧
    -Real.log (62050517599 / 62500000000) ≤ (902213 / 125000000) := by
  have h := checkLog_sound (w := (449482401 / 124550517599)) (n := 12)
    (lo := (7217703 / 1000000000)) (hi := (902213 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62050517599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62050517599) = 1/(62050517599 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2626 : Bounds (-902213 / 125000000) (-7217703 / 1000000000) (Real.log (62050517599 / 62500000000)) := by
  have h := reflection_log_2626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2627_neg : (85008177 / 500000000) ≤ -Real.log (250000000000 / 296331059139) ∧
    -Real.log (250000000000 / 296331059139) ≤ (34003271 / 200000000) := by
  have h := checkLog_sound (w := (46331059139 / 546331059139)) (n := 12)
    (lo := (85008177 / 500000000)) (hi := (34003271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296331059139 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296331059139 / 250000000000) = 1/(250000000000 / 296331059139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2627 : Bounds (85008177 / 500000000) (34003271 / 200000000) (Real.log (296331059139 / 250000000000)) := by
  have h := reflection_log_2627_neg
  have he : Real.log (296331059139 / 250000000000) = -Real.log (250000000000 / 296331059139) := by
    rw [show ((296331059139 / 250000000000) : ℝ) = ((250000000000 / 296331059139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2628_neg : (34091507 / 200000000) ≤ -Real.log (250000000000 / 296461823631) ∧
    -Real.log (250000000000 / 296461823631) ≤ (2663399 / 15625000) := by
  have h := checkLog_sound (w := (46461823631 / 546461823631)) (n := 12)
    (lo := (34091507 / 200000000)) (hi := (2663399 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296461823631 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296461823631 / 250000000000) = 1/(250000000000 / 296461823631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2628 : Bounds (34091507 / 200000000) (2663399 / 15625000) (Real.log (296461823631 / 250000000000)) := by
  have h := reflection_log_2628_neg
  have he : Real.log (296461823631 / 250000000000) = -Real.log (250000000000 / 296461823631) := by
    rw [show ((296461823631 / 250000000000) : ℝ) = ((250000000000 / 296461823631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2629_neg : (34106829 / 100000000) ≤ -Real.log (12500000000 / 17580616051) ∧
    -Real.log (12500000000 / 17580616051) ≤ (341068291 / 1000000000) := by
  have h := checkLog_sound (w := (5080616051 / 30080616051)) (n := 12)
    (lo := (34106829 / 100000000)) (hi := (341068291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17580616051 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17580616051 / 12500000000) = 1/(12500000000 / 17580616051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2629 : Bounds (34106829 / 100000000) (341068291 / 1000000000) (Real.log (17580616051 / 12500000000)) := by
  have h := reflection_log_2629_neg
  have he : Real.log (17580616051 / 12500000000) = -Real.log (12500000000 / 17580616051) := by
    rw [show ((17580616051 / 12500000000) : ℝ) = ((12500000000 / 17580616051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2630_neg : (170637083 / 500000000) ≤ -Real.log (500000000000 / 703369434417) ∧
    -Real.log (500000000000 / 703369434417) ≤ (341274167 / 1000000000) := by
  have h := checkLog_sound (w := (203369434417 / 1203369434417)) (n := 12)
    (lo := (170637083 / 500000000)) (hi := (341274167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703369434417 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703369434417 / 500000000000) = 1/(500000000000 / 703369434417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2630 : Bounds (170637083 / 500000000) (341274167 / 1000000000) (Real.log (703369434417 / 500000000000)) := by
  have h := reflection_log_2630_neg
  have he : Real.log (703369434417 / 500000000000) = -Real.log (500000000000 / 703369434417) := by
    rw [show ((703369434417 / 500000000000) : ℝ) = ((500000000000 / 703369434417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2631_neg : (78117111 / 500000000) ≤ -Real.log (10000 / 11691) ∧
    -Real.log (10000 / 11691) ≤ (156234223 / 1000000000) := by
  have h := checkLog_sound (w := (1691 / 21691)) (n := 12)
    (lo := (78117111 / 500000000)) (hi := (156234223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11691 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11691 / 10000) = 1/(10000 / 11691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2631 : Bounds (78117111 / 500000000) (156234223 / 1000000000) (Real.log (11691 / 10000)) := by
  have h := reflection_log_2631_neg
  have he : Real.log (11691 / 10000) = -Real.log (10000 / 11691) := by
    rw [show ((11691 / 10000) : ℝ) = ((10000 / 11691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2632_neg : (46311457 / 250000000) ≤ -Real.log (8309 / 10000) ∧
    -Real.log (8309 / 10000) ≤ (185245829 / 1000000000) := by
  have h := checkLog_sound (w := (1691 / 18309)) (n := 12)
    (lo := (46311457 / 250000000)) (hi := (185245829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8309) = 1/(8309 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2632 : Bounds (-185245829 / 1000000000) (-46311457 / 250000000) (Real.log (8309 / 10000)) := by
  have h := reflection_log_2632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2633_neg : (33817 / 200000000) ≤ -Real.log (10000000 / 10001691) ∧
    -Real.log (10000000 / 10001691) ≤ (84543 / 500000000) := by
  have h := checkLog_sound (w := (1691 / 20001691)) (n := 12)
    (lo := (33817 / 200000000)) (hi := (84543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001691 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001691 / 10000000) = 1/(10000000 / 10001691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2633 : Bounds (33817 / 200000000) (84543 / 500000000) (Real.log (10001691 / 10000000)) := by
  have h := reflection_log_2633_neg
  have he : Real.log (10001691 / 10000000) = -Real.log (10000000 / 10001691) := by
    rw [show ((10001691 / 10000000) : ℝ) = ((10000000 / 10001691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2634_neg : (84557 / 500000000) ≤ -Real.log (9998309 / 10000000) ∧
    -Real.log (9998309 / 10000000) ≤ (33823 / 200000000) := by
  have h := checkLog_sound (w := (1691 / 19998309)) (n := 12)
    (lo := (84557 / 500000000)) (hi := (33823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998309) = 1/(9998309 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2634 : Bounds (-33823 / 200000000) (-84557 / 500000000) (Real.log (9998309 / 10000000)) := by
  have h := reflection_log_2634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2635_neg : (16289083 / 200000000) ≤ -Real.log (500000 / 542427) ∧
    -Real.log (500000 / 542427) ≤ (10180677 / 125000000) := by
  have h := checkLog_sound (w := (42427 / 1042427)) (n := 12)
    (lo := (16289083 / 200000000)) (hi := (10180677 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542427 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542427 / 500000) = 1/(500000 / 542427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2635 : Bounds (16289083 / 200000000) (10180677 / 125000000) (Real.log (542427 / 500000)) := by
  have h := reflection_log_2635_neg
  have he : Real.log (542427 / 500000) = -Real.log (500000 / 542427) := by
    rw [show ((542427 / 500000) : ℝ) = ((500000 / 542427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2636_neg : (88671663 / 1000000000) ≤ -Real.log (457573 / 500000) ∧
    -Real.log (457573 / 500000) ≤ (5541979 / 62500000) := by
  have h := checkLog_sound (w := (42427 / 957573)) (n := 12)
    (lo := (88671663 / 1000000000)) (hi := (5541979 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457573) = 1/(457573 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2636 : Bounds (-5541979 / 62500000) (-88671663 / 1000000000) (Real.log (457573 / 500000)) := by
  have h := reflection_log_2636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2637_neg : (81648187 / 1000000000) ≤ -Real.log (500000 / 542537) ∧
    -Real.log (500000 / 542537) ≤ (20412047 / 250000000) := by
  have h := checkLog_sound (w := (42537 / 1042537)) (n := 12)
    (lo := (81648187 / 1000000000)) (hi := (20412047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542537 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542537 / 500000) = 1/(500000 / 542537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2637 : Bounds (81648187 / 1000000000) (20412047 / 250000000) (Real.log (542537 / 500000)) := by
  have h := reflection_log_2637_neg
  have he : Real.log (542537 / 500000) = -Real.log (500000 / 542537) := by
    rw [show ((542537 / 500000) : ℝ) = ((500000 / 542537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2638_neg : (88912091 / 1000000000) ≤ -Real.log (457463 / 500000) ∧
    -Real.log (457463 / 500000) ≤ (22228023 / 250000000) := by
  have h := checkLog_sound (w := (42537 / 957463)) (n := 12)
    (lo := (88912091 / 1000000000)) (hi := (22228023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457463) = 1/(457463 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2638 : Bounds (-22228023 / 250000000) (-88912091 / 1000000000) (Real.log (457463 / 500000)) := by
  have h := reflection_log_2638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2639_neg : (7263903 / 1000000000) ≤ -Real.log (248190603631 / 250000000000) ∧
    -Real.log (248190603631 / 250000000000) ≤ (226997 / 31250000) := by
  have h := checkLog_sound (w := (1809396369 / 498190603631)) (n := 12)
    (lo := (7263903 / 1000000000)) (hi := (226997 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248190603631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248190603631) = 1/(248190603631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2639 : Bounds (-226997 / 31250000) (-7263903 / 1000000000) (Real.log (248190603631 / 250000000000)) := by
  have h := reflection_log_2639_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2640_neg : (7226247 / 1000000000) ≤ -Real.log (248199949671 / 250000000000) ∧
    -Real.log (248199949671 / 250000000000) ≤ (903281 / 125000000) := by
  have h := checkLog_sound (w := (1800050329 / 498199949671)) (n := 12)
    (lo := (7226247 / 1000000000)) (hi := (903281 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248199949671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248199949671) = 1/(248199949671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2640 : Bounds (-903281 / 125000000) (-7226247 / 1000000000) (Real.log (248199949671 / 250000000000)) := by
  have h := reflection_log_2640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2641_neg : (170117079 / 1000000000) ≤ -Real.log (100000000000 / 118544363413) ∧
    -Real.log (100000000000 / 118544363413) ≤ (4252927 / 25000000) := by
  have h := checkLog_sound (w := (18544363413 / 218544363413)) (n := 12)
    (lo := (170117079 / 1000000000)) (hi := (4252927 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118544363413 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118544363413 / 100000000000) = 1/(100000000000 / 118544363413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2641 : Bounds (170117079 / 1000000000) (4252927 / 25000000) (Real.log (118544363413 / 100000000000)) := by
  have h := reflection_log_2641_neg
  have he : Real.log (118544363413 / 100000000000) = -Real.log (100000000000 / 118544363413) := by
    rw [show ((118544363413 / 100000000000) : ℝ) = ((100000000000 / 118544363413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2642_neg : (85280139 / 500000000) ≤ -Real.log (125000000000 / 148246142311) ∧
    -Real.log (125000000000 / 148246142311) ≤ (170560279 / 1000000000) := by
  have h := checkLog_sound (w := (23246142311 / 273246142311)) (n := 12)
    (lo := (85280139 / 500000000)) (hi := (170560279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148246142311 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148246142311 / 125000000000) = 1/(125000000000 / 148246142311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2642 : Bounds (85280139 / 500000000) (170560279 / 1000000000) (Real.log (148246142311 / 125000000000)) := by
  have h := reflection_log_2642_neg
  have he : Real.log (148246142311 / 125000000000) = -Real.log (125000000000 / 148246142311) := by
    rw [show ((148246142311 / 125000000000) : ℝ) = ((125000000000 / 148246142311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2643_neg : (170637083 / 500000000) ≤ -Real.log (31250000000 / 43960589651) ∧
    -Real.log (31250000000 / 43960589651) ≤ (341274167 / 1000000000) := by
  have h := checkLog_sound (w := (12710589651 / 75210589651)) (n := 12)
    (lo := (170637083 / 500000000)) (hi := (341274167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43960589651 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43960589651 / 31250000000) = 1/(31250000000 / 43960589651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2643 : Bounds (170637083 / 500000000) (341274167 / 1000000000) (Real.log (43960589651 / 31250000000)) := by
  have h := reflection_log_2643_neg
  have he : Real.log (43960589651 / 31250000000) = -Real.log (31250000000 / 43960589651) := by
    rw [show ((43960589651 / 31250000000) : ℝ) = ((31250000000 / 43960589651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2644_neg : (6829601 / 20000000) ≤ -Real.log (100000000000 / 140702852329) ∧
    -Real.log (100000000000 / 140702852329) ≤ (341480051 / 1000000000) := by
  have h := checkLog_sound (w := (40702852329 / 240702852329)) (n := 12)
    (lo := (6829601 / 20000000)) (hi := (341480051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140702852329 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140702852329 / 100000000000) = 1/(100000000000 / 140702852329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2644 : Bounds (6829601 / 20000000) (341480051 / 1000000000) (Real.log (140702852329 / 100000000000)) := by
  have h := reflection_log_2644_neg
  have he : Real.log (140702852329 / 100000000000) = -Real.log (100000000000 / 140702852329) := by
    rw [show ((140702852329 / 100000000000) : ℝ) = ((100000000000 / 140702852329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2645_neg : (78159877 / 500000000) ≤ -Real.log (2500 / 2923) ∧
    -Real.log (2500 / 2923) ≤ (31263951 / 200000000) := by
  have h := checkLog_sound (w := (423 / 5423)) (n := 12)
    (lo := (78159877 / 500000000)) (hi := (31263951 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2923 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2923 / 2500) = 1/(2500 / 2923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2645 : Bounds (78159877 / 500000000) (31263951 / 200000000) (Real.log (2923 / 2500)) := by
  have h := reflection_log_2645_neg
  have he : Real.log (2923 / 2500) = -Real.log (2500 / 2923) := by
    rw [show ((2923 / 2500) : ℝ) = ((2500 / 2923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2646_neg : (92683093 / 500000000) ≤ -Real.log (2077 / 2500) ∧
    -Real.log (2077 / 2500) ≤ (185366187 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 4577)) (n := 12)
    (lo := (92683093 / 500000000)) (hi := (185366187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2077) = 1/(2077 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2646 : Bounds (-185366187 / 1000000000) (-92683093 / 500000000) (Real.log (2077 / 2500)) := by
  have h := reflection_log_2646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2647_neg : (33837 / 200000000) ≤ -Real.log (2500000 / 2500423) ∧
    -Real.log (2500000 / 2500423) ≤ (84593 / 500000000) := by
  have h := checkLog_sound (w := (423 / 5000423)) (n := 12)
    (lo := (33837 / 200000000)) (hi := (84593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500423 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500423 / 2500000) = 1/(2500000 / 2500423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2647 : Bounds (33837 / 200000000) (84593 / 500000000) (Real.log (2500423 / 2500000)) := by
  have h := reflection_log_2647_neg
  have he : Real.log (2500423 / 2500000) = -Real.log (2500000 / 2500423) := by
    rw [show ((2500423 / 2500000) : ℝ) = ((2500000 / 2500423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2648_neg : (84607 / 500000000) ≤ -Real.log (2499577 / 2500000) ∧
    -Real.log (2499577 / 2500000) ≤ (33843 / 200000000) := by
  have h := checkLog_sound (w := (423 / 4999577)) (n := 12)
    (lo := (84607 / 500000000)) (hi := (33843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499577) = 1/(2499577 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2648 : Bounds (-33843 / 200000000) (-84607 / 500000000) (Real.log (2499577 / 2500000)) := by
  have h := reflection_log_2648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2649_neg : (3259697 / 40000000) ≤ -Real.log (200000 / 216981) ∧
    -Real.log (200000 / 216981) ≤ (40746213 / 500000000) := by
  have h := checkLog_sound (w := (16981 / 416981)) (n := 12)
    (lo := (3259697 / 40000000)) (hi := (40746213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216981 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216981 / 200000) = 1/(200000 / 216981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2649 : Bounds (3259697 / 40000000) (40746213 / 500000000) (Real.log (216981 / 200000)) := by
  have h := reflection_log_2649_neg
  have he : Real.log (216981 / 200000) = -Real.log (200000 / 216981) := by
    rw [show ((216981 / 200000) : ℝ) = ((200000 / 216981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2650_neg : (88727393 / 1000000000) ≤ -Real.log (183019 / 200000) ∧
    -Real.log (183019 / 200000) ≤ (44363697 / 500000000) := by
  have h := checkLog_sound (w := (16981 / 383019)) (n := 12)
    (lo := (88727393 / 1000000000)) (hi := (44363697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183019) = 1/(183019 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2650 : Bounds (-44363697 / 500000000) (-88727393 / 1000000000) (Real.log (183019 / 200000)) := by
  have h := reflection_log_2650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2651_neg : (81695187 / 1000000000) ≤ -Real.log (8000 / 8681) ∧
    -Real.log (8000 / 8681) ≤ (20423797 / 250000000) := by
  have h := checkLog_sound (w := (681 / 16681)) (n := 12)
    (lo := (81695187 / 1000000000)) (hi := (20423797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8681 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8681 / 8000) = 1/(8000 / 8681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2651 : Bounds (81695187 / 1000000000) (20423797 / 250000000) (Real.log (8681 / 8000)) := by
  have h := reflection_log_2651_neg
  have he : Real.log (8681 / 8000) = -Real.log (8000 / 8681) := by
    rw [show ((8681 / 8000) : ℝ) = ((8000 / 8681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2652_neg : (17793567 / 200000000) ≤ -Real.log (7319 / 8000) ∧
    -Real.log (7319 / 8000) ≤ (22241959 / 250000000) := by
  have h := checkLog_sound (w := (681 / 15319)) (n := 12)
    (lo := (17793567 / 200000000)) (hi := (22241959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 7319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 7319) = 1/(7319 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2652 : Bounds (-22241959 / 250000000) (-17793567 / 200000000) (Real.log (7319 / 8000)) := by
  have h := reflection_log_2652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2653_neg : (7272647 / 1000000000) ≤ -Real.log (63536239 / 64000000) ∧
    -Real.log (63536239 / 64000000) ≤ (909081 / 125000000) := by
  have h := checkLog_sound (w := (463761 / 127536239)) (n := 12)
    (lo := (7272647 / 1000000000)) (hi := (909081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64000000 / 63536239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64000000 / 63536239) = 1/(63536239 / 64000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2653 : Bounds (-909081 / 125000000) (-7272647 / 1000000000) (Real.log (63536239 / 64000000)) := by
  have h := reflection_log_2653_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2654_neg : (904371 / 125000000) ≤ -Real.log (39711645639 / 40000000000) ∧
    -Real.log (39711645639 / 40000000000) ≤ (7234969 / 1000000000) := by
  have h := checkLog_sound (w := (288354361 / 79711645639)) (n := 12)
    (lo := (904371 / 125000000)) (hi := (7234969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39711645639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39711645639) = 1/(39711645639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2654 : Bounds (-7234969 / 1000000000) (-904371 / 125000000) (Real.log (39711645639 / 40000000000)) := by
  have h := reflection_log_2654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2655_neg : (170219819 / 1000000000) ≤ -Real.log (125000000000 / 148195679137) ∧
    -Real.log (125000000000 / 148195679137) ≤ (8510991 / 50000000) := by
  have h := checkLog_sound (w := (23195679137 / 273195679137)) (n := 12)
    (lo := (170219819 / 1000000000)) (hi := (8510991 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148195679137 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148195679137 / 125000000000) = 1/(125000000000 / 148195679137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2655 : Bounds (170219819 / 1000000000) (8510991 / 50000000) (Real.log (148195679137 / 125000000000)) := by
  have h := reflection_log_2655_neg
  have he : Real.log (148195679137 / 125000000000) = -Real.log (125000000000 / 148195679137) := by
    rw [show ((148195679137 / 125000000000) : ℝ) = ((125000000000 / 148195679137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2656_neg : (85331511 / 500000000) ≤ -Real.log (500000000000 / 593045498019) ∧
    -Real.log (500000000000 / 593045498019) ≤ (170663023 / 1000000000) := by
  have h := checkLog_sound (w := (93045498019 / 1093045498019)) (n := 12)
    (lo := (85331511 / 500000000)) (hi := (170663023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593045498019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593045498019 / 500000000000) = 1/(500000000000 / 593045498019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2656 : Bounds (85331511 / 500000000) (170663023 / 1000000000) (Real.log (593045498019 / 500000000000)) := by
  have h := reflection_log_2656_neg
  have he : Real.log (593045498019 / 500000000000) = -Real.log (500000000000 / 593045498019) := by
    rw [show ((593045498019 / 500000000000) : ℝ) = ((500000000000 / 593045498019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2657_neg : (6829601 / 20000000) ≤ -Real.log (125000000000 / 175878565411) ∧
    -Real.log (125000000000 / 175878565411) ≤ (341480051 / 1000000000) := by
  have h := checkLog_sound (w := (50878565411 / 300878565411)) (n := 12)
    (lo := (6829601 / 20000000)) (hi := (341480051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175878565411 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175878565411 / 125000000000) = 1/(125000000000 / 175878565411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2657 : Bounds (6829601 / 20000000) (341480051 / 1000000000) (Real.log (175878565411 / 125000000000)) := by
  have h := reflection_log_2657_neg
  have he : Real.log (175878565411 / 125000000000) = -Real.log (125000000000 / 175878565411) := by
    rw [show ((175878565411 / 125000000000) : ℝ) = ((125000000000 / 175878565411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2658_neg : (341685941 / 1000000000) ≤ -Real.log (500000000000 / 703659123737) ∧
    -Real.log (500000000000 / 703659123737) ≤ (170842971 / 500000000) := by
  have h := checkLog_sound (w := (203659123737 / 1203659123737)) (n := 12)
    (lo := (341685941 / 1000000000)) (hi := (170842971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703659123737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703659123737 / 500000000000) = 1/(500000000000 / 703659123737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2658 : Bounds (341685941 / 1000000000) (170842971 / 500000000) (Real.log (703659123737 / 500000000000)) := by
  have h := reflection_log_2658_neg
  have he : Real.log (703659123737 / 500000000000) = -Real.log (500000000000 / 703659123737) := by
    rw [show ((703659123737 / 500000000000) : ℝ) = ((500000000000 / 703659123737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2659_neg : (156405279 / 1000000000) ≤ -Real.log (10000 / 11693) ∧
    -Real.log (10000 / 11693) ≤ (977533 / 6250000) := by
  have h := checkLog_sound (w := (1693 / 21693)) (n := 12)
    (lo := (156405279 / 1000000000)) (hi := (977533 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11693 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11693 / 10000) = 1/(10000 / 11693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2659 : Bounds (156405279 / 1000000000) (977533 / 6250000) (Real.log (11693 / 10000)) := by
  have h := reflection_log_2659_neg
  have he : Real.log (11693 / 10000) = -Real.log (10000 / 11693) := by
    rw [show ((11693 / 10000) : ℝ) = ((10000 / 11693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2660_neg : (1159291 / 6250000) ≤ -Real.log (8307 / 10000) ∧
    -Real.log (8307 / 10000) ≤ (185486561 / 1000000000) := by
  have h := checkLog_sound (w := (1693 / 18307)) (n := 12)
    (lo := (1159291 / 6250000)) (hi := (185486561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8307) = 1/(8307 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2660 : Bounds (-185486561 / 1000000000) (-1159291 / 6250000) (Real.log (8307 / 10000)) := by
  have h := reflection_log_2660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2661_neg : (33857 / 200000000) ≤ -Real.log (10000000 / 10001693) ∧
    -Real.log (10000000 / 10001693) ≤ (84643 / 500000000) := by
  have h := checkLog_sound (w := (1693 / 20001693)) (n := 12)
    (lo := (33857 / 200000000)) (hi := (84643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001693 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001693 / 10000000) = 1/(10000000 / 10001693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2661 : Bounds (33857 / 200000000) (84643 / 500000000) (Real.log (10001693 / 10000000)) := by
  have h := reflection_log_2661_neg
  have he : Real.log (10001693 / 10000000) = -Real.log (10000000 / 10001693) := by
    rw [show ((10001693 / 10000000) : ℝ) = ((10000000 / 10001693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2662_neg : (84657 / 500000000) ≤ -Real.log (9998307 / 10000000) ∧
    -Real.log (9998307 / 10000000) ≤ (33863 / 200000000) := by
  have h := checkLog_sound (w := (1693 / 19998307)) (n := 12)
    (lo := (84657 / 500000000)) (hi := (33863 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998307) = 1/(9998307 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2662 : Bounds (-33863 / 200000000) (-84657 / 500000000) (Real.log (9998307 / 10000000)) := by
  have h := reflection_log_2662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2663_neg : (81539433 / 1000000000) ≤ -Real.log (250000 / 271239) ∧
    -Real.log (250000 / 271239) ≤ (40769717 / 500000000) := by
  have h := checkLog_sound (w := (21239 / 521239)) (n := 12)
    (lo := (81539433 / 1000000000)) (hi := (40769717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271239 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271239 / 250000) = 1/(250000 / 271239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2663 : Bounds (81539433 / 1000000000) (40769717 / 500000000) (Real.log (271239 / 250000)) := by
  have h := reflection_log_2663_neg
  have he : Real.log (271239 / 250000) = -Real.log (250000 / 271239) := by
    rw [show ((271239 / 250000) : ℝ) = ((250000 / 271239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2664_neg : (88783127 / 1000000000) ≤ -Real.log (228761 / 250000) ∧
    -Real.log (228761 / 250000) ≤ (11097891 / 125000000) := by
  have h := checkLog_sound (w := (21239 / 478761)) (n := 12)
    (lo := (88783127 / 1000000000)) (hi := (11097891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228761) = 1/(228761 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2664 : Bounds (-11097891 / 125000000) (-88783127 / 1000000000) (Real.log (228761 / 250000)) := by
  have h := reflection_log_2664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2665_neg : (16348437 / 200000000) ≤ -Real.log (125000 / 135647) ∧
    -Real.log (125000 / 135647) ≤ (40871093 / 500000000) := by
  have h := checkLog_sound (w := (10647 / 260647)) (n := 12)
    (lo := (16348437 / 200000000)) (hi := (40871093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135647 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135647 / 125000) = 1/(125000 / 135647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2665 : Bounds (16348437 / 200000000) (40871093 / 500000000) (Real.log (135647 / 125000)) := by
  have h := reflection_log_2665_neg
  have he : Real.log (135647 / 125000) = -Real.log (125000 / 135647) := by
    rw [show ((135647 / 125000) : ℝ) = ((125000 / 135647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2666_neg : (89023581 / 1000000000) ≤ -Real.log (114353 / 125000) ∧
    -Real.log (114353 / 125000) ≤ (44511791 / 500000000) := by
  have h := checkLog_sound (w := (10647 / 239353)) (n := 12)
    (lo := (89023581 / 1000000000)) (hi := (44511791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114353) = 1/(114353 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2666 : Bounds (-44511791 / 500000000) (-89023581 / 1000000000) (Real.log (114353 / 125000)) := by
  have h := reflection_log_2666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2667_neg : (1820349 / 250000000) ≤ -Real.log (15511641391 / 15625000000) ∧
    -Real.log (15511641391 / 15625000000) ≤ (7281397 / 1000000000) := by
  have h := checkLog_sound (w := (113358609 / 31136641391)) (n := 12)
    (lo := (1820349 / 250000000)) (hi := (7281397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15511641391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15511641391) = 1/(15511641391 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2667 : Bounds (-7281397 / 1000000000) (-1820349 / 250000000) (Real.log (15511641391 / 15625000000)) := by
  have h := reflection_log_2667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2668_neg : (3621847 / 500000000) ≤ -Real.log (62048904879 / 62500000000) ∧
    -Real.log (62048904879 / 62500000000) ≤ (1448739 / 200000000) := by
  have h := checkLog_sound (w := (451095121 / 124548904879)) (n := 12)
    (lo := (3621847 / 500000000)) (hi := (1448739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62048904879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62048904879) = 1/(62048904879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2668 : Bounds (-1448739 / 200000000) (-3621847 / 500000000) (Real.log (62048904879 / 62500000000)) := by
  have h := reflection_log_2668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2669_neg : (266129 / 1562500) ≤ -Real.log (25000000000 / 29642181141) ∧
    -Real.log (25000000000 / 29642181141) ≤ (170322561 / 1000000000) := by
  have h := checkLog_sound (w := (4642181141 / 54642181141)) (n := 12)
    (lo := (266129 / 1562500)) (hi := (170322561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29642181141 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29642181141 / 25000000000) = 1/(25000000000 / 29642181141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2669 : Bounds (266129 / 1562500) (170322561 / 1000000000) (Real.log (29642181141 / 25000000000)) := by
  have h := reflection_log_2669_neg
  have he : Real.log (29642181141 / 25000000000) = -Real.log (25000000000 / 29642181141) := by
    rw [show ((29642181141 / 25000000000) : ℝ) = ((25000000000 / 29642181141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2670_neg : (170765767 / 1000000000) ≤ -Real.log (125000000000 / 148276608397) ∧
    -Real.log (125000000000 / 148276608397) ≤ (21345721 / 125000000) := by
  have h := checkLog_sound (w := (23276608397 / 273276608397)) (n := 12)
    (lo := (170765767 / 1000000000)) (hi := (21345721 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148276608397 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148276608397 / 125000000000) = 1/(125000000000 / 148276608397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2670 : Bounds (170765767 / 1000000000) (21345721 / 125000000) (Real.log (148276608397 / 125000000000)) := by
  have h := reflection_log_2670_neg
  have he : Real.log (148276608397 / 125000000000) = -Real.log (125000000000 / 148276608397) := by
    rw [show ((148276608397 / 125000000000) : ℝ) = ((125000000000 / 148276608397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2671_neg : (341685941 / 1000000000) ≤ -Real.log (62500000000 / 87957390467) ∧
    -Real.log (62500000000 / 87957390467) ≤ (170842971 / 500000000) := by
  have h := checkLog_sound (w := (25457390467 / 150457390467)) (n := 12)
    (lo := (341685941 / 1000000000)) (hi := (170842971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87957390467 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87957390467 / 62500000000) = 1/(62500000000 / 87957390467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2671 : Bounds (341685941 / 1000000000) (170842971 / 500000000) (Real.log (87957390467 / 62500000000)) := by
  have h := reflection_log_2671_neg
  have he : Real.log (87957390467 / 62500000000) = -Real.log (62500000000 / 87957390467) := by
    rw [show ((87957390467 / 62500000000) : ℝ) = ((62500000000 / 87957390467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2672_neg : (341891839 / 1000000000) ≤ -Real.log (250000000000 / 351902010353) ∧
    -Real.log (250000000000 / 351902010353) ≤ (267103 / 781250) := by
  have h := checkLog_sound (w := (101902010353 / 601902010353)) (n := 12)
    (lo := (341891839 / 1000000000)) (hi := (267103 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351902010353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351902010353 / 250000000000) = 1/(250000000000 / 351902010353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2672 : Bounds (341891839 / 1000000000) (267103 / 781250) (Real.log (351902010353 / 250000000000)) := by
  have h := reflection_log_2672_neg
  have he : Real.log (351902010353 / 250000000000) = -Real.log (250000000000 / 351902010353) := by
    rw [show ((351902010353 / 250000000000) : ℝ) = ((250000000000 / 351902010353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2673_neg : (39122699 / 250000000) ≤ -Real.log (5000 / 5847) ∧
    -Real.log (5000 / 5847) ≤ (156490797 / 1000000000) := by
  have h := checkLog_sound (w := (847 / 10847)) (n := 12)
    (lo := (39122699 / 250000000)) (hi := (156490797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5847 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5847 / 5000) = 1/(5000 / 5847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2673 : Bounds (39122699 / 250000000) (156490797 / 1000000000) (Real.log (5847 / 5000)) := by
  have h := reflection_log_2673_neg
  have he : Real.log (5847 / 5000) = -Real.log (5000 / 5847) := by
    rw [show ((5847 / 5000) : ℝ) = ((5000 / 5847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2674_neg : (185606947 / 1000000000) ≤ -Real.log (4153 / 5000) ∧
    -Real.log (4153 / 5000) ≤ (46401737 / 250000000) := by
  have h := checkLog_sound (w := (847 / 9153)) (n := 12)
    (lo := (185606947 / 1000000000)) (hi := (46401737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4153) = 1/(4153 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2674 : Bounds (-46401737 / 250000000) (-185606947 / 1000000000) (Real.log (4153 / 5000)) := by
  have h := reflection_log_2674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2675_neg : (33877 / 200000000) ≤ -Real.log (5000000 / 5000847) ∧
    -Real.log (5000000 / 5000847) ≤ (84693 / 500000000) := by
  have h := checkLog_sound (w := (847 / 10000847)) (n := 12)
    (lo := (33877 / 200000000)) (hi := (84693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000847 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000847 / 5000000) = 1/(5000000 / 5000847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2675 : Bounds (33877 / 200000000) (84693 / 500000000) (Real.log (5000847 / 5000000)) := by
  have h := reflection_log_2675_neg
  have he : Real.log (5000847 / 5000000) = -Real.log (5000000 / 5000847) := by
    rw [show ((5000847 / 5000000) : ℝ) = ((5000000 / 5000847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2676_neg : (84707 / 500000000) ≤ -Real.log (4999153 / 5000000) ∧
    -Real.log (4999153 / 5000000) ≤ (33883 / 200000000) := by
  have h := checkLog_sound (w := (847 / 9999153)) (n := 12)
    (lo := (84707 / 500000000)) (hi := (33883 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999153) = 1/(4999153 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2676 : Bounds (-33883 / 200000000) (-84707 / 500000000) (Real.log (4999153 / 5000000)) := by
  have h := reflection_log_2676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2677_neg : (40793219 / 500000000) ≤ -Real.log (1000000 / 1085007) ∧
    -Real.log (1000000 / 1085007) ≤ (81586439 / 1000000000) := by
  have h := checkLog_sound (w := (85007 / 2085007)) (n := 12)
    (lo := (40793219 / 500000000)) (hi := (81586439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085007 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085007 / 1000000) = 1/(1000000 / 1085007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2677 : Bounds (40793219 / 500000000) (81586439 / 1000000000) (Real.log (1085007 / 1000000)) := by
  have h := reflection_log_2677_neg
  have he : Real.log (1085007 / 1000000) = -Real.log (1000000 / 1085007) := by
    rw [show ((1085007 / 1000000) : ℝ) = ((1000000 / 1085007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2678_neg : (5552429 / 62500000) ≤ -Real.log (914993 / 1000000) ∧
    -Real.log (914993 / 1000000) ≤ (17767773 / 200000000) := by
  have h := checkLog_sound (w := (85007 / 1914993)) (n := 12)
    (lo := (5552429 / 62500000)) (hi := (17767773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914993) = 1/(914993 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2678 : Bounds (-17767773 / 200000000) (-5552429 / 62500000) (Real.log (914993 / 1000000)) := by
  have h := reflection_log_2678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2679_neg : (81789181 / 1000000000) ≤ -Real.log (1000000 / 1085227) ∧
    -Real.log (1000000 / 1085227) ≤ (40894591 / 500000000) := by
  have h := checkLog_sound (w := (85227 / 2085227)) (n := 12)
    (lo := (81789181 / 1000000000)) (hi := (40894591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085227 / 1000000) = 1/(1000000 / 1085227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2679 : Bounds (81789181 / 1000000000) (40894591 / 500000000) (Real.log (1085227 / 1000000)) := by
  have h := reflection_log_2679_neg
  have he : Real.log (1085227 / 1000000) = -Real.log (1000000 / 1085227) := by
    rw [show ((1085227 / 1000000) : ℝ) = ((1000000 / 1085227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2680_neg : (89079331 / 1000000000) ≤ -Real.log (914773 / 1000000) ∧
    -Real.log (914773 / 1000000) ≤ (22269833 / 250000000) := by
  have h := checkLog_sound (w := (85227 / 1914773)) (n := 12)
    (lo := (89079331 / 1000000000)) (hi := (22269833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914773) = 1/(914773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2680 : Bounds (-22269833 / 250000000) (-89079331 / 1000000000) (Real.log (914773 / 1000000)) := by
  have h := reflection_log_2680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2681_neg : (145803 / 20000000) ≤ -Real.log (992736358471 / 1000000000000) ∧
    -Real.log (992736358471 / 1000000000000) ≤ (7290151 / 1000000000) := by
  have h := checkLog_sound (w := (7263641529 / 1992736358471)) (n := 12)
    (lo := (145803 / 20000000)) (hi := (7290151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992736358471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992736358471) = 1/(992736358471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2681 : Bounds (-7290151 / 1000000000) (-145803 / 20000000) (Real.log (992736358471 / 1000000000000)) := by
  have h := reflection_log_2681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2682_neg : (290097 / 40000000) ≤ -Real.log (992773809951 / 1000000000000) ∧
    -Real.log (992773809951 / 1000000000000) ≤ (3626213 / 500000000) := by
  have h := checkLog_sound (w := (7226190049 / 1992773809951)) (n := 12)
    (lo := (290097 / 40000000)) (hi := (3626213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992773809951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992773809951) = 1/(992773809951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2682 : Bounds (-3626213 / 500000000) (-290097 / 40000000) (Real.log (992773809951 / 1000000000000)) := by
  have h := reflection_log_2682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2683_neg : (85212651 / 500000000) ≤ -Real.log (500000000000 / 592904535881) ∧
    -Real.log (500000000000 / 592904535881) ≤ (170425303 / 1000000000) := by
  have h := checkLog_sound (w := (92904535881 / 1092904535881)) (n := 12)
    (lo := (85212651 / 500000000)) (hi := (170425303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592904535881 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592904535881 / 500000000000) = 1/(500000000000 / 592904535881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2683 : Bounds (85212651 / 500000000) (170425303 / 1000000000) (Real.log (592904535881 / 500000000000)) := by
  have h := reflection_log_2683_neg
  have he : Real.log (592904535881 / 500000000000) = -Real.log (500000000000 / 592904535881) := by
    rw [show ((592904535881 / 500000000000) : ℝ) = ((500000000000 / 592904535881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2684_neg : (170868513 / 1000000000) ≤ -Real.log (500000000000 / 593167375951) ∧
    -Real.log (500000000000 / 593167375951) ≤ (85434257 / 500000000) := by
  have h := checkLog_sound (w := (93167375951 / 1093167375951)) (n := 12)
    (lo := (170868513 / 1000000000)) (hi := (85434257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593167375951 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593167375951 / 500000000000) = 1/(500000000000 / 593167375951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2684 : Bounds (170868513 / 1000000000) (85434257 / 500000000) (Real.log (593167375951 / 500000000000)) := by
  have h := reflection_log_2684_neg
  have he : Real.log (593167375951 / 500000000000) = -Real.log (500000000000 / 593167375951) := by
    rw [show ((593167375951 / 500000000000) : ℝ) = ((500000000000 / 593167375951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2685_neg : (341891839 / 1000000000) ≤ -Real.log (100000000000 / 140760804141) ∧
    -Real.log (100000000000 / 140760804141) ≤ (267103 / 781250) := by
  have h := checkLog_sound (w := (40760804141 / 240760804141)) (n := 12)
    (lo := (341891839 / 1000000000)) (hi := (267103 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140760804141 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140760804141 / 100000000000) = 1/(100000000000 / 140760804141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2685 : Bounds (341891839 / 1000000000) (267103 / 781250) (Real.log (140760804141 / 100000000000)) := by
  have h := reflection_log_2685_neg
  have he : Real.log (140760804141 / 100000000000) = -Real.log (100000000000 / 140760804141) := by
    rw [show ((140760804141 / 100000000000) : ℝ) = ((100000000000 / 140760804141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2686_neg : (21381109 / 62500000) ≤ -Real.log (100000000000 / 140789790513) ∧
    -Real.log (100000000000 / 140789790513) ≤ (68419549 / 200000000) := by
  have h := checkLog_sound (w := (40789790513 / 240789790513)) (n := 12)
    (lo := (21381109 / 62500000)) (hi := (68419549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140789790513 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140789790513 / 100000000000) = 1/(100000000000 / 140789790513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2686 : Bounds (21381109 / 62500000) (68419549 / 200000000) (Real.log (140789790513 / 100000000000)) := by
  have h := reflection_log_2686_neg
  have he : Real.log (140789790513 / 100000000000) = -Real.log (100000000000 / 140789790513) := by
    rw [show ((140789790513 / 100000000000) : ℝ) = ((100000000000 / 140789790513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2687_neg : (156576307 / 1000000000) ≤ -Real.log (2000 / 2339) ∧
    -Real.log (2000 / 2339) ≤ (39144077 / 250000000) := by
  have h := checkLog_sound (w := (339 / 4339)) (n := 12)
    (lo := (156576307 / 1000000000)) (hi := (39144077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2339 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2339 / 2000) = 1/(2000 / 2339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2687 : Bounds (156576307 / 1000000000) (39144077 / 250000000) (Real.log (2339 / 2000)) := by
  have h := reflection_log_2687_neg
  have he : Real.log (2339 / 2000) = -Real.log (2000 / 2339) := by
    rw [show ((2339 / 2000) : ℝ) = ((2000 / 2339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0042 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2688_neg : (185727349 / 1000000000) ≤ -Real.log (1661 / 2000) ∧
    -Real.log (1661 / 2000) ≤ (3714547 / 20000000) := by
  have h := checkLog_sound (w := (339 / 3661)) (n := 12)
    (lo := (185727349 / 1000000000)) (hi := (3714547 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1661) = 1/(1661 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2688 : Bounds (-3714547 / 20000000) (-185727349 / 1000000000) (Real.log (1661 / 2000)) := by
  have h := reflection_log_2688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2689_neg : (33897 / 200000000) ≤ -Real.log (2000000 / 2000339) ∧
    -Real.log (2000000 / 2000339) ≤ (84743 / 500000000) := by
  have h := checkLog_sound (w := (339 / 4000339)) (n := 12)
    (lo := (33897 / 200000000)) (hi := (84743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000339 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000339 / 2000000) = 1/(2000000 / 2000339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2689 : Bounds (33897 / 200000000) (84743 / 500000000) (Real.log (2000339 / 2000000)) := by
  have h := reflection_log_2689_neg
  have he : Real.log (2000339 / 2000000) = -Real.log (2000000 / 2000339) := by
    rw [show ((2000339 / 2000000) : ℝ) = ((2000000 / 2000339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2690_neg : (84757 / 500000000) ≤ -Real.log (1999661 / 2000000) ∧
    -Real.log (1999661 / 2000000) ≤ (33903 / 200000000) := by
  have h := checkLog_sound (w := (339 / 3999661)) (n := 12)
    (lo := (84757 / 500000000)) (hi := (33903 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999661) = 1/(1999661 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2690 : Bounds (-33903 / 200000000) (-84757 / 500000000) (Real.log (1999661 / 2000000)) := by
  have h := reflection_log_2690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2691_neg : (2040813 / 25000000) ≤ -Real.log (1000000 / 1085057) ∧
    -Real.log (1000000 / 1085057) ≤ (81632521 / 1000000000) := by
  have h := checkLog_sound (w := (85057 / 2085057)) (n := 12)
    (lo := (2040813 / 25000000)) (hi := (81632521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085057 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085057 / 1000000) = 1/(1000000 / 1085057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2691 : Bounds (2040813 / 25000000) (81632521 / 1000000000) (Real.log (1085057 / 1000000)) := by
  have h := reflection_log_2691_neg
  have he : Real.log (1085057 / 1000000) = -Real.log (1000000 / 1085057) := by
    rw [show ((1085057 / 1000000) : ℝ) = ((1000000 / 1085057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2692_neg : (8889351 / 100000000) ≤ -Real.log (914943 / 1000000) ∧
    -Real.log (914943 / 1000000) ≤ (88893511 / 1000000000) := by
  have h := checkLog_sound (w := (85057 / 1914943)) (n := 12)
    (lo := (8889351 / 100000000)) (hi := (88893511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914943) = 1/(914943 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2692 : Bounds (-88893511 / 1000000000) (-8889351 / 100000000) (Real.log (914943 / 1000000)) := by
  have h := reflection_log_2692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2693_neg : (3273447 / 40000000) ≤ -Real.log (500000 / 542639) ∧
    -Real.log (500000 / 542639) ≤ (5114761 / 62500000) := by
  have h := checkLog_sound (w := (42639 / 1042639)) (n := 12)
    (lo := (3273447 / 40000000)) (hi := (5114761 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542639 / 500000) = 1/(500000 / 542639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2693 : Bounds (3273447 / 40000000) (5114761 / 62500000) (Real.log (542639 / 500000)) := by
  have h := reflection_log_2693_neg
  have he : Real.log (542639 / 500000) = -Real.log (500000 / 542639) := by
    rw [show ((542639 / 500000) : ℝ) = ((500000 / 542639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2694_neg : (17827017 / 200000000) ≤ -Real.log (457361 / 500000) ∧
    -Real.log (457361 / 500000) ≤ (44567543 / 500000000) := by
  have h := checkLog_sound (w := (42639 / 957361)) (n := 12)
    (lo := (17827017 / 200000000)) (hi := (44567543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457361) = 1/(457361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2694 : Bounds (-44567543 / 500000000) (-17827017 / 200000000) (Real.log (457361 / 500000)) := by
  have h := reflection_log_2694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2695_neg : (7298909 / 1000000000) ≤ -Real.log (248181915679 / 250000000000) ∧
    -Real.log (248181915679 / 250000000000) ≤ (729891 / 100000000) := by
  have h := checkLog_sound (w := (1818084321 / 498181915679)) (n := 12)
    (lo := (7298909 / 1000000000)) (hi := (729891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248181915679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248181915679) = 1/(248181915679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2695 : Bounds (-729891 / 100000000) (-7298909 / 1000000000) (Real.log (248181915679 / 250000000000)) := by
  have h := reflection_log_2695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2696_neg : (726099 / 100000000) ≤ -Real.log (992765306751 / 1000000000000) ∧
    -Real.log (992765306751 / 1000000000000) ≤ (7260991 / 1000000000) := by
  have h := checkLog_sound (w := (7234693249 / 1992765306751)) (n := 12)
    (lo := (726099 / 100000000)) (hi := (7260991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992765306751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992765306751) = 1/(992765306751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2696 : Bounds (-7260991 / 1000000000) (-726099 / 100000000) (Real.log (992765306751 / 1000000000000)) := by
  have h := reflection_log_2696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2697_neg : (17052603 / 100000000) ≤ -Real.log (500000000000 / 592964261161) ∧
    -Real.log (500000000000 / 592964261161) ≤ (170526031 / 1000000000) := by
  have h := checkLog_sound (w := (92964261161 / 1092964261161)) (n := 12)
    (lo := (17052603 / 100000000)) (hi := (170526031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592964261161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592964261161 / 500000000000) = 1/(500000000000 / 592964261161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2697 : Bounds (17052603 / 100000000) (170526031 / 1000000000) (Real.log (592964261161 / 500000000000)) := by
  have h := reflection_log_2697_neg
  have he : Real.log (592964261161 / 500000000000) = -Real.log (500000000000 / 592964261161) := by
    rw [show ((592964261161 / 500000000000) : ℝ) = ((500000000000 / 592964261161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2698_neg : (8548563 / 50000000) ≤ -Real.log (500000000000 / 593228325109) ∧
    -Real.log (500000000000 / 593228325109) ≤ (170971261 / 1000000000) := by
  have h := checkLog_sound (w := (93228325109 / 1093228325109)) (n := 12)
    (lo := (8548563 / 50000000)) (hi := (170971261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593228325109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593228325109 / 500000000000) = 1/(500000000000 / 593228325109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2698 : Bounds (8548563 / 50000000) (170971261 / 1000000000) (Real.log (593228325109 / 500000000000)) := by
  have h := reflection_log_2698_neg
  have he : Real.log (593228325109 / 500000000000) = -Real.log (500000000000 / 593228325109) := by
    rw [show ((593228325109 / 500000000000) : ℝ) = ((500000000000 / 593228325109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2699_neg : (21381109 / 62500000) ≤ -Real.log (125000000000 / 175987238141) ∧
    -Real.log (125000000000 / 175987238141) ≤ (68419549 / 200000000) := by
  have h := checkLog_sound (w := (50987238141 / 300987238141)) (n := 12)
    (lo := (21381109 / 62500000)) (hi := (68419549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175987238141 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175987238141 / 125000000000) = 1/(125000000000 / 175987238141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2699 : Bounds (21381109 / 62500000) (68419549 / 200000000) (Real.log (175987238141 / 125000000000)) := by
  have h := reflection_log_2699_neg
  have he : Real.log (175987238141 / 125000000000) = -Real.log (125000000000 / 175987238141) := by
    rw [show ((175987238141 / 125000000000) : ℝ) = ((125000000000 / 175987238141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2700_neg : (42787957 / 125000000) ≤ -Real.log (250000000000 / 352046959663) ∧
    -Real.log (250000000000 / 352046959663) ≤ (342303657 / 1000000000) := by
  have h := checkLog_sound (w := (102046959663 / 602046959663)) (n := 12)
    (lo := (42787957 / 125000000)) (hi := (342303657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352046959663 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352046959663 / 250000000000) = 1/(250000000000 / 352046959663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2700 : Bounds (42787957 / 125000000) (342303657 / 1000000000) (Real.log (352046959663 / 250000000000)) := by
  have h := reflection_log_2700_neg
  have he : Real.log (352046959663 / 250000000000) = -Real.log (250000000000 / 352046959663) := by
    rw [show ((352046959663 / 250000000000) : ℝ) = ((250000000000 / 352046959663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2701_neg : (15666181 / 100000000) ≤ -Real.log (625 / 731) ∧
    -Real.log (625 / 731) ≤ (156661811 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 678)) (n := 12)
    (lo := (15666181 / 100000000)) (hi := (156661811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731 / 625) = 1/(625 / 731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2701 : Bounds (15666181 / 100000000) (156661811 / 1000000000) (Real.log (731 / 625)) := by
  have h := reflection_log_2701_neg
  have he : Real.log (731 / 625) = -Real.log (625 / 731) := by
    rw [show ((731 / 625) : ℝ) = ((625 / 731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2702_neg : (92923883 / 500000000) ≤ -Real.log (519 / 625) ∧
    -Real.log (519 / 625) ≤ (185847767 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 572)) (n := 12)
    (lo := (92923883 / 500000000)) (hi := (185847767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 519) = 1/(519 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2702 : Bounds (-185847767 / 1000000000) (-92923883 / 500000000) (Real.log (519 / 625)) := by
  have h := reflection_log_2702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2703_neg : (33917 / 200000000) ≤ -Real.log (312500 / 312553) ∧
    -Real.log (312500 / 312553) ≤ (84793 / 500000000) := by
  have h := checkLog_sound (w := (53 / 625053)) (n := 12)
    (lo := (33917 / 200000000)) (hi := (84793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312553 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312553 / 312500) = 1/(312500 / 312553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2703 : Bounds (33917 / 200000000) (84793 / 500000000) (Real.log (312553 / 312500)) := by
  have h := reflection_log_2703_neg
  have he : Real.log (312553 / 312500) = -Real.log (312500 / 312553) := by
    rw [show ((312553 / 312500) : ℝ) = ((312500 / 312553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2704_neg : (84807 / 500000000) ≤ -Real.log (312447 / 312500) ∧
    -Real.log (312447 / 312500) ≤ (33923 / 200000000) := by
  have h := checkLog_sound (w := (53 / 624947)) (n := 12)
    (lo := (84807 / 500000000)) (hi := (33923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312447) = 1/(312447 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2704 : Bounds (-33923 / 200000000) (-84807 / 500000000) (Real.log (312447 / 312500)) := by
  have h := reflection_log_2704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2705_neg : (81679521 / 1000000000) ≤ -Real.log (250000 / 271277) ∧
    -Real.log (250000 / 271277) ≤ (40839761 / 500000000) := by
  have h := checkLog_sound (w := (21277 / 521277)) (n := 12)
    (lo := (81679521 / 1000000000)) (hi := (40839761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271277 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271277 / 250000) = 1/(250000 / 271277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2705 : Bounds (81679521 / 1000000000) (40839761 / 500000000) (Real.log (271277 / 250000)) := by
  have h := reflection_log_2705_neg
  have he : Real.log (271277 / 250000) = -Real.log (250000 / 271277) := by
    rw [show ((271277 / 250000) : ℝ) = ((250000 / 271277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2706_neg : (88949253 / 1000000000) ≤ -Real.log (228723 / 250000) ∧
    -Real.log (228723 / 250000) ≤ (44474627 / 500000000) := by
  have h := checkLog_sound (w := (21277 / 478723)) (n := 12)
    (lo := (88949253 / 1000000000)) (hi := (44474627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228723) = 1/(228723 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2706 : Bounds (-44474627 / 500000000) (-88949253 / 1000000000) (Real.log (228723 / 250000)) := by
  have h := reflection_log_2706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2707_neg : (16376449 / 200000000) ≤ -Real.log (62500 / 67833) ∧
    -Real.log (62500 / 67833) ≤ (40941123 / 500000000) := by
  have h := checkLog_sound (w := (5333 / 130333)) (n := 12)
    (lo := (16376449 / 200000000)) (hi := (40941123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67833 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67833 / 62500) = 1/(62500 / 67833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2707 : Bounds (16376449 / 200000000) (40941123 / 500000000) (Real.log (67833 / 62500)) := by
  have h := reflection_log_2707_neg
  have he : Real.log (67833 / 62500) = -Real.log (62500 / 67833) := by
    rw [show ((67833 / 62500) : ℝ) = ((62500 / 67833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2708_neg : (89189747 / 1000000000) ≤ -Real.log (57167 / 62500) ∧
    -Real.log (57167 / 62500) ≤ (22297437 / 250000000) := by
  have h := checkLog_sound (w := (5333 / 119667)) (n := 12)
    (lo := (89189747 / 1000000000)) (hi := (22297437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57167) = 1/(57167 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2708 : Bounds (-22297437 / 250000000) (-89189747 / 1000000000) (Real.log (57167 / 62500)) := by
  have h := reflection_log_2708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2709_neg : (3653751 / 500000000) ≤ -Real.log (3877809111 / 3906250000) ∧
    -Real.log (3877809111 / 3906250000) ≤ (7307503 / 1000000000) := by
  have h := checkLog_sound (w := (28440889 / 7784059111)) (n := 12)
    (lo := (3653751 / 500000000)) (hi := (7307503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3877809111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3877809111) = 1/(3877809111 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2709 : Bounds (-7307503 / 1000000000) (-3653751 / 500000000) (Real.log (3877809111 / 3906250000)) := by
  have h := reflection_log_2709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2710_neg : (1817433 / 250000000) ≤ -Real.log (62047289271 / 62500000000) ∧
    -Real.log (62047289271 / 62500000000) ≤ (7269733 / 1000000000) := by
  have h := checkLog_sound (w := (452710729 / 124547289271)) (n := 12)
    (lo := (1817433 / 250000000)) (hi := (7269733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62047289271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62047289271) = 1/(62047289271 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2710 : Bounds (-7269733 / 1000000000) (-1817433 / 250000000) (Real.log (62047289271 / 62500000000)) := by
  have h := reflection_log_2710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2711_neg : (85314387 / 500000000) ≤ -Real.log (62500000000 / 74128148459) ∧
    -Real.log (62500000000 / 74128148459) ≤ (6825151 / 40000000) := by
  have h := checkLog_sound (w := (11628148459 / 136628148459)) (n := 12)
    (lo := (85314387 / 500000000)) (hi := (6825151 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74128148459 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74128148459 / 62500000000) = 1/(62500000000 / 74128148459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2711 : Bounds (85314387 / 500000000) (6825151 / 40000000) (Real.log (74128148459 / 62500000000)) := by
  have h := reflection_log_2711_neg
  have he : Real.log (74128148459 / 62500000000) = -Real.log (62500000000 / 74128148459) := by
    rw [show ((74128148459 / 62500000000) : ℝ) = ((62500000000 / 74128148459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2712_neg : (171071993 / 1000000000) ≤ -Real.log (62500000000 / 74161010723) ∧
    -Real.log (62500000000 / 74161010723) ≤ (85535997 / 500000000) := by
  have h := checkLog_sound (w := (11661010723 / 136661010723)) (n := 12)
    (lo := (171071993 / 1000000000)) (hi := (85535997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74161010723 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74161010723 / 62500000000) = 1/(62500000000 / 74161010723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2712 : Bounds (171071993 / 1000000000) (85535997 / 500000000) (Real.log (74161010723 / 62500000000)) := by
  have h := reflection_log_2712_neg
  have he : Real.log (74161010723 / 62500000000) = -Real.log (62500000000 / 74161010723) := by
    rw [show ((74161010723 / 62500000000) : ℝ) = ((62500000000 / 74161010723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2713_neg : (42787957 / 125000000) ≤ -Real.log (20000000000 / 28163756773) ∧
    -Real.log (20000000000 / 28163756773) ≤ (342303657 / 1000000000) := by
  have h := checkLog_sound (w := (8163756773 / 48163756773)) (n := 12)
    (lo := (42787957 / 125000000)) (hi := (342303657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28163756773 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28163756773 / 20000000000) = 1/(20000000000 / 28163756773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2713 : Bounds (42787957 / 125000000) (342303657 / 1000000000) (Real.log (28163756773 / 20000000000)) := by
  have h := reflection_log_2713_neg
  have he : Real.log (28163756773 / 20000000000) = -Real.log (20000000000 / 28163756773) := by
    rw [show ((28163756773 / 20000000000) : ℝ) = ((20000000000 / 28163756773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2714_neg : (42813697 / 125000000) ≤ -Real.log (250000000000 / 352119460501) ∧
    -Real.log (250000000000 / 352119460501) ≤ (342509577 / 1000000000) := by
  have h := checkLog_sound (w := (102119460501 / 602119460501)) (n := 12)
    (lo := (42813697 / 125000000)) (hi := (342509577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352119460501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352119460501 / 250000000000) = 1/(250000000000 / 352119460501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2714 : Bounds (42813697 / 125000000) (342509577 / 1000000000) (Real.log (352119460501 / 250000000000)) := by
  have h := reflection_log_2714_neg
  have he : Real.log (352119460501 / 250000000000) = -Real.log (250000000000 / 352119460501) := by
    rw [show ((352119460501 / 250000000000) : ℝ) = ((250000000000 / 352119460501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2715_neg : (31349461 / 200000000) ≤ -Real.log (10000 / 11697) ∧
    -Real.log (10000 / 11697) ≤ (78373653 / 500000000) := by
  have h := checkLog_sound (w := (1697 / 21697)) (n := 12)
    (lo := (31349461 / 200000000)) (hi := (78373653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11697 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11697 / 10000) = 1/(10000 / 11697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2715 : Bounds (31349461 / 200000000) (78373653 / 500000000) (Real.log (11697 / 10000)) := by
  have h := reflection_log_2715_neg
  have he : Real.log (11697 / 10000) = -Real.log (10000 / 11697) := by
    rw [show ((11697 / 10000) : ℝ) = ((10000 / 11697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2716_neg : (185968197 / 1000000000) ≤ -Real.log (8303 / 10000) ∧
    -Real.log (8303 / 10000) ≤ (92984099 / 500000000) := by
  have h := checkLog_sound (w := (1697 / 18303)) (n := 12)
    (lo := (185968197 / 1000000000)) (hi := (92984099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8303) = 1/(8303 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2716 : Bounds (-92984099 / 500000000) (-185968197 / 1000000000) (Real.log (8303 / 10000)) := by
  have h := reflection_log_2716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2717_neg : (33937 / 200000000) ≤ -Real.log (10000000 / 10001697) ∧
    -Real.log (10000000 / 10001697) ≤ (84843 / 500000000) := by
  have h := checkLog_sound (w := (1697 / 20001697)) (n := 12)
    (lo := (33937 / 200000000)) (hi := (84843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001697 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001697 / 10000000) = 1/(10000000 / 10001697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2717 : Bounds (33937 / 200000000) (84843 / 500000000) (Real.log (10001697 / 10000000)) := by
  have h := reflection_log_2717_neg
  have he : Real.log (10001697 / 10000000) = -Real.log (10000000 / 10001697) := by
    rw [show ((10001697 / 10000000) : ℝ) = ((10000000 / 10001697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2718_neg : (84857 / 500000000) ≤ -Real.log (9998303 / 10000000) ∧
    -Real.log (9998303 / 10000000) ≤ (33943 / 200000000) := by
  have h := checkLog_sound (w := (1697 / 19998303)) (n := 12)
    (lo := (84857 / 500000000)) (hi := (33943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998303) = 1/(9998303 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2718 : Bounds (-33943 / 200000000) (-84857 / 500000000) (Real.log (9998303 / 10000000)) := by
  have h := reflection_log_2718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2719_neg : (2043163 / 25000000) ≤ -Real.log (1000000 / 1085159) ∧
    -Real.log (1000000 / 1085159) ≤ (81726521 / 1000000000) := by
  have h := checkLog_sound (w := (85159 / 2085159)) (n := 12)
    (lo := (2043163 / 25000000)) (hi := (81726521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085159 / 1000000) = 1/(1000000 / 1085159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2719 : Bounds (2043163 / 25000000) (81726521 / 1000000000) (Real.log (1085159 / 1000000)) := by
  have h := reflection_log_2719_neg
  have he : Real.log (1085159 / 1000000) = -Real.log (1000000 / 1085159) := by
    rw [show ((1085159 / 1000000) : ℝ) = ((1000000 / 1085159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2720_neg : (89004999 / 1000000000) ≤ -Real.log (914841 / 1000000) ∧
    -Real.log (914841 / 1000000) ≤ (17801 / 200000) := by
  have h := checkLog_sound (w := (85159 / 1914841)) (n := 12)
    (lo := (89004999 / 1000000000)) (hi := (17801 / 200000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914841) = 1/(914841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2720 : Bounds (-17801 / 200000) (-89004999 / 1000000000) (Real.log (914841 / 1000000)) := by
  have h := reflection_log_2720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2721_neg : (40964617 / 500000000) ≤ -Real.log (1000000 / 1085379) ∧
    -Real.log (1000000 / 1085379) ≤ (16385847 / 200000000) := by
  have h := checkLog_sound (w := (85379 / 2085379)) (n := 12)
    (lo := (40964617 / 500000000)) (hi := (16385847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085379 / 1000000) = 1/(1000000 / 1085379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2721 : Bounds (40964617 / 500000000) (16385847 / 200000000) (Real.log (1085379 / 1000000)) := by
  have h := reflection_log_2721_neg
  have he : Real.log (1085379 / 1000000) = -Real.log (1000000 / 1085379) := by
    rw [show ((1085379 / 1000000) : ℝ) = ((1000000 / 1085379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2722_neg : (89245507 / 1000000000) ≤ -Real.log (914621 / 1000000) ∧
    -Real.log (914621 / 1000000) ≤ (22311377 / 250000000) := by
  have h := checkLog_sound (w := (85379 / 1914621)) (n := 12)
    (lo := (89245507 / 1000000000)) (hi := (22311377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914621) = 1/(914621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2722 : Bounds (-22311377 / 250000000) (-89245507 / 1000000000) (Real.log (914621 / 1000000)) := by
  have h := reflection_log_2722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2723_neg : (457267 / 62500000) ≤ -Real.log (992710426359 / 1000000000000) ∧
    -Real.log (992710426359 / 1000000000000) ≤ (7316273 / 1000000000) := by
  have h := checkLog_sound (w := (7289573641 / 1992710426359)) (n := 12)
    (lo := (457267 / 62500000)) (hi := (7316273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992710426359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992710426359) = 1/(992710426359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2723 : Bounds (-7316273 / 1000000000) (-457267 / 62500000) (Real.log (992710426359 / 1000000000000)) := by
  have h := reflection_log_2723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2724_neg : (7278479 / 1000000000) ≤ -Real.log (992747944719 / 1000000000000) ∧
    -Real.log (992747944719 / 1000000000000) ≤ (90981 / 12500000) := by
  have h := checkLog_sound (w := (7252055281 / 1992747944719)) (n := 12)
    (lo := (7278479 / 1000000000)) (hi := (90981 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992747944719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992747944719) = 1/(992747944719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2724 : Bounds (-90981 / 12500000) (-7278479 / 1000000000) (Real.log (992747944719 / 1000000000000)) := by
  have h := reflection_log_2724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2725_neg : (170731519 / 1000000000) ≤ -Real.log (31250000000 / 37067882561) ∧
    -Real.log (31250000000 / 37067882561) ≤ (66692 / 390625) := by
  have h := checkLog_sound (w := (5817882561 / 68317882561)) (n := 12)
    (lo := (170731519 / 1000000000)) (hi := (66692 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37067882561 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37067882561 / 31250000000) = 1/(31250000000 / 37067882561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2725 : Bounds (170731519 / 1000000000) (66692 / 390625) (Real.log (37067882561 / 31250000000)) := by
  have h := reflection_log_2725_neg
  have he : Real.log (37067882561 / 31250000000) = -Real.log (31250000000 / 37067882561) := by
    rw [show ((37067882561 / 31250000000) : ℝ) = ((31250000000 / 37067882561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2726_neg : (171174741 / 1000000000) ≤ -Real.log (125000000000 / 148337262101) ∧
    -Real.log (125000000000 / 148337262101) ≤ (85587371 / 500000000) := by
  have h := checkLog_sound (w := (23337262101 / 273337262101)) (n := 12)
    (lo := (171174741 / 1000000000)) (hi := (85587371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148337262101 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148337262101 / 125000000000) = 1/(125000000000 / 148337262101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2726 : Bounds (171174741 / 1000000000) (85587371 / 500000000) (Real.log (148337262101 / 125000000000)) := by
  have h := reflection_log_2726_neg
  have he : Real.log (148337262101 / 125000000000) = -Real.log (125000000000 / 148337262101) := by
    rw [show ((148337262101 / 125000000000) : ℝ) = ((125000000000 / 148337262101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2727_neg : (42813697 / 125000000) ≤ -Real.log (500000000000 / 704238921001) ∧
    -Real.log (500000000000 / 704238921001) ≤ (342509577 / 1000000000) := by
  have h := checkLog_sound (w := (204238921001 / 1204238921001)) (n := 12)
    (lo := (42813697 / 125000000)) (hi := (342509577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704238921001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704238921001 / 500000000000) = 1/(500000000000 / 704238921001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2727 : Bounds (42813697 / 125000000) (342509577 / 1000000000) (Real.log (704238921001 / 500000000000)) := by
  have h := reflection_log_2727_neg
  have he : Real.log (704238921001 / 500000000000) = -Real.log (500000000000 / 704238921001) := by
    rw [show ((704238921001 / 500000000000) : ℝ) = ((500000000000 / 704238921001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2728_neg : (342715503 / 1000000000) ≤ -Real.log (250000000000 / 352191978803) ∧
    -Real.log (250000000000 / 352191978803) ≤ (21419719 / 62500000) := by
  have h := checkLog_sound (w := (102191978803 / 602191978803)) (n := 12)
    (lo := (342715503 / 1000000000)) (hi := (21419719 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352191978803 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352191978803 / 250000000000) = 1/(250000000000 / 352191978803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2728 : Bounds (342715503 / 1000000000) (21419719 / 62500000) (Real.log (352191978803 / 250000000000)) := by
  have h := reflection_log_2728_neg
  have he : Real.log (352191978803 / 250000000000) = -Real.log (250000000000 / 352191978803) := by
    rw [show ((352191978803 / 250000000000) : ℝ) = ((250000000000 / 352191978803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2729_neg : (78416397 / 500000000) ≤ -Real.log (5000 / 5849) ∧
    -Real.log (5000 / 5849) ≤ (31366559 / 200000000) := by
  have h := checkLog_sound (w := (849 / 10849)) (n := 12)
    (lo := (78416397 / 500000000)) (hi := (31366559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5849 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5849 / 5000) = 1/(5000 / 5849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2729 : Bounds (78416397 / 500000000) (31366559 / 200000000) (Real.log (5849 / 5000)) := by
  have h := reflection_log_2729_neg
  have he : Real.log (5849 / 5000) = -Real.log (5000 / 5849) := by
    rw [show ((5849 / 5000) : ℝ) = ((5000 / 5849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2730_neg : (186088643 / 1000000000) ≤ -Real.log (4151 / 5000) ∧
    -Real.log (4151 / 5000) ≤ (46522161 / 250000000) := by
  have h := checkLog_sound (w := (849 / 9151)) (n := 12)
    (lo := (186088643 / 1000000000)) (hi := (46522161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4151) = 1/(4151 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2730 : Bounds (-46522161 / 250000000) (-186088643 / 1000000000) (Real.log (4151 / 5000)) := by
  have h := reflection_log_2730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2731_neg : (33957 / 200000000) ≤ -Real.log (5000000 / 5000849) ∧
    -Real.log (5000000 / 5000849) ≤ (84893 / 500000000) := by
  have h := checkLog_sound (w := (849 / 10000849)) (n := 12)
    (lo := (33957 / 200000000)) (hi := (84893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000849 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000849 / 5000000) = 1/(5000000 / 5000849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2731 : Bounds (33957 / 200000000) (84893 / 500000000) (Real.log (5000849 / 5000000)) := by
  have h := reflection_log_2731_neg
  have he : Real.log (5000849 / 5000000) = -Real.log (5000000 / 5000849) := by
    rw [show ((5000849 / 5000000) : ℝ) = ((5000000 / 5000849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2732_neg : (84907 / 500000000) ≤ -Real.log (4999151 / 5000000) ∧
    -Real.log (4999151 / 5000000) ≤ (33963 / 200000000) := by
  have h := checkLog_sound (w := (849 / 9999151)) (n := 12)
    (lo := (84907 / 500000000)) (hi := (33963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999151) = 1/(4999151 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2732 : Bounds (-33963 / 200000000) (-84907 / 500000000) (Real.log (4999151 / 5000000)) := by
  have h := reflection_log_2732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2733_neg : (20443379 / 250000000) ≤ -Real.log (100000 / 108521) ∧
    -Real.log (100000 / 108521) ≤ (81773517 / 1000000000) := by
  have h := checkLog_sound (w := (8521 / 208521)) (n := 12)
    (lo := (20443379 / 250000000)) (hi := (81773517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108521 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108521 / 100000) = 1/(100000 / 108521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2733 : Bounds (20443379 / 250000000) (81773517 / 1000000000) (Real.log (108521 / 100000)) := by
  have h := reflection_log_2733_neg
  have he : Real.log (108521 / 100000) = -Real.log (100000 / 108521) := by
    rw [show ((108521 / 100000) : ℝ) = ((100000 / 108521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2734_neg : (22265187 / 250000000) ≤ -Real.log (91479 / 100000) ∧
    -Real.log (91479 / 100000) ≤ (89060749 / 1000000000) := by
  have h := checkLog_sound (w := (8521 / 191479)) (n := 12)
    (lo := (22265187 / 250000000)) (hi := (89060749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91479) = 1/(91479 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2734 : Bounds (-89060749 / 1000000000) (-22265187 / 250000000) (Real.log (91479 / 100000)) := by
  have h := reflection_log_2734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2735_neg : (81976221 / 1000000000) ≤ -Real.log (100000 / 108543) ∧
    -Real.log (100000 / 108543) ≤ (40988111 / 500000000) := by
  have h := checkLog_sound (w := (8543 / 208543)) (n := 12)
    (lo := (81976221 / 1000000000)) (hi := (40988111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108543 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108543 / 100000) = 1/(100000 / 108543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2735 : Bounds (81976221 / 1000000000) (40988111 / 500000000) (Real.log (108543 / 100000)) := by
  have h := reflection_log_2735_neg
  have he : Real.log (108543 / 100000) = -Real.log (100000 / 108543) := by
    rw [show ((108543 / 100000) : ℝ) = ((100000 / 108543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2736_neg : (89301269 / 1000000000) ≤ -Real.log (91457 / 100000) ∧
    -Real.log (91457 / 100000) ≤ (8930127 / 100000000) := by
  have h := checkLog_sound (w := (8543 / 191457)) (n := 12)
    (lo := (89301269 / 1000000000)) (hi := (8930127 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91457) = 1/(91457 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2736 : Bounds (-8930127 / 100000000) (-89301269 / 1000000000) (Real.log (91457 / 100000)) := by
  have h := reflection_log_2736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2737_neg : (7325047 / 1000000000) ≤ -Real.log (9927017151 / 10000000000) ∧
    -Real.log (9927017151 / 10000000000) ≤ (915631 / 125000000) := by
  have h := checkLog_sound (w := (72982849 / 19927017151)) (n := 12)
    (lo := (7325047 / 1000000000)) (hi := (915631 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9927017151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9927017151) = 1/(9927017151 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2737 : Bounds (-915631 / 125000000) (-7325047 / 1000000000) (Real.log (9927017151 / 10000000000)) := by
  have h := reflection_log_2737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2738_neg : (7287231 / 1000000000) ≤ -Real.log (9927392559 / 10000000000) ∧
    -Real.log (9927392559 / 10000000000) ≤ (113863 / 15625000) := by
  have h := checkLog_sound (w := (72607441 / 19927392559)) (n := 12)
    (lo := (7287231 / 1000000000)) (hi := (113863 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9927392559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9927392559) = 1/(9927392559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2738 : Bounds (-113863 / 15625000) (-7287231 / 1000000000) (Real.log (9927392559 / 10000000000)) := by
  have h := reflection_log_2738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2739_neg : (21354283 / 125000000) ≤ -Real.log (250000000000 / 296573530537) ∧
    -Real.log (250000000000 / 296573530537) ≤ (34166853 / 200000000) := by
  have h := checkLog_sound (w := (46573530537 / 546573530537)) (n := 12)
    (lo := (21354283 / 125000000)) (hi := (34166853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296573530537 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296573530537 / 250000000000) = 1/(250000000000 / 296573530537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2739 : Bounds (21354283 / 125000000) (34166853 / 200000000) (Real.log (296573530537 / 250000000000)) := by
  have h := reflection_log_2739_neg
  have he : Real.log (296573530537 / 250000000000) = -Real.log (250000000000 / 296573530537) := by
    rw [show ((296573530537 / 250000000000) : ℝ) = ((250000000000 / 296573530537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2740_neg : (171277491 / 1000000000) ≤ -Real.log (500000000000 / 593410017823) ∧
    -Real.log (500000000000 / 593410017823) ≤ (42819373 / 250000000) := by
  have h := checkLog_sound (w := (93410017823 / 1093410017823)) (n := 12)
    (lo := (171277491 / 1000000000)) (hi := (42819373 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593410017823 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593410017823 / 500000000000) = 1/(500000000000 / 593410017823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2740 : Bounds (171277491 / 1000000000) (42819373 / 250000000) (Real.log (593410017823 / 500000000000)) := by
  have h := reflection_log_2740_neg
  have he : Real.log (593410017823 / 500000000000) = -Real.log (500000000000 / 593410017823) := by
    rw [show ((593410017823 / 500000000000) : ℝ) = ((500000000000 / 593410017823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2741_neg : (342715503 / 1000000000) ≤ -Real.log (100000000000 / 140876791521) ∧
    -Real.log (100000000000 / 140876791521) ≤ (21419719 / 62500000) := by
  have h := checkLog_sound (w := (40876791521 / 240876791521)) (n := 12)
    (lo := (342715503 / 1000000000)) (hi := (21419719 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140876791521 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140876791521 / 100000000000) = 1/(100000000000 / 140876791521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2741 : Bounds (342715503 / 1000000000) (21419719 / 62500000) (Real.log (140876791521 / 100000000000)) := by
  have h := reflection_log_2741_neg
  have he : Real.log (140876791521 / 100000000000) = -Real.log (100000000000 / 140876791521) := by
    rw [show ((140876791521 / 100000000000) : ℝ) = ((100000000000 / 140876791521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2742_neg : (342921437 / 1000000000) ≤ -Real.log (10000000000 / 14090580583) ∧
    -Real.log (10000000000 / 14090580583) ≤ (171460719 / 500000000) := by
  have h := checkLog_sound (w := (4090580583 / 24090580583)) (n := 12)
    (lo := (342921437 / 1000000000)) (hi := (171460719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14090580583 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14090580583 / 10000000000) = 1/(10000000000 / 14090580583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2742 : Bounds (342921437 / 1000000000) (171460719 / 500000000) (Real.log (14090580583 / 10000000000)) := by
  have h := reflection_log_2742_neg
  have he : Real.log (14090580583 / 10000000000) = -Real.log (10000000000 / 14090580583) := by
    rw [show ((14090580583 / 10000000000) : ℝ) = ((10000000000 / 14090580583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2743_neg : (6276731 / 40000000) ≤ -Real.log (10000 / 11699) ∧
    -Real.log (10000 / 11699) ≤ (39229569 / 250000000) := by
  have h := checkLog_sound (w := (1699 / 21699)) (n := 12)
    (lo := (6276731 / 40000000)) (hi := (39229569 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11699 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11699 / 10000) = 1/(10000 / 11699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2743 : Bounds (6276731 / 40000000) (39229569 / 250000000) (Real.log (11699 / 10000)) := by
  have h := reflection_log_2743_neg
  have he : Real.log (11699 / 10000) = -Real.log (10000 / 11699) := by
    rw [show ((11699 / 10000) : ℝ) = ((10000 / 11699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2744_neg : (186209103 / 1000000000) ≤ -Real.log (8301 / 10000) ∧
    -Real.log (8301 / 10000) ≤ (11638069 / 62500000) := by
  have h := checkLog_sound (w := (1699 / 18301)) (n := 12)
    (lo := (186209103 / 1000000000)) (hi := (11638069 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8301) = 1/(8301 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2744 : Bounds (-11638069 / 62500000) (-186209103 / 1000000000) (Real.log (8301 / 10000)) := by
  have h := reflection_log_2744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2745_neg : (33977 / 200000000) ≤ -Real.log (10000000 / 10001699) ∧
    -Real.log (10000000 / 10001699) ≤ (84943 / 500000000) := by
  have h := checkLog_sound (w := (1699 / 20001699)) (n := 12)
    (lo := (33977 / 200000000)) (hi := (84943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001699 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001699 / 10000000) = 1/(10000000 / 10001699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2745 : Bounds (33977 / 200000000) (84943 / 500000000) (Real.log (10001699 / 10000000)) := by
  have h := reflection_log_2745_neg
  have he : Real.log (10001699 / 10000000) = -Real.log (10000000 / 10001699) := by
    rw [show ((10001699 / 10000000) : ℝ) = ((10000000 / 10001699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2746_neg : (84957 / 500000000) ≤ -Real.log (9998301 / 10000000) ∧
    -Real.log (9998301 / 10000000) ≤ (33983 / 200000000) := by
  have h := checkLog_sound (w := (1699 / 19998301)) (n := 12)
    (lo := (84957 / 500000000)) (hi := (33983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998301) = 1/(9998301 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2746 : Bounds (-33983 / 200000000) (-84957 / 500000000) (Real.log (9998301 / 10000000)) := by
  have h := reflection_log_2746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2747_neg : (81819589 / 1000000000) ≤ -Real.log (50000 / 54263) ∧
    -Real.log (50000 / 54263) ≤ (8181959 / 100000000) := by
  have h := checkLog_sound (w := (4263 / 104263)) (n := 12)
    (lo := (81819589 / 1000000000)) (hi := (8181959 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54263 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54263 / 50000) = 1/(50000 / 54263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2747 : Bounds (81819589 / 1000000000) (8181959 / 100000000) (Real.log (54263 / 50000)) := by
  have h := reflection_log_2747_neg
  have he : Real.log (54263 / 50000) = -Real.log (50000 / 54263) := by
    rw [show ((54263 / 50000) : ℝ) = ((50000 / 54263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2748_neg : (89115407 / 1000000000) ≤ -Real.log (45737 / 50000) ∧
    -Real.log (45737 / 50000) ≤ (5569713 / 62500000) := by
  have h := checkLog_sound (w := (4263 / 95737)) (n := 12)
    (lo := (89115407 / 1000000000)) (hi := (5569713 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45737) = 1/(45737 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2748 : Bounds (-5569713 / 62500000) (-89115407 / 1000000000) (Real.log (45737 / 50000)) := by
  have h := reflection_log_2748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2749_neg : (41011603 / 500000000) ≤ -Real.log (1000000 / 1085481) ∧
    -Real.log (1000000 / 1085481) ≤ (82023207 / 1000000000) := by
  have h := checkLog_sound (w := (85481 / 2085481)) (n := 12)
    (lo := (41011603 / 500000000)) (hi := (82023207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085481 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085481 / 1000000) = 1/(1000000 / 1085481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2749 : Bounds (41011603 / 500000000) (82023207 / 1000000000) (Real.log (1085481 / 1000000)) := by
  have h := reflection_log_2749_neg
  have he : Real.log (1085481 / 1000000) = -Real.log (1000000 / 1085481) := by
    rw [show ((1085481 / 1000000) : ℝ) = ((1000000 / 1085481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2750_neg : (44678517 / 500000000) ≤ -Real.log (914519 / 1000000) ∧
    -Real.log (914519 / 1000000) ≤ (17871407 / 200000000) := by
  have h := checkLog_sound (w := (85481 / 1914519)) (n := 12)
    (lo := (44678517 / 500000000)) (hi := (17871407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914519) = 1/(914519 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2750 : Bounds (-17871407 / 200000000) (-44678517 / 500000000) (Real.log (914519 / 1000000)) := by
  have h := reflection_log_2750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2751_neg : (1833457 / 250000000) ≤ -Real.log (992692998639 / 1000000000000) ∧
    -Real.log (992692998639 / 1000000000000) ≤ (7333829 / 1000000000) := by
  have h := checkLog_sound (w := (7307001361 / 1992692998639)) (n := 12)
    (lo := (1833457 / 250000000)) (hi := (7333829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992692998639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992692998639) = 1/(992692998639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2751 : Bounds (-7333829 / 1000000000) (-1833457 / 250000000) (Real.log (992692998639 / 1000000000000)) := by
  have h := reflection_log_2751_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


