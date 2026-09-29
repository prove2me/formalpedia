-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0077__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0077__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:31:28.296058+00:00
-- url     : https://prove2.me/theorems/a318fcc1-e703-406a-8e98-c1f2eb302d29
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0077 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0078, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0077 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0078, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0079)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0077 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0078, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0079)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0077 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0078, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0079) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0077 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0078, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0079).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0077 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4928_neg : (92741 / 500000000) ≤ -Real.log (2000000 / 2000371) ∧
    -Real.log (2000000 / 2000371) ≤ (185483 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 4000371)) (n := 12)
    (lo := (92741 / 500000000)) (hi := (185483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000371 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000371 / 2000000) = 1/(2000000 / 2000371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4928 : Bounds (92741 / 500000000) (185483 / 1000000000) (Real.log (2000371 / 2000000)) := by
  have h := reflection_log_4928_neg
  have he : Real.log (2000371 / 2000000) = -Real.log (2000000 / 2000371) := by
    rw [show ((2000371 / 2000000) : ℝ) = ((2000000 / 2000371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4929_neg : (185517 / 1000000000) ≤ -Real.log (1999629 / 2000000) ∧
    -Real.log (1999629 / 2000000) ≤ (92759 / 500000000) := by
  have h := checkLog_sound (w := (371 / 3999629)) (n := 12)
    (lo := (185517 / 1000000000)) (hi := (92759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999629) = 1/(1999629 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4929 : Bounds (-92759 / 500000000) (-185517 / 1000000000) (Real.log (1999629 / 2000000)) := by
  have h := reflection_log_4929_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4930_neg : (44549099 / 500000000) ≤ -Real.log (250000 / 273297) ∧
    -Real.log (250000 / 273297) ≤ (89098199 / 1000000000) := by
  have h := checkLog_sound (w := (23297 / 523297)) (n := 12)
    (lo := (44549099 / 500000000)) (hi := (89098199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273297 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273297 / 250000) = 1/(250000 / 273297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4930 : Bounds (44549099 / 500000000) (89098199 / 1000000000) (Real.log (273297 / 250000)) := by
  have h := reflection_log_4930_neg
  have he : Real.log (273297 / 250000) = -Real.log (250000 / 273297) := by
    rw [show ((273297 / 250000) : ℝ) = ((250000 / 273297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4931_neg : (97820127 / 1000000000) ≤ -Real.log (226703 / 250000) ∧
    -Real.log (226703 / 250000) ≤ (3056879 / 31250000) := by
  have h := checkLog_sound (w := (23297 / 476703)) (n := 12)
    (lo := (97820127 / 1000000000)) (hi := (3056879 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226703) = 1/(226703 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4931 : Bounds (-3056879 / 31250000) (-97820127 / 1000000000) (Real.log (226703 / 250000)) := by
  have h := reflection_log_4931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4932_neg : (89314057 / 1000000000) ≤ -Real.log (62500 / 68339) ∧
    -Real.log (62500 / 68339) ≤ (44657029 / 500000000) := by
  have h := checkLog_sound (w := (5839 / 130839)) (n := 12)
    (lo := (89314057 / 1000000000)) (hi := (44657029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68339 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68339 / 62500) = 1/(62500 / 68339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4932 : Bounds (89314057 / 1000000000) (44657029 / 500000000) (Real.log (68339 / 62500)) := by
  have h := reflection_log_4932_neg
  have he : Real.log (68339 / 62500) = -Real.log (62500 / 68339) := by
    rw [show ((68339 / 62500) : ℝ) = ((62500 / 68339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4933_neg : (98080413 / 1000000000) ≤ -Real.log (56661 / 62500) ∧
    -Real.log (56661 / 62500) ≤ (49040207 / 500000000) := by
  have h := checkLog_sound (w := (5839 / 119161)) (n := 12)
    (lo := (98080413 / 1000000000)) (hi := (49040207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56661) = 1/(56661 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4933 : Bounds (-49040207 / 500000000) (-98080413 / 1000000000) (Real.log (56661 / 62500)) := by
  have h := reflection_log_4933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4934_neg : (2191589 / 250000000) ≤ -Real.log (3872156079 / 3906250000) ∧
    -Real.log (3872156079 / 3906250000) ≤ (8766357 / 1000000000) := by
  have h := checkLog_sound (w := (34093921 / 7778406079)) (n := 12)
    (lo := (2191589 / 250000000)) (hi := (8766357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3872156079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3872156079) = 1/(3872156079 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4934 : Bounds (-8766357 / 1000000000) (-2191589 / 250000000) (Real.log (3872156079 / 3906250000)) := by
  have h := reflection_log_4934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4935_neg : (8721929 / 1000000000) ≤ -Real.log (61957249791 / 62500000000) ∧
    -Real.log (61957249791 / 62500000000) ≤ (872193 / 100000000) := by
  have h := checkLog_sound (w := (542750209 / 124457249791)) (n := 12)
    (lo := (8721929 / 1000000000)) (hi := (872193 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61957249791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61957249791) = 1/(61957249791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4935 : Bounds (-872193 / 100000000) (-8721929 / 1000000000) (Real.log (61957249791 / 62500000000)) := by
  have h := reflection_log_4935_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4936_neg : (7476733 / 40000000) ≤ -Real.log (250000000000 / 301382204911) ∧
    -Real.log (250000000000 / 301382204911) ≤ (93459163 / 500000000) := by
  have h := checkLog_sound (w := (51382204911 / 551382204911)) (n := 12)
    (lo := (7476733 / 40000000)) (hi := (93459163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301382204911 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301382204911 / 250000000000) = 1/(250000000000 / 301382204911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4936 : Bounds (7476733 / 40000000) (93459163 / 500000000) (Real.log (301382204911 / 250000000000)) := by
  have h := reflection_log_4936_neg
  have he : Real.log (301382204911 / 250000000000) = -Real.log (250000000000 / 301382204911) := by
    rw [show ((301382204911 / 250000000000) : ℝ) = ((250000000000 / 301382204911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4937_neg : (18739447 / 100000000) ≤ -Real.log (500000000000 / 603051481619) ∧
    -Real.log (500000000000 / 603051481619) ≤ (187394471 / 1000000000) := by
  have h := checkLog_sound (w := (103051481619 / 1103051481619)) (n := 12)
    (lo := (18739447 / 100000000)) (hi := (187394471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603051481619 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603051481619 / 500000000000) = 1/(500000000000 / 603051481619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4937 : Bounds (18739447 / 100000000) (187394471 / 1000000000) (Real.log (603051481619 / 500000000000)) := by
  have h := reflection_log_4937_neg
  have he : Real.log (603051481619 / 500000000000) = -Real.log (500000000000 / 603051481619) := by
    rw [show ((603051481619 / 500000000000) : ℝ) = ((500000000000 / 603051481619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4938_neg : (187569177 / 500000000) ≤ -Real.log (250000000000 / 363798183157) ∧
    -Real.log (250000000000 / 363798183157) ≤ (75027671 / 200000000) := by
  have h := checkLog_sound (w := (113798183157 / 613798183157)) (n := 12)
    (lo := (187569177 / 500000000)) (hi := (75027671 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363798183157 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363798183157 / 250000000000) = 1/(250000000000 / 363798183157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4938 : Bounds (187569177 / 500000000) (75027671 / 200000000) (Real.log (363798183157 / 250000000000)) := by
  have h := reflection_log_4938_neg
  have he : Real.log (363798183157 / 250000000000) = -Real.log (250000000000 / 363798183157) := by
    rw [show ((363798183157 / 250000000000) : ℝ) = ((250000000000 / 363798183157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4939_neg : (375345477 / 1000000000) ≤ -Real.log (500000000000 / 727747084101) ∧
    -Real.log (500000000000 / 727747084101) ≤ (187672739 / 500000000) := by
  have h := checkLog_sound (w := (227747084101 / 1227747084101)) (n := 12)
    (lo := (375345477 / 1000000000)) (hi := (187672739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727747084101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727747084101 / 500000000000) = 1/(500000000000 / 727747084101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4939 : Bounds (375345477 / 1000000000) (187672739 / 500000000) (Real.log (727747084101 / 500000000000)) := by
  have h := reflection_log_4939_neg
  have he : Real.log (727747084101 / 500000000000) = -Real.log (500000000000 / 727747084101) := by
    rw [show ((727747084101 / 500000000000) : ℝ) = ((500000000000 / 727747084101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4940_neg : (6809959 / 40000000) ≤ -Real.log (625 / 741) ∧
    -Real.log (625 / 741) ≤ (10640561 / 62500000) := by
  have h := checkLog_sound (w := (58 / 683)) (n := 12)
    (lo := (6809959 / 40000000)) (hi := (10640561 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741 / 625) = 1/(625 / 741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4940 : Bounds (6809959 / 40000000) (10640561 / 62500000) (Real.log (741 / 625)) := by
  have h := reflection_log_4940_neg
  have he : Real.log (741 / 625) = -Real.log (625 / 741) := by
    rw [show ((741 / 625) : ℝ) = ((625 / 741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4941_neg : (205303633 / 1000000000) ≤ -Real.log (509 / 625) ∧
    -Real.log (509 / 625) ≤ (102651817 / 500000000) := by
  have h := checkLog_sound (w := (58 / 567)) (n := 12)
    (lo := (205303633 / 1000000000)) (hi := (102651817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 509) = 1/(509 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4941 : Bounds (-102651817 / 500000000) (-205303633 / 1000000000) (Real.log (509 / 625)) := by
  have h := reflection_log_4941_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4942_neg : (92791 / 500000000) ≤ -Real.log (156250 / 156279) ∧
    -Real.log (156250 / 156279) ≤ (185583 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 312529)) (n := 12)
    (lo := (92791 / 500000000)) (hi := (185583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156279 / 156250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156279 / 156250) = 1/(156250 / 156279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4942 : Bounds (92791 / 500000000) (185583 / 1000000000) (Real.log (156279 / 156250)) := by
  have h := reflection_log_4942_neg
  have he : Real.log (156279 / 156250) = -Real.log (156250 / 156279) := by
    rw [show ((156279 / 156250) : ℝ) = ((156250 / 156279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4943_neg : (185617 / 1000000000) ≤ -Real.log (156221 / 156250) ∧
    -Real.log (156221 / 156250) ≤ (92809 / 500000000) := by
  have h := checkLog_sound (w := (29 / 312471)) (n := 12)
    (lo := (185617 / 1000000000)) (hi := (92809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250 / 156221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250 / 156221) = 1/(156221 / 156250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4943 : Bounds (-92809 / 500000000) (-185617 / 1000000000) (Real.log (156221 / 156250)) := by
  have h := reflection_log_4943_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4944_neg : (89144849 / 1000000000) ≤ -Real.log (1000000 / 1093239) ∧
    -Real.log (1000000 / 1093239) ≤ (1782897 / 20000000) := by
  have h := checkLog_sound (w := (93239 / 2093239)) (n := 12)
    (lo := (89144849 / 1000000000)) (hi := (1782897 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093239 / 1000000) = 1/(1000000 / 1093239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4944 : Bounds (89144849 / 1000000000) (1782897 / 20000000) (Real.log (1093239 / 1000000)) := by
  have h := reflection_log_4944_neg
  have he : Real.log (1093239 / 1000000) = -Real.log (1000000 / 1093239) := by
    rw [show ((1093239 / 1000000) : ℝ) = ((1000000 / 1093239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4945_neg : (97876369 / 1000000000) ≤ -Real.log (906761 / 1000000) ∧
    -Real.log (906761 / 1000000) ≤ (9787637 / 100000000) := by
  have h := checkLog_sound (w := (93239 / 1906761)) (n := 12)
    (lo := (97876369 / 1000000000)) (hi := (9787637 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906761) = 1/(906761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4945 : Bounds (-9787637 / 100000000) (-97876369 / 1000000000) (Real.log (906761 / 1000000)) := by
  have h := reflection_log_4945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4946_neg : (44680349 / 500000000) ≤ -Real.log (40000 / 43739) ∧
    -Real.log (40000 / 43739) ≤ (89360699 / 1000000000) := by
  have h := checkLog_sound (w := (3739 / 83739)) (n := 12)
    (lo := (44680349 / 500000000)) (hi := (89360699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43739 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43739 / 40000) = 1/(40000 / 43739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4946 : Bounds (44680349 / 500000000) (89360699 / 1000000000) (Real.log (43739 / 40000)) := by
  have h := reflection_log_4946_neg
  have he : Real.log (43739 / 40000) = -Real.log (40000 / 43739) := by
    rw [show ((43739 / 40000) : ℝ) = ((40000 / 43739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4947_neg : (9813667 / 100000000) ≤ -Real.log (36261 / 40000) ∧
    -Real.log (36261 / 40000) ≤ (98136671 / 1000000000) := by
  have h := checkLog_sound (w := (3739 / 76261)) (n := 12)
    (lo := (9813667 / 100000000)) (hi := (98136671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36261) = 1/(36261 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4947 : Bounds (-98136671 / 1000000000) (-9813667 / 100000000) (Real.log (36261 / 40000)) := by
  have h := reflection_log_4947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4948_neg : (2193993 / 250000000) ≤ -Real.log (1586019879 / 1600000000) ∧
    -Real.log (1586019879 / 1600000000) ≤ (8775973 / 1000000000) := by
  have h := checkLog_sound (w := (13980121 / 3186019879)) (n := 12)
    (lo := (2193993 / 250000000)) (hi := (8775973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1586019879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1586019879) = 1/(1586019879 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4948 : Bounds (-8775973 / 1000000000) (-2193993 / 250000000) (Real.log (1586019879 / 1600000000)) := by
  have h := reflection_log_4948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4949_neg : (13643 / 1562500) ≤ -Real.log (991306488879 / 1000000000000) ∧
    -Real.log (991306488879 / 1000000000000) ≤ (8731521 / 1000000000) := by
  have h := checkLog_sound (w := (8693511121 / 1991306488879)) (n := 12)
    (lo := (13643 / 1562500)) (hi := (8731521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991306488879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991306488879) = 1/(991306488879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4949 : Bounds (-8731521 / 1000000000) (-13643 / 1562500) (Real.log (991306488879 / 1000000000000)) := by
  have h := reflection_log_4949_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4950_neg : (187021219 / 1000000000) ≤ -Real.log (500000000000 / 602826433867) ∧
    -Real.log (500000000000 / 602826433867) ≤ (9351061 / 50000000) := by
  have h := checkLog_sound (w := (102826433867 / 1102826433867)) (n := 12)
    (lo := (187021219 / 1000000000)) (hi := (9351061 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602826433867 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602826433867 / 500000000000) = 1/(500000000000 / 602826433867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4950 : Bounds (187021219 / 1000000000) (9351061 / 50000000) (Real.log (602826433867 / 500000000000)) := by
  have h := reflection_log_4950_neg
  have he : Real.log (602826433867 / 500000000000) = -Real.log (500000000000 / 602826433867) := by
    rw [show ((602826433867 / 500000000000) : ℝ) = ((500000000000 / 602826433867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4951_neg : (187497369 / 1000000000) ≤ -Real.log (500000000000 / 603113537961) ∧
    -Real.log (500000000000 / 603113537961) ≤ (18749737 / 100000000) := by
  have h := checkLog_sound (w := (103113537961 / 1103113537961)) (n := 12)
    (lo := (187497369 / 1000000000)) (hi := (18749737 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603113537961 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603113537961 / 500000000000) = 1/(500000000000 / 603113537961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4951 : Bounds (187497369 / 1000000000) (18749737 / 100000000) (Real.log (603113537961 / 500000000000)) := by
  have h := reflection_log_4951_neg
  have he : Real.log (603113537961 / 500000000000) = -Real.log (500000000000 / 603113537961) := by
    rw [show ((603113537961 / 500000000000) : ℝ) = ((500000000000 / 603113537961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4952_neg : (375345477 / 1000000000) ≤ -Real.log (5000000000 / 7277470841) ∧
    -Real.log (5000000000 / 7277470841) ≤ (187672739 / 500000000) := by
  have h := checkLog_sound (w := (2277470841 / 12277470841)) (n := 12)
    (lo := (375345477 / 1000000000)) (hi := (187672739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7277470841 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7277470841 / 5000000000) = 1/(5000000000 / 7277470841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4952 : Bounds (375345477 / 1000000000) (187672739 / 500000000) (Real.log (7277470841 / 5000000000)) := by
  have h := reflection_log_4952_neg
  have he : Real.log (7277470841 / 5000000000) = -Real.log (5000000000 / 7277470841) := by
    rw [show ((7277470841 / 5000000000) : ℝ) = ((5000000000 / 7277470841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4953_neg : (11736019 / 31250000) ≤ -Real.log (5000000000 / 7278978389) ∧
    -Real.log (5000000000 / 7278978389) ≤ (375552609 / 1000000000) := by
  have h := checkLog_sound (w := (2278978389 / 12278978389)) (n := 12)
    (lo := (11736019 / 31250000)) (hi := (375552609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7278978389 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7278978389 / 5000000000) = 1/(5000000000 / 7278978389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4953 : Bounds (11736019 / 31250000) (375552609 / 1000000000) (Real.log (7278978389 / 5000000000)) := by
  have h := reflection_log_4953_neg
  have he : Real.log (7278978389 / 5000000000) = -Real.log (5000000000 / 7278978389) := by
    rw [show ((7278978389 / 5000000000) : ℝ) = ((5000000000 / 7278978389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4954_neg : (170333317 / 1000000000) ≤ -Real.log (10000 / 11857) ∧
    -Real.log (10000 / 11857) ≤ (85166659 / 500000000) := by
  have h := checkLog_sound (w := (1857 / 21857)) (n := 12)
    (lo := (170333317 / 1000000000)) (hi := (85166659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11857 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11857 / 10000) = 1/(10000 / 11857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4954 : Bounds (170333317 / 1000000000) (85166659 / 500000000) (Real.log (11857 / 10000)) := by
  have h := reflection_log_4954_neg
  have he : Real.log (11857 / 10000) = -Real.log (10000 / 11857) := by
    rw [show ((11857 / 10000) : ℝ) = ((10000 / 11857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4955_neg : (20542643 / 100000000) ≤ -Real.log (8143 / 10000) ∧
    -Real.log (8143 / 10000) ≤ (205426431 / 1000000000) := by
  have h := checkLog_sound (w := (1857 / 18143)) (n := 12)
    (lo := (20542643 / 100000000)) (hi := (205426431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8143) = 1/(8143 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4955 : Bounds (-205426431 / 1000000000) (-20542643 / 100000000) (Real.log (8143 / 10000)) := by
  have h := reflection_log_4955_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4956_neg : (92841 / 500000000) ≤ -Real.log (10000000 / 10001857) ∧
    -Real.log (10000000 / 10001857) ≤ (185683 / 1000000000) := by
  have h := checkLog_sound (w := (1857 / 20001857)) (n := 12)
    (lo := (92841 / 500000000)) (hi := (185683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001857 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001857 / 10000000) = 1/(10000000 / 10001857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4956 : Bounds (92841 / 500000000) (185683 / 1000000000) (Real.log (10001857 / 10000000)) := by
  have h := reflection_log_4956_neg
  have he : Real.log (10001857 / 10000000) = -Real.log (10000000 / 10001857) := by
    rw [show ((10001857 / 10000000) : ℝ) = ((10000000 / 10001857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4957_neg : (185717 / 1000000000) ≤ -Real.log (9998143 / 10000000) ∧
    -Real.log (9998143 / 10000000) ≤ (92859 / 500000000) := by
  have h := checkLog_sound (w := (1857 / 19998143)) (n := 12)
    (lo := (185717 / 1000000000)) (hi := (92859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998143) = 1/(9998143 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4957 : Bounds (-92859 / 500000000) (-185717 / 1000000000) (Real.log (9998143 / 10000000)) := by
  have h := reflection_log_4957_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4958_neg : (44595749 / 500000000) ≤ -Real.log (100000 / 109329) ∧
    -Real.log (100000 / 109329) ≤ (89191499 / 1000000000) := by
  have h := checkLog_sound (w := (9329 / 209329)) (n := 12)
    (lo := (44595749 / 500000000)) (hi := (89191499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109329 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109329 / 100000) = 1/(100000 / 109329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4958 : Bounds (44595749 / 500000000) (89191499 / 1000000000) (Real.log (109329 / 100000)) := by
  have h := reflection_log_4958_neg
  have he : Real.log (109329 / 100000) = -Real.log (100000 / 109329) := by
    rw [show ((109329 / 100000) : ℝ) = ((100000 / 109329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4959_neg : (19586523 / 200000000) ≤ -Real.log (90671 / 100000) ∧
    -Real.log (90671 / 100000) ≤ (12241577 / 125000000) := by
  have h := checkLog_sound (w := (9329 / 190671)) (n := 12)
    (lo := (19586523 / 200000000)) (hi := (12241577 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90671) = 1/(90671 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4959 : Bounds (-12241577 / 125000000) (-19586523 / 200000000) (Real.log (90671 / 100000)) := by
  have h := reflection_log_4959_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4960_neg : (89407337 / 1000000000) ≤ -Real.log (500000 / 546763) ∧
    -Real.log (500000 / 546763) ≤ (44703669 / 500000000) := by
  have h := checkLog_sound (w := (46763 / 1046763)) (n := 12)
    (lo := (89407337 / 1000000000)) (hi := (44703669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546763 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546763 / 500000) = 1/(500000 / 546763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4960 : Bounds (89407337 / 1000000000) (44703669 / 500000000) (Real.log (546763 / 500000)) := by
  have h := reflection_log_4960_neg
  have he : Real.log (546763 / 500000) = -Real.log (500000 / 546763) := by
    rw [show ((546763 / 500000) : ℝ) = ((500000 / 546763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4961_neg : (9819293 / 100000000) ≤ -Real.log (453237 / 500000) ∧
    -Real.log (453237 / 500000) ≤ (98192931 / 1000000000) := by
  have h := checkLog_sound (w := (46763 / 953237)) (n := 12)
    (lo := (9819293 / 100000000)) (hi := (98192931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453237) = 1/(453237 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4961 : Bounds (-98192931 / 1000000000) (-9819293 / 100000000) (Real.log (453237 / 500000)) := by
  have h := reflection_log_4961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4962_neg : (8785593 / 1000000000) ≤ -Real.log (247813221831 / 250000000000) ∧
    -Real.log (247813221831 / 250000000000) ≤ (4392797 / 500000000) := by
  have h := checkLog_sound (w := (2186778169 / 497813221831)) (n := 12)
    (lo := (8785593 / 1000000000)) (hi := (4392797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247813221831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247813221831) = 1/(247813221831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4962 : Bounds (-4392797 / 500000000) (-8785593 / 1000000000) (Real.log (247813221831 / 250000000000)) := by
  have h := reflection_log_4962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4963_neg : (2185279 / 250000000) ≤ -Real.log (9912969759 / 10000000000) ∧
    -Real.log (9912969759 / 10000000000) ≤ (8741117 / 1000000000) := by
  have h := checkLog_sound (w := (87030241 / 19912969759)) (n := 12)
    (lo := (2185279 / 250000000)) (hi := (8741117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9912969759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9912969759) = 1/(9912969759 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4963 : Bounds (-8741117 / 1000000000) (-2185279 / 250000000) (Real.log (9912969759 / 10000000000)) := by
  have h := reflection_log_4963_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4964_neg : (93562057 / 500000000) ≤ -Real.log (500000000000 / 602888464889) ∧
    -Real.log (500000000000 / 602888464889) ≤ (37424823 / 200000000) := by
  have h := checkLog_sound (w := (102888464889 / 1102888464889)) (n := 12)
    (lo := (93562057 / 500000000)) (hi := (37424823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602888464889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602888464889 / 500000000000) = 1/(500000000000 / 602888464889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4964 : Bounds (93562057 / 500000000) (37424823 / 200000000) (Real.log (602888464889 / 500000000000)) := by
  have h := reflection_log_4964_neg
  have he : Real.log (602888464889 / 500000000000) = -Real.log (500000000000 / 602888464889) := by
    rw [show ((602888464889 / 500000000000) : ℝ) = ((500000000000 / 602888464889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4965_neg : (46900067 / 250000000) ≤ -Real.log (250000000000 / 301587800643) ∧
    -Real.log (250000000000 / 301587800643) ≤ (187600269 / 1000000000) := by
  have h := checkLog_sound (w := (51587800643 / 551587800643)) (n := 12)
    (lo := (46900067 / 250000000)) (hi := (187600269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301587800643 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301587800643 / 250000000000) = 1/(250000000000 / 301587800643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4965 : Bounds (46900067 / 250000000) (187600269 / 1000000000) (Real.log (301587800643 / 250000000000)) := by
  have h := reflection_log_4965_neg
  have he : Real.log (301587800643 / 250000000000) = -Real.log (250000000000 / 301587800643) := by
    rw [show ((301587800643 / 250000000000) : ℝ) = ((250000000000 / 301587800643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4966_neg : (11736019 / 31250000) ≤ -Real.log (500000000000 / 727897838899) ∧
    -Real.log (500000000000 / 727897838899) ≤ (375552609 / 1000000000) := by
  have h := checkLog_sound (w := (227897838899 / 1227897838899)) (n := 12)
    (lo := (11736019 / 31250000)) (hi := (375552609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727897838899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727897838899 / 500000000000) = 1/(500000000000 / 727897838899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4966 : Bounds (11736019 / 31250000) (375552609 / 1000000000) (Real.log (727897838899 / 500000000000)) := by
  have h := reflection_log_4966_neg
  have he : Real.log (727897838899 / 500000000000) = -Real.log (500000000000 / 727897838899) := by
    rw [show ((727897838899 / 500000000000) : ℝ) = ((500000000000 / 727897838899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4967_neg : (375759747 / 1000000000) ≤ -Real.log (250000000000 / 364024315363) ∧
    -Real.log (250000000000 / 364024315363) ≤ (93939937 / 250000000) := by
  have h := checkLog_sound (w := (114024315363 / 614024315363)) (n := 12)
    (lo := (375759747 / 1000000000)) (hi := (93939937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364024315363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364024315363 / 250000000000) = 1/(250000000000 / 364024315363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4967 : Bounds (375759747 / 1000000000) (93939937 / 250000000) (Real.log (364024315363 / 250000000000)) := by
  have h := reflection_log_4967_neg
  have he : Real.log (364024315363 / 250000000000) = -Real.log (250000000000 / 364024315363) := by
    rw [show ((364024315363 / 250000000000) : ℝ) = ((250000000000 / 364024315363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4968_neg : (42604413 / 250000000) ≤ -Real.log (5000 / 5929) ∧
    -Real.log (5000 / 5929) ≤ (170417653 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 10929)) (n := 12)
    (lo := (42604413 / 250000000)) (hi := (170417653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5929 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5929 / 5000) = 1/(5000 / 5929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4968 : Bounds (42604413 / 250000000) (170417653 / 1000000000) (Real.log (5929 / 5000)) := by
  have h := reflection_log_4968_neg
  have he : Real.log (5929 / 5000) = -Real.log (5000 / 5929) := by
    rw [show ((5929 / 5000) : ℝ) = ((5000 / 5929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4969_neg : (102774621 / 500000000) ≤ -Real.log (4071 / 5000) ∧
    -Real.log (4071 / 5000) ≤ (205549243 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 9071)) (n := 12)
    (lo := (102774621 / 500000000)) (hi := (205549243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4071) = 1/(4071 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4969 : Bounds (-205549243 / 1000000000) (-102774621 / 500000000) (Real.log (4071 / 5000)) := by
  have h := reflection_log_4969_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4970_neg : (92891 / 500000000) ≤ -Real.log (5000000 / 5000929) ∧
    -Real.log (5000000 / 5000929) ≤ (185783 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 10000929)) (n := 12)
    (lo := (92891 / 500000000)) (hi := (185783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000929 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000929 / 5000000) = 1/(5000000 / 5000929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4970 : Bounds (92891 / 500000000) (185783 / 1000000000) (Real.log (5000929 / 5000000)) := by
  have h := reflection_log_4970_neg
  have he : Real.log (5000929 / 5000000) = -Real.log (5000000 / 5000929) := by
    rw [show ((5000929 / 5000000) : ℝ) = ((5000000 / 5000929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4971_neg : (185817 / 1000000000) ≤ -Real.log (4999071 / 5000000) ∧
    -Real.log (4999071 / 5000000) ≤ (92909 / 500000000) := by
  have h := checkLog_sound (w := (929 / 9999071)) (n := 12)
    (lo := (185817 / 1000000000)) (hi := (92909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999071) = 1/(4999071 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4971 : Bounds (-92909 / 500000000) (-185817 / 1000000000) (Real.log (4999071 / 5000000)) := by
  have h := reflection_log_4971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4972_neg : (17847629 / 200000000) ≤ -Real.log (1000000 / 1093341) ∧
    -Real.log (1000000 / 1093341) ≤ (44619073 / 500000000) := by
  have h := checkLog_sound (w := (93341 / 2093341)) (n := 12)
    (lo := (17847629 / 200000000)) (hi := (44619073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093341 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093341 / 1000000) = 1/(1000000 / 1093341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4972 : Bounds (17847629 / 200000000) (44619073 / 500000000) (Real.log (1093341 / 1000000)) := by
  have h := reflection_log_4972_neg
  have he : Real.log (1093341 / 1000000) = -Real.log (1000000 / 1093341) := by
    rw [show ((1093341 / 1000000) : ℝ) = ((1000000 / 1093341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4973_neg : (382769 / 3906250) ≤ -Real.log (906659 / 1000000) ∧
    -Real.log (906659 / 1000000) ≤ (19597773 / 200000000) := by
  have h := checkLog_sound (w := (93341 / 1906659)) (n := 12)
    (lo := (382769 / 3906250)) (hi := (19597773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906659) = 1/(906659 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4973 : Bounds (-19597773 / 200000000) (-382769 / 3906250) (Real.log (906659 / 1000000)) := by
  have h := reflection_log_4973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4974_neg : (44726987 / 500000000) ≤ -Real.log (1000000 / 1093577) ∧
    -Real.log (1000000 / 1093577) ≤ (3578159 / 40000000) := by
  have h := checkLog_sound (w := (93577 / 2093577)) (n := 12)
    (lo := (44726987 / 500000000)) (hi := (3578159 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093577 / 1000000) = 1/(1000000 / 1093577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4974 : Bounds (44726987 / 500000000) (3578159 / 40000000) (Real.log (1093577 / 1000000)) := by
  have h := reflection_log_4974_neg
  have he : Real.log (1093577 / 1000000) = -Real.log (1000000 / 1093577) := by
    rw [show ((1093577 / 1000000) : ℝ) = ((1000000 / 1093577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4975_neg : (49124597 / 500000000) ≤ -Real.log (906423 / 1000000) ∧
    -Real.log (906423 / 1000000) ≤ (19649839 / 200000000) := by
  have h := checkLog_sound (w := (93577 / 1906423)) (n := 12)
    (lo := (49124597 / 500000000)) (hi := (19649839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906423) = 1/(906423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4975 : Bounds (-19649839 / 200000000) (-49124597 / 500000000) (Real.log (906423 / 1000000)) := by
  have h := reflection_log_4975_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4976_neg : (8795219 / 1000000000) ≤ -Real.log (991243345071 / 1000000000000) ∧
    -Real.log (991243345071 / 1000000000000) ≤ (439761 / 50000000) := by
  have h := checkLog_sound (w := (8756654929 / 1991243345071)) (n := 12)
    (lo := (8795219 / 1000000000)) (hi := (439761 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991243345071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991243345071) = 1/(991243345071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4976 : Bounds (-439761 / 50000000) (-8795219 / 1000000000) (Real.log (991243345071 / 1000000000000)) := by
  have h := reflection_log_4976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4977_neg : (4375359 / 500000000) ≤ -Real.log (991287457719 / 1000000000000) ∧
    -Real.log (991287457719 / 1000000000000) ≤ (8750719 / 1000000000) := by
  have h := checkLog_sound (w := (8712542281 / 1991287457719)) (n := 12)
    (lo := (4375359 / 500000000)) (hi := (8750719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991287457719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991287457719) = 1/(991287457719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4977 : Bounds (-8750719 / 1000000000) (-4375359 / 500000000) (Real.log (991287457719 / 1000000000000)) := by
  have h := reflection_log_4977_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4978_neg : (18722701 / 100000000) ≤ -Real.log (50000000000 / 60295050289) ∧
    -Real.log (50000000000 / 60295050289) ≤ (187227011 / 1000000000) := by
  have h := checkLog_sound (w := (10295050289 / 110295050289)) (n := 12)
    (lo := (18722701 / 100000000)) (hi := (187227011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60295050289 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60295050289 / 50000000000) = 1/(50000000000 / 60295050289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4978 : Bounds (18722701 / 100000000) (187227011 / 1000000000) (Real.log (60295050289 / 50000000000)) := by
  have h := reflection_log_4978_neg
  have he : Real.log (60295050289 / 50000000000) = -Real.log (50000000000 / 60295050289) := by
    rw [show ((60295050289 / 50000000000) : ℝ) = ((50000000000 / 60295050289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4979_neg : (187703169 / 1000000000) ≤ -Real.log (100000000000 / 120647534319) ∧
    -Real.log (100000000000 / 120647534319) ≤ (18770317 / 100000000) := by
  have h := checkLog_sound (w := (20647534319 / 220647534319)) (n := 12)
    (lo := (187703169 / 1000000000)) (hi := (18770317 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120647534319 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120647534319 / 100000000000) = 1/(100000000000 / 120647534319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4979 : Bounds (187703169 / 1000000000) (18770317 / 100000000) (Real.log (120647534319 / 100000000000)) := by
  have h := reflection_log_4979_neg
  have he : Real.log (120647534319 / 100000000000) = -Real.log (100000000000 / 120647534319) := by
    rw [show ((120647534319 / 100000000000) : ℝ) = ((100000000000 / 120647534319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4980_neg : (375759747 / 1000000000) ≤ -Real.log (20000000000 / 29121945229) ∧
    -Real.log (20000000000 / 29121945229) ≤ (93939937 / 250000000) := by
  have h := checkLog_sound (w := (9121945229 / 49121945229)) (n := 12)
    (lo := (375759747 / 1000000000)) (hi := (93939937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29121945229 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29121945229 / 20000000000) = 1/(20000000000 / 29121945229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4980 : Bounds (375759747 / 1000000000) (93939937 / 250000000) (Real.log (29121945229 / 20000000000)) := by
  have h := reflection_log_4980_neg
  have he : Real.log (29121945229 / 20000000000) = -Real.log (20000000000 / 29121945229) := by
    rw [show ((29121945229 / 20000000000) : ℝ) = ((20000000000 / 29121945229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4981_neg : (75193379 / 200000000) ≤ -Real.log (500000000000 / 728199459593) ∧
    -Real.log (500000000000 / 728199459593) ≤ (23497931 / 62500000) := by
  have h := checkLog_sound (w := (228199459593 / 1228199459593)) (n := 12)
    (lo := (75193379 / 200000000)) (hi := (23497931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728199459593 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728199459593 / 500000000000) = 1/(500000000000 / 728199459593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4981 : Bounds (75193379 / 200000000) (23497931 / 62500000) (Real.log (728199459593 / 500000000000)) := by
  have h := reflection_log_4981_neg
  have he : Real.log (728199459593 / 500000000000) = -Real.log (500000000000 / 728199459593) := by
    rw [show ((728199459593 / 500000000000) : ℝ) = ((500000000000 / 728199459593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4982_neg : (170501979 / 1000000000) ≤ -Real.log (10000 / 11859) ∧
    -Real.log (10000 / 11859) ≤ (8525099 / 50000000) := by
  have h := checkLog_sound (w := (1859 / 21859)) (n := 12)
    (lo := (170501979 / 1000000000)) (hi := (8525099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11859 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11859 / 10000) = 1/(10000 / 11859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4982 : Bounds (170501979 / 1000000000) (8525099 / 50000000) (Real.log (11859 / 10000)) := by
  have h := reflection_log_4982_neg
  have he : Real.log (11859 / 10000) = -Real.log (10000 / 11859) := by
    rw [show ((11859 / 10000) : ℝ) = ((10000 / 11859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4983_neg : (20567207 / 100000000) ≤ -Real.log (8141 / 10000) ∧
    -Real.log (8141 / 10000) ≤ (205672071 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 18141)) (n := 12)
    (lo := (20567207 / 100000000)) (hi := (205672071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8141) = 1/(8141 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4983 : Bounds (-205672071 / 1000000000) (-20567207 / 100000000) (Real.log (8141 / 10000)) := by
  have h := reflection_log_4983_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4984_neg : (92941 / 500000000) ≤ -Real.log (10000000 / 10001859) ∧
    -Real.log (10000000 / 10001859) ≤ (185883 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 20001859)) (n := 12)
    (lo := (92941 / 500000000)) (hi := (185883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001859 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001859 / 10000000) = 1/(10000000 / 10001859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4984 : Bounds (92941 / 500000000) (185883 / 1000000000) (Real.log (10001859 / 10000000)) := by
  have h := reflection_log_4984_neg
  have he : Real.log (10001859 / 10000000) = -Real.log (10000000 / 10001859) := by
    rw [show ((10001859 / 10000000) : ℝ) = ((10000000 / 10001859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4985_neg : (185917 / 1000000000) ≤ -Real.log (9998141 / 10000000) ∧
    -Real.log (9998141 / 10000000) ≤ (92959 / 500000000) := by
  have h := checkLog_sound (w := (1859 / 19998141)) (n := 12)
    (lo := (185917 / 1000000000)) (hi := (92959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998141) = 1/(9998141 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4985 : Bounds (-92959 / 500000000) (-185917 / 1000000000) (Real.log (9998141 / 10000000)) := by
  have h := reflection_log_4985_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4986_neg : (22320969 / 250000000) ≤ -Real.log (1000000 / 1093391) ∧
    -Real.log (1000000 / 1093391) ≤ (89283877 / 1000000000) := by
  have h := checkLog_sound (w := (93391 / 2093391)) (n := 12)
    (lo := (22320969 / 250000000)) (hi := (89283877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093391 / 1000000) = 1/(1000000 / 1093391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4986 : Bounds (22320969 / 250000000) (89283877 / 1000000000) (Real.log (1093391 / 1000000)) := by
  have h := reflection_log_4986_neg
  have he : Real.log (1093391 / 1000000) = -Real.log (1000000 / 1093391) := by
    rw [show ((1093391 / 1000000) : ℝ) = ((1000000 / 1093391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4987_neg : (98044013 / 1000000000) ≤ -Real.log (906609 / 1000000) ∧
    -Real.log (906609 / 1000000) ≤ (49022007 / 500000000) := by
  have h := checkLog_sound (w := (93391 / 1906609)) (n := 12)
    (lo := (98044013 / 1000000000)) (hi := (49022007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906609) = 1/(906609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4987 : Bounds (-49022007 / 500000000) (-98044013 / 1000000000) (Real.log (906609 / 1000000)) := by
  have h := reflection_log_4987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4988_neg : (89500609 / 1000000000) ≤ -Real.log (250000 / 273407) ∧
    -Real.log (250000 / 273407) ≤ (8950061 / 100000000) := by
  have h := checkLog_sound (w := (23407 / 523407)) (n := 12)
    (lo := (89500609 / 1000000000)) (hi := (8950061 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273407 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273407 / 250000) = 1/(250000 / 273407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4988 : Bounds (89500609 / 1000000000) (8950061 / 100000000) (Real.log (273407 / 250000)) := by
  have h := reflection_log_4988_neg
  have he : Real.log (273407 / 250000) = -Real.log (250000 / 273407) := by
    rw [show ((273407 / 250000) : ℝ) = ((250000 / 273407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4989_neg : (98305461 / 1000000000) ≤ -Real.log (226593 / 250000) ∧
    -Real.log (226593 / 250000) ≤ (49152731 / 500000000) := by
  have h := checkLog_sound (w := (23407 / 476593)) (n := 12)
    (lo := (98305461 / 1000000000)) (hi := (49152731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226593) = 1/(226593 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4989 : Bounds (-49152731 / 500000000) (-98305461 / 1000000000) (Real.log (226593 / 250000)) := by
  have h := reflection_log_4989_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4990_neg : (8804851 / 1000000000) ≤ -Real.log (61952112351 / 62500000000) ∧
    -Real.log (61952112351 / 62500000000) ≤ (2201213 / 250000000) := by
  have h := checkLog_sound (w := (547887649 / 124452112351)) (n := 12)
    (lo := (8804851 / 1000000000)) (hi := (2201213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61952112351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61952112351) = 1/(61952112351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4990 : Bounds (-2201213 / 250000000) (-8804851 / 1000000000) (Real.log (61952112351 / 62500000000)) := by
  have h := reflection_log_4990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4991_neg : (8760137 / 1000000000) ≤ -Real.log (991278121119 / 1000000000000) ∧
    -Real.log (991278121119 / 1000000000000) ≤ (4380069 / 500000000) := by
  have h := checkLog_sound (w := (8721878881 / 1991278121119)) (n := 12)
    (lo := (8760137 / 1000000000)) (hi := (4380069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991278121119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991278121119) = 1/(991278121119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4991 : Bounds (-4380069 / 500000000) (-8760137 / 1000000000) (Real.log (991278121119 / 1000000000000)) := by
  have h := reflection_log_4991_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0078 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4992_neg : (187327889 / 1000000000) ≤ -Real.log (100000000000 / 120602266247) ∧
    -Real.log (100000000000 / 120602266247) ≤ (18732789 / 100000000) := by
  have h := checkLog_sound (w := (20602266247 / 220602266247)) (n := 12)
    (lo := (187327889 / 1000000000)) (hi := (18732789 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120602266247 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120602266247 / 100000000000) = 1/(100000000000 / 120602266247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4992 : Bounds (187327889 / 1000000000) (18732789 / 100000000) (Real.log (120602266247 / 100000000000)) := by
  have h := reflection_log_4992_neg
  have he : Real.log (120602266247 / 100000000000) = -Real.log (100000000000 / 120602266247) := by
    rw [show ((120602266247 / 100000000000) : ℝ) = ((100000000000 / 120602266247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4993_neg : (18780607 / 100000000) ≤ -Real.log (500000000000 / 603299748889) ∧
    -Real.log (500000000000 / 603299748889) ≤ (187806071 / 1000000000) := by
  have h := checkLog_sound (w := (103299748889 / 1103299748889)) (n := 12)
    (lo := (18780607 / 100000000)) (hi := (187806071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603299748889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603299748889 / 500000000000) = 1/(500000000000 / 603299748889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4993 : Bounds (18780607 / 100000000) (187806071 / 1000000000) (Real.log (603299748889 / 500000000000)) := by
  have h := reflection_log_4993_neg
  have he : Real.log (603299748889 / 500000000000) = -Real.log (500000000000 / 603299748889) := by
    rw [show ((603299748889 / 500000000000) : ℝ) = ((500000000000 / 603299748889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4994_neg : (75193379 / 200000000) ≤ -Real.log (62500000000 / 91024932449) ∧
    -Real.log (62500000000 / 91024932449) ≤ (23497931 / 62500000) := by
  have h := checkLog_sound (w := (28524932449 / 153524932449)) (n := 12)
    (lo := (75193379 / 200000000)) (hi := (23497931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91024932449 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91024932449 / 62500000000) = 1/(62500000000 / 91024932449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4994 : Bounds (75193379 / 200000000) (23497931 / 62500000) (Real.log (91024932449 / 62500000000)) := by
  have h := reflection_log_4994_neg
  have he : Real.log (91024932449 / 62500000000) = -Real.log (62500000000 / 91024932449) := by
    rw [show ((91024932449 / 62500000000) : ℝ) = ((62500000000 / 91024932449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4995_neg : (7523481 / 20000000) ≤ -Real.log (500000000000 / 728350325513) ∧
    -Real.log (500000000000 / 728350325513) ≤ (376174051 / 1000000000) := by
  have h := checkLog_sound (w := (228350325513 / 1228350325513)) (n := 12)
    (lo := (7523481 / 20000000)) (hi := (376174051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728350325513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728350325513 / 500000000000) = 1/(500000000000 / 728350325513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4995 : Bounds (7523481 / 20000000) (376174051 / 1000000000) (Real.log (728350325513 / 500000000000)) := by
  have h := reflection_log_4995_neg
  have he : Real.log (728350325513 / 500000000000) = -Real.log (500000000000 / 728350325513) := by
    rw [show ((728350325513 / 500000000000) : ℝ) = ((500000000000 / 728350325513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4996_neg : (1705863 / 10000000) ≤ -Real.log (500 / 593) ∧
    -Real.log (500 / 593) ≤ (170586301 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 1093)) (n := 12)
    (lo := (1705863 / 10000000)) (hi := (170586301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593 / 500) = 1/(500 / 593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4996 : Bounds (1705863 / 10000000) (170586301 / 1000000000) (Real.log (593 / 500)) := by
  have h := reflection_log_4996_neg
  have he : Real.log (593 / 500) = -Real.log (500 / 593) := by
    rw [show ((593 / 500) : ℝ) = ((500 / 593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4997_neg : (6431091 / 31250000) ≤ -Real.log (407 / 500) ∧
    -Real.log (407 / 500) ≤ (205794913 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 907)) (n := 12)
    (lo := (6431091 / 31250000)) (hi := (205794913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 407) = 1/(407 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4997 : Bounds (-205794913 / 1000000000) (-6431091 / 31250000) (Real.log (407 / 500)) := by
  have h := reflection_log_4997_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4998_neg : (92991 / 500000000) ≤ -Real.log (500000 / 500093) ∧
    -Real.log (500000 / 500093) ≤ (185983 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 1000093)) (n := 12)
    (lo := (92991 / 500000000)) (hi := (185983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500093 / 500000) = 1/(500000 / 500093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4998 : Bounds (92991 / 500000000) (185983 / 1000000000) (Real.log (500093 / 500000)) := by
  have h := reflection_log_4998_neg
  have he : Real.log (500093 / 500000) = -Real.log (500000 / 500093) := by
    rw [show ((500093 / 500000) : ℝ) = ((500000 / 500093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4999_neg : (186017 / 1000000000) ≤ -Real.log (499907 / 500000) ∧
    -Real.log (499907 / 500000) ≤ (93009 / 500000000) := by
  have h := checkLog_sound (w := (93 / 999907)) (n := 12)
    (lo := (186017 / 1000000000)) (hi := (93009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499907) = 1/(499907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4999 : Bounds (-93009 / 500000000) (-186017 / 1000000000) (Real.log (499907 / 500000)) := by
  have h := reflection_log_4999_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5000_neg : (89330519 / 1000000000) ≤ -Real.log (500000 / 546721) ∧
    -Real.log (500000 / 546721) ≤ (2233263 / 25000000) := by
  have h := checkLog_sound (w := (46721 / 1046721)) (n := 12)
    (lo := (89330519 / 1000000000)) (hi := (2233263 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546721 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546721 / 500000) = 1/(500000 / 546721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5000 : Bounds (89330519 / 1000000000) (2233263 / 25000000) (Real.log (546721 / 500000)) := by
  have h := reflection_log_5000_neg
  have he : Real.log (546721 / 500000) = -Real.log (500000 / 546721) := by
    rw [show ((546721 / 500000) : ℝ) = ((500000 / 546721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5001_neg : (24525067 / 250000000) ≤ -Real.log (453279 / 500000) ∧
    -Real.log (453279 / 500000) ≤ (98100269 / 1000000000) := by
  have h := checkLog_sound (w := (46721 / 953279)) (n := 12)
    (lo := (24525067 / 250000000)) (hi := (98100269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453279) = 1/(453279 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5001 : Bounds (-98100269 / 1000000000) (-24525067 / 250000000) (Real.log (453279 / 500000)) := by
  have h := reflection_log_5001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5002_neg : (44773621 / 500000000) ≤ -Real.log (1000000 / 1093679) ∧
    -Real.log (1000000 / 1093679) ≤ (89547243 / 1000000000) := by
  have h := checkLog_sound (w := (93679 / 2093679)) (n := 12)
    (lo := (44773621 / 500000000)) (hi := (89547243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093679 / 1000000) = 1/(1000000 / 1093679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5002 : Bounds (44773621 / 500000000) (89547243 / 1000000000) (Real.log (1093679 / 1000000)) := by
  have h := reflection_log_5002_neg
  have he : Real.log (1093679 / 1000000) = -Real.log (1000000 / 1093679) := by
    rw [show ((1093679 / 1000000) : ℝ) = ((1000000 / 1093679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5003_neg : (98361731 / 1000000000) ≤ -Real.log (906321 / 1000000) ∧
    -Real.log (906321 / 1000000) ≤ (24590433 / 250000000) := by
  have h := checkLog_sound (w := (93679 / 1906321)) (n := 12)
    (lo := (98361731 / 1000000000)) (hi := (24590433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906321) = 1/(906321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5003 : Bounds (-24590433 / 250000000) (-98361731 / 1000000000) (Real.log (906321 / 1000000)) := by
  have h := reflection_log_5003_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5004_neg : (1101811 / 125000000) ≤ -Real.log (991224244959 / 1000000000000) ∧
    -Real.log (991224244959 / 1000000000000) ≤ (8814489 / 1000000000) := by
  have h := checkLog_sound (w := (8775755041 / 1991224244959)) (n := 12)
    (lo := (1101811 / 125000000)) (hi := (8814489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991224244959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991224244959) = 1/(991224244959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5004 : Bounds (-8814489 / 1000000000) (-1101811 / 125000000) (Real.log (991224244959 / 1000000000000)) := by
  have h := reflection_log_5004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5005_neg : (8769749 / 1000000000) ≤ -Real.log (247817148159 / 250000000000) ∧
    -Real.log (247817148159 / 250000000000) ≤ (35079 / 4000000) := by
  have h := checkLog_sound (w := (2182851841 / 497817148159)) (n := 12)
    (lo := (8769749 / 1000000000)) (hi := (35079 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247817148159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247817148159) = 1/(247817148159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5005 : Bounds (-35079 / 4000000) (-8769749 / 1000000000) (Real.log (247817148159 / 250000000000)) := by
  have h := reflection_log_5005_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5006_neg : (187430787 / 1000000000) ≤ -Real.log (500000000000 / 603073383059) ∧
    -Real.log (500000000000 / 603073383059) ≤ (46857697 / 250000000) := by
  have h := checkLog_sound (w := (103073383059 / 1103073383059)) (n := 12)
    (lo := (187430787 / 1000000000)) (hi := (46857697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603073383059 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603073383059 / 500000000000) = 1/(500000000000 / 603073383059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5006 : Bounds (187430787 / 1000000000) (46857697 / 250000000) (Real.log (603073383059 / 500000000000)) := by
  have h := reflection_log_5006_neg
  have he : Real.log (603073383059 / 500000000000) = -Real.log (500000000000 / 603073383059) := by
    rw [show ((603073383059 / 500000000000) : ℝ) = ((500000000000 / 603073383059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5007_neg : (187908973 / 1000000000) ≤ -Real.log (50000000000 / 60336183317) ∧
    -Real.log (50000000000 / 60336183317) ≤ (93954487 / 500000000) := by
  have h := checkLog_sound (w := (10336183317 / 110336183317)) (n := 12)
    (lo := (187908973 / 1000000000)) (hi := (93954487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60336183317 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60336183317 / 50000000000) = 1/(50000000000 / 60336183317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5007 : Bounds (187908973 / 1000000000) (93954487 / 500000000) (Real.log (60336183317 / 50000000000)) := by
  have h := reflection_log_5007_neg
  have he : Real.log (60336183317 / 50000000000) = -Real.log (50000000000 / 60336183317) := by
    rw [show ((60336183317 / 50000000000) : ℝ) = ((50000000000 / 60336183317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5008_neg : (7523481 / 20000000) ≤ -Real.log (62500000000 / 91043790689) ∧
    -Real.log (62500000000 / 91043790689) ≤ (376174051 / 1000000000) := by
  have h := checkLog_sound (w := (28543790689 / 153543790689)) (n := 12)
    (lo := (7523481 / 20000000)) (hi := (376174051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91043790689 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91043790689 / 62500000000) = 1/(62500000000 / 91043790689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5008 : Bounds (7523481 / 20000000) (376174051 / 1000000000) (Real.log (91043790689 / 62500000000)) := by
  have h := reflection_log_5008_neg
  have he : Real.log (91043790689 / 62500000000) = -Real.log (62500000000 / 91043790689) := by
    rw [show ((91043790689 / 62500000000) : ℝ) = ((62500000000 / 91043790689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5009_neg : (376381213 / 1000000000) ≤ -Real.log (250000000000 / 364250614251) ∧
    -Real.log (250000000000 / 364250614251) ≤ (188190607 / 500000000) := by
  have h := checkLog_sound (w := (114250614251 / 614250614251)) (n := 12)
    (lo := (376381213 / 1000000000)) (hi := (188190607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364250614251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364250614251 / 250000000000) = 1/(250000000000 / 364250614251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5009 : Bounds (376381213 / 1000000000) (188190607 / 500000000) (Real.log (364250614251 / 250000000000)) := by
  have h := reflection_log_5009_neg
  have he : Real.log (364250614251 / 250000000000) = -Real.log (250000000000 / 364250614251) := by
    rw [show ((364250614251 / 250000000000) : ℝ) = ((250000000000 / 364250614251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5010_neg : (85335307 / 500000000) ≤ -Real.log (10000 / 11861) ∧
    -Real.log (10000 / 11861) ≤ (34134123 / 200000000) := by
  have h := checkLog_sound (w := (1861 / 21861)) (n := 12)
    (lo := (85335307 / 500000000)) (hi := (34134123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11861 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11861 / 10000) = 1/(10000 / 11861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5010 : Bounds (85335307 / 500000000) (34134123 / 200000000) (Real.log (11861 / 10000)) := by
  have h := reflection_log_5010_neg
  have he : Real.log (11861 / 10000) = -Real.log (10000 / 11861) := by
    rw [show ((11861 / 10000) : ℝ) = ((10000 / 11861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5011_neg : (20591777 / 100000000) ≤ -Real.log (8139 / 10000) ∧
    -Real.log (8139 / 10000) ≤ (205917771 / 1000000000) := by
  have h := checkLog_sound (w := (1861 / 18139)) (n := 12)
    (lo := (20591777 / 100000000)) (hi := (205917771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8139) = 1/(8139 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5011 : Bounds (-205917771 / 1000000000) (-20591777 / 100000000) (Real.log (8139 / 10000)) := by
  have h := reflection_log_5011_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5012_neg : (93041 / 500000000) ≤ -Real.log (10000000 / 10001861) ∧
    -Real.log (10000000 / 10001861) ≤ (186083 / 1000000000) := by
  have h := checkLog_sound (w := (1861 / 20001861)) (n := 12)
    (lo := (93041 / 500000000)) (hi := (186083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001861 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001861 / 10000000) = 1/(10000000 / 10001861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5012 : Bounds (93041 / 500000000) (186083 / 1000000000) (Real.log (10001861 / 10000000)) := by
  have h := reflection_log_5012_neg
  have he : Real.log (10001861 / 10000000) = -Real.log (10000000 / 10001861) := by
    rw [show ((10001861 / 10000000) : ℝ) = ((10000000 / 10001861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5013_neg : (186117 / 1000000000) ≤ -Real.log (9998139 / 10000000) ∧
    -Real.log (9998139 / 10000000) ≤ (93059 / 500000000) := by
  have h := checkLog_sound (w := (1861 / 19998139)) (n := 12)
    (lo := (186117 / 1000000000)) (hi := (93059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998139) = 1/(9998139 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5013 : Bounds (-93059 / 500000000) (-186117 / 1000000000) (Real.log (9998139 / 10000000)) := by
  have h := reflection_log_5013_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5014_neg : (89377159 / 1000000000) ≤ -Real.log (1000000 / 1093493) ∧
    -Real.log (1000000 / 1093493) ≤ (2234429 / 25000000) := by
  have h := checkLog_sound (w := (93493 / 2093493)) (n := 12)
    (lo := (89377159 / 1000000000)) (hi := (2234429 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093493 / 1000000) = 1/(1000000 / 1093493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5014 : Bounds (89377159 / 1000000000) (2234429 / 25000000) (Real.log (1093493 / 1000000)) := by
  have h := reflection_log_5014_neg
  have he : Real.log (1093493 / 1000000) = -Real.log (1000000 / 1093493) := by
    rw [show ((1093493 / 1000000) : ℝ) = ((1000000 / 1093493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5015_neg : (49078263 / 500000000) ≤ -Real.log (906507 / 1000000) ∧
    -Real.log (906507 / 1000000) ≤ (98156527 / 1000000000) := by
  have h := checkLog_sound (w := (93493 / 1906507)) (n := 12)
    (lo := (49078263 / 500000000)) (hi := (98156527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906507) = 1/(906507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5015 : Bounds (-98156527 / 1000000000) (-49078263 / 500000000) (Real.log (906507 / 1000000)) := by
  have h := reflection_log_5015_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5016_neg : (5599617 / 62500000) ≤ -Real.log (100000 / 109373) ∧
    -Real.log (100000 / 109373) ≤ (89593873 / 1000000000) := by
  have h := checkLog_sound (w := (9373 / 209373)) (n := 12)
    (lo := (5599617 / 62500000)) (hi := (89593873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109373 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109373 / 100000) = 1/(100000 / 109373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5016 : Bounds (5599617 / 62500000) (89593873 / 1000000000) (Real.log (109373 / 100000)) := by
  have h := reflection_log_5016_neg
  have he : Real.log (109373 / 100000) = -Real.log (100000 / 109373) := by
    rw [show ((109373 / 100000) : ℝ) = ((100000 / 109373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5017_neg : (24604501 / 250000000) ≤ -Real.log (90627 / 100000) ∧
    -Real.log (90627 / 100000) ≤ (19683601 / 200000000) := by
  have h := checkLog_sound (w := (9373 / 190627)) (n := 12)
    (lo := (24604501 / 250000000)) (hi := (19683601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90627) = 1/(90627 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5017 : Bounds (-19683601 / 200000000) (-24604501 / 250000000) (Real.log (90627 / 100000)) := by
  have h := reflection_log_5017_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5018_neg : (8824131 / 1000000000) ≤ -Real.log (9912146871 / 10000000000) ∧
    -Real.log (9912146871 / 10000000000) ≤ (2206033 / 250000000) := by
  have h := checkLog_sound (w := (87853129 / 19912146871)) (n := 12)
    (lo := (8824131 / 1000000000)) (hi := (2206033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9912146871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9912146871) = 1/(9912146871 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5018 : Bounds (-2206033 / 250000000) (-8824131 / 1000000000) (Real.log (9912146871 / 10000000000)) := by
  have h := reflection_log_5018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5019_neg : (8779367 / 1000000000) ≤ -Real.log (991259058951 / 1000000000000) ∧
    -Real.log (991259058951 / 1000000000000) ≤ (1097421 / 125000000) := by
  have h := checkLog_sound (w := (8740941049 / 1991259058951)) (n := 12)
    (lo := (8779367 / 1000000000)) (hi := (1097421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991259058951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991259058951) = 1/(991259058951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5019 : Bounds (-1097421 / 125000000) (-8779367 / 1000000000) (Real.log (991259058951 / 1000000000000)) := by
  have h := reflection_log_5019_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5020_neg : (93766843 / 500000000) ≤ -Real.log (250000000000 / 301567720933) ∧
    -Real.log (250000000000 / 301567720933) ≤ (187533687 / 1000000000) := by
  have h := checkLog_sound (w := (51567720933 / 551567720933)) (n := 12)
    (lo := (93766843 / 500000000)) (hi := (187533687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301567720933 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301567720933 / 250000000000) = 1/(250000000000 / 301567720933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5020 : Bounds (93766843 / 500000000) (187533687 / 1000000000) (Real.log (301567720933 / 250000000000)) := by
  have h := reflection_log_5020_neg
  have he : Real.log (301567720933 / 250000000000) = -Real.log (250000000000 / 301567720933) := by
    rw [show ((301567720933 / 250000000000) : ℝ) = ((250000000000 / 301567720933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5021_neg : (47002969 / 250000000) ≤ -Real.log (250000000000 / 301711962219) ∧
    -Real.log (250000000000 / 301711962219) ≤ (188011877 / 1000000000) := by
  have h := checkLog_sound (w := (51711962219 / 551711962219)) (n := 12)
    (lo := (47002969 / 250000000)) (hi := (188011877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301711962219 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301711962219 / 250000000000) = 1/(250000000000 / 301711962219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5021 : Bounds (47002969 / 250000000) (188011877 / 1000000000) (Real.log (301711962219 / 250000000000)) := by
  have h := reflection_log_5021_neg
  have he : Real.log (301711962219 / 250000000000) = -Real.log (250000000000 / 301711962219) := by
    rw [show ((301711962219 / 250000000000) : ℝ) = ((250000000000 / 301711962219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5022_neg : (376381213 / 1000000000) ≤ -Real.log (500000000000 / 728501228501) ∧
    -Real.log (500000000000 / 728501228501) ≤ (188190607 / 500000000) := by
  have h := checkLog_sound (w := (228501228501 / 1228501228501)) (n := 12)
    (lo := (376381213 / 1000000000)) (hi := (188190607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728501228501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728501228501 / 500000000000) = 1/(500000000000 / 728501228501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5022 : Bounds (376381213 / 1000000000) (188190607 / 500000000) (Real.log (728501228501 / 500000000000)) := by
  have h := reflection_log_5022_neg
  have he : Real.log (728501228501 / 500000000000) = -Real.log (500000000000 / 728501228501) := by
    rw [show ((728501228501 / 500000000000) : ℝ) = ((500000000000 / 728501228501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5023_neg : (11768387 / 31250000) ≤ -Real.log (125000000000 / 182163042143) ∧
    -Real.log (125000000000 / 182163042143) ≤ (75317677 / 200000000) := by
  have h := checkLog_sound (w := (57163042143 / 307163042143)) (n := 12)
    (lo := (11768387 / 31250000)) (hi := (75317677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182163042143 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182163042143 / 125000000000) = 1/(125000000000 / 182163042143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5023 : Bounds (11768387 / 31250000) (75317677 / 200000000) (Real.log (182163042143 / 125000000000)) := by
  have h := reflection_log_5023_neg
  have he : Real.log (182163042143 / 125000000000) = -Real.log (125000000000 / 182163042143) := by
    rw [show ((182163042143 / 125000000000) : ℝ) = ((125000000000 / 182163042143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5024_neg : (4268873 / 25000000) ≤ -Real.log (5000 / 5931) ∧
    -Real.log (5000 / 5931) ≤ (170754921 / 1000000000) := by
  have h := checkLog_sound (w := (931 / 10931)) (n := 12)
    (lo := (4268873 / 25000000)) (hi := (170754921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5931 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5931 / 5000) = 1/(5000 / 5931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5024 : Bounds (4268873 / 25000000) (170754921 / 1000000000) (Real.log (5931 / 5000)) := by
  have h := reflection_log_5024_neg
  have he : Real.log (5931 / 5000) = -Real.log (5000 / 5931) := by
    rw [show ((5931 / 5000) : ℝ) = ((5000 / 5931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5025_neg : (206040643 / 1000000000) ≤ -Real.log (4069 / 5000) ∧
    -Real.log (4069 / 5000) ≤ (51510161 / 250000000) := by
  have h := checkLog_sound (w := (931 / 9069)) (n := 12)
    (lo := (206040643 / 1000000000)) (hi := (51510161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4069) = 1/(4069 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5025 : Bounds (-51510161 / 250000000) (-206040643 / 1000000000) (Real.log (4069 / 5000)) := by
  have h := reflection_log_5025_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5026_neg : (93091 / 500000000) ≤ -Real.log (5000000 / 5000931) ∧
    -Real.log (5000000 / 5000931) ≤ (186183 / 1000000000) := by
  have h := checkLog_sound (w := (931 / 10000931)) (n := 12)
    (lo := (93091 / 500000000)) (hi := (186183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000931 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000931 / 5000000) = 1/(5000000 / 5000931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5026 : Bounds (93091 / 500000000) (186183 / 1000000000) (Real.log (5000931 / 5000000)) := by
  have h := reflection_log_5026_neg
  have he : Real.log (5000931 / 5000000) = -Real.log (5000000 / 5000931) := by
    rw [show ((5000931 / 5000000) : ℝ) = ((5000000 / 5000931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5027_neg : (186217 / 1000000000) ≤ -Real.log (4999069 / 5000000) ∧
    -Real.log (4999069 / 5000000) ≤ (93109 / 500000000) := by
  have h := checkLog_sound (w := (931 / 9999069)) (n := 12)
    (lo := (186217 / 1000000000)) (hi := (93109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999069) = 1/(4999069 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5027 : Bounds (-93109 / 500000000) (-186217 / 1000000000) (Real.log (4999069 / 5000000)) := by
  have h := reflection_log_5027_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5028_neg : (44711899 / 500000000) ≤ -Real.log (125000 / 136693) ∧
    -Real.log (125000 / 136693) ≤ (89423799 / 1000000000) := by
  have h := checkLog_sound (w := (11693 / 261693)) (n := 12)
    (lo := (44711899 / 500000000)) (hi := (89423799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136693 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136693 / 125000) = 1/(125000 / 136693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5028 : Bounds (44711899 / 500000000) (89423799 / 1000000000) (Real.log (136693 / 125000)) := by
  have h := reflection_log_5028_neg
  have he : Real.log (136693 / 125000) = -Real.log (125000 / 136693) := by
    rw [show ((136693 / 125000) : ℝ) = ((125000 / 136693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5029_neg : (24553197 / 250000000) ≤ -Real.log (113307 / 125000) ∧
    -Real.log (113307 / 125000) ≤ (98212789 / 1000000000) := by
  have h := checkLog_sound (w := (11693 / 238307)) (n := 12)
    (lo := (24553197 / 250000000)) (hi := (98212789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113307) = 1/(113307 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5029 : Bounds (-98212789 / 1000000000) (-24553197 / 250000000) (Real.log (113307 / 125000)) := by
  have h := reflection_log_5029_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5030_neg : (89640501 / 1000000000) ≤ -Real.log (1000000 / 1093781) ∧
    -Real.log (1000000 / 1093781) ≤ (44820251 / 500000000) := by
  have h := checkLog_sound (w := (93781 / 2093781)) (n := 12)
    (lo := (89640501 / 1000000000)) (hi := (44820251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093781 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093781 / 1000000) = 1/(1000000 / 1093781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5030 : Bounds (89640501 / 1000000000) (44820251 / 500000000) (Real.log (1093781 / 1000000)) := by
  have h := reflection_log_5030_neg
  have he : Real.log (1093781 / 1000000) = -Real.log (1000000 / 1093781) := by
    rw [show ((1093781 / 1000000) : ℝ) = ((1000000 / 1093781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5031_neg : (2461857 / 25000000) ≤ -Real.log (906219 / 1000000) ∧
    -Real.log (906219 / 1000000) ≤ (98474281 / 1000000000) := by
  have h := checkLog_sound (w := (93781 / 1906219)) (n := 12)
    (lo := (2461857 / 25000000)) (hi := (98474281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906219) = 1/(906219 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5031 : Bounds (-98474281 / 1000000000) (-2461857 / 25000000) (Real.log (906219 / 1000000)) := by
  have h := reflection_log_5031_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5032_neg : (8833779 / 1000000000) ≤ -Real.log (991205124039 / 1000000000000) ∧
    -Real.log (991205124039 / 1000000000000) ≤ (441689 / 50000000) := by
  have h := checkLog_sound (w := (8794875961 / 1991205124039)) (n := 12)
    (lo := (8833779 / 1000000000)) (hi := (441689 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991205124039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991205124039) = 1/(991205124039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5032 : Bounds (-441689 / 50000000) (-8833779 / 1000000000) (Real.log (991205124039 / 1000000000000)) := by
  have h := reflection_log_5032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5033_neg : (878899 / 100000000) ≤ -Real.log (15488273751 / 15625000000) ∧
    -Real.log (15488273751 / 15625000000) ≤ (8788991 / 1000000000) := by
  have h := checkLog_sound (w := (136726249 / 31113273751)) (n := 12)
    (lo := (878899 / 100000000)) (hi := (8788991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15488273751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15488273751) = 1/(15488273751 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5033 : Bounds (-8788991 / 1000000000) (-878899 / 100000000) (Real.log (15488273751 / 15625000000)) := by
  have h := reflection_log_5033_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5034_neg : (93818293 / 500000000) ≤ -Real.log (62500000000 / 75399688457) ∧
    -Real.log (62500000000 / 75399688457) ≤ (187636587 / 1000000000) := by
  have h := checkLog_sound (w := (12899688457 / 137899688457)) (n := 12)
    (lo := (93818293 / 500000000)) (hi := (187636587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75399688457 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75399688457 / 62500000000) = 1/(62500000000 / 75399688457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5034 : Bounds (93818293 / 500000000) (187636587 / 1000000000) (Real.log (75399688457 / 62500000000)) := by
  have h := reflection_log_5034_neg
  have he : Real.log (75399688457 / 62500000000) = -Real.log (62500000000 / 75399688457) := by
    rw [show ((75399688457 / 62500000000) : ℝ) = ((62500000000 / 75399688457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5035_neg : (188114781 / 1000000000) ≤ -Real.log (100000000000 / 120697204539) ∧
    -Real.log (100000000000 / 120697204539) ≤ (94057391 / 500000000) := by
  have h := checkLog_sound (w := (20697204539 / 220697204539)) (n := 12)
    (lo := (188114781 / 1000000000)) (hi := (94057391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120697204539 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120697204539 / 100000000000) = 1/(100000000000 / 120697204539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5035 : Bounds (188114781 / 1000000000) (94057391 / 500000000) (Real.log (120697204539 / 100000000000)) := by
  have h := reflection_log_5035_neg
  have he : Real.log (120697204539 / 100000000000) = -Real.log (100000000000 / 120697204539) := by
    rw [show ((120697204539 / 100000000000) : ℝ) = ((100000000000 / 120697204539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5036_neg : (11768387 / 31250000) ≤ -Real.log (500000000000 / 728652168571) ∧
    -Real.log (500000000000 / 728652168571) ≤ (75317677 / 200000000) := by
  have h := checkLog_sound (w := (228652168571 / 1228652168571)) (n := 12)
    (lo := (11768387 / 31250000)) (hi := (75317677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728652168571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728652168571 / 500000000000) = 1/(500000000000 / 728652168571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5036 : Bounds (11768387 / 31250000) (75317677 / 200000000) (Real.log (728652168571 / 500000000000)) := by
  have h := reflection_log_5036_neg
  have he : Real.log (728652168571 / 500000000000) = -Real.log (500000000000 / 728652168571) := by
    rw [show ((728652168571 / 500000000000) : ℝ) = ((500000000000 / 728652168571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5037_neg : (376795563 / 1000000000) ≤ -Real.log (500000000000 / 728803145737) ∧
    -Real.log (500000000000 / 728803145737) ≤ (94198891 / 250000000) := by
  have h := checkLog_sound (w := (228803145737 / 1228803145737)) (n := 12)
    (lo := (376795563 / 1000000000)) (hi := (94198891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728803145737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728803145737 / 500000000000) = 1/(500000000000 / 728803145737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5037 : Bounds (376795563 / 1000000000) (94198891 / 250000000) (Real.log (728803145737 / 500000000000)) := by
  have h := reflection_log_5037_neg
  have he : Real.log (728803145737 / 500000000000) = -Real.log (500000000000 / 728803145737) := by
    rw [show ((728803145737 / 500000000000) : ℝ) = ((500000000000 / 728803145737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5038_neg : (170839219 / 1000000000) ≤ -Real.log (10000 / 11863) ∧
    -Real.log (10000 / 11863) ≤ (8541961 / 50000000) := by
  have h := checkLog_sound (w := (1863 / 21863)) (n := 12)
    (lo := (170839219 / 1000000000)) (hi := (8541961 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11863 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11863 / 10000) = 1/(10000 / 11863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5038 : Bounds (170839219 / 1000000000) (8541961 / 50000000) (Real.log (11863 / 10000)) := by
  have h := reflection_log_5038_neg
  have he : Real.log (11863 / 10000) = -Real.log (10000 / 11863) := by
    rw [show ((11863 / 10000) : ℝ) = ((10000 / 11863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5039_neg : (206163531 / 1000000000) ≤ -Real.log (8137 / 10000) ∧
    -Real.log (8137 / 10000) ≤ (51540883 / 250000000) := by
  have h := checkLog_sound (w := (1863 / 18137)) (n := 12)
    (lo := (206163531 / 1000000000)) (hi := (51540883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8137) = 1/(8137 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5039 : Bounds (-51540883 / 250000000) (-206163531 / 1000000000) (Real.log (8137 / 10000)) := by
  have h := reflection_log_5039_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5040_neg : (93141 / 500000000) ≤ -Real.log (10000000 / 10001863) ∧
    -Real.log (10000000 / 10001863) ≤ (186283 / 1000000000) := by
  have h := checkLog_sound (w := (1863 / 20001863)) (n := 12)
    (lo := (93141 / 500000000)) (hi := (186283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001863 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001863 / 10000000) = 1/(10000000 / 10001863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5040 : Bounds (93141 / 500000000) (186283 / 1000000000) (Real.log (10001863 / 10000000)) := by
  have h := reflection_log_5040_neg
  have he : Real.log (10001863 / 10000000) = -Real.log (10000000 / 10001863) := by
    rw [show ((10001863 / 10000000) : ℝ) = ((10000000 / 10001863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5041_neg : (186317 / 1000000000) ≤ -Real.log (9998137 / 10000000) ∧
    -Real.log (9998137 / 10000000) ≤ (93159 / 500000000) := by
  have h := checkLog_sound (w := (1863 / 19998137)) (n := 12)
    (lo := (186317 / 1000000000)) (hi := (93159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998137) = 1/(9998137 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5041 : Bounds (-93159 / 500000000) (-186317 / 1000000000) (Real.log (9998137 / 10000000)) := by
  have h := reflection_log_5041_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5042_neg : (44735217 / 500000000) ≤ -Real.log (200000 / 218719) ∧
    -Real.log (200000 / 218719) ≤ (17894087 / 200000000) := by
  have h := checkLog_sound (w := (18719 / 418719)) (n := 12)
    (lo := (44735217 / 500000000)) (hi := (17894087 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218719 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218719 / 200000) = 1/(200000 / 218719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5042 : Bounds (44735217 / 500000000) (17894087 / 200000000) (Real.log (218719 / 200000)) := by
  have h := reflection_log_5042_neg
  have he : Real.log (218719 / 200000) = -Real.log (200000 / 218719) := by
    rw [show ((218719 / 200000) : ℝ) = ((200000 / 218719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5043_neg : (24567263 / 250000000) ≤ -Real.log (181281 / 200000) ∧
    -Real.log (181281 / 200000) ≤ (98269053 / 1000000000) := by
  have h := checkLog_sound (w := (18719 / 381281)) (n := 12)
    (lo := (24567263 / 250000000)) (hi := (98269053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181281) = 1/(181281 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5043 : Bounds (-98269053 / 1000000000) (-24567263 / 250000000) (Real.log (181281 / 200000)) := by
  have h := reflection_log_5043_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5044_neg : (89687127 / 1000000000) ≤ -Real.log (125000 / 136729) ∧
    -Real.log (125000 / 136729) ≤ (11210891 / 125000000) := by
  have h := checkLog_sound (w := (11729 / 261729)) (n := 12)
    (lo := (89687127 / 1000000000)) (hi := (11210891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136729 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136729 / 125000) = 1/(125000 / 136729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5044 : Bounds (89687127 / 1000000000) (11210891 / 125000000) (Real.log (136729 / 125000)) := by
  have h := reflection_log_5044_neg
  have he : Real.log (136729 / 125000) = -Real.log (125000 / 136729) := by
    rw [show ((136729 / 125000) : ℝ) = ((125000 / 136729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5045_neg : (98530559 / 1000000000) ≤ -Real.log (113271 / 125000) ∧
    -Real.log (113271 / 125000) ≤ (76977 / 781250) := by
  have h := checkLog_sound (w := (11729 / 238271)) (n := 12)
    (lo := (98530559 / 1000000000)) (hi := (76977 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113271) = 1/(113271 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5045 : Bounds (-76977 / 781250) (-98530559 / 1000000000) (Real.log (113271 / 125000)) := by
  have h := reflection_log_5045_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5046_neg : (1105429 / 125000000) ≤ -Real.log (15487430559 / 15625000000) ∧
    -Real.log (15487430559 / 15625000000) ≤ (8843433 / 1000000000) := by
  have h := checkLog_sound (w := (137569441 / 31112430559)) (n := 12)
    (lo := (1105429 / 125000000)) (hi := (8843433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15487430559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15487430559) = 1/(15487430559 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5046 : Bounds (-8843433 / 1000000000) (-1105429 / 125000000) (Real.log (15487430559 / 15625000000)) := by
  have h := reflection_log_5046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5047_neg : (4399309 / 500000000) ≤ -Real.log (39649599039 / 40000000000) ∧
    -Real.log (39649599039 / 40000000000) ≤ (8798619 / 1000000000) := by
  have h := checkLog_sound (w := (350400961 / 79649599039)) (n := 12)
    (lo := (4399309 / 500000000)) (hi := (8798619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39649599039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39649599039) = 1/(39649599039 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5047 : Bounds (-8798619 / 1000000000) (-4399309 / 500000000) (Real.log (39649599039 / 40000000000)) := by
  have h := reflection_log_5047_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5048_neg : (187739487 / 1000000000) ≤ -Real.log (50000000000 / 60325958043) ∧
    -Real.log (50000000000 / 60325958043) ≤ (5866859 / 31250000) := by
  have h := checkLog_sound (w := (10325958043 / 110325958043)) (n := 12)
    (lo := (187739487 / 1000000000)) (hi := (5866859 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60325958043 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60325958043 / 50000000000) = 1/(50000000000 / 60325958043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5048 : Bounds (187739487 / 1000000000) (5866859 / 31250000) (Real.log (60325958043 / 50000000000)) := by
  have h := reflection_log_5048_neg
  have he : Real.log (60325958043 / 50000000000) = -Real.log (50000000000 / 60325958043) := by
    rw [show ((60325958043 / 50000000000) : ℝ) = ((50000000000 / 60325958043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5049_neg : (94108843 / 500000000) ≤ -Real.log (500000000000 / 603548127941) ∧
    -Real.log (500000000000 / 603548127941) ≤ (188217687 / 1000000000) := by
  have h := checkLog_sound (w := (103548127941 / 1103548127941)) (n := 12)
    (lo := (94108843 / 500000000)) (hi := (188217687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603548127941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603548127941 / 500000000000) = 1/(500000000000 / 603548127941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5049 : Bounds (94108843 / 500000000) (188217687 / 1000000000) (Real.log (603548127941 / 500000000000)) := by
  have h := reflection_log_5049_neg
  have he : Real.log (603548127941 / 500000000000) = -Real.log (500000000000 / 603548127941) := by
    rw [show ((603548127941 / 500000000000) : ℝ) = ((500000000000 / 603548127941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5050_neg : (376795563 / 1000000000) ≤ -Real.log (62500000000 / 91100393217) ∧
    -Real.log (62500000000 / 91100393217) ≤ (94198891 / 250000000) := by
  have h := checkLog_sound (w := (28600393217 / 153600393217)) (n := 12)
    (lo := (376795563 / 1000000000)) (hi := (94198891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91100393217 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91100393217 / 62500000000) = 1/(62500000000 / 91100393217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5050 : Bounds (376795563 / 1000000000) (94198891 / 250000000) (Real.log (91100393217 / 62500000000)) := by
  have h := reflection_log_5050_neg
  have he : Real.log (91100393217 / 62500000000) = -Real.log (62500000000 / 91100393217) := by
    rw [show ((91100393217 / 62500000000) : ℝ) = ((62500000000 / 91100393217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5051_neg : (1508011 / 4000000) ≤ -Real.log (50000000000 / 72895416001) ∧
    -Real.log (50000000000 / 72895416001) ≤ (377002751 / 1000000000) := by
  have h := checkLog_sound (w := (22895416001 / 122895416001)) (n := 12)
    (lo := (1508011 / 4000000)) (hi := (377002751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72895416001 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72895416001 / 50000000000) = 1/(50000000000 / 72895416001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5051 : Bounds (1508011 / 4000000) (377002751 / 1000000000) (Real.log (72895416001 / 50000000000)) := by
  have h := reflection_log_5051_neg
  have he : Real.log (72895416001 / 50000000000) = -Real.log (50000000000 / 72895416001) := by
    rw [show ((72895416001 / 50000000000) : ℝ) = ((50000000000 / 72895416001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5052_neg : (170923511 / 1000000000) ≤ -Real.log (1250 / 1483) ∧
    -Real.log (1250 / 1483) ≤ (21365439 / 125000000) := by
  have h := checkLog_sound (w := (233 / 2733)) (n := 12)
    (lo := (170923511 / 1000000000)) (hi := (21365439 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1483 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1483 / 1250) = 1/(1250 / 1483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5052 : Bounds (170923511 / 1000000000) (21365439 / 125000000) (Real.log (1483 / 1250)) := by
  have h := reflection_log_5052_neg
  have he : Real.log (1483 / 1250) = -Real.log (1250 / 1483) := by
    rw [show ((1483 / 1250) : ℝ) = ((1250 / 1483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5053_neg : (103143217 / 500000000) ≤ -Real.log (1017 / 1250) ∧
    -Real.log (1017 / 1250) ≤ (41257287 / 200000000) := by
  have h := checkLog_sound (w := (233 / 2267)) (n := 12)
    (lo := (103143217 / 500000000)) (hi := (41257287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1017) = 1/(1017 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5053 : Bounds (-41257287 / 200000000) (-103143217 / 500000000) (Real.log (1017 / 1250)) := by
  have h := reflection_log_5053_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5054_neg : (93191 / 500000000) ≤ -Real.log (1250000 / 1250233) ∧
    -Real.log (1250000 / 1250233) ≤ (186383 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 2500233)) (n := 12)
    (lo := (93191 / 500000000)) (hi := (186383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250233 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250233 / 1250000) = 1/(1250000 / 1250233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5054 : Bounds (93191 / 500000000) (186383 / 1000000000) (Real.log (1250233 / 1250000)) := by
  have h := reflection_log_5054_neg
  have he : Real.log (1250233 / 1250000) = -Real.log (1250000 / 1250233) := by
    rw [show ((1250233 / 1250000) : ℝ) = ((1250000 / 1250233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5055_neg : (186417 / 1000000000) ≤ -Real.log (1249767 / 1250000) ∧
    -Real.log (1249767 / 1250000) ≤ (93209 / 500000000) := by
  have h := checkLog_sound (w := (233 / 2499767)) (n := 12)
    (lo := (186417 / 1000000000)) (hi := (93209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249767) = 1/(1249767 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5055 : Bounds (-93209 / 500000000) (-186417 / 1000000000) (Real.log (1249767 / 1250000)) := by
  have h := reflection_log_5055_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0079 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5056_neg : (22379267 / 250000000) ≤ -Real.log (500000 / 546823) ∧
    -Real.log (500000 / 546823) ≤ (89517069 / 1000000000) := by
  have h := checkLog_sound (w := (46823 / 1046823)) (n := 12)
    (lo := (22379267 / 250000000)) (hi := (89517069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546823 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546823 / 500000) = 1/(500000 / 546823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5056 : Bounds (22379267 / 250000000) (89517069 / 1000000000) (Real.log (546823 / 500000)) := by
  have h := reflection_log_5056_neg
  have he : Real.log (546823 / 500000) = -Real.log (500000 / 546823) := by
    rw [show ((546823 / 500000) : ℝ) = ((500000 / 546823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5057_neg : (2458133 / 25000000) ≤ -Real.log (453177 / 500000) ∧
    -Real.log (453177 / 500000) ≤ (98325321 / 1000000000) := by
  have h := checkLog_sound (w := (46823 / 953177)) (n := 12)
    (lo := (2458133 / 25000000)) (hi := (98325321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453177) = 1/(453177 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5057 : Bounds (-98325321 / 1000000000) (-2458133 / 25000000) (Real.log (453177 / 500000)) := by
  have h := reflection_log_5057_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5058_neg : (89733751 / 1000000000) ≤ -Real.log (1000000 / 1093883) ∧
    -Real.log (1000000 / 1093883) ≤ (11216719 / 125000000) := by
  have h := checkLog_sound (w := (93883 / 2093883)) (n := 12)
    (lo := (89733751 / 1000000000)) (hi := (11216719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093883 / 1000000) = 1/(1000000 / 1093883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5058 : Bounds (89733751 / 1000000000) (11216719 / 125000000) (Real.log (1093883 / 1000000)) := by
  have h := reflection_log_5058_neg
  have he : Real.log (1093883 / 1000000) = -Real.log (1000000 / 1093883) := by
    rw [show ((1093883 / 1000000) : ℝ) = ((1000000 / 1093883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5059_neg : (49293421 / 500000000) ≤ -Real.log (906117 / 1000000) ∧
    -Real.log (906117 / 1000000) ≤ (98586843 / 1000000000) := by
  have h := checkLog_sound (w := (93883 / 1906117)) (n := 12)
    (lo := (49293421 / 500000000)) (hi := (98586843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906117) = 1/(906117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5059 : Bounds (-98586843 / 1000000000) (-49293421 / 500000000) (Real.log (906117 / 1000000)) := by
  have h := reflection_log_5059_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5060_neg : (885309 / 100000000) ≤ -Real.log (991185982311 / 1000000000000) ∧
    -Real.log (991185982311 / 1000000000000) ≤ (8853091 / 1000000000) := by
  have h := checkLog_sound (w := (8814017689 / 1991185982311)) (n := 12)
    (lo := (885309 / 100000000)) (hi := (8853091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991185982311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991185982311) = 1/(991185982311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5060 : Bounds (-8853091 / 1000000000) (-885309 / 100000000) (Real.log (991185982311 / 1000000000000)) := by
  have h := reflection_log_5060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5061_neg : (2202063 / 250000000) ≤ -Real.log (247807606671 / 250000000000) ∧
    -Real.log (247807606671 / 250000000000) ≤ (8808253 / 1000000000) := by
  have h := checkLog_sound (w := (2192393329 / 497807606671)) (n := 12)
    (lo := (2202063 / 250000000)) (hi := (8808253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247807606671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247807606671) = 1/(247807606671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5061 : Bounds (-8808253 / 1000000000) (-2202063 / 250000000) (Real.log (247807606671 / 250000000000)) := by
  have h := reflection_log_5061_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5062_neg : (187842389 / 1000000000) ≤ -Real.log (50000000000 / 60332166019) ∧
    -Real.log (50000000000 / 60332166019) ≤ (18784239 / 100000000) := by
  have h := checkLog_sound (w := (10332166019 / 110332166019)) (n := 12)
    (lo := (187842389 / 1000000000)) (hi := (18784239 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60332166019 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60332166019 / 50000000000) = 1/(50000000000 / 60332166019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5062 : Bounds (187842389 / 1000000000) (18784239 / 100000000) (Real.log (60332166019 / 50000000000)) := by
  have h := reflection_log_5062_neg
  have he : Real.log (60332166019 / 50000000000) = -Real.log (50000000000 / 60332166019) := by
    rw [show ((60332166019 / 50000000000) : ℝ) = ((50000000000 / 60332166019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5063_neg : (188320593 / 1000000000) ≤ -Real.log (500000000000 / 603610240179) ∧
    -Real.log (500000000000 / 603610240179) ≤ (94160297 / 500000000) := by
  have h := checkLog_sound (w := (103610240179 / 1103610240179)) (n := 12)
    (lo := (188320593 / 1000000000)) (hi := (94160297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603610240179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603610240179 / 500000000000) = 1/(500000000000 / 603610240179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5063 : Bounds (188320593 / 1000000000) (94160297 / 500000000) (Real.log (603610240179 / 500000000000)) := by
  have h := reflection_log_5063_neg
  have he : Real.log (603610240179 / 500000000000) = -Real.log (500000000000 / 603610240179) := by
    rw [show ((603610240179 / 500000000000) : ℝ) = ((500000000000 / 603610240179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5064_neg : (1508011 / 4000000) ≤ -Real.log (500000000000 / 728954160009) ∧
    -Real.log (500000000000 / 728954160009) ≤ (377002751 / 1000000000) := by
  have h := checkLog_sound (w := (228954160009 / 1228954160009)) (n := 12)
    (lo := (1508011 / 4000000)) (hi := (377002751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728954160009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728954160009 / 500000000000) = 1/(500000000000 / 728954160009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5064 : Bounds (1508011 / 4000000) (377002751 / 1000000000) (Real.log (728954160009 / 500000000000)) := by
  have h := reflection_log_5064_neg
  have he : Real.log (728954160009 / 500000000000) = -Real.log (500000000000 / 728954160009) := by
    rw [show ((728954160009 / 500000000000) : ℝ) = ((500000000000 / 728954160009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5065_neg : (188604973 / 500000000) ≤ -Real.log (500000000000 / 729105211407) ∧
    -Real.log (500000000000 / 729105211407) ≤ (377209947 / 1000000000) := by
  have h := checkLog_sound (w := (229105211407 / 1229105211407)) (n := 12)
    (lo := (188604973 / 500000000)) (hi := (377209947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729105211407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729105211407 / 500000000000) = 1/(500000000000 / 729105211407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5065 : Bounds (188604973 / 500000000) (377209947 / 1000000000) (Real.log (729105211407 / 500000000000)) := by
  have h := reflection_log_5065_neg
  have he : Real.log (729105211407 / 500000000000) = -Real.log (500000000000 / 729105211407) := by
    rw [show ((729105211407 / 500000000000) : ℝ) = ((500000000000 / 729105211407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5066_neg : (42751949 / 250000000) ≤ -Real.log (2000 / 2373) ∧
    -Real.log (2000 / 2373) ≤ (171007797 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 4373)) (n := 12)
    (lo := (42751949 / 250000000)) (hi := (171007797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2373 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2373 / 2000) = 1/(2000 / 2373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5066 : Bounds (42751949 / 250000000) (171007797 / 1000000000) (Real.log (2373 / 2000)) := by
  have h := reflection_log_5066_neg
  have he : Real.log (2373 / 2000) = -Real.log (2000 / 2373) := by
    rw [show ((2373 / 2000) : ℝ) = ((2000 / 2373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5067_neg : (25801169 / 125000000) ≤ -Real.log (1627 / 2000) ∧
    -Real.log (1627 / 2000) ≤ (206409353 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 3627)) (n := 12)
    (lo := (25801169 / 125000000)) (hi := (206409353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1627) = 1/(1627 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5067 : Bounds (-206409353 / 1000000000) (-25801169 / 125000000) (Real.log (1627 / 2000)) := by
  have h := reflection_log_5067_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5068_neg : (93241 / 500000000) ≤ -Real.log (2000000 / 2000373) ∧
    -Real.log (2000000 / 2000373) ≤ (186483 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 4000373)) (n := 12)
    (lo := (93241 / 500000000)) (hi := (186483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000373 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000373 / 2000000) = 1/(2000000 / 2000373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5068 : Bounds (93241 / 500000000) (186483 / 1000000000) (Real.log (2000373 / 2000000)) := by
  have h := reflection_log_5068_neg
  have he : Real.log (2000373 / 2000000) = -Real.log (2000000 / 2000373) := by
    rw [show ((2000373 / 2000000) : ℝ) = ((2000000 / 2000373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5069_neg : (186517 / 1000000000) ≤ -Real.log (1999627 / 2000000) ∧
    -Real.log (1999627 / 2000000) ≤ (93259 / 500000000) := by
  have h := checkLog_sound (w := (373 / 3999627)) (n := 12)
    (lo := (186517 / 1000000000)) (hi := (93259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999627) = 1/(1999627 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5069 : Bounds (-93259 / 500000000) (-186517 / 1000000000) (Real.log (1999627 / 2000000)) := by
  have h := reflection_log_5069_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5070_neg : (895637 / 10000000) ≤ -Real.log (1000000 / 1093697) ∧
    -Real.log (1000000 / 1093697) ≤ (89563701 / 1000000000) := by
  have h := checkLog_sound (w := (93697 / 2093697)) (n := 12)
    (lo := (895637 / 10000000)) (hi := (89563701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093697 / 1000000) = 1/(1000000 / 1093697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5070 : Bounds (895637 / 10000000) (89563701 / 1000000000) (Real.log (1093697 / 1000000)) := by
  have h := reflection_log_5070_neg
  have he : Real.log (1093697 / 1000000) = -Real.log (1000000 / 1093697) := by
    rw [show ((1093697 / 1000000) : ℝ) = ((1000000 / 1093697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5071_neg : (98381591 / 1000000000) ≤ -Real.log (906303 / 1000000) ∧
    -Real.log (906303 / 1000000) ≤ (12297699 / 125000000) := by
  have h := checkLog_sound (w := (93697 / 1906303)) (n := 12)
    (lo := (98381591 / 1000000000)) (hi := (12297699 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906303) = 1/(906303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5071 : Bounds (-12297699 / 125000000) (-98381591 / 1000000000) (Real.log (906303 / 1000000)) := by
  have h := reflection_log_5071_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5072_neg : (89780373 / 1000000000) ≤ -Real.log (500000 / 546967) ∧
    -Real.log (500000 / 546967) ≤ (44890187 / 500000000) := by
  have h := checkLog_sound (w := (46967 / 1046967)) (n := 12)
    (lo := (89780373 / 1000000000)) (hi := (44890187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546967 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546967 / 500000) = 1/(500000 / 546967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5072 : Bounds (89780373 / 1000000000) (44890187 / 500000000) (Real.log (546967 / 500000)) := by
  have h := reflection_log_5072_neg
  have he : Real.log (546967 / 500000) = -Real.log (500000 / 546967) := by
    rw [show ((546967 / 500000) : ℝ) = ((500000 / 546967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5073_neg : (98643127 / 1000000000) ≤ -Real.log (453033 / 500000) ∧
    -Real.log (453033 / 500000) ≤ (12330391 / 125000000) := by
  have h := checkLog_sound (w := (46967 / 953033)) (n := 12)
    (lo := (98643127 / 1000000000)) (hi := (12330391 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453033) = 1/(453033 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5073 : Bounds (-12330391 / 125000000) (-98643127 / 1000000000) (Real.log (453033 / 500000)) := by
  have h := reflection_log_5073_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5074_neg : (4431377 / 500000000) ≤ -Real.log (247794100911 / 250000000000) ∧
    -Real.log (247794100911 / 250000000000) ≤ (1772551 / 200000000) := by
  have h := checkLog_sound (w := (2205899089 / 497794100911)) (n := 12)
    (lo := (4431377 / 500000000)) (hi := (1772551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247794100911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247794100911) = 1/(247794100911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5074 : Bounds (-1772551 / 200000000) (-4431377 / 500000000) (Real.log (247794100911 / 250000000000)) := by
  have h := reflection_log_5074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5075_neg : (8817891 / 1000000000) ≤ -Real.log (991220872191 / 1000000000000) ∧
    -Real.log (991220872191 / 1000000000000) ≤ (2204473 / 250000000) := by
  have h := checkLog_sound (w := (8779127809 / 1991220872191)) (n := 12)
    (lo := (8817891 / 1000000000)) (hi := (2204473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991220872191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991220872191) = 1/(991220872191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5075 : Bounds (-2204473 / 250000000) (-8817891 / 1000000000) (Real.log (991220872191 / 1000000000000)) := by
  have h := reflection_log_5075_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5076_neg : (46986323 / 250000000) ≤ -Real.log (62500000000 / 75422968367) ∧
    -Real.log (62500000000 / 75422968367) ≤ (187945293 / 1000000000) := by
  have h := checkLog_sound (w := (12922968367 / 137922968367)) (n := 12)
    (lo := (46986323 / 250000000)) (hi := (187945293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75422968367 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75422968367 / 62500000000) = 1/(62500000000 / 75422968367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5076 : Bounds (46986323 / 250000000) (187945293 / 1000000000) (Real.log (75422968367 / 62500000000)) := by
  have h := reflection_log_5076_neg
  have he : Real.log (75422968367 / 62500000000) = -Real.log (62500000000 / 75422968367) := by
    rw [show ((75422968367 / 62500000000) : ℝ) = ((62500000000 / 75422968367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5077_neg : (188423501 / 1000000000) ≤ -Real.log (500000000000 / 603672359409) ∧
    -Real.log (500000000000 / 603672359409) ≤ (94211751 / 500000000) := by
  have h := checkLog_sound (w := (103672359409 / 1103672359409)) (n := 12)
    (lo := (188423501 / 1000000000)) (hi := (94211751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603672359409 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603672359409 / 500000000000) = 1/(500000000000 / 603672359409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5077 : Bounds (188423501 / 1000000000) (94211751 / 500000000) (Real.log (603672359409 / 500000000000)) := by
  have h := reflection_log_5077_neg
  have he : Real.log (603672359409 / 500000000000) = -Real.log (500000000000 / 603672359409) := by
    rw [show ((603672359409 / 500000000000) : ℝ) = ((500000000000 / 603672359409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5078_neg : (188604973 / 500000000) ≤ -Real.log (250000000000 / 364552605703) ∧
    -Real.log (250000000000 / 364552605703) ≤ (377209947 / 1000000000) := by
  have h := checkLog_sound (w := (114552605703 / 614552605703)) (n := 12)
    (lo := (188604973 / 500000000)) (hi := (377209947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364552605703 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364552605703 / 250000000000) = 1/(250000000000 / 364552605703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5078 : Bounds (188604973 / 500000000) (377209947 / 1000000000) (Real.log (364552605703 / 250000000000)) := by
  have h := reflection_log_5078_neg
  have he : Real.log (364552605703 / 250000000000) = -Real.log (250000000000 / 364552605703) := by
    rw [show ((364552605703 / 250000000000) : ℝ) = ((250000000000 / 364552605703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5079_neg : (377417149 / 1000000000) ≤ -Real.log (500000000000 / 729256299939) ∧
    -Real.log (500000000000 / 729256299939) ≤ (7548343 / 20000000) := by
  have h := checkLog_sound (w := (229256299939 / 1229256299939)) (n := 12)
    (lo := (377417149 / 1000000000)) (hi := (7548343 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729256299939 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729256299939 / 500000000000) = 1/(500000000000 / 729256299939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5079 : Bounds (377417149 / 1000000000) (7548343 / 20000000) (Real.log (729256299939 / 500000000000)) := by
  have h := reflection_log_5079_neg
  have he : Real.log (729256299939 / 500000000000) = -Real.log (500000000000 / 729256299939) := by
    rw [show ((729256299939 / 500000000000) : ℝ) = ((500000000000 / 729256299939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5080_neg : (85546037 / 500000000) ≤ -Real.log (5000 / 5933) ∧
    -Real.log (5000 / 5933) ≤ (6843683 / 40000000) := by
  have h := checkLog_sound (w := (933 / 10933)) (n := 12)
    (lo := (85546037 / 500000000)) (hi := (6843683 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5933 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5933 / 5000) = 1/(5000 / 5933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5080 : Bounds (85546037 / 500000000) (6843683 / 40000000) (Real.log (5933 / 5000)) := by
  have h := reflection_log_5080_neg
  have he : Real.log (5933 / 5000) = -Real.log (5000 / 5933) := by
    rw [show ((5933 / 5000) : ℝ) = ((5000 / 5933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5081_neg : (41306457 / 200000000) ≤ -Real.log (4067 / 5000) ∧
    -Real.log (4067 / 5000) ≤ (103266143 / 500000000) := by
  have h := checkLog_sound (w := (933 / 9067)) (n := 12)
    (lo := (41306457 / 200000000)) (hi := (103266143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4067) = 1/(4067 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5081 : Bounds (-103266143 / 500000000) (-41306457 / 200000000) (Real.log (4067 / 5000)) := by
  have h := reflection_log_5081_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5082_neg : (93291 / 500000000) ≤ -Real.log (5000000 / 5000933) ∧
    -Real.log (5000000 / 5000933) ≤ (186583 / 1000000000) := by
  have h := checkLog_sound (w := (933 / 10000933)) (n := 12)
    (lo := (93291 / 500000000)) (hi := (186583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000933 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000933 / 5000000) = 1/(5000000 / 5000933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5082 : Bounds (93291 / 500000000) (186583 / 1000000000) (Real.log (5000933 / 5000000)) := by
  have h := reflection_log_5082_neg
  have he : Real.log (5000933 / 5000000) = -Real.log (5000000 / 5000933) := by
    rw [show ((5000933 / 5000000) : ℝ) = ((5000000 / 5000933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5083_neg : (186617 / 1000000000) ≤ -Real.log (4999067 / 5000000) ∧
    -Real.log (4999067 / 5000000) ≤ (93309 / 500000000) := by
  have h := checkLog_sound (w := (933 / 9999067)) (n := 12)
    (lo := (186617 / 1000000000)) (hi := (93309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999067) = 1/(4999067 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5083 : Bounds (-93309 / 500000000) (-186617 / 1000000000) (Real.log (4999067 / 5000000)) := by
  have h := reflection_log_5083_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5084_neg : (8961033 / 100000000) ≤ -Real.log (250000 / 273437) ∧
    -Real.log (250000 / 273437) ≤ (89610331 / 1000000000) := by
  have h := checkLog_sound (w := (23437 / 523437)) (n := 12)
    (lo := (8961033 / 100000000)) (hi := (89610331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273437 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273437 / 250000) = 1/(250000 / 273437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5084 : Bounds (8961033 / 100000000) (89610331 / 1000000000) (Real.log (273437 / 250000)) := by
  have h := reflection_log_5084_neg
  have he : Real.log (273437 / 250000) = -Real.log (250000 / 273437) := by
    rw [show ((273437 / 250000) : ℝ) = ((250000 / 273437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5085_neg : (19687573 / 200000000) ≤ -Real.log (226563 / 250000) ∧
    -Real.log (226563 / 250000) ≤ (49218933 / 500000000) := by
  have h := checkLog_sound (w := (23437 / 476563)) (n := 12)
    (lo := (19687573 / 200000000)) (hi := (49218933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226563) = 1/(226563 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5085 : Bounds (-49218933 / 500000000) (-19687573 / 200000000) (Real.log (226563 / 250000)) := by
  have h := reflection_log_5085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5086_neg : (5614187 / 62500000) ≤ -Real.log (200000 / 218797) ∧
    -Real.log (200000 / 218797) ≤ (89826993 / 1000000000) := by
  have h := checkLog_sound (w := (18797 / 418797)) (n := 12)
    (lo := (5614187 / 62500000)) (hi := (89826993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218797 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218797 / 200000) = 1/(200000 / 218797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5086 : Bounds (5614187 / 62500000) (89826993 / 1000000000) (Real.log (218797 / 200000)) := by
  have h := reflection_log_5086_neg
  have he : Real.log (218797 / 200000) = -Real.log (200000 / 218797) := by
    rw [show ((218797 / 200000) : ℝ) = ((200000 / 218797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5087_neg : (12337427 / 125000000) ≤ -Real.log (181203 / 200000) ∧
    -Real.log (181203 / 200000) ≤ (98699417 / 1000000000) := by
  have h := checkLog_sound (w := (18797 / 381203)) (n := 12)
    (lo := (12337427 / 125000000)) (hi := (98699417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181203) = 1/(181203 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5087 : Bounds (-98699417 / 1000000000) (-12337427 / 125000000) (Real.log (181203 / 200000)) := by
  have h := reflection_log_5087_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5088_neg : (1109053 / 125000000) ≤ -Real.log (39646672791 / 40000000000) ∧
    -Real.log (39646672791 / 40000000000) ≤ (354897 / 40000000) := by
  have h := checkLog_sound (w := (353327209 / 79646672791)) (n := 12)
    (lo := (1109053 / 125000000)) (hi := (354897 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39646672791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39646672791) = 1/(39646672791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5088 : Bounds (-354897 / 40000000) (-1109053 / 125000000) (Real.log (39646672791 / 40000000000)) := by
  have h := reflection_log_5088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5089_neg : (1765507 / 200000000) ≤ -Real.log (61950707031 / 62500000000) ∧
    -Real.log (61950707031 / 62500000000) ≤ (551721 / 62500000) := by
  have h := checkLog_sound (w := (549292969 / 124450707031)) (n := 12)
    (lo := (1765507 / 200000000)) (hi := (551721 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61950707031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61950707031) = 1/(61950707031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5089 : Bounds (-551721 / 62500000) (-1765507 / 200000000) (Real.log (61950707031 / 62500000000)) := by
  have h := reflection_log_5089_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5090_neg : (47012049 / 250000000) ≤ -Real.log (500000000000 / 603445840671) ∧
    -Real.log (500000000000 / 603445840671) ≤ (188048197 / 1000000000) := by
  have h := checkLog_sound (w := (103445840671 / 1103445840671)) (n := 12)
    (lo := (47012049 / 250000000)) (hi := (188048197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603445840671 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603445840671 / 500000000000) = 1/(500000000000 / 603445840671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5090 : Bounds (47012049 / 250000000) (188048197 / 1000000000) (Real.log (603445840671 / 500000000000)) := by
  have h := reflection_log_5090_neg
  have he : Real.log (603445840671 / 500000000000) = -Real.log (500000000000 / 603445840671) := by
    rw [show ((603445840671 / 500000000000) : ℝ) = ((500000000000 / 603445840671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5091_neg : (188526409 / 1000000000) ≤ -Real.log (500000000000 / 603734485633) ∧
    -Real.log (500000000000 / 603734485633) ≤ (18852641 / 100000000) := by
  have h := checkLog_sound (w := (103734485633 / 1103734485633)) (n := 12)
    (lo := (188526409 / 1000000000)) (hi := (18852641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603734485633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603734485633 / 500000000000) = 1/(500000000000 / 603734485633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5091 : Bounds (188526409 / 1000000000) (18852641 / 100000000) (Real.log (603734485633 / 500000000000)) := by
  have h := reflection_log_5091_neg
  have he : Real.log (603734485633 / 500000000000) = -Real.log (500000000000 / 603734485633) := by
    rw [show ((603734485633 / 500000000000) : ℝ) = ((500000000000 / 603734485633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5092_neg : (377417149 / 1000000000) ≤ -Real.log (250000000000 / 364628149969) ∧
    -Real.log (250000000000 / 364628149969) ≤ (7548343 / 20000000) := by
  have h := checkLog_sound (w := (114628149969 / 614628149969)) (n := 12)
    (lo := (377417149 / 1000000000)) (hi := (7548343 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364628149969 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364628149969 / 250000000000) = 1/(250000000000 / 364628149969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5092 : Bounds (377417149 / 1000000000) (7548343 / 20000000) (Real.log (364628149969 / 250000000000)) := by
  have h := reflection_log_5092_neg
  have he : Real.log (364628149969 / 250000000000) = -Real.log (250000000000 / 364628149969) := by
    rw [show ((364628149969 / 250000000000) : ℝ) = ((250000000000 / 364628149969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5093_neg : (9440609 / 25000000) ≤ -Real.log (500000000000 / 729407425621) ∧
    -Real.log (500000000000 / 729407425621) ≤ (377624361 / 1000000000) := by
  have h := checkLog_sound (w := (229407425621 / 1229407425621)) (n := 12)
    (lo := (9440609 / 25000000)) (hi := (377624361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729407425621 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729407425621 / 500000000000) = 1/(500000000000 / 729407425621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5093 : Bounds (9440609 / 25000000) (377624361 / 1000000000) (Real.log (729407425621 / 500000000000)) := by
  have h := reflection_log_5093_neg
  have he : Real.log (729407425621 / 500000000000) = -Real.log (500000000000 / 729407425621) := by
    rw [show ((729407425621 / 500000000000) : ℝ) = ((500000000000 / 729407425621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5094_neg : (34235269 / 200000000) ≤ -Real.log (10000 / 11867) ∧
    -Real.log (10000 / 11867) ≤ (85588173 / 500000000) := by
  have h := checkLog_sound (w := (1867 / 21867)) (n := 12)
    (lo := (34235269 / 200000000)) (hi := (85588173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11867 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11867 / 10000) = 1/(10000 / 11867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5094 : Bounds (34235269 / 200000000) (85588173 / 500000000) (Real.log (11867 / 10000)) := by
  have h := reflection_log_5094_neg
  have he : Real.log (11867 / 10000) = -Real.log (10000 / 11867) := by
    rw [show ((11867 / 10000) : ℝ) = ((10000 / 11867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5095_neg : (206655233 / 1000000000) ≤ -Real.log (8133 / 10000) ∧
    -Real.log (8133 / 10000) ≤ (103327617 / 500000000) := by
  have h := checkLog_sound (w := (1867 / 18133)) (n := 12)
    (lo := (206655233 / 1000000000)) (hi := (103327617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8133) = 1/(8133 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5095 : Bounds (-103327617 / 500000000) (-206655233 / 1000000000) (Real.log (8133 / 10000)) := by
  have h := reflection_log_5095_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5096_neg : (93341 / 500000000) ≤ -Real.log (10000000 / 10001867) ∧
    -Real.log (10000000 / 10001867) ≤ (186683 / 1000000000) := by
  have h := checkLog_sound (w := (1867 / 20001867)) (n := 12)
    (lo := (93341 / 500000000)) (hi := (186683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001867 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001867 / 10000000) = 1/(10000000 / 10001867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5096 : Bounds (93341 / 500000000) (186683 / 1000000000) (Real.log (10001867 / 10000000)) := by
  have h := reflection_log_5096_neg
  have he : Real.log (10001867 / 10000000) = -Real.log (10000000 / 10001867) := by
    rw [show ((10001867 / 10000000) : ℝ) = ((10000000 / 10001867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5097_neg : (186717 / 1000000000) ≤ -Real.log (9998133 / 10000000) ∧
    -Real.log (9998133 / 10000000) ≤ (93359 / 500000000) := by
  have h := checkLog_sound (w := (1867 / 19998133)) (n := 12)
    (lo := (186717 / 1000000000)) (hi := (93359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998133) = 1/(9998133 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5097 : Bounds (-93359 / 500000000) (-186717 / 1000000000) (Real.log (9998133 / 10000000)) := by
  have h := reflection_log_5097_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5098_neg : (89656957 / 1000000000) ≤ -Real.log (1000000 / 1093799) ∧
    -Real.log (1000000 / 1093799) ≤ (44828479 / 500000000) := by
  have h := checkLog_sound (w := (93799 / 2093799)) (n := 12)
    (lo := (89656957 / 1000000000)) (hi := (44828479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093799 / 1000000) = 1/(1000000 / 1093799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5098 : Bounds (89656957 / 1000000000) (44828479 / 500000000) (Real.log (1093799 / 1000000)) := by
  have h := reflection_log_5098_neg
  have he : Real.log (1093799 / 1000000) = -Real.log (1000000 / 1093799) := by
    rw [show ((1093799 / 1000000) : ℝ) = ((1000000 / 1093799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5099_neg : (98494143 / 1000000000) ≤ -Real.log (906201 / 1000000) ∧
    -Real.log (906201 / 1000000) ≤ (1538971 / 15625000) := by
  have h := checkLog_sound (w := (93799 / 1906201)) (n := 12)
    (lo := (98494143 / 1000000000)) (hi := (1538971 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906201) = 1/(906201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5099 : Bounds (-1538971 / 15625000) (-98494143 / 1000000000) (Real.log (906201 / 1000000)) := by
  have h := reflection_log_5099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5100_neg : (8987361 / 100000000) ≤ -Real.log (250000 / 273509) ∧
    -Real.log (250000 / 273509) ≤ (89873611 / 1000000000) := by
  have h := checkLog_sound (w := (23509 / 523509)) (n := 12)
    (lo := (8987361 / 100000000)) (hi := (89873611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273509 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273509 / 250000) = 1/(250000 / 273509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5100 : Bounds (8987361 / 100000000) (89873611 / 1000000000) (Real.log (273509 / 250000)) := by
  have h := reflection_log_5100_neg
  have he : Real.log (273509 / 250000) = -Real.log (250000 / 273509) := by
    rw [show ((273509 / 250000) : ℝ) = ((250000 / 273509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5101_neg : (24688927 / 250000000) ≤ -Real.log (226491 / 250000) ∧
    -Real.log (226491 / 250000) ≤ (98755709 / 1000000000) := by
  have h := checkLog_sound (w := (23509 / 476491)) (n := 12)
    (lo := (24688927 / 250000000)) (hi := (98755709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226491) = 1/(226491 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5101 : Bounds (-98755709 / 1000000000) (-24688927 / 250000000) (Real.log (226491 / 250000)) := by
  have h := reflection_log_5101_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5102_neg : (4441049 / 500000000) ≤ -Real.log (61947326919 / 62500000000) ∧
    -Real.log (61947326919 / 62500000000) ≤ (8882099 / 1000000000) := by
  have h := checkLog_sound (w := (552673081 / 124447326919)) (n := 12)
    (lo := (4441049 / 500000000)) (hi := (8882099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61947326919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61947326919) = 1/(61947326919 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5102 : Bounds (-8882099 / 1000000000) (-4441049 / 500000000) (Real.log (61947326919 / 62500000000)) := by
  have h := reflection_log_5102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5103_neg : (1767437 / 200000000) ≤ -Real.log (991201747599 / 1000000000000) ∧
    -Real.log (991201747599 / 1000000000000) ≤ (4418593 / 500000000) := by
  have h := checkLog_sound (w := (8798252401 / 1991201747599)) (n := 12)
    (lo := (1767437 / 200000000)) (hi := (4418593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991201747599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991201747599) = 1/(991201747599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5103 : Bounds (-4418593 / 500000000) (-1767437 / 200000000) (Real.log (991201747599 / 1000000000000)) := by
  have h := reflection_log_5103_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5104_neg : (1881511 / 10000000) ≤ -Real.log (250000000000 / 301753970697) ∧
    -Real.log (250000000000 / 301753970697) ≤ (188151101 / 1000000000) := by
  have h := checkLog_sound (w := (51753970697 / 551753970697)) (n := 12)
    (lo := (1881511 / 10000000)) (hi := (188151101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301753970697 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301753970697 / 250000000000) = 1/(250000000000 / 301753970697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5104 : Bounds (1881511 / 10000000) (188151101 / 1000000000) (Real.log (301753970697 / 250000000000)) := by
  have h := reflection_log_5104_neg
  have he : Real.log (301753970697 / 250000000000) = -Real.log (250000000000 / 301753970697) := by
    rw [show ((301753970697 / 250000000000) : ℝ) = ((250000000000 / 301753970697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5105_neg : (188629319 / 1000000000) ≤ -Real.log (500000000000 / 603796618851) ∧
    -Real.log (500000000000 / 603796618851) ≤ (4715733 / 25000000) := by
  have h := checkLog_sound (w := (103796618851 / 1103796618851)) (n := 12)
    (lo := (188629319 / 1000000000)) (hi := (4715733 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603796618851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603796618851 / 500000000000) = 1/(500000000000 / 603796618851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5105 : Bounds (188629319 / 1000000000) (4715733 / 25000000) (Real.log (603796618851 / 500000000000)) := by
  have h := reflection_log_5105_neg
  have he : Real.log (603796618851 / 500000000000) = -Real.log (500000000000 / 603796618851) := by
    rw [show ((603796618851 / 500000000000) : ℝ) = ((500000000000 / 603796618851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5106_neg : (9440609 / 25000000) ≤ -Real.log (25000000000 / 36470371281) ∧
    -Real.log (25000000000 / 36470371281) ≤ (377624361 / 1000000000) := by
  have h := checkLog_sound (w := (11470371281 / 61470371281)) (n := 12)
    (lo := (9440609 / 25000000)) (hi := (377624361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36470371281 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36470371281 / 25000000000) = 1/(25000000000 / 36470371281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5106 : Bounds (9440609 / 25000000) (377624361 / 1000000000) (Real.log (36470371281 / 25000000000)) := by
  have h := reflection_log_5106_neg
  have he : Real.log (36470371281 / 25000000000) = -Real.log (25000000000 / 36470371281) := by
    rw [show ((36470371281 / 25000000000) : ℝ) = ((25000000000 / 36470371281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5107_neg : (377831579 / 1000000000) ≤ -Real.log (500000000000 / 729558588467) ∧
    -Real.log (500000000000 / 729558588467) ≤ (18891579 / 50000000) := by
  have h := checkLog_sound (w := (229558588467 / 1229558588467)) (n := 12)
    (lo := (377831579 / 1000000000)) (hi := (18891579 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729558588467 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729558588467 / 500000000000) = 1/(500000000000 / 729558588467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5107 : Bounds (377831579 / 1000000000) (18891579 / 50000000) (Real.log (729558588467 / 500000000000)) := by
  have h := reflection_log_5107_neg
  have he : Real.log (729558588467 / 500000000000) = -Real.log (500000000000 / 729558588467) := by
    rw [show ((729558588467 / 500000000000) : ℝ) = ((500000000000 / 729558588467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5108_neg : (171260609 / 1000000000) ≤ -Real.log (2500 / 2967) ∧
    -Real.log (2500 / 2967) ≤ (17126061 / 100000000) := by
  have h := checkLog_sound (w := (467 / 5467)) (n := 12)
    (lo := (171260609 / 1000000000)) (hi := (17126061 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2967 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2967 / 2500) = 1/(2500 / 2967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5108 : Bounds (171260609 / 1000000000) (17126061 / 100000000) (Real.log (2967 / 2500)) := by
  have h := reflection_log_5108_neg
  have he : Real.log (2967 / 2500) = -Real.log (2500 / 2967) := by
    rw [show ((2967 / 2500) : ℝ) = ((2500 / 2967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5109_neg : (206778197 / 1000000000) ≤ -Real.log (2033 / 2500) ∧
    -Real.log (2033 / 2500) ≤ (103389099 / 500000000) := by
  have h := checkLog_sound (w := (467 / 4533)) (n := 12)
    (lo := (206778197 / 1000000000)) (hi := (103389099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2033) = 1/(2033 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5109 : Bounds (-103389099 / 500000000) (-206778197 / 1000000000) (Real.log (2033 / 2500)) := by
  have h := reflection_log_5109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5110_neg : (93391 / 500000000) ≤ -Real.log (2500000 / 2500467) ∧
    -Real.log (2500000 / 2500467) ≤ (186783 / 1000000000) := by
  have h := checkLog_sound (w := (467 / 5000467)) (n := 12)
    (lo := (93391 / 500000000)) (hi := (186783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500467 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500467 / 2500000) = 1/(2500000 / 2500467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5110 : Bounds (93391 / 500000000) (186783 / 1000000000) (Real.log (2500467 / 2500000)) := by
  have h := reflection_log_5110_neg
  have he : Real.log (2500467 / 2500000) = -Real.log (2500000 / 2500467) := by
    rw [show ((2500467 / 2500000) : ℝ) = ((2500000 / 2500467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5111_neg : (186817 / 1000000000) ≤ -Real.log (2499533 / 2500000) ∧
    -Real.log (2499533 / 2500000) ≤ (93409 / 500000000) := by
  have h := checkLog_sound (w := (467 / 4999533)) (n := 12)
    (lo := (186817 / 1000000000)) (hi := (93409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499533) = 1/(2499533 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5111 : Bounds (-93409 / 500000000) (-186817 / 1000000000) (Real.log (2499533 / 2500000)) := by
  have h := reflection_log_5111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5112_neg : (89703583 / 1000000000) ≤ -Real.log (20000 / 21877) ∧
    -Real.log (20000 / 21877) ≤ (2803237 / 31250000) := by
  have h := checkLog_sound (w := (1877 / 41877)) (n := 12)
    (lo := (89703583 / 1000000000)) (hi := (2803237 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21877 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21877 / 20000) = 1/(20000 / 21877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5112 : Bounds (89703583 / 1000000000) (2803237 / 31250000) (Real.log (21877 / 20000)) := by
  have h := reflection_log_5112_neg
  have he : Real.log (21877 / 20000) = -Real.log (20000 / 21877) := by
    rw [show ((21877 / 20000) : ℝ) = ((20000 / 21877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5113_neg : (98550423 / 1000000000) ≤ -Real.log (18123 / 20000) ∧
    -Real.log (18123 / 20000) ≤ (12318803 / 125000000) := by
  have h := checkLog_sound (w := (1877 / 38123)) (n := 12)
    (lo := (98550423 / 1000000000)) (hi := (12318803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18123) = 1/(18123 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5113 : Bounds (-12318803 / 125000000) (-98550423 / 1000000000) (Real.log (18123 / 20000)) := by
  have h := reflection_log_5113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5114_neg : (3596809 / 40000000) ≤ -Real.log (1000000 / 1094087) ∧
    -Real.log (1000000 / 1094087) ≤ (44960113 / 500000000) := by
  have h := checkLog_sound (w := (94087 / 2094087)) (n := 12)
    (lo := (3596809 / 40000000)) (hi := (44960113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094087 / 1000000) = 1/(1000000 / 1094087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5114 : Bounds (3596809 / 40000000) (44960113 / 500000000) (Real.log (1094087 / 1000000)) := by
  have h := reflection_log_5114_neg
  have he : Real.log (1094087 / 1000000) = -Real.log (1000000 / 1094087) := by
    rw [show ((1094087 / 1000000) : ℝ) = ((1000000 / 1094087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5115_neg : (24703001 / 250000000) ≤ -Real.log (905913 / 1000000) ∧
    -Real.log (905913 / 1000000) ≤ (19762401 / 200000000) := by
  have h := checkLog_sound (w := (94087 / 1905913)) (n := 12)
    (lo := (24703001 / 250000000)) (hi := (19762401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905913) = 1/(905913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5115 : Bounds (-19762401 / 200000000) (-24703001 / 250000000) (Real.log (905913 / 1000000)) := by
  have h := reflection_log_5115_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5116_neg : (4445889 / 500000000) ≤ -Real.log (991147636431 / 1000000000000) ∧
    -Real.log (991147636431 / 1000000000000) ≤ (8891779 / 1000000000) := by
  have h := checkLog_sound (w := (8852363569 / 1991147636431)) (n := 12)
    (lo := (4445889 / 500000000)) (hi := (8891779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991147636431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991147636431) = 1/(991147636431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5116 : Bounds (-8891779 / 1000000000) (-4445889 / 500000000) (Real.log (991147636431 / 1000000000000)) := by
  have h := reflection_log_5116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5117_neg : (221171 / 25000000) ≤ -Real.log (396476871 / 400000000) ∧
    -Real.log (396476871 / 400000000) ≤ (8846841 / 1000000000) := by
  have h := checkLog_sound (w := (3523129 / 796476871)) (n := 12)
    (lo := (221171 / 25000000)) (hi := (8846841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 396476871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 396476871) = 1/(396476871 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5117 : Bounds (-8846841 / 1000000000) (-221171 / 25000000) (Real.log (396476871 / 400000000)) := by
  have h := reflection_log_5117_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5118_neg : (94127003 / 500000000) ≤ -Real.log (125000000000 / 150892512277) ∧
    -Real.log (125000000000 / 150892512277) ≤ (188254007 / 1000000000) := by
  have h := checkLog_sound (w := (25892512277 / 275892512277)) (n := 12)
    (lo := (94127003 / 500000000)) (hi := (188254007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150892512277 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150892512277 / 125000000000) = 1/(125000000000 / 150892512277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5118 : Bounds (94127003 / 500000000) (188254007 / 1000000000) (Real.log (150892512277 / 125000000000)) := by
  have h := reflection_log_5118_neg
  have he : Real.log (150892512277 / 125000000000) = -Real.log (125000000000 / 150892512277) := by
    rw [show ((150892512277 / 125000000000) : ℝ) = ((125000000000 / 150892512277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5119_neg : (188732229 / 1000000000) ≤ -Real.log (100000000000 / 120771751813) ∧
    -Real.log (100000000000 / 120771751813) ≤ (18873223 / 100000000) := by
  have h := checkLog_sound (w := (20771751813 / 220771751813)) (n := 12)
    (lo := (188732229 / 1000000000)) (hi := (18873223 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120771751813 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120771751813 / 100000000000) = 1/(100000000000 / 120771751813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5119 : Bounds (188732229 / 1000000000) (18873223 / 100000000) (Real.log (120771751813 / 100000000000)) := by
  have h := reflection_log_5119_neg
  have he : Real.log (120771751813 / 100000000000) = -Real.log (100000000000 / 120771751813) := by
    rw [show ((120771751813 / 100000000000) : ℝ) = ((100000000000 / 120771751813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


