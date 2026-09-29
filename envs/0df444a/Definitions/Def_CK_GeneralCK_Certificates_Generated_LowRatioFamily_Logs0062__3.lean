-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0062__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0062__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:33:41.840055+00:00
-- url     : https://prove2.me/theorems/8b8214b3-a74d-4616-a4be-4f5dd5ea8946
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0062 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0063, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0062 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0063, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0064)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0062 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0063, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0064)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0062 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0063, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0064) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0062 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0063, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0064).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0062 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3968_neg : (18841917 / 200000000) ≤ -Real.log (227523 / 250000) ∧
    -Real.log (227523 / 250000) ≤ (47104793 / 500000000) := by
  have h := checkLog_sound (w := (22477 / 477523)) (n := 12)
    (lo := (18841917 / 200000000)) (hi := (47104793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227523) = 1/(227523 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3968 : Bounds (-47104793 / 500000000) (-18841917 / 200000000) (Real.log (227523 / 250000)) := by
  have h := reflection_log_3968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3969_neg : (1014537 / 125000000) ≤ -Real.log (61994784471 / 62500000000) ∧
    -Real.log (61994784471 / 62500000000) ≤ (8116297 / 1000000000) := by
  have h := checkLog_sound (w := (505215529 / 124494784471)) (n := 12)
    (lo := (1014537 / 125000000)) (hi := (8116297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61994784471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61994784471) = 1/(61994784471 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3969 : Bounds (-8116297 / 1000000000) (-1014537 / 125000000) (Real.log (61994784471 / 62500000000)) := by
  have h := reflection_log_3969_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3970_neg : (252333 / 31250000) ≤ -Real.log (247989464079 / 250000000000) ∧
    -Real.log (247989464079 / 250000000000) ≤ (8074657 / 1000000000) := by
  have h := checkLog_sound (w := (2010535921 / 497989464079)) (n := 12)
    (lo := (252333 / 31250000)) (hi := (8074657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247989464079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247989464079) = 1/(247989464079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3970 : Bounds (-8074657 / 1000000000) (-252333 / 31250000) (Real.log (247989464079 / 250000000000)) := by
  have h := reflection_log_3970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3971_neg : (35967827 / 200000000) ≤ -Real.log (100000000000 / 119702478903) ∧
    -Real.log (100000000000 / 119702478903) ≤ (5619973 / 31250000) := by
  have h := checkLog_sound (w := (19702478903 / 219702478903)) (n := 12)
    (lo := (35967827 / 200000000)) (hi := (5619973 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119702478903 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119702478903 / 100000000000) = 1/(100000000000 / 119702478903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3971 : Bounds (35967827 / 200000000) (5619973 / 31250000) (Real.log (119702478903 / 100000000000)) := by
  have h := reflection_log_3971_neg
  have he : Real.log (119702478903 / 100000000000) = -Real.log (100000000000 / 119702478903) := by
    rw [show ((119702478903 / 100000000000) : ℝ) = ((100000000000 / 119702478903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3972_neg : (90151437 / 500000000) ≤ -Real.log (500000000000 / 598790012439) ∧
    -Real.log (500000000000 / 598790012439) ≤ (1442423 / 8000000) := by
  have h := checkLog_sound (w := (98790012439 / 1098790012439)) (n := 12)
    (lo := (90151437 / 500000000)) (hi := (1442423 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598790012439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598790012439 / 500000000000) = 1/(500000000000 / 598790012439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3972 : Bounds (90151437 / 500000000) (1442423 / 8000000) (Real.log (598790012439 / 500000000000)) := by
  have h := reflection_log_3972_neg
  have he : Real.log (598790012439 / 500000000000) = -Real.log (500000000000 / 598790012439) := by
    rw [show ((598790012439 / 500000000000) : ℝ) = ((500000000000 / 598790012439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3973_neg : (45108223 / 125000000) ≤ -Real.log (250000000000 / 358642726719) ∧
    -Real.log (250000000000 / 358642726719) ≤ (72173157 / 200000000) := by
  have h := checkLog_sound (w := (108642726719 / 608642726719)) (n := 12)
    (lo := (45108223 / 125000000)) (hi := (72173157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358642726719 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358642726719 / 250000000000) = 1/(250000000000 / 358642726719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3973 : Bounds (45108223 / 125000000) (72173157 / 200000000) (Real.log (358642726719 / 250000000000)) := by
  have h := reflection_log_3973_neg
  have he : Real.log (358642726719 / 250000000000) = -Real.log (250000000000 / 358642726719) := by
    rw [show ((358642726719 / 250000000000) : ℝ) = ((250000000000 / 358642726719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3974_neg : (36107237 / 100000000) ≤ -Real.log (500000000000 / 717433649867) ∧
    -Real.log (500000000000 / 717433649867) ≤ (361072371 / 1000000000) := by
  have h := checkLog_sound (w := (217433649867 / 1217433649867)) (n := 12)
    (lo := (36107237 / 100000000)) (hi := (361072371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717433649867 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717433649867 / 500000000000) = 1/(500000000000 / 717433649867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3974 : Bounds (36107237 / 100000000) (361072371 / 1000000000) (Real.log (717433649867 / 500000000000)) := by
  have h := reflection_log_3974_neg
  have he : Real.log (717433649867 / 500000000000) = -Real.log (500000000000 / 717433649867) := by
    rw [show ((717433649867 / 500000000000) : ℝ) = ((500000000000 / 717433649867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3975_neg : (20551517 / 125000000) ≤ -Real.log (10000 / 11787) ∧
    -Real.log (10000 / 11787) ≤ (164412137 / 1000000000) := by
  have h := checkLog_sound (w := (1787 / 21787)) (n := 12)
    (lo := (20551517 / 125000000)) (hi := (164412137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11787 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11787 / 10000) = 1/(10000 / 11787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3975 : Bounds (20551517 / 125000000) (164412137 / 1000000000) (Real.log (11787 / 10000)) := by
  have h := reflection_log_3975_neg
  have he : Real.log (11787 / 10000) = -Real.log (10000 / 11787) := by
    rw [show ((11787 / 10000) : ℝ) = ((10000 / 11787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3976_neg : (49216707 / 250000000) ≤ -Real.log (8213 / 10000) ∧
    -Real.log (8213 / 10000) ≤ (196866829 / 1000000000) := by
  have h := checkLog_sound (w := (1787 / 18213)) (n := 12)
    (lo := (49216707 / 250000000)) (hi := (196866829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8213) = 1/(8213 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3976 : Bounds (-196866829 / 1000000000) (-49216707 / 250000000) (Real.log (8213 / 10000)) := by
  have h := reflection_log_3976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3977_neg : (44671 / 250000000) ≤ -Real.log (10000000 / 10001787) ∧
    -Real.log (10000000 / 10001787) ≤ (35737 / 200000000) := by
  have h := checkLog_sound (w := (1787 / 20001787)) (n := 12)
    (lo := (44671 / 250000000)) (hi := (35737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001787 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001787 / 10000000) = 1/(10000000 / 10001787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3977 : Bounds (44671 / 250000000) (35737 / 200000000) (Real.log (10001787 / 10000000)) := by
  have h := reflection_log_3977_neg
  have he : Real.log (10001787 / 10000000) = -Real.log (10000000 / 10001787) := by
    rw [show ((10001787 / 10000000) : ℝ) = ((10000000 / 10001787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3978_neg : (35743 / 200000000) ≤ -Real.log (9998213 / 10000000) ∧
    -Real.log (9998213 / 10000000) ≤ (44679 / 250000000) := by
  have h := checkLog_sound (w := (1787 / 19998213)) (n := 12)
    (lo := (35743 / 200000000)) (hi := (44679 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998213) = 1/(9998213 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3978 : Bounds (-44679 / 250000000) (-35743 / 200000000) (Real.log (9998213 / 10000000)) := by
  have h := reflection_log_3978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3979_neg : (85929041 / 1000000000) ≤ -Real.log (1000000 / 1089729) ∧
    -Real.log (1000000 / 1089729) ≤ (42964521 / 500000000) := by
  have h := checkLog_sound (w := (89729 / 2089729)) (n := 12)
    (lo := (85929041 / 1000000000)) (hi := (42964521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089729 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089729 / 1000000) = 1/(1000000 / 1089729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3979 : Bounds (85929041 / 1000000000) (42964521 / 500000000) (Real.log (1089729 / 1000000)) := by
  have h := reflection_log_3979_neg
  have he : Real.log (1089729 / 1000000) = -Real.log (1000000 / 1089729) := by
    rw [show ((1089729 / 1000000) : ℝ) = ((1000000 / 1089729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3980_neg : (94012921 / 1000000000) ≤ -Real.log (910271 / 1000000) ∧
    -Real.log (910271 / 1000000) ≤ (47006461 / 500000000) := by
  have h := checkLog_sound (w := (89729 / 1910271)) (n := 12)
    (lo := (94012921 / 1000000000)) (hi := (47006461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910271) = 1/(910271 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3980 : Bounds (-47006461 / 500000000) (-94012921 / 1000000000) (Real.log (910271 / 1000000)) := by
  have h := reflection_log_3980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3981_neg : (1076751 / 12500000) ≤ -Real.log (1000000 / 1089959) ∧
    -Real.log (1000000 / 1089959) ≤ (86140081 / 1000000000) := by
  have h := checkLog_sound (w := (89959 / 2089959)) (n := 12)
    (lo := (1076751 / 12500000)) (hi := (86140081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089959 / 1000000) = 1/(1000000 / 1089959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3981 : Bounds (1076751 / 12500000) (86140081 / 1000000000) (Real.log (1089959 / 1000000)) := by
  have h := reflection_log_3981_neg
  have he : Real.log (1089959 / 1000000) = -Real.log (1000000 / 1089959) := by
    rw [show ((1089959 / 1000000) : ℝ) = ((1000000 / 1089959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3982_neg : (6033 / 64000) ≤ -Real.log (910041 / 1000000) ∧
    -Real.log (910041 / 1000000) ≤ (47132813 / 500000000) := by
  have h := checkLog_sound (w := (89959 / 1910041)) (n := 12)
    (lo := (6033 / 64000)) (hi := (47132813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910041) = 1/(910041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3982 : Bounds (-47132813 / 500000000) (-6033 / 64000) (Real.log (910041 / 1000000)) := by
  have h := reflection_log_3982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3983_neg : (1015693 / 125000000) ≤ -Real.log (991907378319 / 1000000000000) ∧
    -Real.log (991907378319 / 1000000000000) ≤ (1625109 / 200000000) := by
  have h := checkLog_sound (w := (8092621681 / 1991907378319)) (n := 12)
    (lo := (1015693 / 125000000)) (hi := (1625109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991907378319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991907378319) = 1/(991907378319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3983 : Bounds (-1625109 / 200000000) (-1015693 / 125000000) (Real.log (991907378319 / 1000000000000)) := by
  have h := reflection_log_3983_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3984_neg : (202097 / 25000000) ≤ -Real.log (991948706559 / 1000000000000) ∧
    -Real.log (991948706559 / 1000000000000) ≤ (8083881 / 1000000000) := by
  have h := checkLog_sound (w := (8051293441 / 1991948706559)) (n := 12)
    (lo := (202097 / 25000000)) (hi := (8083881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991948706559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991948706559) = 1/(991948706559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3984 : Bounds (-8083881 / 1000000000) (-202097 / 25000000) (Real.log (991948706559 / 1000000000000)) := by
  have h := reflection_log_3984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3985_neg : (179941963 / 1000000000) ≤ -Real.log (250000000000 / 299286970583) ∧
    -Real.log (250000000000 / 299286970583) ≤ (44985491 / 250000000) := by
  have h := checkLog_sound (w := (49286970583 / 549286970583)) (n := 12)
    (lo := (179941963 / 1000000000)) (hi := (44985491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299286970583 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299286970583 / 250000000000) = 1/(250000000000 / 299286970583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3985 : Bounds (179941963 / 1000000000) (44985491 / 250000000) (Real.log (299286970583 / 250000000000)) := by
  have h := reflection_log_3985_neg
  have he : Real.log (299286970583 / 250000000000) = -Real.log (250000000000 / 299286970583) := by
    rw [show ((299286970583 / 250000000000) : ℝ) = ((250000000000 / 299286970583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3986_neg : (90202853 / 500000000) ≤ -Real.log (125000000000 / 149712897551) ∧
    -Real.log (125000000000 / 149712897551) ≤ (180405707 / 1000000000) := by
  have h := checkLog_sound (w := (24712897551 / 274712897551)) (n := 12)
    (lo := (90202853 / 500000000)) (hi := (180405707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149712897551 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149712897551 / 125000000000) = 1/(125000000000 / 149712897551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3986 : Bounds (90202853 / 500000000) (180405707 / 1000000000) (Real.log (149712897551 / 125000000000)) := by
  have h := reflection_log_3986_neg
  have he : Real.log (149712897551 / 125000000000) = -Real.log (125000000000 / 149712897551) := by
    rw [show ((149712897551 / 125000000000) : ℝ) = ((125000000000 / 149712897551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3987_neg : (36107237 / 100000000) ≤ -Real.log (250000000000 / 358716824933) ∧
    -Real.log (250000000000 / 358716824933) ≤ (361072371 / 1000000000) := by
  have h := checkLog_sound (w := (108716824933 / 608716824933)) (n := 12)
    (lo := (36107237 / 100000000)) (hi := (361072371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358716824933 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358716824933 / 250000000000) = 1/(250000000000 / 358716824933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3987 : Bounds (36107237 / 100000000) (361072371 / 1000000000) (Real.log (358716824933 / 250000000000)) := by
  have h := reflection_log_3987_neg
  have he : Real.log (358716824933 / 250000000000) = -Real.log (250000000000 / 358716824933) := by
    rw [show ((358716824933 / 250000000000) : ℝ) = ((250000000000 / 358716824933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3988_neg : (90319741 / 250000000) ≤ -Real.log (250000000000 / 358790941191) ∧
    -Real.log (250000000000 / 358790941191) ≤ (72255793 / 200000000) := by
  have h := checkLog_sound (w := (108790941191 / 608790941191)) (n := 12)
    (lo := (90319741 / 250000000)) (hi := (72255793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358790941191 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358790941191 / 250000000000) = 1/(250000000000 / 358790941191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3988 : Bounds (90319741 / 250000000) (72255793 / 200000000) (Real.log (358790941191 / 250000000000)) := by
  have h := reflection_log_3988_neg
  have he : Real.log (358790941191 / 250000000000) = -Real.log (250000000000 / 358790941191) := by
    rw [show ((358790941191 / 250000000000) : ℝ) = ((250000000000 / 358790941191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3989_neg : (164496971 / 1000000000) ≤ -Real.log (2500 / 2947) ∧
    -Real.log (2500 / 2947) ≤ (41124243 / 250000000) := by
  have h := checkLog_sound (w := (447 / 5447)) (n := 12)
    (lo := (164496971 / 1000000000)) (hi := (41124243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2947 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2947 / 2500) = 1/(2500 / 2947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3989 : Bounds (164496971 / 1000000000) (41124243 / 250000000) (Real.log (2947 / 2500)) := by
  have h := reflection_log_3989_neg
  have he : Real.log (2947 / 2500) = -Real.log (2500 / 2947) := by
    rw [show ((2947 / 2500) : ℝ) = ((2500 / 2947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3990_neg : (196988593 / 1000000000) ≤ -Real.log (2053 / 2500) ∧
    -Real.log (2053 / 2500) ≤ (98494297 / 500000000) := by
  have h := checkLog_sound (w := (447 / 4553)) (n := 12)
    (lo := (196988593 / 1000000000)) (hi := (98494297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2053) = 1/(2053 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3990 : Bounds (-98494297 / 500000000) (-196988593 / 1000000000) (Real.log (2053 / 2500)) := by
  have h := reflection_log_3990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3991_neg : (5587 / 31250000) ≤ -Real.log (2500000 / 2500447) ∧
    -Real.log (2500000 / 2500447) ≤ (35757 / 200000000) := by
  have h := checkLog_sound (w := (447 / 5000447)) (n := 12)
    (lo := (5587 / 31250000)) (hi := (35757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500447 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500447 / 2500000) = 1/(2500000 / 2500447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3991 : Bounds (5587 / 31250000) (35757 / 200000000) (Real.log (2500447 / 2500000)) := by
  have h := reflection_log_3991_neg
  have he : Real.log (2500447 / 2500000) = -Real.log (2500000 / 2500447) := by
    rw [show ((2500447 / 2500000) : ℝ) = ((2500000 / 2500447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3992_neg : (35763 / 200000000) ≤ -Real.log (2499553 / 2500000) ∧
    -Real.log (2499553 / 2500000) ≤ (1397 / 7812500) := by
  have h := checkLog_sound (w := (447 / 4999553)) (n := 12)
    (lo := (35763 / 200000000)) (hi := (1397 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499553) = 1/(2499553 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3992 : Bounds (-1397 / 7812500) (-35763 / 200000000) (Real.log (2499553 / 2500000)) := by
  have h := reflection_log_3992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3993_neg : (85975841 / 1000000000) ≤ -Real.log (50000 / 54489) ∧
    -Real.log (50000 / 54489) ≤ (42987921 / 500000000) := by
  have h := checkLog_sound (w := (4489 / 104489)) (n := 12)
    (lo := (85975841 / 1000000000)) (hi := (42987921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54489 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54489 / 50000) = 1/(50000 / 54489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3993 : Bounds (85975841 / 1000000000) (42987921 / 500000000) (Real.log (54489 / 50000)) := by
  have h := reflection_log_3993_neg
  have he : Real.log (54489 / 50000) = -Real.log (50000 / 54489) := by
    rw [show ((54489 / 50000) : ℝ) = ((50000 / 54489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3994_neg : (1881379 / 20000000) ≤ -Real.log (45511 / 50000) ∧
    -Real.log (45511 / 50000) ≤ (94068951 / 1000000000) := by
  have h := checkLog_sound (w := (4489 / 95511)) (n := 12)
    (lo := (1881379 / 20000000)) (hi := (94068951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45511) = 1/(45511 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3994 : Bounds (-94068951 / 1000000000) (-1881379 / 20000000) (Real.log (45511 / 50000)) := by
  have h := reflection_log_3994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3995_neg : (8618687 / 100000000) ≤ -Real.log (100000 / 109001) ∧
    -Real.log (100000 / 109001) ≤ (86186871 / 1000000000) := by
  have h := checkLog_sound (w := (9001 / 209001)) (n := 12)
    (lo := (8618687 / 100000000)) (hi := (86186871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109001 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109001 / 100000) = 1/(100000 / 109001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3995 : Bounds (8618687 / 100000000) (86186871 / 1000000000) (Real.log (109001 / 100000)) := by
  have h := reflection_log_3995_neg
  have he : Real.log (109001 / 100000) = -Real.log (100000 / 109001) := by
    rw [show ((109001 / 100000) : ℝ) = ((100000 / 109001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3996_neg : (23580417 / 250000000) ≤ -Real.log (90999 / 100000) ∧
    -Real.log (90999 / 100000) ≤ (94321669 / 1000000000) := by
  have h := checkLog_sound (w := (9001 / 190999)) (n := 12)
    (lo := (23580417 / 250000000)) (hi := (94321669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90999) = 1/(90999 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3996 : Bounds (-94321669 / 1000000000) (-23580417 / 250000000) (Real.log (90999 / 100000)) := by
  have h := reflection_log_3996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3997_neg : (4067399 / 500000000) ≤ -Real.log (9918981999 / 10000000000) ∧
    -Real.log (9918981999 / 10000000000) ≤ (8134799 / 1000000000) := by
  have h := checkLog_sound (w := (81018001 / 19918981999)) (n := 12)
    (lo := (4067399 / 500000000)) (hi := (8134799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9918981999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9918981999) = 1/(9918981999 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3997 : Bounds (-8134799 / 1000000000) (-4067399 / 500000000) (Real.log (9918981999 / 10000000000)) := by
  have h := reflection_log_3997_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3998_neg : (8093109 / 1000000000) ≤ -Real.log (2479848879 / 2500000000) ∧
    -Real.log (2479848879 / 2500000000) ≤ (809311 / 100000000) := by
  have h := checkLog_sound (w := (20151121 / 4979848879)) (n := 12)
    (lo := (8093109 / 1000000000)) (hi := (809311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2479848879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2479848879) = 1/(2479848879 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3998 : Bounds (-809311 / 100000000) (-8093109 / 1000000000) (Real.log (2479848879 / 2500000000)) := by
  have h := reflection_log_3998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3999_neg : (180044791 / 1000000000) ≤ -Real.log (100000000000 / 119727098943) ∧
    -Real.log (100000000000 / 119727098943) ≤ (22505599 / 125000000) := by
  have h := checkLog_sound (w := (19727098943 / 219727098943)) (n := 12)
    (lo := (180044791 / 1000000000)) (hi := (22505599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119727098943 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119727098943 / 100000000000) = 1/(100000000000 / 119727098943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3999 : Bounds (180044791 / 1000000000) (22505599 / 125000000) (Real.log (119727098943 / 100000000000)) := by
  have h := reflection_log_3999_neg
  have he : Real.log (119727098943 / 100000000000) = -Real.log (100000000000 / 119727098943) := by
    rw [show ((119727098943 / 100000000000) : ℝ) = ((100000000000 / 119727098943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4000_neg : (180508539 / 1000000000) ≤ -Real.log (500000000000 / 598913174871) ∧
    -Real.log (500000000000 / 598913174871) ≤ (9025427 / 50000000) := by
  have h := checkLog_sound (w := (98913174871 / 1098913174871)) (n := 12)
    (lo := (180508539 / 1000000000)) (hi := (9025427 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598913174871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598913174871 / 500000000000) = 1/(500000000000 / 598913174871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4000 : Bounds (180508539 / 1000000000) (9025427 / 50000000) (Real.log (598913174871 / 500000000000)) := by
  have h := reflection_log_4000_neg
  have he : Real.log (598913174871 / 500000000000) = -Real.log (500000000000 / 598913174871) := by
    rw [show ((598913174871 / 500000000000) : ℝ) = ((500000000000 / 598913174871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4001_neg : (90319741 / 250000000) ≤ -Real.log (500000000000 / 717581882381) ∧
    -Real.log (500000000000 / 717581882381) ≤ (72255793 / 200000000) := by
  have h := checkLog_sound (w := (217581882381 / 1217581882381)) (n := 12)
    (lo := (90319741 / 250000000)) (hi := (72255793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717581882381 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717581882381 / 500000000000) = 1/(500000000000 / 717581882381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4001 : Bounds (90319741 / 250000000) (72255793 / 200000000) (Real.log (717581882381 / 500000000000)) := by
  have h := reflection_log_4001_neg
  have he : Real.log (717581882381 / 500000000000) = -Real.log (500000000000 / 717581882381) := by
    rw [show ((717581882381 / 500000000000) : ℝ) = ((500000000000 / 717581882381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4002_neg : (72297113 / 200000000) ≤ -Real.log (500000000000 / 717730150999) ∧
    -Real.log (500000000000 / 717730150999) ≤ (180742783 / 500000000) := by
  have h := checkLog_sound (w := (217730150999 / 1217730150999)) (n := 12)
    (lo := (72297113 / 200000000)) (hi := (180742783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717730150999 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717730150999 / 500000000000) = 1/(500000000000 / 717730150999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4002 : Bounds (72297113 / 200000000) (180742783 / 500000000) (Real.log (717730150999 / 500000000000)) := by
  have h := reflection_log_4002_neg
  have he : Real.log (717730150999 / 500000000000) = -Real.log (500000000000 / 717730150999) := by
    rw [show ((717730150999 / 500000000000) : ℝ) = ((500000000000 / 717730150999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4003_neg : (822909 / 5000000) ≤ -Real.log (10000 / 11789) ∧
    -Real.log (10000 / 11789) ≤ (164581801 / 1000000000) := by
  have h := checkLog_sound (w := (1789 / 21789)) (n := 12)
    (lo := (822909 / 5000000)) (hi := (164581801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11789 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11789 / 10000) = 1/(10000 / 11789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4003 : Bounds (822909 / 5000000) (164581801 / 1000000000) (Real.log (11789 / 10000)) := by
  have h := reflection_log_4003_neg
  have he : Real.log (11789 / 10000) = -Real.log (10000 / 11789) := by
    rw [show ((11789 / 10000) : ℝ) = ((10000 / 11789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4004_neg : (98555187 / 500000000) ≤ -Real.log (8211 / 10000) ∧
    -Real.log (8211 / 10000) ≤ (1576883 / 8000000) := by
  have h := checkLog_sound (w := (1789 / 18211)) (n := 12)
    (lo := (98555187 / 500000000)) (hi := (1576883 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8211) = 1/(8211 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4004 : Bounds (-1576883 / 8000000) (-98555187 / 500000000) (Real.log (8211 / 10000)) := by
  have h := reflection_log_4004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4005_neg : (178883 / 1000000000) ≤ -Real.log (10000000 / 10001789) ∧
    -Real.log (10000000 / 10001789) ≤ (44721 / 250000000) := by
  have h := checkLog_sound (w := (1789 / 20001789)) (n := 12)
    (lo := (178883 / 1000000000)) (hi := (44721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001789 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001789 / 10000000) = 1/(10000000 / 10001789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4005 : Bounds (178883 / 1000000000) (44721 / 250000000) (Real.log (10001789 / 10000000)) := by
  have h := reflection_log_4005_neg
  have he : Real.log (10001789 / 10000000) = -Real.log (10000000 / 10001789) := by
    rw [show ((10001789 / 10000000) : ℝ) = ((10000000 / 10001789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4006_neg : (44729 / 250000000) ≤ -Real.log (9998211 / 10000000) ∧
    -Real.log (9998211 / 10000000) ≤ (178917 / 1000000000) := by
  have h := checkLog_sound (w := (1789 / 19998211)) (n := 12)
    (lo := (44729 / 250000000)) (hi := (178917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998211) = 1/(9998211 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4006 : Bounds (-178917 / 1000000000) (-44729 / 250000000) (Real.log (9998211 / 10000000)) := by
  have h := reflection_log_4006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4007_neg : (43011319 / 500000000) ≤ -Real.log (1000000 / 1089831) ∧
    -Real.log (1000000 / 1089831) ≤ (86022639 / 1000000000) := by
  have h := checkLog_sound (w := (89831 / 2089831)) (n := 12)
    (lo := (43011319 / 500000000)) (hi := (86022639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089831 / 1000000) = 1/(1000000 / 1089831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4007 : Bounds (43011319 / 500000000) (86022639 / 1000000000) (Real.log (1089831 / 1000000)) := by
  have h := reflection_log_4007_neg
  have he : Real.log (1089831 / 1000000) = -Real.log (1000000 / 1089831) := by
    rw [show ((1089831 / 1000000) : ℝ) = ((1000000 / 1089831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4008_neg : (47062491 / 500000000) ≤ -Real.log (910169 / 1000000) ∧
    -Real.log (910169 / 1000000) ≤ (94124983 / 1000000000) := by
  have h := checkLog_sound (w := (89831 / 1910169)) (n := 12)
    (lo := (47062491 / 500000000)) (hi := (94124983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910169) = 1/(910169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4008 : Bounds (-94124983 / 1000000000) (-47062491 / 500000000) (Real.log (910169 / 1000000)) := by
  have h := reflection_log_4008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4009_neg : (86233657 / 1000000000) ≤ -Real.log (1000000 / 1090061) ∧
    -Real.log (1000000 / 1090061) ≤ (43116829 / 500000000) := by
  have h := checkLog_sound (w := (90061 / 2090061)) (n := 12)
    (lo := (86233657 / 1000000000)) (hi := (43116829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090061 / 1000000) = 1/(1000000 / 1090061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4009 : Bounds (86233657 / 1000000000) (43116829 / 500000000) (Real.log (1090061 / 1000000)) := by
  have h := reflection_log_4009_neg
  have he : Real.log (1090061 / 1000000) = -Real.log (1000000 / 1090061) := by
    rw [show ((1090061 / 1000000) : ℝ) = ((1000000 / 1090061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4010_neg : (47188857 / 500000000) ≤ -Real.log (909939 / 1000000) ∧
    -Real.log (909939 / 1000000) ≤ (18875543 / 200000000) := by
  have h := checkLog_sound (w := (90061 / 1909939)) (n := 12)
    (lo := (47188857 / 500000000)) (hi := (18875543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909939) = 1/(909939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4010 : Bounds (-18875543 / 200000000) (-47188857 / 500000000) (Real.log (909939 / 1000000)) := by
  have h := reflection_log_4010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4011_neg : (1018007 / 125000000) ≤ -Real.log (991889016279 / 1000000000000) ∧
    -Real.log (991889016279 / 1000000000000) ≤ (8144057 / 1000000000) := by
  have h := checkLog_sound (w := (8110983721 / 1991889016279)) (n := 12)
    (lo := (1018007 / 125000000)) (hi := (8144057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991889016279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991889016279) = 1/(991889016279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4011 : Bounds (-8144057 / 1000000000) (-1018007 / 125000000) (Real.log (991889016279 / 1000000000000)) := by
  have h := reflection_log_4011_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4012_neg : (1012793 / 125000000) ≤ -Real.log (991930391439 / 1000000000000) ∧
    -Real.log (991930391439 / 1000000000000) ≤ (1620469 / 200000000) := by
  have h := checkLog_sound (w := (8069608561 / 1991930391439)) (n := 12)
    (lo := (1012793 / 125000000)) (hi := (1620469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991930391439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991930391439) = 1/(991930391439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4012 : Bounds (-1620469 / 200000000) (-1012793 / 125000000) (Real.log (991930391439 / 1000000000000)) := by
  have h := reflection_log_4012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4013_neg : (9007381 / 50000000) ≤ -Real.log (250000000000 / 299348527581) ∧
    -Real.log (250000000000 / 299348527581) ≤ (180147621 / 1000000000) := by
  have h := checkLog_sound (w := (49348527581 / 549348527581)) (n := 12)
    (lo := (9007381 / 50000000)) (hi := (180147621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299348527581 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299348527581 / 250000000000) = 1/(250000000000 / 299348527581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4013 : Bounds (9007381 / 50000000) (180147621 / 1000000000) (Real.log (299348527581 / 250000000000)) := by
  have h := reflection_log_4013_neg
  have he : Real.log (299348527581 / 250000000000) = -Real.log (250000000000 / 299348527581) := by
    rw [show ((299348527581 / 250000000000) : ℝ) = ((250000000000 / 299348527581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4014_neg : (45152843 / 250000000) ≤ -Real.log (500000000000 / 598974766441) ∧
    -Real.log (500000000000 / 598974766441) ≤ (180611373 / 1000000000) := by
  have h := checkLog_sound (w := (98974766441 / 1098974766441)) (n := 12)
    (lo := (45152843 / 250000000)) (hi := (180611373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598974766441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598974766441 / 500000000000) = 1/(500000000000 / 598974766441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4014 : Bounds (45152843 / 250000000) (180611373 / 1000000000) (Real.log (598974766441 / 500000000000)) := by
  have h := reflection_log_4014_neg
  have he : Real.log (598974766441 / 500000000000) = -Real.log (500000000000 / 598974766441) := by
    rw [show ((598974766441 / 500000000000) : ℝ) = ((500000000000 / 598974766441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4015_neg : (72297113 / 200000000) ≤ -Real.log (250000000000 / 358865075499) ∧
    -Real.log (250000000000 / 358865075499) ≤ (180742783 / 500000000) := by
  have h := checkLog_sound (w := (108865075499 / 608865075499)) (n := 12)
    (lo := (72297113 / 200000000)) (hi := (180742783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358865075499 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358865075499 / 250000000000) = 1/(250000000000 / 358865075499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4015 : Bounds (72297113 / 200000000) (180742783 / 500000000) (Real.log (358865075499 / 250000000000)) := by
  have h := reflection_log_4015_neg
  have he : Real.log (358865075499 / 250000000000) = -Real.log (250000000000 / 358865075499) := by
    rw [show ((358865075499 / 250000000000) : ℝ) = ((250000000000 / 358865075499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4016_neg : (180846087 / 500000000) ≤ -Real.log (500000000000 / 717878455731) ∧
    -Real.log (500000000000 / 717878455731) ≤ (14467687 / 40000000) := by
  have h := checkLog_sound (w := (217878455731 / 1217878455731)) (n := 12)
    (lo := (180846087 / 500000000)) (hi := (14467687 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717878455731 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717878455731 / 500000000000) = 1/(500000000000 / 717878455731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4016 : Bounds (180846087 / 500000000) (14467687 / 40000000) (Real.log (717878455731 / 500000000000)) := by
  have h := reflection_log_4016_neg
  have he : Real.log (717878455731 / 500000000000) = -Real.log (500000000000 / 717878455731) := by
    rw [show ((717878455731 / 500000000000) : ℝ) = ((500000000000 / 717878455731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4017_neg : (164666621 / 1000000000) ≤ -Real.log (1000 / 1179) ∧
    -Real.log (1000 / 1179) ≤ (82333311 / 500000000) := by
  have h := checkLog_sound (w := (179 / 2179)) (n := 12)
    (lo := (164666621 / 1000000000)) (hi := (82333311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179 / 1000) = 1/(1000 / 1179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4017 : Bounds (164666621 / 1000000000) (82333311 / 500000000) (Real.log (1179 / 1000)) := by
  have h := reflection_log_4017_neg
  have he : Real.log (1179 / 1000) = -Real.log (1000 / 1179) := by
    rw [show ((1179 / 1000) : ℝ) = ((1000 / 1179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4018_neg : (197232169 / 1000000000) ≤ -Real.log (821 / 1000) ∧
    -Real.log (821 / 1000) ≤ (19723217 / 100000000) := by
  have h := checkLog_sound (w := (179 / 1821)) (n := 12)
    (lo := (197232169 / 1000000000)) (hi := (19723217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 821) = 1/(821 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4018 : Bounds (-19723217 / 100000000) (-197232169 / 1000000000) (Real.log (821 / 1000)) := by
  have h := reflection_log_4018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4019_neg : (178983 / 1000000000) ≤ -Real.log (1000000 / 1000179) ∧
    -Real.log (1000000 / 1000179) ≤ (22373 / 125000000) := by
  have h := checkLog_sound (w := (179 / 2000179)) (n := 12)
    (lo := (178983 / 1000000000)) (hi := (22373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000179 / 1000000) = 1/(1000000 / 1000179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4019 : Bounds (178983 / 1000000000) (22373 / 125000000) (Real.log (1000179 / 1000000)) := by
  have h := reflection_log_4019_neg
  have he : Real.log (1000179 / 1000000) = -Real.log (1000000 / 1000179) := by
    rw [show ((1000179 / 1000000) : ℝ) = ((1000000 / 1000179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4020_neg : (22377 / 125000000) ≤ -Real.log (999821 / 1000000) ∧
    -Real.log (999821 / 1000000) ≤ (179017 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 1999821)) (n := 12)
    (lo := (22377 / 125000000)) (hi := (179017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999821) = 1/(999821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4020 : Bounds (-179017 / 1000000000) (-22377 / 125000000) (Real.log (999821 / 1000000)) := by
  have h := reflection_log_4020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4021_neg : (86069433 / 1000000000) ≤ -Real.log (500000 / 544941) ∧
    -Real.log (500000 / 544941) ≤ (43034717 / 500000000) := by
  have h := checkLog_sound (w := (44941 / 1044941)) (n := 12)
    (lo := (86069433 / 1000000000)) (hi := (43034717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544941 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544941 / 500000) = 1/(500000 / 544941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4021 : Bounds (86069433 / 1000000000) (43034717 / 500000000) (Real.log (544941 / 500000)) := by
  have h := reflection_log_4021_neg
  have he : Real.log (544941 / 500000) = -Real.log (500000 / 544941) := by
    rw [show ((544941 / 500000) : ℝ) = ((500000 / 544941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4022_neg : (94181017 / 1000000000) ≤ -Real.log (455059 / 500000) ∧
    -Real.log (455059 / 500000) ≤ (47090509 / 500000000) := by
  have h := checkLog_sound (w := (44941 / 955059)) (n := 12)
    (lo := (94181017 / 1000000000)) (hi := (47090509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455059) = 1/(455059 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4022 : Bounds (-47090509 / 500000000) (-94181017 / 1000000000) (Real.log (455059 / 500000)) := by
  have h := reflection_log_4022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4023_neg : (86280443 / 1000000000) ≤ -Real.log (15625 / 17033) ∧
    -Real.log (15625 / 17033) ≤ (21570111 / 250000000) := by
  have h := checkLog_sound (w := (704 / 16329)) (n := 12)
    (lo := (86280443 / 1000000000)) (hi := (21570111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17033 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17033 / 15625) = 1/(15625 / 17033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4023 : Bounds (86280443 / 1000000000) (21570111 / 250000000) (Real.log (17033 / 15625)) := by
  have h := reflection_log_4023_neg
  have he : Real.log (17033 / 15625) = -Real.log (15625 / 17033) := by
    rw [show ((17033 / 15625) : ℝ) = ((15625 / 17033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4024_neg : (94433763 / 1000000000) ≤ -Real.log (14217 / 15625) ∧
    -Real.log (14217 / 15625) ≤ (23608441 / 250000000) := by
  have h := checkLog_sound (w := (704 / 14921)) (n := 12)
    (lo := (94433763 / 1000000000)) (hi := (23608441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14217) = 1/(14217 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4024 : Bounds (-23608441 / 250000000) (-94433763 / 1000000000) (Real.log (14217 / 15625)) := by
  have h := reflection_log_4024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4025_neg : (203833 / 25000000) ≤ -Real.log (242158161 / 244140625) ∧
    -Real.log (242158161 / 244140625) ≤ (8153321 / 1000000000) := by
  have h := checkLog_sound (w := (991232 / 243149393)) (n := 12)
    (lo := (203833 / 25000000)) (hi := (8153321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242158161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242158161) = 1/(242158161 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4025 : Bounds (-8153321 / 1000000000) (-203833 / 25000000) (Real.log (242158161 / 244140625)) := by
  have h := reflection_log_4025_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4026_neg : (253487 / 31250000) ≤ -Real.log (247980306519 / 250000000000) ∧
    -Real.log (247980306519 / 250000000000) ≤ (1622317 / 200000000) := by
  have h := checkLog_sound (w := (2019693481 / 497980306519)) (n := 12)
    (lo := (253487 / 31250000)) (hi := (1622317 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247980306519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247980306519) = 1/(247980306519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4026 : Bounds (-1622317 / 200000000) (-253487 / 31250000) (Real.log (247980306519 / 250000000000)) := by
  have h := reflection_log_4026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4027_neg : (180250451 / 1000000000) ≤ -Real.log (125000000000 / 149689655627) ∧
    -Real.log (125000000000 / 149689655627) ≤ (45062613 / 250000000) := by
  have h := checkLog_sound (w := (24689655627 / 274689655627)) (n := 12)
    (lo := (180250451 / 1000000000)) (hi := (45062613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149689655627 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149689655627 / 125000000000) = 1/(125000000000 / 149689655627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4027 : Bounds (180250451 / 1000000000) (45062613 / 250000000) (Real.log (149689655627 / 125000000000)) := by
  have h := reflection_log_4027_neg
  have he : Real.log (149689655627 / 125000000000) = -Real.log (125000000000 / 149689655627) := by
    rw [show ((149689655627 / 125000000000) : ℝ) = ((125000000000 / 149689655627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4028_neg : (180714207 / 1000000000) ≤ -Real.log (125000000000 / 149759091229) ∧
    -Real.log (125000000000 / 149759091229) ≤ (5647319 / 31250000) := by
  have h := checkLog_sound (w := (24759091229 / 274759091229)) (n := 12)
    (lo := (180714207 / 1000000000)) (hi := (5647319 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149759091229 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149759091229 / 125000000000) = 1/(125000000000 / 149759091229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4028 : Bounds (180714207 / 1000000000) (5647319 / 31250000) (Real.log (149759091229 / 125000000000)) := by
  have h := reflection_log_4028_neg
  have he : Real.log (149759091229 / 125000000000) = -Real.log (125000000000 / 149759091229) := by
    rw [show ((149759091229 / 125000000000) : ℝ) = ((125000000000 / 149759091229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4029_neg : (180846087 / 500000000) ≤ -Real.log (50000000000 / 71787845573) ∧
    -Real.log (50000000000 / 71787845573) ≤ (14467687 / 40000000) := by
  have h := checkLog_sound (w := (21787845573 / 121787845573)) (n := 12)
    (lo := (180846087 / 500000000)) (hi := (14467687 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71787845573 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71787845573 / 50000000000) = 1/(50000000000 / 71787845573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4029 : Bounds (180846087 / 500000000) (14467687 / 40000000) (Real.log (71787845573 / 50000000000)) := by
  have h := reflection_log_4029_neg
  have he : Real.log (71787845573 / 50000000000) = -Real.log (50000000000 / 71787845573) := by
    rw [show ((71787845573 / 50000000000) : ℝ) = ((50000000000 / 71787845573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4030_neg : (361898791 / 1000000000) ≤ -Real.log (50000000000 / 71802679659) ∧
    -Real.log (50000000000 / 71802679659) ≤ (45237349 / 125000000) := by
  have h := checkLog_sound (w := (21802679659 / 121802679659)) (n := 12)
    (lo := (361898791 / 1000000000)) (hi := (45237349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71802679659 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71802679659 / 50000000000) = 1/(50000000000 / 71802679659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4030 : Bounds (361898791 / 1000000000) (45237349 / 125000000) (Real.log (71802679659 / 50000000000)) := by
  have h := reflection_log_4030_neg
  have he : Real.log (71802679659 / 50000000000) = -Real.log (50000000000 / 71802679659) := by
    rw [show ((71802679659 / 50000000000) : ℝ) = ((50000000000 / 71802679659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4031_neg : (32950287 / 200000000) ≤ -Real.log (10000 / 11791) ∧
    -Real.log (10000 / 11791) ≤ (41187859 / 250000000) := by
  have h := checkLog_sound (w := (1791 / 21791)) (n := 12)
    (lo := (32950287 / 200000000)) (hi := (41187859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11791 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11791 / 10000) = 1/(10000 / 11791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4031 : Bounds (32950287 / 200000000) (41187859 / 250000000) (Real.log (11791 / 10000)) := by
  have h := reflection_log_4031_neg
  have he : Real.log (11791 / 10000) = -Real.log (10000 / 11791) := by
    rw [show ((11791 / 10000) : ℝ) = ((10000 / 11791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0063 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4032_neg : (197353979 / 1000000000) ≤ -Real.log (8209 / 10000) ∧
    -Real.log (8209 / 10000) ≤ (9867699 / 50000000) := by
  have h := checkLog_sound (w := (1791 / 18209)) (n := 12)
    (lo := (197353979 / 1000000000)) (hi := (9867699 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8209) = 1/(8209 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4032 : Bounds (-9867699 / 50000000) (-197353979 / 1000000000) (Real.log (8209 / 10000)) := by
  have h := reflection_log_4032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4033_neg : (179083 / 1000000000) ≤ -Real.log (10000000 / 10001791) ∧
    -Real.log (10000000 / 10001791) ≤ (44771 / 250000000) := by
  have h := checkLog_sound (w := (1791 / 20001791)) (n := 12)
    (lo := (179083 / 1000000000)) (hi := (44771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001791 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001791 / 10000000) = 1/(10000000 / 10001791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4033 : Bounds (179083 / 1000000000) (44771 / 250000000) (Real.log (10001791 / 10000000)) := by
  have h := reflection_log_4033_neg
  have he : Real.log (10001791 / 10000000) = -Real.log (10000000 / 10001791) := by
    rw [show ((10001791 / 10000000) : ℝ) = ((10000000 / 10001791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4034_neg : (44779 / 250000000) ≤ -Real.log (9998209 / 10000000) ∧
    -Real.log (9998209 / 10000000) ≤ (179117 / 1000000000) := by
  have h := checkLog_sound (w := (1791 / 19998209)) (n := 12)
    (lo := (44779 / 250000000)) (hi := (179117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998209) = 1/(9998209 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4034 : Bounds (-179117 / 1000000000) (-44779 / 250000000) (Real.log (9998209 / 10000000)) := by
  have h := reflection_log_4034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4035_neg : (43058113 / 500000000) ≤ -Real.log (1000000 / 1089933) ∧
    -Real.log (1000000 / 1089933) ≤ (86116227 / 1000000000) := by
  have h := checkLog_sound (w := (89933 / 2089933)) (n := 12)
    (lo := (43058113 / 500000000)) (hi := (86116227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089933 / 1000000) = 1/(1000000 / 1089933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4035 : Bounds (43058113 / 500000000) (86116227 / 1000000000) (Real.log (1089933 / 1000000)) := by
  have h := reflection_log_4035_neg
  have he : Real.log (1089933 / 1000000) = -Real.log (1000000 / 1089933) := by
    rw [show ((1089933 / 1000000) : ℝ) = ((1000000 / 1089933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4036_neg : (18847411 / 200000000) ≤ -Real.log (910067 / 1000000) ∧
    -Real.log (910067 / 1000000) ≤ (736227 / 7812500) := by
  have h := checkLog_sound (w := (89933 / 1910067)) (n := 12)
    (lo := (18847411 / 200000000)) (hi := (736227 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910067) = 1/(910067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4036 : Bounds (-736227 / 7812500) (-18847411 / 200000000) (Real.log (910067 / 1000000)) := by
  have h := reflection_log_4036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4037_neg : (86326309 / 1000000000) ≤ -Real.log (500000 / 545081) ∧
    -Real.log (500000 / 545081) ≤ (8632631 / 100000000) := by
  have h := checkLog_sound (w := (45081 / 1045081)) (n := 12)
    (lo := (86326309 / 1000000000)) (hi := (8632631 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545081 / 500000) = 1/(500000 / 545081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4037 : Bounds (86326309 / 1000000000) (8632631 / 100000000) (Real.log (545081 / 500000)) := by
  have h := reflection_log_4037_neg
  have he : Real.log (545081 / 500000) = -Real.log (500000 / 545081) := by
    rw [show ((545081 / 500000) : ℝ) = ((500000 / 545081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4038_neg : (94488717 / 1000000000) ≤ -Real.log (454919 / 500000) ∧
    -Real.log (454919 / 500000) ≤ (47244359 / 500000000) := by
  have h := checkLog_sound (w := (45081 / 954919)) (n := 12)
    (lo := (94488717 / 1000000000)) (hi := (47244359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454919) = 1/(454919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4038 : Bounds (-47244359 / 500000000) (-94488717 / 1000000000) (Real.log (454919 / 500000)) := by
  have h := reflection_log_4038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4039_neg : (1020301 / 125000000) ≤ -Real.log (247967703439 / 250000000000) ∧
    -Real.log (247967703439 / 250000000000) ≤ (8162409 / 1000000000) := by
  have h := checkLog_sound (w := (2032296561 / 497967703439)) (n := 12)
    (lo := (1020301 / 125000000)) (hi := (8162409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247967703439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247967703439) = 1/(247967703439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4039 : Bounds (-8162409 / 1000000000) (-1020301 / 125000000) (Real.log (247967703439 / 250000000000)) := by
  have h := reflection_log_4039_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4040_neg : (8120829 / 1000000000) ≤ -Real.log (991912055511 / 1000000000000) ∧
    -Real.log (991912055511 / 1000000000000) ≤ (812083 / 100000000) := by
  have h := checkLog_sound (w := (8087944489 / 1991912055511)) (n := 12)
    (lo := (8120829 / 1000000000)) (hi := (812083 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991912055511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991912055511) = 1/(991912055511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4040 : Bounds (-812083 / 100000000) (-8120829 / 1000000000) (Real.log (991912055511 / 1000000000000)) := by
  have h := reflection_log_4040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4041_neg : (90176641 / 500000000) ≤ -Real.log (250000000000 / 299410098377) ∧
    -Real.log (250000000000 / 299410098377) ≤ (180353283 / 1000000000) := by
  have h := checkLog_sound (w := (49410098377 / 549410098377)) (n := 12)
    (lo := (90176641 / 500000000)) (hi := (180353283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299410098377 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299410098377 / 250000000000) = 1/(250000000000 / 299410098377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4041 : Bounds (90176641 / 500000000) (180353283 / 1000000000) (Real.log (299410098377 / 250000000000)) := by
  have h := reflection_log_4041_neg
  have he : Real.log (299410098377 / 250000000000) = -Real.log (250000000000 / 299410098377) := by
    rw [show ((299410098377 / 250000000000) : ℝ) = ((250000000000 / 299410098377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4042_neg : (90407513 / 500000000) ≤ -Real.log (500000000000 / 599096762281) ∧
    -Real.log (500000000000 / 599096762281) ≤ (180815027 / 1000000000) := by
  have h := checkLog_sound (w := (99096762281 / 1099096762281)) (n := 12)
    (lo := (90407513 / 500000000)) (hi := (180815027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599096762281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599096762281 / 500000000000) = 1/(500000000000 / 599096762281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4042 : Bounds (90407513 / 500000000) (180815027 / 1000000000) (Real.log (599096762281 / 500000000000)) := by
  have h := reflection_log_4042_neg
  have he : Real.log (599096762281 / 500000000000) = -Real.log (500000000000 / 599096762281) := by
    rw [show ((599096762281 / 500000000000) : ℝ) = ((500000000000 / 599096762281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4043_neg : (361898791 / 1000000000) ≤ -Real.log (500000000000 / 718026796589) ∧
    -Real.log (500000000000 / 718026796589) ≤ (45237349 / 125000000) := by
  have h := checkLog_sound (w := (218026796589 / 1218026796589)) (n := 12)
    (lo := (361898791 / 1000000000)) (hi := (45237349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718026796589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718026796589 / 500000000000) = 1/(500000000000 / 718026796589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4043 : Bounds (361898791 / 1000000000) (45237349 / 125000000) (Real.log (718026796589 / 500000000000)) := by
  have h := reflection_log_4043_neg
  have he : Real.log (718026796589 / 500000000000) = -Real.log (500000000000 / 718026796589) := by
    rw [show ((718026796589 / 500000000000) : ℝ) = ((500000000000 / 718026796589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4044_neg : (72421083 / 200000000) ≤ -Real.log (50000000000 / 71817517359) ∧
    -Real.log (50000000000 / 71817517359) ≤ (45263177 / 125000000) := by
  have h := checkLog_sound (w := (21817517359 / 121817517359)) (n := 12)
    (lo := (72421083 / 200000000)) (hi := (45263177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71817517359 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71817517359 / 50000000000) = 1/(50000000000 / 71817517359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4044 : Bounds (72421083 / 200000000) (45263177 / 125000000) (Real.log (71817517359 / 50000000000)) := by
  have h := reflection_log_4044_neg
  have he : Real.log (71817517359 / 50000000000) = -Real.log (50000000000 / 71817517359) := by
    rw [show ((71817517359 / 50000000000) : ℝ) = ((50000000000 / 71817517359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4045_neg : (82418121 / 500000000) ≤ -Real.log (625 / 737) ∧
    -Real.log (625 / 737) ≤ (164836243 / 1000000000) := by
  have h := checkLog_sound (w := (56 / 681)) (n := 12)
    (lo := (82418121 / 500000000)) (hi := (164836243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737 / 625) = 1/(625 / 737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4045 : Bounds (82418121 / 500000000) (164836243 / 1000000000) (Real.log (737 / 625)) := by
  have h := reflection_log_4045_neg
  have he : Real.log (737 / 625) = -Real.log (625 / 737) := by
    rw [show ((737 / 625) : ℝ) = ((625 / 737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4046_neg : (49368951 / 250000000) ≤ -Real.log (513 / 625) ∧
    -Real.log (513 / 625) ≤ (39495161 / 200000000) := by
  have h := checkLog_sound (w := (56 / 569)) (n := 12)
    (lo := (49368951 / 250000000)) (hi := (39495161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 513) = 1/(513 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4046 : Bounds (-39495161 / 200000000) (-49368951 / 250000000) (Real.log (513 / 625)) := by
  have h := reflection_log_4046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4047_neg : (179183 / 1000000000) ≤ -Real.log (78125 / 78139) ∧
    -Real.log (78125 / 78139) ≤ (11199 / 62500000) := by
  have h := checkLog_sound (w := (7 / 78132)) (n := 12)
    (lo := (179183 / 1000000000)) (hi := (11199 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78139 / 78125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78139 / 78125) = 1/(78125 / 78139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4047 : Bounds (179183 / 1000000000) (11199 / 62500000) (Real.log (78139 / 78125)) := by
  have h := reflection_log_4047_neg
  have he : Real.log (78139 / 78125) = -Real.log (78125 / 78139) := by
    rw [show ((78139 / 78125) : ℝ) = ((78125 / 78139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4048_neg : (11201 / 62500000) ≤ -Real.log (78111 / 78125) ∧
    -Real.log (78111 / 78125) ≤ (179217 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 78118)) (n := 12)
    (lo := (11201 / 62500000)) (hi := (179217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78125 / 78111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78125 / 78111) = 1/(78111 / 78125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4048 : Bounds (-179217 / 1000000000) (-11201 / 62500000) (Real.log (78111 / 78125)) := by
  have h := reflection_log_4048_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4049_neg : (86162099 / 1000000000) ≤ -Real.log (1000000 / 1089983) ∧
    -Real.log (1000000 / 1089983) ≤ (861621 / 10000000) := by
  have h := checkLog_sound (w := (89983 / 2089983)) (n := 12)
    (lo := (86162099 / 1000000000)) (hi := (861621 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089983 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089983 / 1000000) = 1/(1000000 / 1089983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4049 : Bounds (86162099 / 1000000000) (861621 / 10000000) (Real.log (1089983 / 1000000)) := by
  have h := reflection_log_4049_neg
  have he : Real.log (1089983 / 1000000) = -Real.log (1000000 / 1089983) := by
    rw [show ((1089983 / 1000000) : ℝ) = ((1000000 / 1089983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4050_neg : (47145999 / 500000000) ≤ -Real.log (910017 / 1000000) ∧
    -Real.log (910017 / 1000000) ≤ (94291999 / 1000000000) := by
  have h := checkLog_sound (w := (89983 / 1910017)) (n := 12)
    (lo := (47145999 / 500000000)) (hi := (94291999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910017) = 1/(910017 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4050 : Bounds (-94291999 / 1000000000) (-47145999 / 500000000) (Real.log (910017 / 1000000)) := by
  have h := reflection_log_4050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4051_neg : (86373089 / 1000000000) ≤ -Real.log (1000000 / 1090213) ∧
    -Real.log (1000000 / 1090213) ≤ (8637309 / 100000000) := by
  have h := checkLog_sound (w := (90213 / 2090213)) (n := 12)
    (lo := (86373089 / 1000000000)) (hi := (8637309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090213 / 1000000) = 1/(1000000 / 1090213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4051 : Bounds (86373089 / 1000000000) (8637309 / 100000000) (Real.log (1090213 / 1000000)) := by
  have h := reflection_log_4051_neg
  have he : Real.log (1090213 / 1000000) = -Real.log (1000000 / 1090213) := by
    rw [show ((1090213 / 1000000) : ℝ) = ((1000000 / 1090213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4052_neg : (23636193 / 250000000) ≤ -Real.log (909787 / 1000000) ∧
    -Real.log (909787 / 1000000) ≤ (94544773 / 1000000000) := by
  have h := checkLog_sound (w := (90213 / 1909787)) (n := 12)
    (lo := (23636193 / 250000000)) (hi := (94544773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909787) = 1/(909787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4052 : Bounds (-94544773 / 1000000000) (-23636193 / 250000000) (Real.log (909787 / 1000000)) := by
  have h := reflection_log_4052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4053_neg : (4085841 / 500000000) ≤ -Real.log (991861614631 / 1000000000000) ∧
    -Real.log (991861614631 / 1000000000000) ≤ (8171683 / 1000000000) := by
  have h := checkLog_sound (w := (8138385369 / 1991861614631)) (n := 12)
    (lo := (4085841 / 500000000)) (hi := (8171683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991861614631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991861614631) = 1/(991861614631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4053 : Bounds (-8171683 / 1000000000) (-4085841 / 500000000) (Real.log (991861614631 / 1000000000000)) := by
  have h := reflection_log_4053_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4054_neg : (4064949 / 500000000) ≤ -Real.log (991903059711 / 1000000000000) ∧
    -Real.log (991903059711 / 1000000000000) ≤ (8129899 / 1000000000) := by
  have h := checkLog_sound (w := (8096940289 / 1991903059711)) (n := 12)
    (lo := (4064949 / 500000000)) (hi := (8129899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991903059711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991903059711) = 1/(991903059711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4054 : Bounds (-8129899 / 1000000000) (-4064949 / 500000000) (Real.log (991903059711 / 1000000000000)) := by
  have h := reflection_log_4054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4055_neg : (90227049 / 500000000) ≤ -Real.log (250000000000 / 299440285181) ∧
    -Real.log (250000000000 / 299440285181) ≤ (180454099 / 1000000000) := by
  have h := checkLog_sound (w := (49440285181 / 549440285181)) (n := 12)
    (lo := (90227049 / 500000000)) (hi := (180454099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299440285181 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299440285181 / 250000000000) = 1/(250000000000 / 299440285181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4055 : Bounds (90227049 / 500000000) (180454099 / 1000000000) (Real.log (299440285181 / 250000000000)) := by
  have h := reflection_log_4055_neg
  have he : Real.log (299440285181 / 250000000000) = -Real.log (250000000000 / 299440285181) := by
    rw [show ((299440285181 / 250000000000) : ℝ) = ((250000000000 / 299440285181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4056_neg : (90458931 / 500000000) ≤ -Real.log (500000000000 / 599158374433) ∧
    -Real.log (500000000000 / 599158374433) ≤ (180917863 / 1000000000) := by
  have h := checkLog_sound (w := (99158374433 / 1099158374433)) (n := 12)
    (lo := (90458931 / 500000000)) (hi := (180917863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599158374433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599158374433 / 500000000000) = 1/(500000000000 / 599158374433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4056 : Bounds (90458931 / 500000000) (180917863 / 1000000000) (Real.log (599158374433 / 500000000000)) := by
  have h := reflection_log_4056_neg
  have he : Real.log (599158374433 / 500000000000) = -Real.log (500000000000 / 599158374433) := by
    rw [show ((599158374433 / 500000000000) : ℝ) = ((500000000000 / 599158374433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4057_neg : (72421083 / 200000000) ≤ -Real.log (500000000000 / 718175173589) ∧
    -Real.log (500000000000 / 718175173589) ≤ (45263177 / 125000000) := by
  have h := checkLog_sound (w := (218175173589 / 1218175173589)) (n := 12)
    (lo := (72421083 / 200000000)) (hi := (45263177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718175173589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718175173589 / 500000000000) = 1/(500000000000 / 718175173589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4057 : Bounds (72421083 / 200000000) (45263177 / 125000000) (Real.log (718175173589 / 500000000000)) := by
  have h := reflection_log_4057_neg
  have he : Real.log (718175173589 / 500000000000) = -Real.log (500000000000 / 718175173589) := by
    rw [show ((718175173589 / 500000000000) : ℝ) = ((500000000000 / 718175173589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4058_neg : (362312047 / 1000000000) ≤ -Real.log (100000000000 / 143664717349) ∧
    -Real.log (100000000000 / 143664717349) ≤ (22644503 / 62500000) := by
  have h := checkLog_sound (w := (43664717349 / 243664717349)) (n := 12)
    (lo := (362312047 / 1000000000)) (hi := (22644503 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143664717349 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143664717349 / 100000000000) = 1/(100000000000 / 143664717349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4058 : Bounds (362312047 / 1000000000) (22644503 / 62500000) (Real.log (143664717349 / 100000000000)) := by
  have h := reflection_log_4058_neg
  have he : Real.log (143664717349 / 100000000000) = -Real.log (100000000000 / 143664717349) := by
    rw [show ((143664717349 / 100000000000) : ℝ) = ((100000000000 / 143664717349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4059_neg : (82460521 / 500000000) ≤ -Real.log (10000 / 11793) ∧
    -Real.log (10000 / 11793) ≤ (164921043 / 1000000000) := by
  have h := checkLog_sound (w := (1793 / 21793)) (n := 12)
    (lo := (82460521 / 500000000)) (hi := (164921043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11793 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11793 / 10000) = 1/(10000 / 11793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4059 : Bounds (82460521 / 500000000) (164921043 / 1000000000) (Real.log (11793 / 10000)) := by
  have h := reflection_log_4059_neg
  have he : Real.log (11793 / 10000) = -Real.log (10000 / 11793) := by
    rw [show ((11793 / 10000) : ℝ) = ((10000 / 11793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4060_neg : (49399411 / 250000000) ≤ -Real.log (8207 / 10000) ∧
    -Real.log (8207 / 10000) ≤ (39519529 / 200000000) := by
  have h := checkLog_sound (w := (1793 / 18207)) (n := 12)
    (lo := (49399411 / 250000000)) (hi := (39519529 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8207) = 1/(8207 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4060 : Bounds (-39519529 / 200000000) (-49399411 / 250000000) (Real.log (8207 / 10000)) := by
  have h := reflection_log_4060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4061_neg : (179283 / 1000000000) ≤ -Real.log (10000000 / 10001793) ∧
    -Real.log (10000000 / 10001793) ≤ (44821 / 250000000) := by
  have h := checkLog_sound (w := (1793 / 20001793)) (n := 12)
    (lo := (179283 / 1000000000)) (hi := (44821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001793 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001793 / 10000000) = 1/(10000000 / 10001793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4061 : Bounds (179283 / 1000000000) (44821 / 250000000) (Real.log (10001793 / 10000000)) := by
  have h := reflection_log_4061_neg
  have he : Real.log (10001793 / 10000000) = -Real.log (10000000 / 10001793) := by
    rw [show ((10001793 / 10000000) : ℝ) = ((10000000 / 10001793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4062_neg : (44829 / 250000000) ≤ -Real.log (9998207 / 10000000) ∧
    -Real.log (9998207 / 10000000) ≤ (179317 / 1000000000) := by
  have h := checkLog_sound (w := (1793 / 19998207)) (n := 12)
    (lo := (44829 / 250000000)) (hi := (179317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998207) = 1/(9998207 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4062 : Bounds (-179317 / 1000000000) (-44829 / 250000000) (Real.log (9998207 / 10000000)) := by
  have h := reflection_log_4062_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4063_neg : (10776111 / 125000000) ≤ -Real.log (500000 / 545017) ∧
    -Real.log (500000 / 545017) ≤ (86208889 / 1000000000) := by
  have h := checkLog_sound (w := (45017 / 1045017)) (n := 12)
    (lo := (10776111 / 125000000)) (hi := (86208889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545017 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545017 / 500000) = 1/(500000 / 545017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4063 : Bounds (10776111 / 125000000) (86208889 / 1000000000) (Real.log (545017 / 500000)) := by
  have h := reflection_log_4063_neg
  have he : Real.log (545017 / 500000) = -Real.log (500000 / 545017) := by
    rw [show ((545017 / 500000) : ℝ) = ((500000 / 545017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4064_neg : (47174021 / 500000000) ≤ -Real.log (454983 / 500000) ∧
    -Real.log (454983 / 500000) ≤ (94348043 / 1000000000) := by
  have h := checkLog_sound (w := (45017 / 954983)) (n := 12)
    (lo := (47174021 / 500000000)) (hi := (94348043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454983) = 1/(454983 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4064 : Bounds (-94348043 / 1000000000) (-47174021 / 500000000) (Real.log (454983 / 500000)) := by
  have h := reflection_log_4064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4065_neg : (21604967 / 250000000) ≤ -Real.log (125000 / 136283) ∧
    -Real.log (125000 / 136283) ≤ (86419869 / 1000000000) := by
  have h := checkLog_sound (w := (11283 / 261283)) (n := 12)
    (lo := (21604967 / 250000000)) (hi := (86419869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136283 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136283 / 125000) = 1/(125000 / 136283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4065 : Bounds (21604967 / 250000000) (86419869 / 1000000000) (Real.log (136283 / 125000)) := by
  have h := reflection_log_4065_neg
  have he : Real.log (136283 / 125000) = -Real.log (125000 / 136283) := by
    rw [show ((136283 / 125000) : ℝ) = ((125000 / 136283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4066_neg : (94600831 / 1000000000) ≤ -Real.log (113717 / 125000) ∧
    -Real.log (113717 / 125000) ≤ (739069 / 7812500) := by
  have h := checkLog_sound (w := (11283 / 238717)) (n := 12)
    (lo := (94600831 / 1000000000)) (hi := (739069 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113717) = 1/(113717 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4066 : Bounds (-739069 / 7812500) (-94600831 / 1000000000) (Real.log (113717 / 125000)) := by
  have h := reflection_log_4066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4067_neg : (4090481 / 500000000) ≤ -Real.log (15497693911 / 15625000000) ∧
    -Real.log (15497693911 / 15625000000) ≤ (8180963 / 1000000000) := by
  have h := checkLog_sound (w := (127306089 / 31122693911)) (n := 12)
    (lo := (4090481 / 500000000)) (hi := (8180963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15497693911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15497693911) = 1/(15497693911 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4067 : Bounds (-8180963 / 1000000000) (-4090481 / 500000000) (Real.log (15497693911 / 15625000000)) := by
  have h := reflection_log_4067_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4068_neg : (4069577 / 500000000) ≤ -Real.log (247973469711 / 250000000000) ∧
    -Real.log (247973469711 / 250000000000) ≤ (1627831 / 200000000) := by
  have h := checkLog_sound (w := (2026530289 / 497973469711)) (n := 12)
    (lo := (4069577 / 500000000)) (hi := (1627831 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247973469711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247973469711) = 1/(247973469711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4068 : Bounds (-1627831 / 200000000) (-4069577 / 500000000) (Real.log (247973469711 / 250000000000)) := by
  have h := reflection_log_4068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4069_neg : (180556931 / 1000000000) ≤ -Real.log (250000000000 / 299471079139) ∧
    -Real.log (250000000000 / 299471079139) ≤ (45139233 / 250000000) := by
  have h := checkLog_sound (w := (49471079139 / 549471079139)) (n := 12)
    (lo := (180556931 / 1000000000)) (hi := (45139233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299471079139 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299471079139 / 250000000000) = 1/(250000000000 / 299471079139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4069 : Bounds (180556931 / 1000000000) (45139233 / 250000000) (Real.log (299471079139 / 250000000000)) := by
  have h := reflection_log_4069_neg
  have he : Real.log (299471079139 / 250000000000) = -Real.log (250000000000 / 299471079139) := by
    rw [show ((299471079139 / 250000000000) : ℝ) = ((250000000000 / 299471079139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4070_neg : (1810207 / 10000000) ≤ -Real.log (500000000000 / 599219993493) ∧
    -Real.log (500000000000 / 599219993493) ≤ (181020701 / 1000000000) := by
  have h := checkLog_sound (w := (99219993493 / 1099219993493)) (n := 12)
    (lo := (1810207 / 10000000)) (hi := (181020701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599219993493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599219993493 / 500000000000) = 1/(500000000000 / 599219993493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4070 : Bounds (1810207 / 10000000) (181020701 / 1000000000) (Real.log (599219993493 / 500000000000)) := by
  have h := reflection_log_4070_neg
  have he : Real.log (599219993493 / 500000000000) = -Real.log (500000000000 / 599219993493) := by
    rw [show ((599219993493 / 500000000000) : ℝ) = ((500000000000 / 599219993493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4071_neg : (362312047 / 1000000000) ≤ -Real.log (62500000000 / 89790448343) ∧
    -Real.log (62500000000 / 89790448343) ≤ (22644503 / 62500000) := by
  have h := checkLog_sound (w := (27290448343 / 152290448343)) (n := 12)
    (lo := (362312047 / 1000000000)) (hi := (22644503 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89790448343 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89790448343 / 62500000000) = 1/(62500000000 / 89790448343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4071 : Bounds (362312047 / 1000000000) (22644503 / 62500000) (Real.log (89790448343 / 62500000000)) := by
  have h := reflection_log_4071_neg
  have he : Real.log (89790448343 / 62500000000) = -Real.log (62500000000 / 89790448343) := by
    rw [show ((89790448343 / 62500000000) : ℝ) = ((62500000000 / 89790448343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4072_neg : (181259343 / 500000000) ≤ -Real.log (500000000000 / 718472036067) ∧
    -Real.log (500000000000 / 718472036067) ≤ (362518687 / 1000000000) := by
  have h := checkLog_sound (w := (218472036067 / 1218472036067)) (n := 12)
    (lo := (181259343 / 500000000)) (hi := (362518687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718472036067 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718472036067 / 500000000000) = 1/(500000000000 / 718472036067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4072 : Bounds (181259343 / 500000000) (362518687 / 1000000000) (Real.log (718472036067 / 500000000000)) := by
  have h := reflection_log_4072_neg
  have he : Real.log (718472036067 / 500000000000) = -Real.log (500000000000 / 718472036067) := by
    rw [show ((718472036067 / 500000000000) : ℝ) = ((500000000000 / 718472036067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4073_neg : (82502917 / 500000000) ≤ -Real.log (5000 / 5897) ∧
    -Real.log (5000 / 5897) ≤ (33001167 / 200000000) := by
  have h := checkLog_sound (w := (897 / 10897)) (n := 12)
    (lo := (82502917 / 500000000)) (hi := (33001167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5897 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5897 / 5000) = 1/(5000 / 5897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4073 : Bounds (82502917 / 500000000) (33001167 / 200000000) (Real.log (5897 / 5000)) := by
  have h := reflection_log_4073_neg
  have he : Real.log (5897 / 5000) = -Real.log (5000 / 5897) := by
    rw [show ((5897 / 5000) : ℝ) = ((5000 / 5897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4074_neg : (98859749 / 500000000) ≤ -Real.log (4103 / 5000) ∧
    -Real.log (4103 / 5000) ≤ (197719499 / 1000000000) := by
  have h := checkLog_sound (w := (897 / 9103)) (n := 12)
    (lo := (98859749 / 500000000)) (hi := (197719499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4103) = 1/(4103 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4074 : Bounds (-197719499 / 1000000000) (-98859749 / 500000000) (Real.log (4103 / 5000)) := by
  have h := reflection_log_4074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4075_neg : (179383 / 1000000000) ≤ -Real.log (5000000 / 5000897) ∧
    -Real.log (5000000 / 5000897) ≤ (22423 / 125000000) := by
  have h := checkLog_sound (w := (897 / 10000897)) (n := 12)
    (lo := (179383 / 1000000000)) (hi := (22423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000897 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000897 / 5000000) = 1/(5000000 / 5000897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4075 : Bounds (179383 / 1000000000) (22423 / 125000000) (Real.log (5000897 / 5000000)) := by
  have h := reflection_log_4075_neg
  have he : Real.log (5000897 / 5000000) = -Real.log (5000000 / 5000897) := by
    rw [show ((5000897 / 5000000) : ℝ) = ((5000000 / 5000897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4076_neg : (22427 / 125000000) ≤ -Real.log (4999103 / 5000000) ∧
    -Real.log (4999103 / 5000000) ≤ (179417 / 1000000000) := by
  have h := checkLog_sound (w := (897 / 9999103)) (n := 12)
    (lo := (22427 / 125000000)) (hi := (179417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999103) = 1/(4999103 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4076 : Bounds (-179417 / 1000000000) (-22427 / 125000000) (Real.log (4999103 / 5000000)) := by
  have h := reflection_log_4076_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4077_neg : (43127837 / 500000000) ≤ -Real.log (200000 / 218017) ∧
    -Real.log (200000 / 218017) ≤ (3450227 / 40000000) := by
  have h := checkLog_sound (w := (18017 / 418017)) (n := 12)
    (lo := (43127837 / 500000000)) (hi := (3450227 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218017 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218017 / 200000) = 1/(200000 / 218017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4077 : Bounds (43127837 / 500000000) (3450227 / 40000000) (Real.log (218017 / 200000)) := by
  have h := reflection_log_4077_neg
  have he : Real.log (218017 / 200000) = -Real.log (200000 / 218017) := by
    rw [show ((218017 / 200000) : ℝ) = ((200000 / 218017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4078_neg : (9440409 / 100000000) ≤ -Real.log (181983 / 200000) ∧
    -Real.log (181983 / 200000) ≤ (94404091 / 1000000000) := by
  have h := checkLog_sound (w := (18017 / 381983)) (n := 12)
    (lo := (9440409 / 100000000)) (hi := (94404091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181983) = 1/(181983 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4078 : Bounds (-94404091 / 1000000000) (-9440409 / 100000000) (Real.log (181983 / 200000)) := by
  have h := reflection_log_4078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4079_neg : (17293329 / 200000000) ≤ -Real.log (200000 / 218063) ∧
    -Real.log (200000 / 218063) ≤ (43233323 / 500000000) := by
  have h := checkLog_sound (w := (18063 / 418063)) (n := 12)
    (lo := (17293329 / 200000000)) (hi := (43233323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218063 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218063 / 200000) = 1/(200000 / 218063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4079 : Bounds (17293329 / 200000000) (43233323 / 500000000) (Real.log (218063 / 200000)) := by
  have h := reflection_log_4079_neg
  have he : Real.log (218063 / 200000) = -Real.log (200000 / 218063) := by
    rw [show ((218063 / 200000) : ℝ) = ((200000 / 218063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4080_neg : (94656893 / 1000000000) ≤ -Real.log (181937 / 200000) ∧
    -Real.log (181937 / 200000) ≤ (47328447 / 500000000) := by
  have h := checkLog_sound (w := (18063 / 381937)) (n := 12)
    (lo := (94656893 / 1000000000)) (hi := (47328447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181937) = 1/(181937 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4080 : Bounds (-47328447 / 500000000) (-94656893 / 1000000000) (Real.log (181937 / 200000)) := by
  have h := reflection_log_4080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4081_neg : (8190247 / 1000000000) ≤ -Real.log (39673728031 / 40000000000) ∧
    -Real.log (39673728031 / 40000000000) ≤ (1023781 / 125000000) := by
  have h := checkLog_sound (w := (326271969 / 79673728031)) (n := 12)
    (lo := (8190247 / 1000000000)) (hi := (1023781 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39673728031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39673728031) = 1/(39673728031 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4081 : Bounds (-1023781 / 125000000) (-8190247 / 1000000000) (Real.log (39673728031 / 40000000000)) := by
  have h := reflection_log_4081_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4082_neg : (1629683 / 200000000) ≤ -Real.log (39675387711 / 40000000000) ∧
    -Real.log (39675387711 / 40000000000) ≤ (127319 / 15625000) := by
  have h := checkLog_sound (w := (324612289 / 79675387711)) (n := 12)
    (lo := (1629683 / 200000000)) (hi := (127319 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39675387711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39675387711) = 1/(39675387711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4082 : Bounds (-127319 / 15625000) (-1629683 / 200000000) (Real.log (39675387711 / 40000000000)) := by
  have h := reflection_log_4082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4083_neg : (36131953 / 200000000) ≤ -Real.log (500000000000 / 599003753097) ∧
    -Real.log (500000000000 / 599003753097) ≤ (90329883 / 500000000) := by
  have h := checkLog_sound (w := (99003753097 / 1099003753097)) (n := 12)
    (lo := (36131953 / 200000000)) (hi := (90329883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599003753097 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599003753097 / 500000000000) = 1/(500000000000 / 599003753097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4083 : Bounds (36131953 / 200000000) (90329883 / 500000000) (Real.log (599003753097 / 500000000000)) := by
  have h := reflection_log_4083_neg
  have he : Real.log (599003753097 / 500000000000) = -Real.log (500000000000 / 599003753097) := by
    rw [show ((599003753097 / 500000000000) : ℝ) = ((500000000000 / 599003753097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4084_neg : (90561769 / 500000000) ≤ -Real.log (250000000000 / 299640809731) ∧
    -Real.log (250000000000 / 299640809731) ≤ (181123539 / 1000000000) := by
  have h := checkLog_sound (w := (49640809731 / 549640809731)) (n := 12)
    (lo := (90561769 / 500000000)) (hi := (181123539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299640809731 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299640809731 / 250000000000) = 1/(250000000000 / 299640809731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4084 : Bounds (90561769 / 500000000) (181123539 / 1000000000) (Real.log (299640809731 / 250000000000)) := by
  have h := reflection_log_4084_neg
  have he : Real.log (299640809731 / 250000000000) = -Real.log (250000000000 / 299640809731) := by
    rw [show ((299640809731 / 250000000000) : ℝ) = ((250000000000 / 299640809731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4085_neg : (181259343 / 500000000) ≤ -Real.log (250000000000 / 359236018033) ∧
    -Real.log (250000000000 / 359236018033) ≤ (362518687 / 1000000000) := by
  have h := checkLog_sound (w := (109236018033 / 609236018033)) (n := 12)
    (lo := (181259343 / 500000000)) (hi := (362518687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359236018033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359236018033 / 250000000000) = 1/(250000000000 / 359236018033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4085 : Bounds (181259343 / 500000000) (362518687 / 1000000000) (Real.log (359236018033 / 250000000000)) := by
  have h := reflection_log_4085_neg
  have he : Real.log (359236018033 / 250000000000) = -Real.log (250000000000 / 359236018033) := by
    rw [show ((359236018033 / 250000000000) : ℝ) = ((250000000000 / 359236018033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4086_neg : (362725333 / 1000000000) ≤ -Real.log (50000000000 / 71862052157) ∧
    -Real.log (50000000000 / 71862052157) ≤ (181362667 / 500000000) := by
  have h := checkLog_sound (w := (21862052157 / 121862052157)) (n := 12)
    (lo := (362725333 / 1000000000)) (hi := (181362667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71862052157 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71862052157 / 50000000000) = 1/(50000000000 / 71862052157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4086 : Bounds (362725333 / 1000000000) (181362667 / 500000000) (Real.log (71862052157 / 50000000000)) := by
  have h := reflection_log_4086_neg
  have he : Real.log (71862052157 / 50000000000) = -Real.log (50000000000 / 71862052157) := by
    rw [show ((71862052157 / 50000000000) : ℝ) = ((50000000000 / 71862052157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4087_neg : (165090619 / 1000000000) ≤ -Real.log (2000 / 2359) ∧
    -Real.log (2000 / 2359) ≤ (8254531 / 50000000) := by
  have h := checkLog_sound (w := (359 / 4359)) (n := 12)
    (lo := (165090619 / 1000000000)) (hi := (8254531 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2359 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2359 / 2000) = 1/(2000 / 2359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4087 : Bounds (165090619 / 1000000000) (8254531 / 50000000) (Real.log (2359 / 2000)) := by
  have h := reflection_log_4087_neg
  have he : Real.log (2359 / 2000) = -Real.log (2000 / 2359) := by
    rw [show ((2359 / 2000) : ℝ) = ((2000 / 2359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4088_neg : (24730171 / 125000000) ≤ -Real.log (1641 / 2000) ∧
    -Real.log (1641 / 2000) ≤ (197841369 / 1000000000) := by
  have h := checkLog_sound (w := (359 / 3641)) (n := 12)
    (lo := (24730171 / 125000000)) (hi := (197841369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1641) = 1/(1641 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4088 : Bounds (-197841369 / 1000000000) (-24730171 / 125000000) (Real.log (1641 / 2000)) := by
  have h := reflection_log_4088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4089_neg : (179483 / 1000000000) ≤ -Real.log (2000000 / 2000359) ∧
    -Real.log (2000000 / 2000359) ≤ (44871 / 250000000) := by
  have h := checkLog_sound (w := (359 / 4000359)) (n := 12)
    (lo := (179483 / 1000000000)) (hi := (44871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000359 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000359 / 2000000) = 1/(2000000 / 2000359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4089 : Bounds (179483 / 1000000000) (44871 / 250000000) (Real.log (2000359 / 2000000)) := by
  have h := reflection_log_4089_neg
  have he : Real.log (2000359 / 2000000) = -Real.log (2000000 / 2000359) := by
    rw [show ((2000359 / 2000000) : ℝ) = ((2000000 / 2000359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4090_neg : (44879 / 250000000) ≤ -Real.log (1999641 / 2000000) ∧
    -Real.log (1999641 / 2000000) ≤ (179517 / 1000000000) := by
  have h := checkLog_sound (w := (359 / 3999641)) (n := 12)
    (lo := (44879 / 250000000)) (hi := (179517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999641) = 1/(1999641 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4090 : Bounds (-179517 / 1000000000) (-44879 / 250000000) (Real.log (1999641 / 2000000)) := by
  have h := reflection_log_4090_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4091_neg : (86302459 / 1000000000) ≤ -Real.log (125000 / 136267) ∧
    -Real.log (125000 / 136267) ≤ (4315123 / 50000000) := by
  have h := checkLog_sound (w := (11267 / 261267)) (n := 12)
    (lo := (86302459 / 1000000000)) (hi := (4315123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136267 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136267 / 125000) = 1/(125000 / 136267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4091 : Bounds (86302459 / 1000000000) (4315123 / 50000000) (Real.log (136267 / 125000)) := by
  have h := reflection_log_4091_neg
  have he : Real.log (136267 / 125000) = -Real.log (125000 / 136267) := by
    rw [show ((136267 / 125000) : ℝ) = ((125000 / 136267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4092_neg : (94460141 / 1000000000) ≤ -Real.log (113733 / 125000) ∧
    -Real.log (113733 / 125000) ≤ (47230071 / 500000000) := by
  have h := checkLog_sound (w := (11267 / 238733)) (n := 12)
    (lo := (94460141 / 1000000000)) (hi := (47230071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113733) = 1/(113733 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4092 : Bounds (-47230071 / 500000000) (-94460141 / 1000000000) (Real.log (113733 / 125000)) := by
  have h := reflection_log_4092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4093_neg : (86513419 / 1000000000) ≤ -Real.log (500000 / 545183) ∧
    -Real.log (500000 / 545183) ≤ (4325671 / 50000000) := by
  have h := checkLog_sound (w := (45183 / 1045183)) (n := 12)
    (lo := (86513419 / 1000000000)) (hi := (4325671 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545183 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545183 / 500000) = 1/(500000 / 545183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4093 : Bounds (86513419 / 1000000000) (4325671 / 50000000) (Real.log (545183 / 500000)) := by
  have h := reflection_log_4093_neg
  have he : Real.log (545183 / 500000) = -Real.log (500000 / 545183) := by
    rw [show ((545183 / 500000) : ℝ) = ((500000 / 545183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4094_neg : (47356479 / 500000000) ≤ -Real.log (454817 / 500000) ∧
    -Real.log (454817 / 500000) ≤ (94712959 / 1000000000) := by
  have h := checkLog_sound (w := (45183 / 954817)) (n := 12)
    (lo := (47356479 / 500000000)) (hi := (94712959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454817) = 1/(454817 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4094 : Bounds (-94712959 / 1000000000) (-47356479 / 500000000) (Real.log (454817 / 500000)) := by
  have h := reflection_log_4094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4095_neg : (4099769 / 500000000) ≤ -Real.log (247958496511 / 250000000000) ∧
    -Real.log (247958496511 / 250000000000) ≤ (8199539 / 1000000000) := by
  have h := checkLog_sound (w := (2041503489 / 497958496511)) (n := 12)
    (lo := (4099769 / 500000000)) (hi := (8199539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247958496511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247958496511) = 1/(247958496511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4095 : Bounds (-8199539 / 1000000000) (-4099769 / 500000000) (Real.log (247958496511 / 250000000000)) := by
  have h := reflection_log_4095_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0064 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4096_neg : (4078841 / 500000000) ≤ -Real.log (15498054711 / 15625000000) ∧
    -Real.log (15498054711 / 15625000000) ≤ (8157683 / 1000000000) := by
  have h := checkLog_sound (w := (126945289 / 31123054711)) (n := 12)
    (lo := (4078841 / 500000000)) (hi := (8157683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15498054711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15498054711) = 1/(15498054711 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4096 : Bounds (-8157683 / 1000000000) (-4078841 / 500000000) (Real.log (15498054711 / 15625000000)) := by
  have h := reflection_log_4096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4097_neg : (903813 / 5000000) ≤ -Real.log (250000000000 / 299532677411) ∧
    -Real.log (250000000000 / 299532677411) ≤ (180762601 / 1000000000) := by
  have h := checkLog_sound (w := (49532677411 / 549532677411)) (n := 12)
    (lo := (903813 / 5000000)) (hi := (180762601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299532677411 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299532677411 / 250000000000) = 1/(250000000000 / 299532677411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4097 : Bounds (903813 / 5000000) (180762601 / 1000000000) (Real.log (299532677411 / 250000000000)) := by
  have h := reflection_log_4097_neg
  have he : Real.log (299532677411 / 250000000000) = -Real.log (250000000000 / 299532677411) := by
    rw [show ((299532677411 / 250000000000) : ℝ) = ((250000000000 / 299532677411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4098_neg : (181226377 / 1000000000) ≤ -Real.log (250000000000 / 299671626171) ∧
    -Real.log (250000000000 / 299671626171) ≤ (90613189 / 500000000) := by
  have h := checkLog_sound (w := (49671626171 / 549671626171)) (n := 12)
    (lo := (181226377 / 1000000000)) (hi := (90613189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299671626171 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299671626171 / 250000000000) = 1/(250000000000 / 299671626171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4098 : Bounds (181226377 / 1000000000) (90613189 / 500000000) (Real.log (299671626171 / 250000000000)) := by
  have h := reflection_log_4098_neg
  have he : Real.log (299671626171 / 250000000000) = -Real.log (250000000000 / 299671626171) := by
    rw [show ((299671626171 / 250000000000) : ℝ) = ((250000000000 / 299671626171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4099_neg : (362725333 / 1000000000) ≤ -Real.log (500000000000 / 718620521569) ∧
    -Real.log (500000000000 / 718620521569) ≤ (181362667 / 500000000) := by
  have h := checkLog_sound (w := (218620521569 / 1218620521569)) (n := 12)
    (lo := (362725333 / 1000000000)) (hi := (181362667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718620521569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718620521569 / 500000000000) = 1/(500000000000 / 718620521569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4099 : Bounds (362725333 / 1000000000) (181362667 / 500000000) (Real.log (718620521569 / 500000000000)) := by
  have h := reflection_log_4099_neg
  have he : Real.log (718620521569 / 500000000000) = -Real.log (500000000000 / 718620521569) := by
    rw [show ((718620521569 / 500000000000) : ℝ) = ((500000000000 / 718620521569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4100_neg : (90732997 / 250000000) ≤ -Real.log (500000000000 / 718769043267) ∧
    -Real.log (500000000000 / 718769043267) ≤ (362931989 / 1000000000) := by
  have h := checkLog_sound (w := (218769043267 / 1218769043267)) (n := 12)
    (lo := (90732997 / 250000000)) (hi := (362931989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718769043267 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718769043267 / 500000000000) = 1/(500000000000 / 718769043267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4100 : Bounds (90732997 / 250000000) (362931989 / 1000000000) (Real.log (718769043267 / 500000000000)) := by
  have h := reflection_log_4100_neg
  have he : Real.log (718769043267 / 500000000000) = -Real.log (500000000000 / 718769043267) := by
    rw [show ((718769043267 / 500000000000) : ℝ) = ((500000000000 / 718769043267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4101_neg : (165175397 / 1000000000) ≤ -Real.log (2500 / 2949) ∧
    -Real.log (2500 / 2949) ≤ (82587699 / 500000000) := by
  have h := checkLog_sound (w := (449 / 5449)) (n := 12)
    (lo := (165175397 / 1000000000)) (hi := (82587699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2949 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2949 / 2500) = 1/(2500 / 2949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4101 : Bounds (165175397 / 1000000000) (82587699 / 500000000) (Real.log (2949 / 2500)) := by
  have h := reflection_log_4101_neg
  have he : Real.log (2949 / 2500) = -Real.log (2500 / 2949) := by
    rw [show ((2949 / 2500) : ℝ) = ((2500 / 2949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4102_neg : (49490813 / 250000000) ≤ -Real.log (2051 / 2500) ∧
    -Real.log (2051 / 2500) ≤ (197963253 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 4551)) (n := 12)
    (lo := (49490813 / 250000000)) (hi := (197963253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2051) = 1/(2051 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4102 : Bounds (-197963253 / 1000000000) (-49490813 / 250000000) (Real.log (2051 / 2500)) := by
  have h := reflection_log_4102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4103_neg : (179583 / 1000000000) ≤ -Real.log (2500000 / 2500449) ∧
    -Real.log (2500000 / 2500449) ≤ (1403 / 7812500) := by
  have h := checkLog_sound (w := (449 / 5000449)) (n := 12)
    (lo := (179583 / 1000000000)) (hi := (1403 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500449 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500449 / 2500000) = 1/(2500000 / 2500449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4103 : Bounds (179583 / 1000000000) (1403 / 7812500) (Real.log (2500449 / 2500000)) := by
  have h := reflection_log_4103_neg
  have he : Real.log (2500449 / 2500000) = -Real.log (2500000 / 2500449) := by
    rw [show ((2500449 / 2500000) : ℝ) = ((2500000 / 2500449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4104_neg : (5613 / 31250000) ≤ -Real.log (2499551 / 2500000) ∧
    -Real.log (2499551 / 2500000) ≤ (179617 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 4999551)) (n := 12)
    (lo := (5613 / 31250000)) (hi := (179617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499551) = 1/(2499551 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4104 : Bounds (-179617 / 1000000000) (-5613 / 31250000) (Real.log (2499551 / 2500000)) := by
  have h := reflection_log_4104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4105_neg : (86349241 / 1000000000) ≤ -Real.log (1000000 / 1090187) ∧
    -Real.log (1000000 / 1090187) ≤ (43174621 / 500000000) := by
  have h := checkLog_sound (w := (90187 / 2090187)) (n := 12)
    (lo := (86349241 / 1000000000)) (hi := (43174621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090187 / 1000000) = 1/(1000000 / 1090187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4105 : Bounds (86349241 / 1000000000) (43174621 / 500000000) (Real.log (1090187 / 1000000)) := by
  have h := reflection_log_4105_neg
  have he : Real.log (1090187 / 1000000) = -Real.log (1000000 / 1090187) := by
    rw [show ((1090187 / 1000000) : ℝ) = ((1000000 / 1090187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4106_neg : (18903239 / 200000000) ≤ -Real.log (909813 / 1000000) ∧
    -Real.log (909813 / 1000000) ≤ (23629049 / 250000000) := by
  have h := checkLog_sound (w := (90187 / 1909813)) (n := 12)
    (lo := (18903239 / 200000000)) (hi := (23629049 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909813) = 1/(909813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4106 : Bounds (-23629049 / 250000000) (-18903239 / 200000000) (Real.log (909813 / 1000000)) := by
  have h := reflection_log_4106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4107_neg : (86560191 / 1000000000) ≤ -Real.log (1000000 / 1090417) ∧
    -Real.log (1000000 / 1090417) ≤ (1352503 / 15625000) := by
  have h := checkLog_sound (w := (90417 / 2090417)) (n := 12)
    (lo := (86560191 / 1000000000)) (hi := (1352503 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090417 / 1000000) = 1/(1000000 / 1090417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4107 : Bounds (86560191 / 1000000000) (1352503 / 15625000) (Real.log (1090417 / 1000000)) := by
  have h := reflection_log_4107_neg
  have he : Real.log (1090417 / 1000000) = -Real.log (1000000 / 1090417) := by
    rw [show ((1090417 / 1000000) : ℝ) = ((1000000 / 1090417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4108_neg : (47384513 / 500000000) ≤ -Real.log (909583 / 1000000) ∧
    -Real.log (909583 / 1000000) ≤ (94769027 / 1000000000) := by
  have h := checkLog_sound (w := (90417 / 1909583)) (n := 12)
    (lo := (47384513 / 500000000)) (hi := (94769027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909583) = 1/(909583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4108 : Bounds (-94769027 / 1000000000) (-47384513 / 500000000) (Real.log (909583 / 1000000)) := by
  have h := reflection_log_4108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4109_neg : (4104417 / 500000000) ≤ -Real.log (991824766111 / 1000000000000) ∧
    -Real.log (991824766111 / 1000000000000) ≤ (1641767 / 200000000) := by
  have h := checkLog_sound (w := (8175233889 / 1991824766111)) (n := 12)
    (lo := (4104417 / 500000000)) (hi := (1641767 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991824766111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991824766111) = 1/(991824766111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4109 : Bounds (-1641767 / 200000000) (-4104417 / 500000000) (Real.log (991824766111 / 1000000000000)) := by
  have h := reflection_log_4109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4110_neg : (8166953 / 1000000000) ≤ -Real.log (991866305031 / 1000000000000) ∧
    -Real.log (991866305031 / 1000000000000) ≤ (4083477 / 500000000) := by
  have h := checkLog_sound (w := (8133694969 / 1991866305031)) (n := 12)
    (lo := (8166953 / 1000000000)) (hi := (4083477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991866305031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991866305031) = 1/(991866305031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4110 : Bounds (-4083477 / 500000000) (-8166953 / 1000000000) (Real.log (991866305031 / 1000000000000)) := by
  have h := reflection_log_4110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4111_neg : (45216359 / 250000000) ≤ -Real.log (125000000000 / 149781740863) ∧
    -Real.log (125000000000 / 149781740863) ≤ (180865437 / 1000000000) := by
  have h := checkLog_sound (w := (24781740863 / 274781740863)) (n := 12)
    (lo := (45216359 / 250000000)) (hi := (180865437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149781740863 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149781740863 / 125000000000) = 1/(125000000000 / 149781740863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4111 : Bounds (45216359 / 250000000) (180865437 / 1000000000) (Real.log (149781740863 / 125000000000)) := by
  have h := reflection_log_4111_neg
  have he : Real.log (149781740863 / 125000000000) = -Real.log (125000000000 / 149781740863) := by
    rw [show ((149781740863 / 125000000000) : ℝ) = ((125000000000 / 149781740863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4112_neg : (90664609 / 500000000) ≤ -Real.log (125000000000 / 149851223033) ∧
    -Real.log (125000000000 / 149851223033) ≤ (181329219 / 1000000000) := by
  have h := checkLog_sound (w := (24851223033 / 274851223033)) (n := 12)
    (lo := (90664609 / 500000000)) (hi := (181329219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149851223033 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149851223033 / 125000000000) = 1/(125000000000 / 149851223033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4112 : Bounds (90664609 / 500000000) (181329219 / 1000000000) (Real.log (149851223033 / 125000000000)) := by
  have h := reflection_log_4112_neg
  have he : Real.log (149851223033 / 125000000000) = -Real.log (125000000000 / 149851223033) := by
    rw [show ((149851223033 / 125000000000) : ℝ) = ((125000000000 / 149851223033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4113_neg : (90732997 / 250000000) ≤ -Real.log (250000000000 / 359384521633) ∧
    -Real.log (250000000000 / 359384521633) ≤ (362931989 / 1000000000) := by
  have h := checkLog_sound (w := (109384521633 / 609384521633)) (n := 12)
    (lo := (90732997 / 250000000)) (hi := (362931989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359384521633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359384521633 / 250000000000) = 1/(250000000000 / 359384521633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4113 : Bounds (90732997 / 250000000) (362931989 / 1000000000) (Real.log (359384521633 / 250000000000)) := by
  have h := reflection_log_4113_neg
  have he : Real.log (359384521633 / 250000000000) = -Real.log (250000000000 / 359384521633) := by
    rw [show ((359384521633 / 250000000000) : ℝ) = ((250000000000 / 359384521633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4114_neg : (7262773 / 20000000) ≤ -Real.log (500000000000 / 718917601171) ∧
    -Real.log (500000000000 / 718917601171) ≤ (363138651 / 1000000000) := by
  have h := checkLog_sound (w := (218917601171 / 1218917601171)) (n := 12)
    (lo := (7262773 / 20000000)) (hi := (363138651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718917601171 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718917601171 / 500000000000) = 1/(500000000000 / 718917601171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4114 : Bounds (7262773 / 20000000) (363138651 / 1000000000) (Real.log (718917601171 / 500000000000)) := by
  have h := reflection_log_4114_neg
  have he : Real.log (718917601171 / 500000000000) = -Real.log (500000000000 / 718917601171) := by
    rw [show ((718917601171 / 500000000000) : ℝ) = ((500000000000 / 718917601171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4115_neg : (20657521 / 125000000) ≤ -Real.log (10000 / 11797) ∧
    -Real.log (10000 / 11797) ≤ (165260169 / 1000000000) := by
  have h := checkLog_sound (w := (1797 / 21797)) (n := 12)
    (lo := (20657521 / 125000000)) (hi := (165260169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11797 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11797 / 10000) = 1/(10000 / 11797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4115 : Bounds (20657521 / 125000000) (165260169 / 1000000000) (Real.log (11797 / 10000)) := by
  have h := reflection_log_4115_neg
  have he : Real.log (11797 / 10000) = -Real.log (10000 / 11797) := by
    rw [show ((11797 / 10000) : ℝ) = ((10000 / 11797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4116_neg : (198085151 / 1000000000) ≤ -Real.log (8203 / 10000) ∧
    -Real.log (8203 / 10000) ≤ (6190161 / 31250000) := by
  have h := checkLog_sound (w := (1797 / 18203)) (n := 12)
    (lo := (198085151 / 1000000000)) (hi := (6190161 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8203) = 1/(8203 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4116 : Bounds (-6190161 / 31250000) (-198085151 / 1000000000) (Real.log (8203 / 10000)) := by
  have h := reflection_log_4116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4117_neg : (179683 / 1000000000) ≤ -Real.log (10000000 / 10001797) ∧
    -Real.log (10000000 / 10001797) ≤ (44921 / 250000000) := by
  have h := checkLog_sound (w := (1797 / 20001797)) (n := 12)
    (lo := (179683 / 1000000000)) (hi := (44921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001797 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001797 / 10000000) = 1/(10000000 / 10001797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4117 : Bounds (179683 / 1000000000) (44921 / 250000000) (Real.log (10001797 / 10000000)) := by
  have h := reflection_log_4117_neg
  have he : Real.log (10001797 / 10000000) = -Real.log (10000000 / 10001797) := by
    rw [show ((10001797 / 10000000) : ℝ) = ((10000000 / 10001797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4118_neg : (44929 / 250000000) ≤ -Real.log (9998203 / 10000000) ∧
    -Real.log (9998203 / 10000000) ≤ (179717 / 1000000000) := by
  have h := checkLog_sound (w := (1797 / 19998203)) (n := 12)
    (lo := (44929 / 250000000)) (hi := (179717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998203) = 1/(9998203 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4118 : Bounds (-179717 / 1000000000) (-44929 / 250000000) (Real.log (9998203 / 10000000)) := by
  have h := reflection_log_4118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4119_neg : (86396021 / 1000000000) ≤ -Real.log (500000 / 545119) ∧
    -Real.log (500000 / 545119) ≤ (43198011 / 500000000) := by
  have h := checkLog_sound (w := (45119 / 1045119)) (n := 12)
    (lo := (86396021 / 1000000000)) (hi := (43198011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545119 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545119 / 500000) = 1/(500000 / 545119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4119 : Bounds (86396021 / 1000000000) (43198011 / 500000000) (Real.log (545119 / 500000)) := by
  have h := reflection_log_4119_neg
  have he : Real.log (545119 / 500000) = -Real.log (500000 / 545119) := by
    rw [show ((545119 / 500000) : ℝ) = ((500000 / 545119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4120_neg : (23643063 / 250000000) ≤ -Real.log (454881 / 500000) ∧
    -Real.log (454881 / 500000) ≤ (94572253 / 1000000000) := by
  have h := checkLog_sound (w := (45119 / 954881)) (n := 12)
    (lo := (23643063 / 250000000)) (hi := (94572253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454881) = 1/(454881 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4120 : Bounds (-94572253 / 1000000000) (-23643063 / 250000000) (Real.log (454881 / 500000)) := by
  have h := reflection_log_4120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4121_neg : (86606961 / 1000000000) ≤ -Real.log (250000 / 272617) ∧
    -Real.log (250000 / 272617) ≤ (43303481 / 500000000) := by
  have h := checkLog_sound (w := (22617 / 522617)) (n := 12)
    (lo := (86606961 / 1000000000)) (hi := (43303481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272617 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272617 / 250000) = 1/(250000 / 272617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4121 : Bounds (86606961 / 1000000000) (43303481 / 500000000) (Real.log (272617 / 250000)) := by
  have h := reflection_log_4121_neg
  have he : Real.log (272617 / 250000) = -Real.log (250000 / 272617) := by
    rw [show ((272617 / 250000) : ℝ) = ((250000 / 272617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4122_neg : (94825097 / 1000000000) ≤ -Real.log (227383 / 250000) ∧
    -Real.log (227383 / 250000) ≤ (47412549 / 500000000) := by
  have h := checkLog_sound (w := (22617 / 477383)) (n := 12)
    (lo := (94825097 / 1000000000)) (hi := (47412549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227383) = 1/(227383 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4122 : Bounds (-47412549 / 500000000) (-94825097 / 1000000000) (Real.log (227383 / 250000)) := by
  have h := reflection_log_4122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4123_neg : (1643627 / 200000000) ≤ -Real.log (61988471311 / 62500000000) ∧
    -Real.log (61988471311 / 62500000000) ≤ (1027267 / 125000000) := by
  have h := checkLog_sound (w := (511528689 / 124488471311)) (n := 12)
    (lo := (1643627 / 200000000)) (hi := (1027267 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61988471311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61988471311) = 1/(61988471311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4123 : Bounds (-1027267 / 125000000) (-1643627 / 200000000) (Real.log (61988471311 / 62500000000)) := by
  have h := reflection_log_4123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4124_neg : (8176231 / 1000000000) ≤ -Real.log (247964275839 / 250000000000) ∧
    -Real.log (247964275839 / 250000000000) ≤ (1022029 / 125000000) := by
  have h := checkLog_sound (w := (2035724161 / 497964275839)) (n := 12)
    (lo := (8176231 / 1000000000)) (hi := (1022029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247964275839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247964275839) = 1/(247964275839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4124 : Bounds (-1022029 / 125000000) (-8176231 / 1000000000) (Real.log (247964275839 / 250000000000)) := by
  have h := reflection_log_4124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4125_neg : (180968273 / 1000000000) ≤ -Real.log (50000000000 / 59918857899) ∧
    -Real.log (50000000000 / 59918857899) ≤ (90484137 / 500000000) := by
  have h := checkLog_sound (w := (9918857899 / 109918857899)) (n := 12)
    (lo := (180968273 / 1000000000)) (hi := (90484137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59918857899 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59918857899 / 50000000000) = 1/(50000000000 / 59918857899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4125 : Bounds (180968273 / 1000000000) (90484137 / 500000000) (Real.log (59918857899 / 50000000000)) := by
  have h := reflection_log_4125_neg
  have he : Real.log (59918857899 / 50000000000) = -Real.log (50000000000 / 59918857899) := by
    rw [show ((59918857899 / 50000000000) : ℝ) = ((50000000000 / 59918857899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4126_neg : (181432059 / 1000000000) ≤ -Real.log (125000000000 / 149866634709) ∧
    -Real.log (125000000000 / 149866634709) ≤ (9071603 / 50000000) := by
  have h := checkLog_sound (w := (24866634709 / 274866634709)) (n := 12)
    (lo := (181432059 / 1000000000)) (hi := (9071603 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149866634709 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149866634709 / 125000000000) = 1/(125000000000 / 149866634709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4126 : Bounds (181432059 / 1000000000) (9071603 / 50000000) (Real.log (149866634709 / 125000000000)) := by
  have h := reflection_log_4126_neg
  have he : Real.log (149866634709 / 125000000000) = -Real.log (125000000000 / 149866634709) := by
    rw [show ((149866634709 / 125000000000) : ℝ) = ((125000000000 / 149866634709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4127_neg : (7262773 / 20000000) ≤ -Real.log (50000000000 / 71891760117) ∧
    -Real.log (50000000000 / 71891760117) ≤ (363138651 / 1000000000) := by
  have h := checkLog_sound (w := (21891760117 / 121891760117)) (n := 12)
    (lo := (7262773 / 20000000)) (hi := (363138651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71891760117 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71891760117 / 50000000000) = 1/(50000000000 / 71891760117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4127 : Bounds (7262773 / 20000000) (363138651 / 1000000000) (Real.log (71891760117 / 50000000000)) := by
  have h := reflection_log_4127_neg
  have he : Real.log (71891760117 / 50000000000) = -Real.log (50000000000 / 71891760117) := by
    rw [show ((71891760117 / 50000000000) : ℝ) = ((50000000000 / 71891760117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4128_neg : (9083633 / 25000000) ≤ -Real.log (100000000000 / 143813239059) ∧
    -Real.log (100000000000 / 143813239059) ≤ (363345321 / 1000000000) := by
  have h := checkLog_sound (w := (43813239059 / 243813239059)) (n := 12)
    (lo := (9083633 / 25000000)) (hi := (363345321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143813239059 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143813239059 / 100000000000) = 1/(100000000000 / 143813239059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4128 : Bounds (9083633 / 25000000) (363345321 / 1000000000) (Real.log (143813239059 / 100000000000)) := by
  have h := reflection_log_4128_neg
  have he : Real.log (143813239059 / 100000000000) = -Real.log (100000000000 / 143813239059) := by
    rw [show ((143813239059 / 100000000000) : ℝ) = ((100000000000 / 143813239059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4129_neg : (41336233 / 250000000) ≤ -Real.log (5000 / 5899) ∧
    -Real.log (5000 / 5899) ≤ (165344933 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 10899)) (n := 12)
    (lo := (41336233 / 250000000)) (hi := (165344933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5899 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5899 / 5000) = 1/(5000 / 5899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4129 : Bounds (41336233 / 250000000) (165344933 / 1000000000) (Real.log (5899 / 5000)) := by
  have h := reflection_log_4129_neg
  have he : Real.log (5899 / 5000) = -Real.log (5000 / 5899) := by
    rw [show ((5899 / 5000) : ℝ) = ((5000 / 5899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4130_neg : (99103533 / 500000000) ≤ -Real.log (4101 / 5000) ∧
    -Real.log (4101 / 5000) ≤ (198207067 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 9101)) (n := 12)
    (lo := (99103533 / 500000000)) (hi := (198207067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4101) = 1/(4101 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4130 : Bounds (-198207067 / 1000000000) (-99103533 / 500000000) (Real.log (4101 / 5000)) := by
  have h := reflection_log_4130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4131_neg : (179783 / 1000000000) ≤ -Real.log (5000000 / 5000899) ∧
    -Real.log (5000000 / 5000899) ≤ (22473 / 125000000) := by
  have h := checkLog_sound (w := (899 / 10000899)) (n := 12)
    (lo := (179783 / 1000000000)) (hi := (22473 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000899 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000899 / 5000000) = 1/(5000000 / 5000899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4131 : Bounds (179783 / 1000000000) (22473 / 125000000) (Real.log (5000899 / 5000000)) := by
  have h := reflection_log_4131_neg
  have he : Real.log (5000899 / 5000000) = -Real.log (5000000 / 5000899) := by
    rw [show ((5000899 / 5000000) : ℝ) = ((5000000 / 5000899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4132_neg : (22477 / 125000000) ≤ -Real.log (4999101 / 5000000) ∧
    -Real.log (4999101 / 5000000) ≤ (179817 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 9999101)) (n := 12)
    (lo := (22477 / 125000000)) (hi := (179817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999101) = 1/(4999101 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4132 : Bounds (-179817 / 1000000000) (-22477 / 125000000) (Real.log (4999101 / 5000000)) := by
  have h := reflection_log_4132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4133_neg : (86441881 / 1000000000) ≤ -Real.log (62500 / 68143) ∧
    -Real.log (62500 / 68143) ≤ (43220941 / 500000000) := by
  have h := checkLog_sound (w := (5643 / 130643)) (n := 12)
    (lo := (86441881 / 1000000000)) (hi := (43220941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68143 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68143 / 62500) = 1/(62500 / 68143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4133 : Bounds (86441881 / 1000000000) (43220941 / 500000000) (Real.log (68143 / 62500)) := by
  have h := reflection_log_4133_neg
  have he : Real.log (68143 / 62500) = -Real.log (62500 / 68143) := by
    rw [show ((68143 / 62500) : ℝ) = ((62500 / 68143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4134_neg : (94627213 / 1000000000) ≤ -Real.log (56857 / 62500) ∧
    -Real.log (56857 / 62500) ≤ (47313607 / 500000000) := by
  have h := checkLog_sound (w := (5643 / 119357)) (n := 12)
    (lo := (94627213 / 1000000000)) (hi := (47313607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56857) = 1/(56857 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4134 : Bounds (-47313607 / 500000000) (-94627213 / 1000000000) (Real.log (56857 / 62500)) := by
  have h := reflection_log_4134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4135_neg : (86653729 / 1000000000) ≤ -Real.log (1000000 / 1090519) ∧
    -Real.log (1000000 / 1090519) ≤ (8665373 / 100000000) := by
  have h := checkLog_sound (w := (90519 / 2090519)) (n := 12)
    (lo := (86653729 / 1000000000)) (hi := (8665373 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090519 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090519 / 1000000) = 1/(1000000 / 1090519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4135 : Bounds (86653729 / 1000000000) (8665373 / 100000000) (Real.log (1090519 / 1000000)) := by
  have h := reflection_log_4135_neg
  have he : Real.log (1090519 / 1000000) = -Real.log (1000000 / 1090519) := by
    rw [show ((1090519 / 1000000) : ℝ) = ((1000000 / 1090519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4136_neg : (94881171 / 1000000000) ≤ -Real.log (909481 / 1000000) ∧
    -Real.log (909481 / 1000000) ≤ (23720293 / 250000000) := by
  have h := checkLog_sound (w := (90519 / 1909481)) (n := 12)
    (lo := (94881171 / 1000000000)) (hi := (23720293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909481) = 1/(909481 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4136 : Bounds (-23720293 / 250000000) (-94881171 / 1000000000) (Real.log (909481 / 1000000)) := by
  have h := reflection_log_4136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4137_neg : (4113721 / 500000000) ≤ -Real.log (991806310639 / 1000000000000) ∧
    -Real.log (991806310639 / 1000000000000) ≤ (8227443 / 1000000000) := by
  have h := checkLog_sound (w := (8193689361 / 1991806310639)) (n := 12)
    (lo := (4113721 / 500000000)) (hi := (8227443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991806310639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991806310639) = 1/(991806310639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4137 : Bounds (-8227443 / 1000000000) (-4113721 / 500000000) (Real.log (991806310639 / 1000000000000)) := by
  have h := reflection_log_4137_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4138_neg : (8185331 / 1000000000) ≤ -Real.log (3874406551 / 3906250000) ∧
    -Real.log (3874406551 / 3906250000) ≤ (2046333 / 250000000) := by
  have h := checkLog_sound (w := (31843449 / 7780656551)) (n := 12)
    (lo := (8185331 / 1000000000)) (hi := (2046333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3874406551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3874406551) = 1/(3874406551 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4138 : Bounds (-2046333 / 250000000) (-8185331 / 1000000000) (Real.log (3874406551 / 3906250000)) := by
  have h := reflection_log_4138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4139_neg : (90534547 / 500000000) ≤ -Real.log (500000000000 / 599248993087) ∧
    -Real.log (500000000000 / 599248993087) ≤ (36213819 / 200000000) := by
  have h := checkLog_sound (w := (99248993087 / 1099248993087)) (n := 12)
    (lo := (90534547 / 500000000)) (hi := (36213819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599248993087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599248993087 / 500000000000) = 1/(500000000000 / 599248993087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4139 : Bounds (90534547 / 500000000) (36213819 / 200000000) (Real.log (599248993087 / 500000000000)) := by
  have h := reflection_log_4139_neg
  have he : Real.log (599248993087 / 500000000000) = -Real.log (500000000000 / 599248993087) := by
    rw [show ((599248993087 / 500000000000) : ℝ) = ((500000000000 / 599248993087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4140_neg : (181534901 / 1000000000) ≤ -Real.log (500000000000 / 599528192453) ∧
    -Real.log (500000000000 / 599528192453) ≤ (90767451 / 500000000) := by
  have h := checkLog_sound (w := (99528192453 / 1099528192453)) (n := 12)
    (lo := (181534901 / 1000000000)) (hi := (90767451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599528192453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599528192453 / 500000000000) = 1/(500000000000 / 599528192453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4140 : Bounds (181534901 / 1000000000) (90767451 / 500000000) (Real.log (599528192453 / 500000000000)) := by
  have h := reflection_log_4140_neg
  have he : Real.log (599528192453 / 500000000000) = -Real.log (500000000000 / 599528192453) := by
    rw [show ((599528192453 / 500000000000) : ℝ) = ((500000000000 / 599528192453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4141_neg : (9083633 / 25000000) ≤ -Real.log (250000000000 / 359533097647) ∧
    -Real.log (250000000000 / 359533097647) ≤ (363345321 / 1000000000) := by
  have h := checkLog_sound (w := (109533097647 / 609533097647)) (n := 12)
    (lo := (9083633 / 25000000)) (hi := (363345321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359533097647 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359533097647 / 250000000000) = 1/(250000000000 / 359533097647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4141 : Bounds (9083633 / 25000000) (363345321 / 1000000000) (Real.log (359533097647 / 250000000000)) := by
  have h := reflection_log_4141_neg
  have he : Real.log (359533097647 / 250000000000) = -Real.log (250000000000 / 359533097647) := by
    rw [show ((359533097647 / 250000000000) : ℝ) = ((250000000000 / 359533097647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4142_neg : (181775999 / 500000000) ≤ -Real.log (500000000000 / 719214825653) ∧
    -Real.log (500000000000 / 719214825653) ≤ (363551999 / 1000000000) := by
  have h := checkLog_sound (w := (219214825653 / 1219214825653)) (n := 12)
    (lo := (181775999 / 500000000)) (hi := (363551999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719214825653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719214825653 / 500000000000) = 1/(500000000000 / 719214825653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4142 : Bounds (181775999 / 500000000) (363551999 / 1000000000) (Real.log (719214825653 / 500000000000)) := by
  have h := reflection_log_4142_neg
  have he : Real.log (719214825653 / 500000000000) = -Real.log (500000000000 / 719214825653) := by
    rw [show ((719214825653 / 500000000000) : ℝ) = ((500000000000 / 719214825653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4143_neg : (165429689 / 1000000000) ≤ -Real.log (10000 / 11799) ∧
    -Real.log (10000 / 11799) ≤ (16542969 / 100000000) := by
  have h := checkLog_sound (w := (1799 / 21799)) (n := 12)
    (lo := (165429689 / 1000000000)) (hi := (16542969 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11799 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11799 / 10000) = 1/(10000 / 11799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4143 : Bounds (165429689 / 1000000000) (16542969 / 100000000) (Real.log (11799 / 10000)) := by
  have h := reflection_log_4143_neg
  have he : Real.log (11799 / 10000) = -Real.log (10000 / 11799) := by
    rw [show ((11799 / 10000) : ℝ) = ((10000 / 11799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4144_neg : (99164497 / 500000000) ≤ -Real.log (8201 / 10000) ∧
    -Real.log (8201 / 10000) ≤ (39665799 / 200000000) := by
  have h := checkLog_sound (w := (1799 / 18201)) (n := 12)
    (lo := (99164497 / 500000000)) (hi := (39665799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8201) = 1/(8201 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4144 : Bounds (-39665799 / 200000000) (-99164497 / 500000000) (Real.log (8201 / 10000)) := by
  have h := reflection_log_4144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4145_neg : (179883 / 1000000000) ≤ -Real.log (10000000 / 10001799) ∧
    -Real.log (10000000 / 10001799) ≤ (44971 / 250000000) := by
  have h := checkLog_sound (w := (1799 / 20001799)) (n := 12)
    (lo := (179883 / 1000000000)) (hi := (44971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001799 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001799 / 10000000) = 1/(10000000 / 10001799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4145 : Bounds (179883 / 1000000000) (44971 / 250000000) (Real.log (10001799 / 10000000)) := by
  have h := reflection_log_4145_neg
  have he : Real.log (10001799 / 10000000) = -Real.log (10000000 / 10001799) := by
    rw [show ((10001799 / 10000000) : ℝ) = ((10000000 / 10001799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4146_neg : (44979 / 250000000) ≤ -Real.log (9998201 / 10000000) ∧
    -Real.log (9998201 / 10000000) ≤ (179917 / 1000000000) := by
  have h := checkLog_sound (w := (1799 / 19998201)) (n := 12)
    (lo := (44979 / 250000000)) (hi := (179917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998201) = 1/(9998201 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4146 : Bounds (-179917 / 1000000000) (-44979 / 250000000) (Real.log (9998201 / 10000000)) := by
  have h := reflection_log_4146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4147_neg : (86488657 / 1000000000) ≤ -Real.log (1000000 / 1090339) ∧
    -Real.log (1000000 / 1090339) ≤ (43244329 / 500000000) := by
  have h := checkLog_sound (w := (90339 / 2090339)) (n := 12)
    (lo := (86488657 / 1000000000)) (hi := (43244329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090339 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090339 / 1000000) = 1/(1000000 / 1090339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4147 : Bounds (86488657 / 1000000000) (43244329 / 500000000) (Real.log (1090339 / 1000000)) := by
  have h := reflection_log_4147_neg
  have he : Real.log (1090339 / 1000000) = -Real.log (1000000 / 1090339) := by
    rw [show ((1090339 / 1000000) : ℝ) = ((1000000 / 1090339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4148_neg : (23670819 / 250000000) ≤ -Real.log (909661 / 1000000) ∧
    -Real.log (909661 / 1000000) ≤ (94683277 / 1000000000) := by
  have h := checkLog_sound (w := (90339 / 1909661)) (n := 12)
    (lo := (23670819 / 250000000)) (hi := (94683277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909661) = 1/(909661 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4148 : Bounds (-94683277 / 1000000000) (-23670819 / 250000000) (Real.log (909661 / 1000000)) := by
  have h := reflection_log_4148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4149_neg : (17340099 / 200000000) ≤ -Real.log (100000 / 109057) ∧
    -Real.log (100000 / 109057) ≤ (5418781 / 62500000) := by
  have h := checkLog_sound (w := (9057 / 209057)) (n := 12)
    (lo := (17340099 / 200000000)) (hi := (5418781 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109057 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109057 / 100000) = 1/(100000 / 109057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4149 : Bounds (17340099 / 200000000) (5418781 / 62500000) (Real.log (109057 / 100000)) := by
  have h := reflection_log_4149_neg
  have he : Real.log (109057 / 100000) = -Real.log (100000 / 109057) := by
    rw [show ((109057 / 100000) : ℝ) = ((100000 / 109057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4150_neg : (94937249 / 1000000000) ≤ -Real.log (90943 / 100000) ∧
    -Real.log (90943 / 100000) ≤ (379749 / 4000000) := by
  have h := checkLog_sound (w := (9057 / 190943)) (n := 12)
    (lo := (94937249 / 1000000000)) (hi := (379749 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90943) = 1/(90943 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4150 : Bounds (-379749 / 4000000) (-94937249 / 1000000000) (Real.log (90943 / 100000)) := by
  have h := reflection_log_4150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4151_neg : (4118377 / 500000000) ≤ -Real.log (9917970751 / 10000000000) ∧
    -Real.log (9917970751 / 10000000000) ≤ (1647351 / 200000000) := by
  have h := checkLog_sound (w := (82029249 / 19917970751)) (n := 12)
    (lo := (4118377 / 500000000)) (hi := (1647351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9917970751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9917970751) = 1/(9917970751 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4151 : Bounds (-1647351 / 200000000) (-4118377 / 500000000) (Real.log (9917970751 / 10000000000)) := by
  have h := reflection_log_4151_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4152_neg : (8194619 / 1000000000) ≤ -Real.log (991838865079 / 1000000000000) ∧
    -Real.log (991838865079 / 1000000000000) ≤ (409731 / 50000000) := by
  have h := checkLog_sound (w := (8161134921 / 1991838865079)) (n := 12)
    (lo := (8194619 / 1000000000)) (hi := (409731 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991838865079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991838865079) = 1/(991838865079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4152 : Bounds (-409731 / 50000000) (-8194619 / 1000000000) (Real.log (991838865079 / 1000000000000)) := by
  have h := reflection_log_4152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4153_neg : (181171933 / 1000000000) ≤ -Real.log (125000000000 / 149827655577) ∧
    -Real.log (125000000000 / 149827655577) ≤ (90585967 / 500000000) := by
  have h := checkLog_sound (w := (24827655577 / 274827655577)) (n := 12)
    (lo := (181171933 / 1000000000)) (hi := (90585967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149827655577 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149827655577 / 125000000000) = 1/(125000000000 / 149827655577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4153 : Bounds (181171933 / 1000000000) (90585967 / 500000000) (Real.log (149827655577 / 125000000000)) := by
  have h := reflection_log_4153_neg
  have he : Real.log (149827655577 / 125000000000) = -Real.log (125000000000 / 149827655577) := by
    rw [show ((149827655577 / 125000000000) : ℝ) = ((125000000000 / 149827655577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4154_neg : (11352359 / 62500000) ≤ -Real.log (100000000000 / 119917970597) ∧
    -Real.log (100000000000 / 119917970597) ≤ (36327549 / 200000000) := by
  have h := checkLog_sound (w := (19917970597 / 219917970597)) (n := 12)
    (lo := (11352359 / 62500000)) (hi := (36327549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119917970597 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119917970597 / 100000000000) = 1/(100000000000 / 119917970597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4154 : Bounds (11352359 / 62500000) (36327549 / 200000000) (Real.log (119917970597 / 100000000000)) := by
  have h := reflection_log_4154_neg
  have he : Real.log (119917970597 / 100000000000) = -Real.log (100000000000 / 119917970597) := by
    rw [show ((119917970597 / 100000000000) : ℝ) = ((100000000000 / 119917970597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4155_neg : (181775999 / 500000000) ≤ -Real.log (125000000000 / 179803706413) ∧
    -Real.log (125000000000 / 179803706413) ≤ (363551999 / 1000000000) := by
  have h := checkLog_sound (w := (54803706413 / 304803706413)) (n := 12)
    (lo := (181775999 / 500000000)) (hi := (363551999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179803706413 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179803706413 / 125000000000) = 1/(125000000000 / 179803706413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4155 : Bounds (181775999 / 500000000) (363551999 / 1000000000) (Real.log (179803706413 / 125000000000)) := by
  have h := reflection_log_4155_neg
  have he : Real.log (179803706413 / 125000000000) = -Real.log (125000000000 / 179803706413) := by
    rw [show ((179803706413 / 125000000000) : ℝ) = ((125000000000 / 179803706413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4156_neg : (90939671 / 250000000) ≤ -Real.log (250000000000 / 359681746129) ∧
    -Real.log (250000000000 / 359681746129) ≤ (72751737 / 200000000) := by
  have h := checkLog_sound (w := (109681746129 / 609681746129)) (n := 12)
    (lo := (90939671 / 250000000)) (hi := (72751737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359681746129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359681746129 / 250000000000) = 1/(250000000000 / 359681746129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4156 : Bounds (90939671 / 250000000) (72751737 / 200000000) (Real.log (359681746129 / 250000000000)) := by
  have h := reflection_log_4156_neg
  have he : Real.log (359681746129 / 250000000000) = -Real.log (250000000000 / 359681746129) := by
    rw [show ((359681746129 / 250000000000) : ℝ) = ((250000000000 / 359681746129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4157_neg : (82757219 / 500000000) ≤ -Real.log (50 / 59) ∧
    -Real.log (50 / 59) ≤ (165514439 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 109)) (n := 12)
    (lo := (82757219 / 500000000)) (hi := (165514439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59 / 50) = 1/(50 / 59) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4157 : Bounds (82757219 / 500000000) (165514439 / 1000000000) (Real.log (59 / 50)) := by
  have h := reflection_log_4157_neg
  have he : Real.log (59 / 50) = -Real.log (50 / 59) := by
    rw [show ((59 / 50) : ℝ) = ((50 / 59) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4158_neg : (99225469 / 500000000) ≤ -Real.log (41 / 50) ∧
    -Real.log (41 / 50) ≤ (198450939 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 91)) (n := 12)
    (lo := (99225469 / 500000000)) (hi := (198450939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 41) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 41) = 1/(41 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4158 : Bounds (-198450939 / 1000000000) (-99225469 / 500000000) (Real.log (41 / 50)) := by
  have h := reflection_log_4158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4159_neg : (179983 / 1000000000) ≤ -Real.log (50000 / 50009) ∧
    -Real.log (50000 / 50009) ≤ (11249 / 62500000) := by
  have h := checkLog_sound (w := (9 / 100009)) (n := 12)
    (lo := (179983 / 1000000000)) (hi := (11249 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50009 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50009 / 50000) = 1/(50000 / 50009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4159 : Bounds (179983 / 1000000000) (11249 / 62500000) (Real.log (50009 / 50000)) := by
  have h := reflection_log_4159_neg
  have he : Real.log (50009 / 50000) = -Real.log (50000 / 50009) := by
    rw [show ((50009 / 50000) : ℝ) = ((50000 / 50009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


