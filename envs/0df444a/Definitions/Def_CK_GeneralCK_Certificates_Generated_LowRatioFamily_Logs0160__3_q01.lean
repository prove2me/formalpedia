-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0160__3_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0160__3_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T04:46:14.411431+00:00
-- url     : https://prove2.me/theorems/f2ac1a6f-1df1-49ea-9310-f3efdee29abe
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0162) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0162) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0162) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0160 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0161, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0162) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0160__3_q00

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10304_neg : (7546477 / 250000000) ≤ -Real.log (242566284039 / 250000000000) ∧
    -Real.log (242566284039 / 250000000000) ≤ (30185909 / 1000000000) := by
  have h := checkLog_sound (w := (7433715961 / 492566284039)) (n := 12)
    (lo := (7546477 / 250000000)) (hi := (30185909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242566284039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242566284039) = 1/(242566284039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10304 : Bounds (-30185909 / 1000000000) (-7546477 / 250000000) (Real.log (242566284039 / 250000000000)) := by
  have h := reflection_log_10304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10305_neg : (348356591 / 1000000000) ≤ -Real.log (500000000000 / 708368678117) ∧
    -Real.log (500000000000 / 708368678117) ≤ (21772287 / 62500000) := by
  have h := checkLog_sound (w := (208368678117 / 1208368678117)) (n := 12)
    (lo := (348356591 / 1000000000)) (hi := (21772287 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708368678117 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708368678117 / 500000000000) = 1/(500000000000 / 708368678117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10305 : Bounds (348356591 / 1000000000) (21772287 / 62500000) (Real.log (708368678117 / 500000000000)) := by
  have h := reflection_log_10305_neg
  have he : Real.log (708368678117 / 500000000000) = -Real.log (500000000000 / 708368678117) := by
    rw [show ((708368678117 / 500000000000) : ℝ) = ((500000000000 / 708368678117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10306_neg : (350139883 / 1000000000) ≤ -Real.log (500000000000 / 709633033627) ∧
    -Real.log (500000000000 / 709633033627) ≤ (87534971 / 250000000) := by
  have h := checkLog_sound (w := (209633033627 / 1209633033627)) (n := 12)
    (lo := (350139883 / 1000000000)) (hi := (87534971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709633033627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709633033627 / 500000000000) = 1/(500000000000 / 709633033627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10306 : Bounds (350139883 / 1000000000) (87534971 / 250000000) (Real.log (709633033627 / 500000000000)) := by
  have h := reflection_log_10306_neg
  have he : Real.log (709633033627 / 500000000000) = -Real.log (500000000000 / 709633033627) := by
    rw [show ((709633033627 / 500000000000) : ℝ) = ((500000000000 / 709633033627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10307_neg : (175916421 / 250000000) ≤ -Real.log (250000000000 / 505287009063) ∧
    -Real.log (250000000000 / 505287009063) ≤ (351832843 / 500000000) := by
  have h := checkLog_sound (w := (5287009063 / 1005287009063)) (n := 12)
    (lo := (1314813 / 125000000)) (hi := (2103701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((505287009063 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(505287009063 / 500000000000) = 1/(250000000000 / 505287009063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10307 : Bounds (175916421 / 250000000) (351832843 / 500000000) (Real.log (505287009063 / 250000000000)) := by
  have h := reflection_log_10307_neg
  have he : Real.log (505287009063 / 250000000000) = -Real.log (250000000000 / 505287009063) := by
    rw [show ((505287009063 / 250000000000) : ℝ) = ((250000000000 / 505287009063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10308_neg : (141184901 / 200000000) ≤ -Real.log (100000000000 / 202571860817) ∧
    -Real.log (100000000000 / 202571860817) ≤ (705924507 / 1000000000) := by
  have h := checkLog_sound (w := (2571860817 / 402571860817)) (n := 12)
    (lo := (511093 / 40000000)) (hi := (6388663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202571860817 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(202571860817 / 200000000000) = 1/(100000000000 / 202571860817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10308 : Bounds (141184901 / 200000000) (705924507 / 1000000000) (Real.log (202571860817 / 100000000000)) := by
  have h := reflection_log_10308_neg
  have he : Real.log (202571860817 / 100000000000) = -Real.log (100000000000 / 202571860817) := by
    rw [show ((202571860817 / 100000000000) : ℝ) = ((100000000000 / 202571860817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10309_neg : (292669613 / 1000000000) ≤ -Real.log (50 / 67) ∧
    -Real.log (50 / 67) ≤ (146334807 / 500000000) := by
  have h := checkLog_sound (w := (17 / 117)) (n := 12)
    (lo := (292669613 / 1000000000)) (hi := (146334807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67 / 50) = 1/(50 / 67) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10309 : Bounds (292669613 / 1000000000) (146334807 / 500000000) (Real.log (67 / 50)) := by
  have h := reflection_log_10309_neg
  have he : Real.log (67 / 50) = -Real.log (50 / 67) := by
    rw [show ((67 / 50) : ℝ) = ((50 / 67) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10310_neg : (415515443 / 1000000000) ≤ -Real.log (33 / 50) ∧
    -Real.log (33 / 50) ≤ (103878861 / 250000000) := by
  have h := checkLog_sound (w := (17 / 83)) (n := 12)
    (lo := (415515443 / 1000000000)) (hi := (103878861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 33) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 33) = 1/(33 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10310 : Bounds (-103878861 / 250000000) (-415515443 / 1000000000) (Real.log (33 / 50)) := by
  have h := reflection_log_10310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10311_neg : (169971 / 500000000) ≤ -Real.log (50000 / 50017) ∧
    -Real.log (50000 / 50017) ≤ (339943 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 100017)) (n := 12)
    (lo := (169971 / 500000000)) (hi := (339943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50017 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50017 / 50000) = 1/(50000 / 50017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10311 : Bounds (169971 / 500000000) (339943 / 1000000000) (Real.log (50017 / 50000)) := by
  have h := reflection_log_10311_neg
  have he : Real.log (50017 / 50000) = -Real.log (50000 / 50017) := by
    rw [show ((50017 / 50000) : ℝ) = ((50000 / 50017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10312_neg : (340057 / 1000000000) ≤ -Real.log (49983 / 50000) ∧
    -Real.log (49983 / 50000) ≤ (170029 / 500000000) := by
  have h := checkLog_sound (w := (17 / 99983)) (n := 12)
    (lo := (340057 / 1000000000)) (hi := (170029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49983) = 1/(49983 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10312 : Bounds (-170029 / 500000000) (-340057 / 1000000000) (Real.log (49983 / 50000)) := by
  have h := reflection_log_10312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10313_neg : (79769923 / 500000000) ≤ -Real.log (1000000 / 1172971) ∧
    -Real.log (1000000 / 1172971) ≤ (159539847 / 1000000000) := by
  have h := checkLog_sound (w := (172971 / 2172971)) (n := 12)
    (lo := (79769923 / 500000000)) (hi := (159539847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1172971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1172971 / 1000000) = 1/(1000000 / 1172971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10313 : Bounds (79769923 / 500000000) (159539847 / 1000000000) (Real.log (1172971 / 1000000)) := by
  have h := reflection_log_10313_neg
  have he : Real.log (1172971 / 1000000) = -Real.log (1000000 / 1172971) := by
    rw [show ((1172971 / 1000000) : ℝ) = ((1000000 / 1172971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10314_neg : (94957759 / 500000000) ≤ -Real.log (827029 / 1000000) ∧
    -Real.log (827029 / 1000000) ≤ (189915519 / 1000000000) := by
  have h := checkLog_sound (w := (172971 / 1827029)) (n := 12)
    (lo := (94957759 / 500000000)) (hi := (189915519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 827029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 827029) = 1/(827029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10314 : Bounds (-189915519 / 1000000000) (-94957759 / 500000000) (Real.log (827029 / 1000000)) := by
  have h := reflection_log_10314_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10315_neg : (16027787 / 100000000) ≤ -Real.log (1000000 / 1173837) ∧
    -Real.log (1000000 / 1173837) ≤ (160277871 / 1000000000) := by
  have h := checkLog_sound (w := (173837 / 2173837)) (n := 12)
    (lo := (16027787 / 100000000)) (hi := (160277871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1173837 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1173837 / 1000000) = 1/(1000000 / 1173837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10315 : Bounds (16027787 / 100000000) (160277871 / 1000000000) (Real.log (1173837 / 1000000)) := by
  have h := reflection_log_10315_neg
  have he : Real.log (1173837 / 1000000) = -Real.log (1000000 / 1173837) := by
    rw [show ((1173837 / 1000000) : ℝ) = ((1000000 / 1173837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10316_neg : (47740797 / 250000000) ≤ -Real.log (826163 / 1000000) ∧
    -Real.log (826163 / 1000000) ≤ (190963189 / 1000000000) := by
  have h := checkLog_sound (w := (173837 / 1826163)) (n := 12)
    (lo := (47740797 / 250000000)) (hi := (190963189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 826163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 826163) = 1/(826163 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10316 : Bounds (-190963189 / 1000000000) (-47740797 / 250000000) (Real.log (826163 / 1000000)) := by
  have h := reflection_log_10316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10317_neg : (15342659 / 500000000) ≤ -Real.log (969780697431 / 1000000000000) ∧
    -Real.log (969780697431 / 1000000000000) ≤ (30685319 / 1000000000) := by
  have h := checkLog_sound (w := (30219302569 / 1969780697431)) (n := 12)
    (lo := (15342659 / 500000000)) (hi := (30685319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969780697431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969780697431) = 1/(969780697431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10317 : Bounds (-30685319 / 1000000000) (-15342659 / 500000000) (Real.log (969780697431 / 1000000000000)) := by
  have h := reflection_log_10317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10318_neg : (30375671 / 1000000000) ≤ -Real.log (970081033159 / 1000000000000) ∧
    -Real.log (970081033159 / 1000000000000) ≤ (3796959 / 125000000) := by
  have h := checkLog_sound (w := (29918966841 / 1970081033159)) (n := 12)
    (lo := (30375671 / 1000000000)) (hi := (3796959 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970081033159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970081033159) = 1/(970081033159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10318 : Bounds (-3796959 / 125000000) (-30375671 / 1000000000) (Real.log (970081033159 / 1000000000000)) := by
  have h := reflection_log_10318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10319_neg : (87363841 / 250000000) ≤ -Real.log (500000000000 / 709147442229) ∧
    -Real.log (500000000000 / 709147442229) ≤ (69891073 / 200000000) := by
  have h := checkLog_sound (w := (209147442229 / 1209147442229)) (n := 12)
    (lo := (87363841 / 250000000)) (hi := (69891073 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709147442229 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709147442229 / 500000000000) = 1/(500000000000 / 709147442229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10319 : Bounds (87363841 / 250000000) (69891073 / 200000000) (Real.log (709147442229 / 500000000000)) := by
  have h := reflection_log_10319_neg
  have he : Real.log (709147442229 / 500000000000) = -Real.log (500000000000 / 709147442229) := by
    rw [show ((709147442229 / 500000000000) : ℝ) = ((500000000000 / 709147442229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10320_neg : (175620529 / 500000000) ≤ -Real.log (250000000000 / 355207446957) ∧
    -Real.log (250000000000 / 355207446957) ≤ (351241059 / 1000000000) := by
  have h := checkLog_sound (w := (105207446957 / 605207446957)) (n := 12)
    (lo := (175620529 / 500000000)) (hi := (351241059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355207446957 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355207446957 / 250000000000) = 1/(250000000000 / 355207446957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10320 : Bounds (175620529 / 500000000) (351241059 / 1000000000) (Real.log (355207446957 / 250000000000)) := by
  have h := reflection_log_10320_neg
  have he : Real.log (355207446957 / 250000000000) = -Real.log (250000000000 / 355207446957) := by
    rw [show ((355207446957 / 250000000000) : ℝ) = ((250000000000 / 355207446957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10321_neg : (141184901 / 200000000) ≤ -Real.log (125000000000 / 253214826021) ∧
    -Real.log (125000000000 / 253214826021) ≤ (705924507 / 1000000000) := by
  have h := checkLog_sound (w := (3214826021 / 503214826021)) (n := 12)
    (lo := (511093 / 40000000)) (hi := (6388663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253214826021 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(253214826021 / 250000000000) = 1/(125000000000 / 253214826021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10321 : Bounds (141184901 / 200000000) (705924507 / 1000000000) (Real.log (253214826021 / 125000000000)) := by
  have h := reflection_log_10321_neg
  have he : Real.log (253214826021 / 125000000000) = -Real.log (125000000000 / 253214826021) := by
    rw [show ((253214826021 / 125000000000) : ℝ) = ((125000000000 / 253214826021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10322_neg : (708185057 / 1000000000) ≤ -Real.log (31250000000 / 63446969697) ∧
    -Real.log (31250000000 / 63446969697) ≤ (708185059 / 1000000000) := by
  have h := checkLog_sound (w := (946969697 / 125946969697)) (n := 12)
    (lo := (15037877 / 1000000000)) (hi := (7518939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63446969697 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63446969697 / 62500000000) = 1/(31250000000 / 63446969697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10322 : Bounds (708185057 / 1000000000) (708185059 / 1000000000) (Real.log (63446969697 / 31250000000)) := by
  have h := reflection_log_10322_neg
  have he : Real.log (63446969697 / 31250000000) = -Real.log (31250000000 / 63446969697) := by
    rw [show ((63446969697 / 31250000000) : ℝ) = ((31250000000 / 63446969697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10323_neg : (73353901 / 250000000) ≤ -Real.log (1000 / 1341) ∧
    -Real.log (1000 / 1341) ≤ (58683121 / 200000000) := by
  have h := checkLog_sound (w := (341 / 2341)) (n := 12)
    (lo := (73353901 / 250000000)) (hi := (58683121 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341 / 1000) = 1/(1000 / 1341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10323 : Bounds (73353901 / 250000000) (58683121 / 200000000) (Real.log (1341 / 1000)) := by
  have h := reflection_log_10323_neg
  have he : Real.log (1341 / 1000) = -Real.log (1000 / 1341) := by
    rw [show ((1341 / 1000) : ℝ) = ((1000 / 1341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10324_neg : (6516121 / 15625000) ≤ -Real.log (659 / 1000) ∧
    -Real.log (659 / 1000) ≤ (83406349 / 200000000) := by
  have h := checkLog_sound (w := (341 / 1659)) (n := 12)
    (lo := (6516121 / 15625000)) (hi := (83406349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 659) = 1/(659 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10324 : Bounds (-83406349 / 200000000) (-6516121 / 15625000) (Real.log (659 / 1000)) := by
  have h := reflection_log_10324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10325_neg : (340941 / 1000000000) ≤ -Real.log (1000000 / 1000341) ∧
    -Real.log (1000000 / 1000341) ≤ (170471 / 500000000) := by
  have h := checkLog_sound (w := (341 / 2000341)) (n := 12)
    (lo := (340941 / 1000000000)) (hi := (170471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000341 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000341 / 1000000) = 1/(1000000 / 1000341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10325 : Bounds (340941 / 1000000000) (170471 / 500000000) (Real.log (1000341 / 1000000)) := by
  have h := reflection_log_10325_neg
  have he : Real.log (1000341 / 1000000) = -Real.log (1000000 / 1000341) := by
    rw [show ((1000341 / 1000000) : ℝ) = ((1000000 / 1000341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10326_neg : (170529 / 500000000) ≤ -Real.log (999659 / 1000000) ∧
    -Real.log (999659 / 1000000) ≤ (341059 / 1000000000) := by
  have h := checkLog_sound (w := (341 / 1999659)) (n := 12)
    (lo := (170529 / 500000000)) (hi := (341059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999659) = 1/(999659 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10326 : Bounds (-341059 / 1000000000) (-170529 / 500000000) (Real.log (999659 / 1000000)) := by
  have h := reflection_log_10326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10327_neg : (39998323 / 250000000) ≤ -Real.log (1000000 / 1173503) ∧
    -Real.log (1000000 / 1173503) ≤ (159993293 / 1000000000) := by
  have h := checkLog_sound (w := (173503 / 2173503)) (n := 12)
    (lo := (39998323 / 250000000)) (hi := (159993293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1173503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1173503 / 1000000) = 1/(1000000 / 1173503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10327 : Bounds (39998323 / 250000000) (159993293 / 1000000000) (Real.log (1173503 / 1000000)) := by
  have h := reflection_log_10327_neg
  have he : Real.log (1173503 / 1000000) = -Real.log (1000000 / 1173503) := by
    rw [show ((1173503 / 1000000) : ℝ) = ((1000000 / 1173503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10328_neg : (190558991 / 1000000000) ≤ -Real.log (826497 / 1000000) ∧
    -Real.log (826497 / 1000000) ≤ (11909937 / 62500000) := by
  have h := checkLog_sound (w := (173503 / 1826497)) (n := 12)
    (lo := (190558991 / 1000000000)) (hi := (11909937 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 826497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 826497) = 1/(826497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10328 : Bounds (-11909937 / 62500000) (-190558991 / 1000000000) (Real.log (826497 / 1000000)) := by
  have h := reflection_log_10328_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10329_neg : (160731833 / 1000000000) ≤ -Real.log (100000 / 117437) ∧
    -Real.log (100000 / 117437) ≤ (80365917 / 500000000) := by
  have h := checkLog_sound (w := (17437 / 217437)) (n := 12)
    (lo := (160731833 / 1000000000)) (hi := (80365917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117437 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117437 / 100000) = 1/(100000 / 117437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10329 : Bounds (160731833 / 1000000000) (80365917 / 500000000) (Real.log (117437 / 100000)) := by
  have h := reflection_log_10329_neg
  have he : Real.log (117437 / 100000) = -Real.log (100000 / 117437) := by
    rw [show ((117437 / 100000) : ℝ) = ((100000 / 117437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10330_neg : (191608547 / 1000000000) ≤ -Real.log (82563 / 100000) ∧
    -Real.log (82563 / 100000) ≤ (47902137 / 250000000) := by
  have h := checkLog_sound (w := (17437 / 182563)) (n := 12)
    (lo := (191608547 / 1000000000)) (hi := (47902137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82563) = 1/(82563 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10330 : Bounds (-47902137 / 250000000) (-191608547 / 1000000000) (Real.log (82563 / 100000)) := by
  have h := reflection_log_10330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10331_neg : (15438357 / 500000000) ≤ -Real.log (9695951031 / 10000000000) ∧
    -Real.log (9695951031 / 10000000000) ≤ (6175343 / 200000000) := by
  have h := checkLog_sound (w := (304048969 / 19695951031)) (n := 12)
    (lo := (15438357 / 500000000)) (hi := (6175343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9695951031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9695951031) = 1/(9695951031 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10331 : Bounds (-6175343 / 200000000) (-15438357 / 500000000) (Real.log (9695951031 / 10000000000)) := by
  have h := reflection_log_10331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10332_neg : (15282849 / 500000000) ≤ -Real.log (969896708991 / 1000000000000) ∧
    -Real.log (969896708991 / 1000000000000) ≤ (30565699 / 1000000000) := by
  have h := checkLog_sound (w := (30103291009 / 1969896708991)) (n := 12)
    (lo := (15282849 / 500000000)) (hi := (30565699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969896708991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969896708991) = 1/(969896708991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10332 : Bounds (-30565699 / 1000000000) (-15282849 / 500000000) (Real.log (969896708991 / 1000000000000)) := by
  have h := reflection_log_10332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10333_neg : (87638071 / 250000000) ≤ -Real.log (62500000000 / 88740718357) ∧
    -Real.log (62500000000 / 88740718357) ≤ (70110457 / 200000000) := by
  have h := checkLog_sound (w := (26240718357 / 151240718357)) (n := 12)
    (lo := (87638071 / 250000000)) (hi := (70110457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88740718357 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88740718357 / 62500000000) = 1/(62500000000 / 88740718357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10333 : Bounds (87638071 / 250000000) (70110457 / 200000000) (Real.log (88740718357 / 62500000000)) := by
  have h := reflection_log_10333_neg
  have he : Real.log (88740718357 / 62500000000) = -Real.log (62500000000 / 88740718357) := by
    rw [show ((88740718357 / 62500000000) : ℝ) = ((62500000000 / 88740718357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10334_neg : (352340381 / 1000000000) ≤ -Real.log (100000000000 / 142239259717) ∧
    -Real.log (100000000000 / 142239259717) ≤ (176170191 / 500000000) := by
  have h := checkLog_sound (w := (42239259717 / 242239259717)) (n := 12)
    (lo := (352340381 / 1000000000)) (hi := (176170191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142239259717 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142239259717 / 100000000000) = 1/(100000000000 / 142239259717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10334 : Bounds (352340381 / 1000000000) (176170191 / 500000000) (Real.log (142239259717 / 100000000000)) := by
  have h := reflection_log_10334_neg
  have he : Real.log (142239259717 / 100000000000) = -Real.log (100000000000 / 142239259717) := by
    rw [show ((142239259717 / 100000000000) : ℝ) = ((100000000000 / 142239259717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10335_neg : (708185057 / 1000000000) ≤ -Real.log (500000000000 / 1015151515151) ∧
    -Real.log (500000000000 / 1015151515151) ≤ (708185059 / 1000000000) := by
  have h := checkLog_sound (w := (15151515151 / 2015151515151)) (n := 12)
    (lo := (15037877 / 1000000000)) (hi := (7518939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1015151515151 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1015151515151 / 1000000000000) = 1/(500000000000 / 1015151515151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10335 : Bounds (708185057 / 1000000000) (708185059 / 1000000000) (Real.log (1015151515151 / 500000000000)) := by
  have h := reflection_log_10335_neg
  have he : Real.log (1015151515151 / 500000000000) = -Real.log (500000000000 / 1015151515151) := by
    rw [show ((1015151515151 / 500000000000) : ℝ) = ((500000000000 / 1015151515151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10336_neg : (177611837 / 250000000) ≤ -Real.log (500000000000 / 1017450682853) ∧
    -Real.log (500000000000 / 1017450682853) ≤ (14208947 / 20000000) := by
  have h := checkLog_sound (w := (17450682853 / 2017450682853)) (n := 12)
    (lo := (2162521 / 125000000)) (hi := (17300169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1017450682853 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1017450682853 / 1000000000000) = 1/(500000000000 / 1017450682853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10336 : Bounds (177611837 / 250000000) (14208947 / 20000000) (Real.log (1017450682853 / 500000000000)) := by
  have h := reflection_log_10336_neg
  have he : Real.log (1017450682853 / 500000000000) = -Real.log (500000000000 / 1017450682853) := by
    rw [show ((1017450682853 / 500000000000) : ℝ) = ((500000000000 / 1017450682853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10337_neg : (147080519 / 500000000) ≤ -Real.log (500 / 671) ∧
    -Real.log (500 / 671) ≤ (294161039 / 1000000000) := by
  have h := checkLog_sound (w := (171 / 1171)) (n := 12)
    (lo := (147080519 / 500000000)) (hi := (294161039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671 / 500) = 1/(500 / 671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10337 : Bounds (147080519 / 500000000) (294161039 / 1000000000) (Real.log (671 / 500)) := by
  have h := reflection_log_10337_neg
  have he : Real.log (671 / 500) = -Real.log (500 / 671) := by
    rw [show ((671 / 500) : ℝ) = ((500 / 671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10338_neg : (418550347 / 1000000000) ≤ -Real.log (329 / 500) ∧
    -Real.log (329 / 500) ≤ (104637587 / 250000000) := by
  have h := checkLog_sound (w := (171 / 829)) (n := 12)
    (lo := (418550347 / 1000000000)) (hi := (104637587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 329) = 1/(329 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10338 : Bounds (-104637587 / 250000000) (-418550347 / 1000000000) (Real.log (329 / 500)) := by
  have h := reflection_log_10338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10339_neg : (341941 / 1000000000) ≤ -Real.log (500000 / 500171) ∧
    -Real.log (500000 / 500171) ≤ (170971 / 500000000) := by
  have h := checkLog_sound (w := (171 / 1000171)) (n := 12)
    (lo := (341941 / 1000000000)) (hi := (170971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500171 / 500000) = 1/(500000 / 500171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10339 : Bounds (341941 / 1000000000) (170971 / 500000000) (Real.log (500171 / 500000)) := by
  have h := reflection_log_10339_neg
  have he : Real.log (500171 / 500000) = -Real.log (500000 / 500171) := by
    rw [show ((500171 / 500000) : ℝ) = ((500000 / 500171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10340_neg : (171029 / 500000000) ≤ -Real.log (499829 / 500000) ∧
    -Real.log (499829 / 500000) ≤ (342059 / 1000000000) := by
  have h := checkLog_sound (w := (171 / 999829)) (n := 12)
    (lo := (171029 / 500000000)) (hi := (342059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499829) = 1/(499829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10340 : Bounds (-342059 / 1000000000) (-171029 / 500000000) (Real.log (499829 / 500000)) := by
  have h := reflection_log_10340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10341_neg : (32089477 / 200000000) ≤ -Real.log (250000 / 293509) ∧
    -Real.log (250000 / 293509) ≤ (80223693 / 500000000) := by
  have h := checkLog_sound (w := (43509 / 543509)) (n := 12)
    (lo := (32089477 / 200000000)) (hi := (80223693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293509 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293509 / 250000) = 1/(250000 / 293509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10341 : Bounds (32089477 / 200000000) (80223693 / 500000000) (Real.log (293509 / 250000)) := by
  have h := reflection_log_10341_neg
  have he : Real.log (293509 / 250000) = -Real.log (250000 / 293509) := by
    rw [show ((293509 / 250000) : ℝ) = ((250000 / 293509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10342_neg : (191204089 / 1000000000) ≤ -Real.log (206491 / 250000) ∧
    -Real.log (206491 / 250000) ≤ (19120409 / 100000000) := by
  have h := checkLog_sound (w := (43509 / 456491)) (n := 12)
    (lo := (191204089 / 1000000000)) (hi := (19120409 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 206491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 206491) = 1/(206491 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10342 : Bounds (-19120409 / 100000000) (-191204089 / 1000000000) (Real.log (206491 / 250000)) := by
  have h := reflection_log_10342_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10343_neg : (80593221 / 500000000) ≤ -Real.log (125000 / 146863) ∧
    -Real.log (125000 / 146863) ≤ (161186443 / 1000000000) := by
  have h := checkLog_sound (w := (21863 / 271863)) (n := 12)
    (lo := (80593221 / 500000000)) (hi := (161186443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146863 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146863 / 125000) = 1/(125000 / 146863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10343 : Bounds (80593221 / 500000000) (161186443 / 1000000000) (Real.log (146863 / 125000)) := by
  have h := reflection_log_10343_neg
  have he : Real.log (146863 / 125000) = -Real.log (125000 / 146863) := by
    rw [show ((146863 / 125000) : ℝ) = ((125000 / 146863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10344_neg : (38451107 / 200000000) ≤ -Real.log (103137 / 125000) ∧
    -Real.log (103137 / 125000) ≤ (12015971 / 62500000) := by
  have h := checkLog_sound (w := (21863 / 228137)) (n := 12)
    (lo := (38451107 / 200000000)) (hi := (12015971 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 103137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 103137) = 1/(103137 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10344 : Bounds (-12015971 / 62500000) (-38451107 / 200000000) (Real.log (103137 / 125000)) := by
  have h := reflection_log_10344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10345_neg : (31069093 / 1000000000) ≤ -Real.log (15147009231 / 15625000000) ∧
    -Real.log (15147009231 / 15625000000) ≤ (15534547 / 500000000) := by
  have h := checkLog_sound (w := (477990769 / 30772009231)) (n := 12)
    (lo := (31069093 / 1000000000)) (hi := (15534547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15147009231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15147009231) = 1/(15147009231 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10345 : Bounds (-15534547 / 500000000) (-31069093 / 1000000000) (Real.log (15147009231 / 15625000000)) := by
  have h := reflection_log_10345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10346_neg : (961147 / 31250000) ≤ -Real.log (60606966919 / 62500000000) ∧
    -Real.log (60606966919 / 62500000000) ≤ (6151341 / 200000000) := by
  have h := checkLog_sound (w := (1893033081 / 123106966919)) (n := 12)
    (lo := (961147 / 31250000)) (hi := (6151341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60606966919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60606966919) = 1/(60606966919 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10346 : Bounds (-6151341 / 200000000) (-961147 / 31250000) (Real.log (60606966919 / 62500000000)) := by
  have h := reflection_log_10346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10347_neg : (14066059 / 40000000) ≤ -Real.log (62500000000 / 88838314987) ∧
    -Real.log (62500000000 / 88838314987) ≤ (87912869 / 250000000) := by
  have h := checkLog_sound (w := (26338314987 / 151338314987)) (n := 12)
    (lo := (14066059 / 40000000)) (hi := (87912869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88838314987 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88838314987 / 62500000000) = 1/(62500000000 / 88838314987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10347 : Bounds (14066059 / 40000000) (87912869 / 250000000) (Real.log (88838314987 / 62500000000)) := by
  have h := reflection_log_10347_neg
  have he : Real.log (88838314987 / 62500000000) = -Real.log (62500000000 / 88838314987) := by
    rw [show ((88838314987 / 62500000000) : ℝ) = ((62500000000 / 88838314987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10348_neg : (353441977 / 1000000000) ≤ -Real.log (500000000000 / 711980181701) ∧
    -Real.log (500000000000 / 711980181701) ≤ (176720989 / 500000000) := by
  have h := checkLog_sound (w := (211980181701 / 1211980181701)) (n := 12)
    (lo := (353441977 / 1000000000)) (hi := (176720989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711980181701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711980181701 / 500000000000) = 1/(500000000000 / 711980181701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10348 : Bounds (353441977 / 1000000000) (176720989 / 500000000) (Real.log (711980181701 / 500000000000)) := by
  have h := reflection_log_10348_neg
  have he : Real.log (711980181701 / 500000000000) = -Real.log (500000000000 / 711980181701) := by
    rw [show ((711980181701 / 500000000000) : ℝ) = ((500000000000 / 711980181701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10349_neg : (177611837 / 250000000) ≤ -Real.log (125000000000 / 254362670713) ∧
    -Real.log (125000000000 / 254362670713) ≤ (14208947 / 20000000) := by
  have h := checkLog_sound (w := (4362670713 / 504362670713)) (n := 12)
    (lo := (2162521 / 125000000)) (hi := (17300169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254362670713 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(254362670713 / 250000000000) = 1/(125000000000 / 254362670713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10349 : Bounds (177611837 / 250000000) (14208947 / 20000000) (Real.log (254362670713 / 125000000000)) := by
  have h := reflection_log_10349_neg
  have he : Real.log (254362670713 / 125000000000) = -Real.log (125000000000 / 254362670713) := by
    rw [show ((254362670713 / 125000000000) : ℝ) = ((125000000000 / 254362670713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10350_neg : (142542277 / 200000000) ≤ -Real.log (250000000000 / 509878419453) ∧
    -Real.log (250000000000 / 509878419453) ≤ (712711387 / 1000000000) := by
  have h := checkLog_sound (w := (9878419453 / 1009878419453)) (n := 12)
    (lo := (3912841 / 200000000)) (hi := (9782103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509878419453 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(509878419453 / 500000000000) = 1/(250000000000 / 509878419453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10350 : Bounds (142542277 / 200000000) (712711387 / 1000000000) (Real.log (509878419453 / 250000000000)) := by
  have h := reflection_log_10350_neg
  have he : Real.log (509878419453 / 250000000000) = -Real.log (250000000000 / 509878419453) := by
    rw [show ((509878419453 / 250000000000) : ℝ) = ((250000000000 / 509878419453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10351_neg : (294905917 / 1000000000) ≤ -Real.log (1000 / 1343) ∧
    -Real.log (1000 / 1343) ≤ (147452959 / 500000000) := by
  have h := checkLog_sound (w := (343 / 2343)) (n := 12)
    (lo := (294905917 / 1000000000)) (hi := (147452959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1343 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1343 / 1000) = 1/(1000 / 1343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10351 : Bounds (294905917 / 1000000000) (147452959 / 500000000) (Real.log (1343 / 1000)) := by
  have h := reflection_log_10351_neg
  have he : Real.log (1343 / 1000) = -Real.log (1000 / 1343) := by
    rw [show ((1343 / 1000) : ℝ) = ((1000 / 1343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10352_neg : (21003563 / 50000000) ≤ -Real.log (657 / 1000) ∧
    -Real.log (657 / 1000) ≤ (420071261 / 1000000000) := by
  have h := checkLog_sound (w := (343 / 1657)) (n := 12)
    (lo := (21003563 / 50000000)) (hi := (420071261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 657) = 1/(657 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10352 : Bounds (-420071261 / 1000000000) (-21003563 / 50000000) (Real.log (657 / 1000)) := by
  have h := reflection_log_10352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10353_neg : (342941 / 1000000000) ≤ -Real.log (1000000 / 1000343) ∧
    -Real.log (1000000 / 1000343) ≤ (171471 / 500000000) := by
  have h := checkLog_sound (w := (343 / 2000343)) (n := 12)
    (lo := (342941 / 1000000000)) (hi := (171471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000343 / 1000000) = 1/(1000000 / 1000343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10353 : Bounds (342941 / 1000000000) (171471 / 500000000) (Real.log (1000343 / 1000000)) := by
  have h := reflection_log_10353_neg
  have he : Real.log (1000343 / 1000000) = -Real.log (1000000 / 1000343) := by
    rw [show ((1000343 / 1000000) : ℝ) = ((1000000 / 1000343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10354_neg : (171529 / 500000000) ≤ -Real.log (999657 / 1000000) ∧
    -Real.log (999657 / 1000000) ≤ (343059 / 1000000000) := by
  have h := checkLog_sound (w := (343 / 1999657)) (n := 12)
    (lo := (171529 / 500000000)) (hi := (343059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999657) = 1/(999657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10354 : Bounds (-343059 / 1000000000) (-171529 / 500000000) (Real.log (999657 / 1000000)) := by
  have h := reflection_log_10354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10355_neg : (160901271 / 1000000000) ≤ -Real.log (1000000 / 1174569) ∧
    -Real.log (1000000 / 1174569) ≤ (20112659 / 125000000) := by
  have h := checkLog_sound (w := (174569 / 2174569)) (n := 12)
    (lo := (160901271 / 1000000000)) (hi := (20112659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1174569 / 1000000) = 1/(1000000 / 1174569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10355 : Bounds (160901271 / 1000000000) (20112659 / 125000000) (Real.log (1174569 / 1000000)) := by
  have h := reflection_log_10355_neg
  have he : Real.log (1174569 / 1000000) = -Real.log (1000000 / 1174569) := by
    rw [show ((1174569 / 1000000) : ℝ) = ((1000000 / 1174569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10356_neg : (47962401 / 250000000) ≤ -Real.log (825431 / 1000000) ∧
    -Real.log (825431 / 1000000) ≤ (38369921 / 200000000) := by
  have h := checkLog_sound (w := (174569 / 1825431)) (n := 12)
    (lo := (47962401 / 250000000)) (hi := (38369921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 825431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 825431) = 1/(825431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10356 : Bounds (-38369921 / 200000000) (-47962401 / 250000000) (Real.log (825431 / 1000000)) := by
  have h := reflection_log_10356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10357_neg : (40410211 / 250000000) ≤ -Real.log (500000 / 587719) ∧
    -Real.log (500000 / 587719) ≤ (32328169 / 200000000) := by
  have h := checkLog_sound (w := (87719 / 1087719)) (n := 12)
    (lo := (40410211 / 250000000)) (hi := (32328169 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587719 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587719 / 500000) = 1/(500000 / 587719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10357 : Bounds (40410211 / 250000000) (32328169 / 200000000) (Real.log (587719 / 500000)) := by
  have h := reflection_log_10357_neg
  have he : Real.log (587719 / 500000) = -Real.log (500000 / 587719) := by
    rw [show ((587719 / 500000) : ℝ) = ((500000 / 587719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10358_neg : (96451471 / 500000000) ≤ -Real.log (412281 / 500000) ∧
    -Real.log (412281 / 500000) ≤ (192902943 / 1000000000) := by
  have h := checkLog_sound (w := (87719 / 912281)) (n := 12)
    (lo := (96451471 / 500000000)) (hi := (192902943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 412281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 412281) = 1/(412281 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10358 : Bounds (-192902943 / 1000000000) (-96451471 / 500000000) (Real.log (412281 / 500000)) := by
  have h := reflection_log_10358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10359_neg : (15631049 / 500000000) ≤ -Real.log (242305377039 / 250000000000) ∧
    -Real.log (242305377039 / 250000000000) ≤ (31262099 / 1000000000) := by
  have h := checkLog_sound (w := (7694622961 / 492305377039)) (n := 12)
    (lo := (15631049 / 500000000)) (hi := (31262099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242305377039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242305377039) = 1/(242305377039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10359 : Bounds (-31262099 / 1000000000) (-15631049 / 500000000) (Real.log (242305377039 / 250000000000)) := by
  have h := reflection_log_10359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10360_neg : (30948333 / 1000000000) ≤ -Real.log (969525664239 / 1000000000000) ∧
    -Real.log (969525664239 / 1000000000000) ≤ (15474167 / 500000000) := by
  have h := checkLog_sound (w := (30474335761 / 1969525664239)) (n := 12)
    (lo := (30948333 / 1000000000)) (hi := (15474167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969525664239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969525664239) = 1/(969525664239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10360 : Bounds (-15474167 / 500000000) (-30948333 / 1000000000) (Real.log (969525664239 / 1000000000000)) := by
  have h := reflection_log_10360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10361_neg : (88187719 / 250000000) ≤ -Real.log (500000000000 / 711488301263) ∧
    -Real.log (500000000000 / 711488301263) ≤ (352750877 / 1000000000) := by
  have h := checkLog_sound (w := (211488301263 / 1211488301263)) (n := 12)
    (lo := (88187719 / 250000000)) (hi := (352750877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711488301263 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711488301263 / 500000000000) = 1/(500000000000 / 711488301263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10361 : Bounds (88187719 / 250000000) (352750877 / 1000000000) (Real.log (711488301263 / 500000000000)) := by
  have h := reflection_log_10361_neg
  have he : Real.log (711488301263 / 500000000000) = -Real.log (500000000000 / 711488301263) := by
    rw [show ((711488301263 / 500000000000) : ℝ) = ((500000000000 / 711488301263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10362_neg : (177271893 / 500000000) ≤ -Real.log (7812500000 / 11136954377) ∧
    -Real.log (7812500000 / 11136954377) ≤ (354543787 / 1000000000) := by
  have h := checkLog_sound (w := (3324454377 / 18949454377)) (n := 12)
    (lo := (177271893 / 500000000)) (hi := (354543787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11136954377 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11136954377 / 7812500000) = 1/(7812500000 / 11136954377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10362 : Bounds (177271893 / 500000000) (354543787 / 1000000000) (Real.log (11136954377 / 7812500000)) := by
  have h := reflection_log_10362_neg
  have he : Real.log (11136954377 / 7812500000) = -Real.log (7812500000 / 11136954377) := by
    rw [show ((11136954377 / 7812500000) : ℝ) = ((7812500000 / 11136954377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10363_neg : (142542277 / 200000000) ≤ -Real.log (100000000000 / 203951367781) ∧
    -Real.log (100000000000 / 203951367781) ≤ (712711387 / 1000000000) := by
  have h := checkLog_sound (w := (3951367781 / 403951367781)) (n := 12)
    (lo := (3912841 / 200000000)) (hi := (9782103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203951367781 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(203951367781 / 200000000000) = 1/(100000000000 / 203951367781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10363 : Bounds (142542277 / 200000000) (712711387 / 1000000000) (Real.log (203951367781 / 100000000000)) := by
  have h := reflection_log_10363_neg
  have he : Real.log (203951367781 / 100000000000) = -Real.log (100000000000 / 203951367781) := by
    rw [show ((203951367781 / 100000000000) : ℝ) = ((100000000000 / 203951367781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10364_neg : (714977177 / 1000000000) ≤ -Real.log (500000000000 / 1022070015221) ∧
    -Real.log (500000000000 / 1022070015221) ≤ (714977179 / 1000000000) := by
  have h := checkLog_sound (w := (22070015221 / 2022070015221)) (n := 12)
    (lo := (21829997 / 1000000000)) (hi := (10914999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1022070015221 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1022070015221 / 1000000000000) = 1/(500000000000 / 1022070015221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10364 : Bounds (714977177 / 1000000000) (714977179 / 1000000000) (Real.log (1022070015221 / 500000000000)) := by
  have h := reflection_log_10364_neg
  have he : Real.log (1022070015221 / 500000000000) = -Real.log (500000000000 / 1022070015221) := by
    rw [show ((1022070015221 / 500000000000) : ℝ) = ((500000000000 / 1022070015221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10365_neg : (147825121 / 500000000) ≤ -Real.log (125 / 168) ∧
    -Real.log (125 / 168) ≤ (295650243 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 293)) (n := 12)
    (lo := (147825121 / 500000000)) (hi := (295650243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168 / 125) = 1/(125 / 168) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10365 : Bounds (147825121 / 500000000) (295650243 / 1000000000) (Real.log (168 / 125)) := by
  have h := reflection_log_10365_neg
  have he : Real.log (168 / 125) = -Real.log (125 / 168) := by
    rw [show ((168 / 125) : ℝ) = ((125 / 168) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10366_neg : (42159449 / 100000000) ≤ -Real.log (82 / 125) ∧
    -Real.log (82 / 125) ≤ (421594491 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 207)) (n := 12)
    (lo := (42159449 / 100000000)) (hi := (421594491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 82) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 82) = 1/(82 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10366 : Bounds (-421594491 / 1000000000) (-42159449 / 100000000) (Real.log (82 / 125)) := by
  have h := reflection_log_10366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10367_neg : (17197 / 50000000) ≤ -Real.log (125000 / 125043) ∧
    -Real.log (125000 / 125043) ≤ (343941 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 250043)) (n := 12)
    (lo := (17197 / 50000000)) (hi := (343941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125043 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125043 / 125000) = 1/(125000 / 125043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10367 : Bounds (17197 / 50000000) (343941 / 1000000000) (Real.log (125043 / 125000)) := by
  have h := reflection_log_10367_neg
  have he : Real.log (125043 / 125000) = -Real.log (125000 / 125043) := by
    rw [show ((125043 / 125000) : ℝ) = ((125000 / 125043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


