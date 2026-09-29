-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0015__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0015__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T22:12:11.867986+00:00
-- url     : https://prove2.me/theorems/52553143-1308-4aac-a602-1ec37170b8df
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0015 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0016, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0015 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0016, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0017)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0015 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0016, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0017)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0015 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0016, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0017) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0015 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0016, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0017).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0015 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_960_neg : (6224517 / 1000000000) ≤ -Real.log (993794814471 / 1000000000000) ∧
    -Real.log (993794814471 / 1000000000000) ≤ (3112259 / 500000000) := by
  have h := checkLog_sound (w := (6205185529 / 1993794814471)) (n := 12)
    (lo := (6224517 / 1000000000)) (hi := (3112259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993794814471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993794814471) = 1/(993794814471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_960 : Bounds (-3112259 / 500000000) (-6224517 / 1000000000) (Real.log (993794814471 / 1000000000000)) := by
  have h := reflection_log_960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_961_neg : (78936543 / 500000000) ≤ -Real.log (250000000000 / 292754391697) ∧
    -Real.log (250000000000 / 292754391697) ≤ (157873087 / 1000000000) := by
  have h := checkLog_sound (w := (42754391697 / 542754391697)) (n := 12)
    (lo := (78936543 / 500000000)) (hi := (157873087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292754391697 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292754391697 / 250000000000) = 1/(250000000000 / 292754391697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_961 : Bounds (78936543 / 500000000) (157873087 / 1000000000) (Real.log (292754391697 / 250000000000)) := by
  have h := reflection_log_961_neg
  have he : Real.log (292754391697 / 250000000000) = -Real.log (250000000000 / 292754391697) := by
    rw [show ((292754391697 / 250000000000) : ℝ) = ((250000000000 / 292754391697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_962_neg : (15829169 / 100000000) ≤ -Real.log (125000000000 / 146438482811) ∧
    -Real.log (125000000000 / 146438482811) ≤ (158291691 / 1000000000) := by
  have h := checkLog_sound (w := (21438482811 / 271438482811)) (n := 12)
    (lo := (15829169 / 100000000)) (hi := (158291691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146438482811 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146438482811 / 125000000000) = 1/(125000000000 / 146438482811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_962 : Bounds (15829169 / 100000000) (158291691 / 1000000000) (Real.log (146438482811 / 125000000000)) := by
  have h := reflection_log_962_neg
  have he : Real.log (146438482811 / 125000000000) = -Real.log (125000000000 / 146438482811) := by
    rw [show ((146438482811 / 125000000000) : ℝ) = ((125000000000 / 146438482811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_963_neg : (316618769 / 1000000000) ≤ -Real.log (500000000000 / 686239620403) ∧
    -Real.log (500000000000 / 686239620403) ≤ (31661877 / 100000000) := by
  have h := checkLog_sound (w := (186239620403 / 1186239620403)) (n := 12)
    (lo := (316618769 / 1000000000)) (hi := (31661877 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686239620403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686239620403 / 500000000000) = 1/(500000000000 / 686239620403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_963 : Bounds (316618769 / 1000000000) (31661877 / 100000000) (Real.log (686239620403 / 500000000000)) := by
  have h := reflection_log_963_neg
  have he : Real.log (686239620403 / 500000000000) = -Real.log (500000000000 / 686239620403) := by
    rw [show ((686239620403 / 500000000000) : ℝ) = ((500000000000 / 686239620403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_964_neg : (158411913 / 500000000) ≤ -Real.log (250000000000 / 343190176771) ∧
    -Real.log (250000000000 / 343190176771) ≤ (316823827 / 1000000000) := by
  have h := checkLog_sound (w := (93190176771 / 593190176771)) (n := 12)
    (lo := (158411913 / 500000000)) (hi := (316823827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343190176771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343190176771 / 250000000000) = 1/(250000000000 / 343190176771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_964 : Bounds (158411913 / 500000000) (316823827 / 1000000000) (Real.log (343190176771 / 250000000000)) := by
  have h := reflection_log_964_neg
  have he : Real.log (343190176771 / 250000000000) = -Real.log (250000000000 / 343190176771) := by
    rw [show ((343190176771 / 250000000000) : ℝ) = ((250000000000 / 343190176771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_965_neg : (73001647 / 500000000) ≤ -Real.log (2500 / 2893) ∧
    -Real.log (2500 / 2893) ≤ (29200659 / 200000000) := by
  have h := checkLog_sound (w := (393 / 5393)) (n := 12)
    (lo := (73001647 / 500000000)) (hi := (29200659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2893 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2893 / 2500) = 1/(2500 / 2893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_965 : Bounds (73001647 / 500000000) (29200659 / 200000000) (Real.log (2893 / 2500)) := by
  have h := reflection_log_965_neg
  have he : Real.log (2893 / 2500) = -Real.log (2500 / 2893) := by
    rw [show ((2893 / 2500) : ℝ) = ((2500 / 2893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_966_neg : (171025597 / 1000000000) ≤ -Real.log (2107 / 2500) ∧
    -Real.log (2107 / 2500) ≤ (85512799 / 500000000) := by
  have h := checkLog_sound (w := (393 / 4607)) (n := 12)
    (lo := (171025597 / 1000000000)) (hi := (85512799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2107) = 1/(2107 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_966 : Bounds (-85512799 / 500000000) (-171025597 / 1000000000) (Real.log (2107 / 2500)) := by
  have h := reflection_log_966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_967_neg : (157187 / 1000000000) ≤ -Real.log (2500000 / 2500393) ∧
    -Real.log (2500000 / 2500393) ≤ (39297 / 250000000) := by
  have h := checkLog_sound (w := (393 / 5000393)) (n := 12)
    (lo := (157187 / 1000000000)) (hi := (39297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500393 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500393 / 2500000) = 1/(2500000 / 2500393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_967 : Bounds (157187 / 1000000000) (39297 / 250000000) (Real.log (2500393 / 2500000)) := by
  have h := reflection_log_967_neg
  have he : Real.log (2500393 / 2500000) = -Real.log (2500000 / 2500393) := by
    rw [show ((2500393 / 2500000) : ℝ) = ((2500000 / 2500393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_968_neg : (39303 / 250000000) ≤ -Real.log (2499607 / 2500000) ∧
    -Real.log (2499607 / 2500000) ≤ (157213 / 1000000000) := by
  have h := checkLog_sound (w := (393 / 4999607)) (n := 12)
    (lo := (39303 / 250000000)) (hi := (157213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499607) = 1/(2499607 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_968 : Bounds (-157213 / 1000000000) (-39303 / 250000000) (Real.log (2499607 / 2500000)) := by
  have h := reflection_log_968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_969_neg : (9483829 / 125000000) ≤ -Real.log (1000000 / 1078823) ∧
    -Real.log (1000000 / 1078823) ≤ (75870633 / 1000000000) := by
  have h := checkLog_sound (w := (78823 / 2078823)) (n := 12)
    (lo := (9483829 / 125000000)) (hi := (75870633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078823 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078823 / 1000000) = 1/(1000000 / 1078823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_969 : Bounds (9483829 / 125000000) (75870633 / 1000000000) (Real.log (1078823 / 1000000)) := by
  have h := reflection_log_969_neg
  have he : Real.log (1078823 / 1000000) = -Real.log (1000000 / 1078823) := by
    rw [show ((1078823 / 1000000) : ℝ) = ((1000000 / 1078823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_970_neg : (41051539 / 500000000) ≤ -Real.log (921177 / 1000000) ∧
    -Real.log (921177 / 1000000) ≤ (82103079 / 1000000000) := by
  have h := checkLog_sound (w := (78823 / 1921177)) (n := 12)
    (lo := (41051539 / 500000000)) (hi := (82103079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921177) = 1/(921177 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_970 : Bounds (-82103079 / 1000000000) (-41051539 / 500000000) (Real.log (921177 / 1000000)) := by
  have h := reflection_log_970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_971_neg : (38032171 / 500000000) ≤ -Real.log (125000 / 134879) ∧
    -Real.log (125000 / 134879) ≤ (76064343 / 1000000000) := by
  have h := checkLog_sound (w := (9879 / 259879)) (n := 12)
    (lo := (38032171 / 500000000)) (hi := (76064343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134879 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134879 / 125000) = 1/(125000 / 134879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_971 : Bounds (38032171 / 500000000) (76064343 / 1000000000) (Real.log (134879 / 125000)) := by
  have h := reflection_log_971_neg
  have he : Real.log (134879 / 125000) = -Real.log (125000 / 134879) := by
    rw [show ((134879 / 125000) : ℝ) = ((125000 / 134879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_972_neg : (20582497 / 250000000) ≤ -Real.log (115121 / 125000) ∧
    -Real.log (115121 / 125000) ≤ (82329989 / 1000000000) := by
  have h := checkLog_sound (w := (9879 / 240121)) (n := 12)
    (lo := (20582497 / 250000000)) (hi := (82329989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115121) = 1/(115121 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_972 : Bounds (-82329989 / 1000000000) (-20582497 / 250000000) (Real.log (115121 / 125000)) := by
  have h := reflection_log_972_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_973_neg : (1253129 / 200000000) ≤ -Real.log (15527405359 / 15625000000) ∧
    -Real.log (15527405359 / 15625000000) ≤ (3132823 / 500000000) := by
  have h := checkLog_sound (w := (97594641 / 31152405359)) (n := 12)
    (lo := (1253129 / 200000000)) (hi := (3132823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15527405359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15527405359) = 1/(15527405359 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_973 : Bounds (-3132823 / 500000000) (-1253129 / 200000000) (Real.log (15527405359 / 15625000000)) := by
  have h := reflection_log_973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_974_neg : (3116223 / 500000000) ≤ -Real.log (993786934671 / 1000000000000) ∧
    -Real.log (993786934671 / 1000000000000) ≤ (6232447 / 1000000000) := by
  have h := checkLog_sound (w := (6213065329 / 1993786934671)) (n := 12)
    (lo := (3116223 / 500000000)) (hi := (6232447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993786934671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993786934671) = 1/(993786934671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_974 : Bounds (-6232447 / 1000000000) (-3116223 / 500000000) (Real.log (993786934671 / 1000000000000)) := by
  have h := reflection_log_974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_975_neg : (15797371 / 100000000) ≤ -Real.log (250000000000 / 292783851529) ∧
    -Real.log (250000000000 / 292783851529) ≤ (157973711 / 1000000000) := by
  have h := checkLog_sound (w := (42783851529 / 542783851529)) (n := 12)
    (lo := (15797371 / 100000000)) (hi := (157973711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292783851529 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292783851529 / 250000000000) = 1/(250000000000 / 292783851529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_975 : Bounds (15797371 / 100000000) (157973711 / 1000000000) (Real.log (292783851529 / 250000000000)) := by
  have h := reflection_log_975_neg
  have he : Real.log (292783851529 / 250000000000) = -Real.log (250000000000 / 292783851529) := by
    rw [show ((292783851529 / 250000000000) : ℝ) = ((250000000000 / 292783851529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_976_neg : (158394331 / 1000000000) ≤ -Real.log (100000000000 / 117162811303) ∧
    -Real.log (100000000000 / 117162811303) ≤ (39598583 / 250000000) := by
  have h := checkLog_sound (w := (17162811303 / 217162811303)) (n := 12)
    (lo := (158394331 / 1000000000)) (hi := (39598583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117162811303 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117162811303 / 100000000000) = 1/(100000000000 / 117162811303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_976 : Bounds (158394331 / 1000000000) (39598583 / 250000000) (Real.log (117162811303 / 100000000000)) := by
  have h := reflection_log_976_neg
  have he : Real.log (117162811303 / 100000000000) = -Real.log (100000000000 / 117162811303) := by
    rw [show ((117162811303 / 100000000000) : ℝ) = ((100000000000 / 117162811303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_977_neg : (158411913 / 500000000) ≤ -Real.log (500000000000 / 686380353541) ∧
    -Real.log (500000000000 / 686380353541) ≤ (316823827 / 1000000000) := by
  have h := checkLog_sound (w := (186380353541 / 1186380353541)) (n := 12)
    (lo := (158411913 / 500000000)) (hi := (316823827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686380353541 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686380353541 / 500000000000) = 1/(500000000000 / 686380353541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_977 : Bounds (158411913 / 500000000) (316823827 / 1000000000) (Real.log (686380353541 / 500000000000)) := by
  have h := reflection_log_977_neg
  have he : Real.log (686380353541 / 500000000000) = -Real.log (500000000000 / 686380353541) := by
    rw [show ((686380353541 / 500000000000) : ℝ) = ((500000000000 / 686380353541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_978_neg : (317028891 / 1000000000) ≤ -Real.log (125000000000 / 171630280019) ∧
    -Real.log (125000000000 / 171630280019) ≤ (79257223 / 250000000) := by
  have h := checkLog_sound (w := (46630280019 / 296630280019)) (n := 12)
    (lo := (317028891 / 1000000000)) (hi := (79257223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171630280019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171630280019 / 125000000000) = 1/(125000000000 / 171630280019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_978 : Bounds (317028891 / 1000000000) (79257223 / 250000000) (Real.log (171630280019 / 125000000000)) := by
  have h := reflection_log_978_neg
  have he : Real.log (171630280019 / 125000000000) = -Real.log (125000000000 / 171630280019) := by
    rw [show ((171630280019 / 125000000000) : ℝ) = ((125000000000 / 171630280019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_979_neg : (29217941 / 200000000) ≤ -Real.log (10000 / 11573) ∧
    -Real.log (10000 / 11573) ≤ (73044853 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 21573)) (n := 12)
    (lo := (29217941 / 200000000)) (hi := (73044853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11573 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11573 / 10000) = 1/(10000 / 11573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_979 : Bounds (29217941 / 200000000) (73044853 / 500000000) (Real.log (11573 / 10000)) := by
  have h := reflection_log_979_neg
  have he : Real.log (11573 / 10000) = -Real.log (10000 / 11573) := by
    rw [show ((11573 / 10000) : ℝ) = ((10000 / 11573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_980_neg : (2674129 / 15625000) ≤ -Real.log (8427 / 10000) ∧
    -Real.log (8427 / 10000) ≤ (171144257 / 1000000000) := by
  have h := checkLog_sound (w := (1573 / 18427)) (n := 12)
    (lo := (2674129 / 15625000)) (hi := (171144257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8427) = 1/(8427 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_980 : Bounds (-171144257 / 1000000000) (-2674129 / 15625000) (Real.log (8427 / 10000)) := by
  have h := reflection_log_980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_981_neg : (157287 / 1000000000) ≤ -Real.log (10000000 / 10001573) ∧
    -Real.log (10000000 / 10001573) ≤ (19661 / 125000000) := by
  have h := checkLog_sound (w := (1573 / 20001573)) (n := 12)
    (lo := (157287 / 1000000000)) (hi := (19661 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001573 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001573 / 10000000) = 1/(10000000 / 10001573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_981 : Bounds (157287 / 1000000000) (19661 / 125000000) (Real.log (10001573 / 10000000)) := by
  have h := reflection_log_981_neg
  have he : Real.log (10001573 / 10000000) = -Real.log (10000000 / 10001573) := by
    rw [show ((10001573 / 10000000) : ℝ) = ((10000000 / 10001573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_982_neg : (1229 / 7812500) ≤ -Real.log (9998427 / 10000000) ∧
    -Real.log (9998427 / 10000000) ≤ (157313 / 1000000000) := by
  have h := checkLog_sound (w := (1573 / 19998427)) (n := 12)
    (lo := (1229 / 7812500)) (hi := (157313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998427) = 1/(9998427 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_982 : Bounds (-157313 / 1000000000) (-1229 / 7812500) (Real.log (9998427 / 10000000)) := by
  have h := reflection_log_982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_983_neg : (4744869 / 62500000) ≤ -Real.log (500000 / 539437) ∧
    -Real.log (500000 / 539437) ≤ (15183581 / 200000000) := by
  have h := checkLog_sound (w := (39437 / 1039437)) (n := 12)
    (lo := (4744869 / 62500000)) (hi := (15183581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539437 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539437 / 500000) = 1/(500000 / 539437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_983 : Bounds (4744869 / 62500000) (15183581 / 200000000) (Real.log (539437 / 500000)) := by
  have h := reflection_log_983_neg
  have he : Real.log (539437 / 500000) = -Real.log (500000 / 539437) := by
    rw [show ((539437 / 500000) : ℝ) = ((500000 / 539437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_984_neg : (20539611 / 250000000) ≤ -Real.log (460563 / 500000) ∧
    -Real.log (460563 / 500000) ≤ (16431689 / 200000000) := by
  have h := checkLog_sound (w := (39437 / 960563)) (n := 12)
    (lo := (20539611 / 250000000)) (hi := (16431689 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460563) = 1/(460563 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_984 : Bounds (-16431689 / 200000000) (-20539611 / 250000000) (Real.log (460563 / 500000)) := by
  have h := reflection_log_984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_985_neg : (76110679 / 1000000000) ≤ -Real.log (500000 / 539541) ∧
    -Real.log (500000 / 539541) ≤ (1902767 / 25000000) := by
  have h := checkLog_sound (w := (39541 / 1039541)) (n := 12)
    (lo := (76110679 / 1000000000)) (hi := (1902767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539541 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539541 / 500000) = 1/(500000 / 539541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_985 : Bounds (76110679 / 1000000000) (1902767 / 25000000) (Real.log (539541 / 500000)) := by
  have h := reflection_log_985_neg
  have he : Real.log (539541 / 500000) = -Real.log (500000 / 539541) := by
    rw [show ((539541 / 500000) : ℝ) = ((500000 / 539541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_986_neg : (2059607 / 25000000) ≤ -Real.log (460459 / 500000) ∧
    -Real.log (460459 / 500000) ≤ (82384281 / 1000000000) := by
  have h := checkLog_sound (w := (39541 / 960459)) (n := 12)
    (lo := (2059607 / 25000000)) (hi := (82384281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460459) = 1/(460459 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_986 : Bounds (-82384281 / 1000000000) (-2059607 / 25000000) (Real.log (460459 / 500000)) := by
  have h := reflection_log_986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_987_neg : (3921 / 625000) ≤ -Real.log (248436509319 / 250000000000) ∧
    -Real.log (248436509319 / 250000000000) ≤ (6273601 / 1000000000) := by
  have h := checkLog_sound (w := (1563490681 / 498436509319)) (n := 12)
    (lo := (3921 / 625000)) (hi := (6273601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248436509319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248436509319) = 1/(248436509319 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_987 : Bounds (-6273601 / 1000000000) (-3921 / 625000) (Real.log (248436509319 / 250000000000)) := by
  have h := reflection_log_987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_988_neg : (6240539 / 1000000000) ≤ -Real.log (248444723031 / 250000000000) ∧
    -Real.log (248444723031 / 250000000000) ≤ (312027 / 50000000) := by
  have h := checkLog_sound (w := (1555276969 / 498444723031)) (n := 12)
    (lo := (6240539 / 1000000000)) (hi := (312027 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248444723031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248444723031) = 1/(248444723031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_988 : Bounds (-312027 / 50000000) (-6240539 / 1000000000) (Real.log (248444723031 / 250000000000)) := by
  have h := reflection_log_988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_989_neg : (39519087 / 250000000) ≤ -Real.log (62500000000 / 73203475963) ∧
    -Real.log (62500000000 / 73203475963) ≤ (158076349 / 1000000000) := by
  have h := checkLog_sound (w := (10703475963 / 135703475963)) (n := 12)
    (lo := (39519087 / 250000000)) (hi := (158076349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73203475963 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73203475963 / 62500000000) = 1/(62500000000 / 73203475963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_989 : Bounds (39519087 / 250000000) (158076349 / 1000000000) (Real.log (73203475963 / 62500000000)) := by
  have h := reflection_log_989_neg
  have he : Real.log (73203475963 / 62500000000) = -Real.log (62500000000 / 73203475963) := by
    rw [show ((73203475963 / 62500000000) : ℝ) = ((62500000000 / 73203475963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_990_neg : (1981187 / 12500000) ≤ -Real.log (125000000000 / 146468252331) ∧
    -Real.log (125000000000 / 146468252331) ≤ (158494961 / 1000000000) := by
  have h := checkLog_sound (w := (21468252331 / 271468252331)) (n := 12)
    (lo := (1981187 / 12500000)) (hi := (158494961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146468252331 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146468252331 / 125000000000) = 1/(125000000000 / 146468252331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_990 : Bounds (1981187 / 12500000) (158494961 / 1000000000) (Real.log (146468252331 / 125000000000)) := by
  have h := reflection_log_990_neg
  have he : Real.log (146468252331 / 125000000000) = -Real.log (125000000000 / 146468252331) := by
    rw [show ((146468252331 / 125000000000) : ℝ) = ((125000000000 / 146468252331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_991_neg : (317028891 / 1000000000) ≤ -Real.log (20000000000 / 27460844803) ∧
    -Real.log (20000000000 / 27460844803) ≤ (79257223 / 250000000) := by
  have h := checkLog_sound (w := (7460844803 / 47460844803)) (n := 12)
    (lo := (317028891 / 1000000000)) (hi := (79257223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27460844803 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27460844803 / 20000000000) = 1/(20000000000 / 27460844803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_991 : Bounds (317028891 / 1000000000) (79257223 / 250000000) (Real.log (27460844803 / 20000000000)) := by
  have h := reflection_log_991_neg
  have he : Real.log (27460844803 / 20000000000) = -Real.log (20000000000 / 27460844803) := by
    rw [show ((27460844803 / 20000000000) : ℝ) = ((20000000000 / 27460844803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_992_neg : (158616981 / 500000000) ≤ -Real.log (500000000000 / 686661920019) ∧
    -Real.log (500000000000 / 686661920019) ≤ (317233963 / 1000000000) := by
  have h := checkLog_sound (w := (186661920019 / 1186661920019)) (n := 12)
    (lo := (158616981 / 500000000)) (hi := (317233963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686661920019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686661920019 / 500000000000) = 1/(500000000000 / 686661920019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_992 : Bounds (158616981 / 500000000) (317233963 / 1000000000) (Real.log (686661920019 / 500000000000)) := by
  have h := reflection_log_992_neg
  have he : Real.log (686661920019 / 500000000000) = -Real.log (500000000000 / 686661920019) := by
    rw [show ((686661920019 / 500000000000) : ℝ) = ((500000000000 / 686661920019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_993_neg : (14617611 / 100000000) ≤ -Real.log (5000 / 5787) ∧
    -Real.log (5000 / 5787) ≤ (146176111 / 1000000000) := by
  have h := checkLog_sound (w := (787 / 10787)) (n := 12)
    (lo := (14617611 / 100000000)) (hi := (146176111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5787 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5787 / 5000) = 1/(5000 / 5787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_993 : Bounds (14617611 / 100000000) (146176111 / 1000000000) (Real.log (5787 / 5000)) := by
  have h := reflection_log_993_neg
  have he : Real.log (5787 / 5000) = -Real.log (5000 / 5787) := by
    rw [show ((5787 / 5000) : ℝ) = ((5000 / 5787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_994_neg : (171262929 / 1000000000) ≤ -Real.log (4213 / 5000) ∧
    -Real.log (4213 / 5000) ≤ (17126293 / 100000000) := by
  have h := checkLog_sound (w := (787 / 9213)) (n := 12)
    (lo := (171262929 / 1000000000)) (hi := (17126293 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4213) = 1/(4213 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_994 : Bounds (-17126293 / 100000000) (-171262929 / 1000000000) (Real.log (4213 / 5000)) := by
  have h := reflection_log_994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_995_neg : (157387 / 1000000000) ≤ -Real.log (5000000 / 5000787) ∧
    -Real.log (5000000 / 5000787) ≤ (39347 / 250000000) := by
  have h := checkLog_sound (w := (787 / 10000787)) (n := 12)
    (lo := (157387 / 1000000000)) (hi := (39347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000787 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000787 / 5000000) = 1/(5000000 / 5000787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_995 : Bounds (157387 / 1000000000) (39347 / 250000000) (Real.log (5000787 / 5000000)) := by
  have h := reflection_log_995_neg
  have he : Real.log (5000787 / 5000000) = -Real.log (5000000 / 5000787) := by
    rw [show ((5000787 / 5000000) : ℝ) = ((5000000 / 5000787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_996_neg : (39353 / 250000000) ≤ -Real.log (4999213 / 5000000) ∧
    -Real.log (4999213 / 5000000) ≤ (157413 / 1000000000) := by
  have h := checkLog_sound (w := (787 / 9999213)) (n := 12)
    (lo := (39353 / 250000000)) (hi := (157413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999213) = 1/(4999213 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_996 : Bounds (-157413 / 1000000000) (-39353 / 250000000) (Real.log (4999213 / 5000000)) := by
  have h := reflection_log_996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_997_neg : (3038607 / 40000000) ≤ -Real.log (40000 / 43157) ∧
    -Real.log (40000 / 43157) ≤ (9495647 / 125000000) := by
  have h := checkLog_sound (w := (3157 / 83157)) (n := 12)
    (lo := (3038607 / 40000000)) (hi := (9495647 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43157 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43157 / 40000) = 1/(40000 / 43157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_997 : Bounds (3038607 / 40000000) (9495647 / 125000000) (Real.log (43157 / 40000)) := by
  have h := reflection_log_997_neg
  have he : Real.log (43157 / 40000) = -Real.log (40000 / 43157) := by
    rw [show ((43157 / 40000) : ℝ) = ((40000 / 43157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_998_neg : (20553453 / 250000000) ≤ -Real.log (36843 / 40000) ∧
    -Real.log (36843 / 40000) ≤ (82213813 / 1000000000) := by
  have h := checkLog_sound (w := (3157 / 76843)) (n := 12)
    (lo := (20553453 / 250000000)) (hi := (82213813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36843) = 1/(36843 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_998 : Bounds (-82213813 / 1000000000) (-20553453 / 250000000) (Real.log (36843 / 40000)) := by
  have h := reflection_log_998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_999_neg : (3807897 / 50000000) ≤ -Real.log (1000000 / 1079133) ∧
    -Real.log (1000000 / 1079133) ≤ (76157941 / 1000000000) := by
  have h := checkLog_sound (w := (79133 / 2079133)) (n := 12)
    (lo := (3807897 / 50000000)) (hi := (76157941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079133 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079133 / 1000000) = 1/(1000000 / 1079133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_999 : Bounds (3807897 / 50000000) (76157941 / 1000000000) (Real.log (1079133 / 1000000)) := by
  have h := reflection_log_999_neg
  have he : Real.log (1079133 / 1000000) = -Real.log (1000000 / 1079133) := by
    rw [show ((1079133 / 1000000) : ℝ) = ((1000000 / 1079133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1000_neg : (82439661 / 1000000000) ≤ -Real.log (920867 / 1000000) ∧
    -Real.log (920867 / 1000000) ≤ (41219831 / 500000000) := by
  have h := checkLog_sound (w := (79133 / 1920867)) (n := 12)
    (lo := (82439661 / 1000000000)) (hi := (41219831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920867) = 1/(920867 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1000 : Bounds (-41219831 / 500000000) (-82439661 / 1000000000) (Real.log (920867 / 1000000)) := by
  have h := reflection_log_1000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1001_neg : (157043 / 25000000) ≤ -Real.log (993737968311 / 1000000000000) ∧
    -Real.log (993737968311 / 1000000000000) ≤ (6281721 / 1000000000) := by
  have h := checkLog_sound (w := (6262031689 / 1993737968311)) (n := 12)
    (lo := (157043 / 25000000)) (hi := (6281721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993737968311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993737968311) = 1/(993737968311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1001 : Bounds (-6281721 / 1000000000) (-157043 / 25000000) (Real.log (993737968311 / 1000000000000)) := by
  have h := reflection_log_1001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1002_neg : (6248637 / 1000000000) ≤ -Real.log (1590033351 / 1600000000) ∧
    -Real.log (1590033351 / 1600000000) ≤ (3124319 / 500000000) := by
  have h := checkLog_sound (w := (9966649 / 3190033351)) (n := 12)
    (lo := (6248637 / 1000000000)) (hi := (3124319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1590033351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1590033351) = 1/(1590033351 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1002 : Bounds (-3124319 / 500000000) (-6248637 / 1000000000) (Real.log (1590033351 / 1600000000)) := by
  have h := reflection_log_1002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1003_neg : (158178987 / 1000000000) ≤ -Real.log (500000000000 / 585687919007) ∧
    -Real.log (500000000000 / 585687919007) ≤ (39544747 / 250000000) := by
  have h := checkLog_sound (w := (85687919007 / 1085687919007)) (n := 12)
    (lo := (158178987 / 1000000000)) (hi := (39544747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585687919007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585687919007 / 500000000000) = 1/(500000000000 / 585687919007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1003 : Bounds (158178987 / 1000000000) (39544747 / 250000000) (Real.log (585687919007 / 500000000000)) := by
  have h := reflection_log_1003_neg
  have he : Real.log (585687919007 / 500000000000) = -Real.log (500000000000 / 585687919007) := by
    rw [show ((585687919007 / 500000000000) : ℝ) = ((500000000000 / 585687919007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1004_neg : (79298801 / 500000000) ≤ -Real.log (62500000000 / 73241643473) ∧
    -Real.log (62500000000 / 73241643473) ≤ (158597603 / 1000000000) := by
  have h := checkLog_sound (w := (10741643473 / 135741643473)) (n := 12)
    (lo := (79298801 / 500000000)) (hi := (158597603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73241643473 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73241643473 / 62500000000) = 1/(62500000000 / 73241643473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1004 : Bounds (79298801 / 500000000) (158597603 / 1000000000) (Real.log (73241643473 / 62500000000)) := by
  have h := reflection_log_1004_neg
  have he : Real.log (73241643473 / 62500000000) = -Real.log (62500000000 / 73241643473) := by
    rw [show ((73241643473 / 62500000000) : ℝ) = ((62500000000 / 73241643473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1005_neg : (158616981 / 500000000) ≤ -Real.log (250000000000 / 343330960009) ∧
    -Real.log (250000000000 / 343330960009) ≤ (317233963 / 1000000000) := by
  have h := checkLog_sound (w := (93330960009 / 593330960009)) (n := 12)
    (lo := (158616981 / 500000000)) (hi := (317233963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343330960009 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343330960009 / 250000000000) = 1/(250000000000 / 343330960009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1005 : Bounds (158616981 / 500000000) (317233963 / 1000000000) (Real.log (343330960009 / 250000000000)) := by
  have h := reflection_log_1005_neg
  have he : Real.log (343330960009 / 250000000000) = -Real.log (250000000000 / 343330960009) := by
    rw [show ((343330960009 / 250000000000) : ℝ) = ((250000000000 / 343330960009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1006_neg : (317439039 / 1000000000) ≤ -Real.log (500000000000 / 686802753383) ∧
    -Real.log (500000000000 / 686802753383) ≤ (991997 / 3125000) := by
  have h := checkLog_sound (w := (186802753383 / 1186802753383)) (n := 12)
    (lo := (317439039 / 1000000000)) (hi := (991997 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686802753383 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686802753383 / 500000000000) = 1/(500000000000 / 686802753383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1006 : Bounds (317439039 / 1000000000) (991997 / 3125000) (Real.log (686802753383 / 500000000000)) := by
  have h := reflection_log_1006_neg
  have he : Real.log (686802753383 / 500000000000) = -Real.log (500000000000 / 686802753383) := by
    rw [show ((686802753383 / 500000000000) : ℝ) = ((500000000000 / 686802753383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1007_neg : (73131253 / 500000000) ≤ -Real.log (400 / 463) ∧
    -Real.log (400 / 463) ≤ (146262507 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 863)) (n := 12)
    (lo := (73131253 / 500000000)) (hi := (146262507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463 / 400) = 1/(400 / 463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1007 : Bounds (73131253 / 500000000) (146262507 / 1000000000) (Real.log (463 / 400)) := by
  have h := reflection_log_1007_neg
  have he : Real.log (463 / 400) = -Real.log (400 / 463) := by
    rw [show ((463 / 400) : ℝ) = ((400 / 463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1008_neg : (10711351 / 62500000) ≤ -Real.log (337 / 400) ∧
    -Real.log (337 / 400) ≤ (171381617 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 737)) (n := 12)
    (lo := (10711351 / 62500000)) (hi := (171381617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 337) = 1/(337 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1008 : Bounds (-171381617 / 1000000000) (-10711351 / 62500000) (Real.log (337 / 400)) := by
  have h := reflection_log_1008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1009_neg : (157487 / 1000000000) ≤ -Real.log (400000 / 400063) ∧
    -Real.log (400000 / 400063) ≤ (9843 / 62500000) := by
  have h := checkLog_sound (w := (63 / 800063)) (n := 12)
    (lo := (157487 / 1000000000)) (hi := (9843 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400063 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400063 / 400000) = 1/(400000 / 400063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1009 : Bounds (157487 / 1000000000) (9843 / 62500000) (Real.log (400063 / 400000)) := by
  have h := reflection_log_1009_neg
  have he : Real.log (400063 / 400000) = -Real.log (400000 / 400063) := by
    rw [show ((400063 / 400000) : ℝ) = ((400000 / 400063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1010_neg : (19689 / 125000000) ≤ -Real.log (399937 / 400000) ∧
    -Real.log (399937 / 400000) ≤ (157513 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 799937)) (n := 12)
    (lo := (19689 / 125000000)) (hi := (157513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399937) = 1/(399937 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1010 : Bounds (-157513 / 1000000000) (-19689 / 125000000) (Real.log (399937 / 400000)) := by
  have h := reflection_log_1010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1011_neg : (19002879 / 250000000) ≤ -Real.log (40000 / 43159) ∧
    -Real.log (40000 / 43159) ≤ (76011517 / 1000000000) := by
  have h := checkLog_sound (w := (3159 / 83159)) (n := 12)
    (lo := (19002879 / 250000000)) (hi := (76011517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43159 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43159 / 40000) = 1/(40000 / 43159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1011 : Bounds (19002879 / 250000000) (76011517 / 1000000000) (Real.log (43159 / 40000)) := by
  have h := reflection_log_1011_neg
  have he : Real.log (43159 / 40000) = -Real.log (40000 / 43159) := by
    rw [show ((43159 / 40000) : ℝ) = ((40000 / 43159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1012_neg : (41134049 / 500000000) ≤ -Real.log (36841 / 40000) ∧
    -Real.log (36841 / 40000) ≤ (82268099 / 1000000000) := by
  have h := checkLog_sound (w := (3159 / 76841)) (n := 12)
    (lo := (41134049 / 500000000)) (hi := (82268099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36841) = 1/(36841 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1012 : Bounds (-82268099 / 1000000000) (-41134049 / 500000000) (Real.log (36841 / 40000)) := by
  have h := reflection_log_1012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1013_neg : (190513 / 2500000) ≤ -Real.log (62500 / 67449) ∧
    -Real.log (62500 / 67449) ≤ (76205201 / 1000000000) := by
  have h := checkLog_sound (w := (4949 / 129949)) (n := 12)
    (lo := (190513 / 2500000)) (hi := (76205201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67449 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67449 / 62500) = 1/(62500 / 67449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1013 : Bounds (190513 / 2500000) (76205201 / 1000000000) (Real.log (67449 / 62500)) := by
  have h := reflection_log_1013_neg
  have he : Real.log (67449 / 62500) = -Real.log (62500 / 67449) := by
    rw [show ((67449 / 62500) : ℝ) = ((62500 / 67449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1014_neg : (16499009 / 200000000) ≤ -Real.log (57551 / 62500) ∧
    -Real.log (57551 / 62500) ≤ (41247523 / 500000000) := by
  have h := checkLog_sound (w := (4949 / 120051)) (n := 12)
    (lo := (16499009 / 200000000)) (hi := (41247523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57551) = 1/(57551 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1014 : Bounds (-41247523 / 500000000) (-16499009 / 200000000) (Real.log (57551 / 62500)) := by
  have h := reflection_log_1014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1015_neg : (1257969 / 200000000) ≤ -Real.log (3881757399 / 3906250000) ∧
    -Real.log (3881757399 / 3906250000) ≤ (3144923 / 500000000) := by
  have h := checkLog_sound (w := (24492601 / 7788007399)) (n := 12)
    (lo := (1257969 / 200000000)) (hi := (3144923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3881757399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3881757399) = 1/(3881757399 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1015 : Bounds (-3144923 / 500000000) (-1257969 / 200000000) (Real.log (3881757399 / 3906250000)) := by
  have h := reflection_log_1015_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1016_neg : (3128291 / 500000000) ≤ -Real.log (1590020719 / 1600000000) ∧
    -Real.log (1590020719 / 1600000000) ≤ (6256583 / 1000000000) := by
  have h := checkLog_sound (w := (9979281 / 3190020719)) (n := 12)
    (lo := (3128291 / 500000000)) (hi := (6256583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1590020719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1590020719) = 1/(1590020719 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1016 : Bounds (-6256583 / 1000000000) (-3128291 / 500000000) (Real.log (1590020719 / 1600000000)) := by
  have h := reflection_log_1016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1017_neg : (31655923 / 200000000) ≤ -Real.log (12500000000 / 14643671453) ∧
    -Real.log (12500000000 / 14643671453) ≤ (2473119 / 15625000) := by
  have h := checkLog_sound (w := (2143671453 / 27143671453)) (n := 12)
    (lo := (31655923 / 200000000)) (hi := (2473119 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14643671453 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14643671453 / 12500000000) = 1/(12500000000 / 14643671453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1017 : Bounds (31655923 / 200000000) (2473119 / 15625000) (Real.log (14643671453 / 12500000000)) := by
  have h := reflection_log_1017_neg
  have he : Real.log (14643671453 / 12500000000) = -Real.log (12500000000 / 14643671453) := by
    rw [show ((14643671453 / 12500000000) : ℝ) = ((12500000000 / 14643671453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1018_neg : (31740049 / 200000000) ≤ -Real.log (250000000000 / 292996646453) ∧
    -Real.log (250000000000 / 292996646453) ≤ (79350123 / 500000000) := by
  have h := checkLog_sound (w := (42996646453 / 542996646453)) (n := 12)
    (lo := (31740049 / 200000000)) (hi := (79350123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292996646453 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292996646453 / 250000000000) = 1/(250000000000 / 292996646453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1018 : Bounds (31740049 / 200000000) (79350123 / 500000000) (Real.log (292996646453 / 250000000000)) := by
  have h := reflection_log_1018_neg
  have he : Real.log (292996646453 / 250000000000) = -Real.log (250000000000 / 292996646453) := by
    rw [show ((292996646453 / 250000000000) : ℝ) = ((250000000000 / 292996646453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1019_neg : (317439039 / 1000000000) ≤ -Real.log (250000000000 / 343401376691) ∧
    -Real.log (250000000000 / 343401376691) ≤ (991997 / 3125000) := by
  have h := checkLog_sound (w := (93401376691 / 593401376691)) (n := 12)
    (lo := (317439039 / 1000000000)) (hi := (991997 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343401376691 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343401376691 / 250000000000) = 1/(250000000000 / 343401376691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1019 : Bounds (317439039 / 1000000000) (991997 / 3125000) (Real.log (343401376691 / 250000000000)) := by
  have h := reflection_log_1019_neg
  have he : Real.log (343401376691 / 250000000000) = -Real.log (250000000000 / 343401376691) := by
    rw [show ((343401376691 / 250000000000) : ℝ) = ((250000000000 / 343401376691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1020_neg : (317644123 / 1000000000) ≤ -Real.log (500000000000 / 686943620179) ∧
    -Real.log (500000000000 / 686943620179) ≤ (79411031 / 250000000) := by
  have h := checkLog_sound (w := (186943620179 / 1186943620179)) (n := 12)
    (lo := (317644123 / 1000000000)) (hi := (79411031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686943620179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686943620179 / 500000000000) = 1/(500000000000 / 686943620179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1020 : Bounds (317644123 / 1000000000) (79411031 / 250000000) (Real.log (686943620179 / 500000000000)) := by
  have h := reflection_log_1020_neg
  have he : Real.log (686943620179 / 500000000000) = -Real.log (500000000000 / 686943620179) := by
    rw [show ((686943620179 / 500000000000) : ℝ) = ((500000000000 / 686943620179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1021_neg : (4573403 / 31250000) ≤ -Real.log (1250 / 1447) ∧
    -Real.log (1250 / 1447) ≤ (146348897 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2697)) (n := 12)
    (lo := (4573403 / 31250000)) (hi := (146348897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1447 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1447 / 1250) = 1/(1250 / 1447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1021 : Bounds (4573403 / 31250000) (146348897 / 1000000000) (Real.log (1447 / 1250)) := by
  have h := reflection_log_1021_neg
  have he : Real.log (1447 / 1250) = -Real.log (1250 / 1447) := by
    rw [show ((1447 / 1250) : ℝ) = ((1250 / 1447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1022_neg : (85750159 / 500000000) ≤ -Real.log (1053 / 1250) ∧
    -Real.log (1053 / 1250) ≤ (171500319 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2303)) (n := 12)
    (lo := (85750159 / 500000000)) (hi := (171500319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1053) = 1/(1053 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1022 : Bounds (-171500319 / 1000000000) (-85750159 / 500000000) (Real.log (1053 / 1250)) := by
  have h := reflection_log_1022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1023_neg : (157587 / 1000000000) ≤ -Real.log (1250000 / 1250197) ∧
    -Real.log (1250000 / 1250197) ≤ (39397 / 250000000) := by
  have h := checkLog_sound (w := (197 / 2500197)) (n := 12)
    (lo := (157587 / 1000000000)) (hi := (39397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250197 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250197 / 1250000) = 1/(1250000 / 1250197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1023 : Bounds (157587 / 1000000000) (39397 / 250000000) (Real.log (1250197 / 1250000)) := by
  have h := reflection_log_1023_neg
  have he : Real.log (1250197 / 1250000) = -Real.log (1250000 / 1250197) := by
    rw [show ((1250197 / 1250000) : ℝ) = ((1250000 / 1250197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0016 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1024_neg : (39403 / 250000000) ≤ -Real.log (1249803 / 1250000) ∧
    -Real.log (1249803 / 1250000) ≤ (157613 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2499803)) (n := 12)
    (lo := (39403 / 250000000)) (hi := (157613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249803) = 1/(1249803 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1024 : Bounds (-157613 / 1000000000) (-39403 / 250000000) (Real.log (1249803 / 1250000)) := by
  have h := reflection_log_1024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1025_neg : (38029391 / 500000000) ≤ -Real.log (500000 / 539513) ∧
    -Real.log (500000 / 539513) ≤ (76058783 / 1000000000) := by
  have h := checkLog_sound (w := (39513 / 1039513)) (n := 12)
    (lo := (38029391 / 500000000)) (hi := (76058783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539513 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539513 / 500000) = 1/(500000 / 539513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1025 : Bounds (38029391 / 500000000) (76058783 / 1000000000) (Real.log (539513 / 500000)) := by
  have h := reflection_log_1025_neg
  have he : Real.log (539513 / 500000) = -Real.log (500000 / 539513) := by
    rw [show ((539513 / 500000) : ℝ) = ((500000 / 539513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1026_neg : (82323473 / 1000000000) ≤ -Real.log (460487 / 500000) ∧
    -Real.log (460487 / 500000) ≤ (41161737 / 500000000) := by
  have h := checkLog_sound (w := (39513 / 960487)) (n := 12)
    (lo := (82323473 / 1000000000)) (hi := (41161737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460487) = 1/(460487 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1026 : Bounds (-41161737 / 500000000) (-82323473 / 1000000000) (Real.log (460487 / 500000)) := by
  have h := reflection_log_1026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1027_neg : (7625153 / 100000000) ≤ -Real.log (500000 / 539617) ∧
    -Real.log (500000 / 539617) ≤ (76251531 / 1000000000) := by
  have h := checkLog_sound (w := (39617 / 1039617)) (n := 12)
    (lo := (7625153 / 100000000)) (hi := (76251531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539617 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539617 / 500000) = 1/(500000 / 539617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1027 : Bounds (7625153 / 100000000) (76251531 / 1000000000) (Real.log (539617 / 500000)) := by
  have h := reflection_log_1027_neg
  have he : Real.log (539617 / 500000) = -Real.log (500000 / 539617) := by
    rw [show ((539617 / 500000) : ℝ) = ((500000 / 539617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1028_neg : (41274673 / 500000000) ≤ -Real.log (460383 / 500000) ∧
    -Real.log (460383 / 500000) ≤ (82549347 / 1000000000) := by
  have h := checkLog_sound (w := (39617 / 960383)) (n := 12)
    (lo := (41274673 / 500000000)) (hi := (82549347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460383) = 1/(460383 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1028 : Bounds (-82549347 / 1000000000) (-41274673 / 500000000) (Real.log (460383 / 500000)) := by
  have h := reflection_log_1028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1029_neg : (787227 / 125000000) ≤ -Real.log (248430493311 / 250000000000) ∧
    -Real.log (248430493311 / 250000000000) ≤ (6297817 / 1000000000) := by
  have h := checkLog_sound (w := (1569506689 / 498430493311)) (n := 12)
    (lo := (787227 / 125000000)) (hi := (6297817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248430493311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248430493311) = 1/(248430493311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1029 : Bounds (-6297817 / 1000000000) (-787227 / 125000000) (Real.log (248430493311 / 250000000000)) := by
  have h := reflection_log_1029_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1030_neg : (626469 / 100000000) ≤ -Real.log (248438722831 / 250000000000) ∧
    -Real.log (248438722831 / 250000000000) ≤ (6264691 / 1000000000) := by
  have h := checkLog_sound (w := (1561277169 / 498438722831)) (n := 12)
    (lo := (626469 / 100000000)) (hi := (6264691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248438722831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248438722831) = 1/(248438722831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1030 : Bounds (-6264691 / 1000000000) (-626469 / 100000000) (Real.log (248438722831 / 250000000000)) := by
  have h := reflection_log_1030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1031_neg : (31676451 / 200000000) ≤ -Real.log (500000000000 / 585806982607) ∧
    -Real.log (500000000000 / 585806982607) ≤ (9898891 / 62500000) := by
  have h := checkLog_sound (w := (85806982607 / 1085806982607)) (n := 12)
    (lo := (31676451 / 200000000)) (hi := (9898891 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585806982607 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585806982607 / 500000000000) = 1/(500000000000 / 585806982607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1031 : Bounds (31676451 / 200000000) (9898891 / 62500000) (Real.log (585806982607 / 500000000000)) := by
  have h := reflection_log_1031_neg
  have he : Real.log (585806982607 / 500000000000) = -Real.log (500000000000 / 585806982607) := by
    rw [show ((585806982607 / 500000000000) : ℝ) = ((500000000000 / 585806982607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1032_neg : (39700219 / 250000000) ≤ -Real.log (25000000000 / 29302613259) ∧
    -Real.log (25000000000 / 29302613259) ≤ (158800877 / 1000000000) := by
  have h := checkLog_sound (w := (4302613259 / 54302613259)) (n := 12)
    (lo := (39700219 / 250000000)) (hi := (158800877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29302613259 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29302613259 / 25000000000) = 1/(25000000000 / 29302613259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1032 : Bounds (39700219 / 250000000) (158800877 / 1000000000) (Real.log (29302613259 / 25000000000)) := by
  have h := reflection_log_1032_neg
  have he : Real.log (29302613259 / 25000000000) = -Real.log (25000000000 / 29302613259) := by
    rw [show ((29302613259 / 25000000000) : ℝ) = ((25000000000 / 29302613259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1033_neg : (317644123 / 1000000000) ≤ -Real.log (250000000000 / 343471810089) ∧
    -Real.log (250000000000 / 343471810089) ≤ (79411031 / 250000000) := by
  have h := checkLog_sound (w := (93471810089 / 593471810089)) (n := 12)
    (lo := (317644123 / 1000000000)) (hi := (79411031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343471810089 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343471810089 / 250000000000) = 1/(250000000000 / 343471810089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1033 : Bounds (317644123 / 1000000000) (79411031 / 250000000) (Real.log (343471810089 / 250000000000)) := by
  have h := reflection_log_1033_neg
  have he : Real.log (343471810089 / 250000000000) = -Real.log (250000000000 / 343471810089) := by
    rw [show ((343471810089 / 250000000000) : ℝ) = ((250000000000 / 343471810089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1034_neg : (158924607 / 500000000) ≤ -Real.log (250000000000 / 343542260209) ∧
    -Real.log (250000000000 / 343542260209) ≤ (63569843 / 200000000) := by
  have h := checkLog_sound (w := (93542260209 / 593542260209)) (n := 12)
    (lo := (158924607 / 500000000)) (hi := (63569843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343542260209 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343542260209 / 250000000000) = 1/(250000000000 / 343542260209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1034 : Bounds (158924607 / 500000000) (63569843 / 200000000) (Real.log (343542260209 / 250000000000)) := by
  have h := reflection_log_1034_neg
  have he : Real.log (343542260209 / 250000000000) = -Real.log (250000000000 / 343542260209) := by
    rw [show ((343542260209 / 250000000000) : ℝ) = ((250000000000 / 343542260209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1035_neg : (73217639 / 500000000) ≤ -Real.log (10000 / 11577) ∧
    -Real.log (10000 / 11577) ≤ (146435279 / 1000000000) := by
  have h := checkLog_sound (w := (1577 / 21577)) (n := 12)
    (lo := (73217639 / 500000000)) (hi := (146435279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11577 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11577 / 10000) = 1/(10000 / 11577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1035 : Bounds (73217639 / 500000000) (146435279 / 1000000000) (Real.log (11577 / 10000)) := by
  have h := reflection_log_1035_neg
  have he : Real.log (11577 / 10000) = -Real.log (10000 / 11577) := by
    rw [show ((11577 / 10000) : ℝ) = ((10000 / 11577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1036_neg : (171619033 / 1000000000) ≤ -Real.log (8423 / 10000) ∧
    -Real.log (8423 / 10000) ≤ (85809517 / 500000000) := by
  have h := checkLog_sound (w := (1577 / 18423)) (n := 12)
    (lo := (171619033 / 1000000000)) (hi := (85809517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8423) = 1/(8423 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1036 : Bounds (-85809517 / 500000000) (-171619033 / 1000000000) (Real.log (8423 / 10000)) := by
  have h := reflection_log_1036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1037_neg : (157687 / 1000000000) ≤ -Real.log (10000000 / 10001577) ∧
    -Real.log (10000000 / 10001577) ≤ (19711 / 125000000) := by
  have h := checkLog_sound (w := (1577 / 20001577)) (n := 12)
    (lo := (157687 / 1000000000)) (hi := (19711 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001577 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001577 / 10000000) = 1/(10000000 / 10001577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1037 : Bounds (157687 / 1000000000) (19711 / 125000000) (Real.log (10001577 / 10000000)) := by
  have h := reflection_log_1037_neg
  have he : Real.log (10001577 / 10000000) = -Real.log (10000000 / 10001577) := by
    rw [show ((10001577 / 10000000) : ℝ) = ((10000000 / 10001577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1038_neg : (9857 / 62500000) ≤ -Real.log (9998423 / 10000000) ∧
    -Real.log (9998423 / 10000000) ≤ (157713 / 1000000000) := by
  have h := checkLog_sound (w := (1577 / 19998423)) (n := 12)
    (lo := (9857 / 62500000)) (hi := (157713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998423) = 1/(9998423 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1038 : Bounds (-157713 / 1000000000) (-9857 / 62500000) (Real.log (9998423 / 10000000)) := by
  have h := reflection_log_1038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1039_neg : (38053023 / 500000000) ≤ -Real.log (1000000 / 1079077) ∧
    -Real.log (1000000 / 1079077) ≤ (76106047 / 1000000000) := by
  have h := checkLog_sound (w := (79077 / 2079077)) (n := 12)
    (lo := (38053023 / 500000000)) (hi := (76106047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079077 / 1000000) = 1/(1000000 / 1079077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1039 : Bounds (38053023 / 500000000) (76106047 / 1000000000) (Real.log (1079077 / 1000000)) := by
  have h := reflection_log_1039_neg
  have he : Real.log (1079077 / 1000000) = -Real.log (1000000 / 1079077) := by
    rw [show ((1079077 / 1000000) : ℝ) = ((1000000 / 1079077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1040_neg : (1647577 / 20000000) ≤ -Real.log (920923 / 1000000) ∧
    -Real.log (920923 / 1000000) ≤ (82378851 / 1000000000) := by
  have h := checkLog_sound (w := (79077 / 1920923)) (n := 12)
    (lo := (1647577 / 20000000)) (hi := (82378851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920923) = 1/(920923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1040 : Bounds (-82378851 / 1000000000) (-1647577 / 20000000) (Real.log (920923 / 1000000)) := by
  have h := reflection_log_1040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1041_neg : (2384337 / 31250000) ≤ -Real.log (200000 / 215857) ∧
    -Real.log (200000 / 215857) ≤ (15259757 / 200000000) := by
  have h := checkLog_sound (w := (15857 / 415857)) (n := 12)
    (lo := (2384337 / 31250000)) (hi := (15259757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215857 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215857 / 200000) = 1/(200000 / 215857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1041 : Bounds (2384337 / 31250000) (15259757 / 200000000) (Real.log (215857 / 200000)) := by
  have h := reflection_log_1041_neg
  have he : Real.log (215857 / 200000) = -Real.log (200000 / 215857) := by
    rw [show ((215857 / 200000) : ℝ) = ((200000 / 215857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1042_neg : (1290699 / 15625000) ≤ -Real.log (184143 / 200000) ∧
    -Real.log (184143 / 200000) ≤ (82604737 / 1000000000) := by
  have h := checkLog_sound (w := (15857 / 384143)) (n := 12)
    (lo := (1290699 / 15625000)) (hi := (82604737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184143) = 1/(184143 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1042 : Bounds (-82604737 / 1000000000) (-1290699 / 15625000) (Real.log (184143 / 200000)) := by
  have h := reflection_log_1042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1043_neg : (197061 / 31250000) ≤ -Real.log (39748555551 / 40000000000) ∧
    -Real.log (39748555551 / 40000000000) ≤ (6305953 / 1000000000) := by
  have h := checkLog_sound (w := (251444449 / 79748555551)) (n := 12)
    (lo := (197061 / 31250000)) (hi := (6305953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39748555551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39748555551) = 1/(39748555551 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1043 : Bounds (-6305953 / 1000000000) (-197061 / 31250000) (Real.log (39748555551 / 40000000000)) := by
  have h := reflection_log_1043_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1044_neg : (1568201 / 250000000) ≤ -Real.log (993746828071 / 1000000000000) ∧
    -Real.log (993746828071 / 1000000000000) ≤ (1254561 / 200000000) := by
  have h := checkLog_sound (w := (6253171929 / 1993746828071)) (n := 12)
    (lo := (1568201 / 250000000)) (hi := (1254561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993746828071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993746828071) = 1/(993746828071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1044 : Bounds (-1254561 / 200000000) (-1568201 / 250000000) (Real.log (993746828071 / 1000000000000)) := by
  have h := reflection_log_1044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1045_neg : (158484897 / 1000000000) ≤ -Real.log (250000000000 / 292933556877) ∧
    -Real.log (250000000000 / 292933556877) ≤ (79242449 / 500000000) := by
  have h := checkLog_sound (w := (42933556877 / 542933556877)) (n := 12)
    (lo := (158484897 / 1000000000)) (hi := (79242449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292933556877 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292933556877 / 250000000000) = 1/(250000000000 / 292933556877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1045 : Bounds (158484897 / 1000000000) (79242449 / 500000000) (Real.log (292933556877 / 250000000000)) := by
  have h := reflection_log_1045_neg
  have he : Real.log (292933556877 / 250000000000) = -Real.log (250000000000 / 292933556877) := by
    rw [show ((292933556877 / 250000000000) : ℝ) = ((250000000000 / 292933556877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1046_neg : (158903521 / 1000000000) ≤ -Real.log (500000000000 / 586112423497) ∧
    -Real.log (500000000000 / 586112423497) ≤ (79451761 / 500000000) := by
  have h := checkLog_sound (w := (86112423497 / 1086112423497)) (n := 12)
    (lo := (158903521 / 1000000000)) (hi := (79451761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586112423497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586112423497 / 500000000000) = 1/(500000000000 / 586112423497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1046 : Bounds (158903521 / 1000000000) (79451761 / 500000000) (Real.log (586112423497 / 500000000000)) := by
  have h := reflection_log_1046_neg
  have he : Real.log (586112423497 / 500000000000) = -Real.log (500000000000 / 586112423497) := by
    rw [show ((586112423497 / 500000000000) : ℝ) = ((500000000000 / 586112423497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1047_neg : (158924607 / 500000000) ≤ -Real.log (500000000000 / 687084520417) ∧
    -Real.log (500000000000 / 687084520417) ≤ (63569843 / 200000000) := by
  have h := checkLog_sound (w := (187084520417 / 1187084520417)) (n := 12)
    (lo := (158924607 / 500000000)) (hi := (63569843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687084520417 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687084520417 / 500000000000) = 1/(500000000000 / 687084520417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1047 : Bounds (158924607 / 500000000) (63569843 / 200000000) (Real.log (687084520417 / 500000000000)) := by
  have h := reflection_log_1047_neg
  have he : Real.log (687084520417 / 500000000000) = -Real.log (500000000000 / 687084520417) := by
    rw [show ((687084520417 / 500000000000) : ℝ) = ((500000000000 / 687084520417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1048_neg : (318054311 / 1000000000) ≤ -Real.log (250000000000 / 343612727057) ∧
    -Real.log (250000000000 / 343612727057) ≤ (39756789 / 125000000) := by
  have h := checkLog_sound (w := (93612727057 / 593612727057)) (n := 12)
    (lo := (318054311 / 1000000000)) (hi := (39756789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343612727057 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343612727057 / 250000000000) = 1/(250000000000 / 343612727057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1048 : Bounds (318054311 / 1000000000) (39756789 / 125000000) (Real.log (343612727057 / 250000000000)) := by
  have h := reflection_log_1048_neg
  have he : Real.log (343612727057 / 250000000000) = -Real.log (250000000000 / 343612727057) := by
    rw [show ((343612727057 / 250000000000) : ℝ) = ((250000000000 / 343612727057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1049_neg : (36630413 / 250000000) ≤ -Real.log (5000 / 5789) ∧
    -Real.log (5000 / 5789) ≤ (146521653 / 1000000000) := by
  have h := checkLog_sound (w := (789 / 10789)) (n := 12)
    (lo := (36630413 / 250000000)) (hi := (146521653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5789 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5789 / 5000) = 1/(5000 / 5789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1049 : Bounds (36630413 / 250000000) (146521653 / 1000000000) (Real.log (5789 / 5000)) := by
  have h := reflection_log_1049_neg
  have he : Real.log (5789 / 5000) = -Real.log (5000 / 5789) := by
    rw [show ((5789 / 5000) : ℝ) = ((5000 / 5789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1050_neg : (171737763 / 1000000000) ≤ -Real.log (4211 / 5000) ∧
    -Real.log (4211 / 5000) ≤ (42934441 / 250000000) := by
  have h := checkLog_sound (w := (789 / 9211)) (n := 12)
    (lo := (171737763 / 1000000000)) (hi := (42934441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4211) = 1/(4211 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1050 : Bounds (-42934441 / 250000000) (-171737763 / 1000000000) (Real.log (4211 / 5000)) := by
  have h := reflection_log_1050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1051_neg : (157787 / 1000000000) ≤ -Real.log (5000000 / 5000789) ∧
    -Real.log (5000000 / 5000789) ≤ (39447 / 250000000) := by
  have h := checkLog_sound (w := (789 / 10000789)) (n := 12)
    (lo := (157787 / 1000000000)) (hi := (39447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000789 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000789 / 5000000) = 1/(5000000 / 5000789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1051 : Bounds (157787 / 1000000000) (39447 / 250000000) (Real.log (5000789 / 5000000)) := by
  have h := reflection_log_1051_neg
  have he : Real.log (5000789 / 5000000) = -Real.log (5000000 / 5000789) := by
    rw [show ((5000789 / 5000000) : ℝ) = ((5000000 / 5000789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1052_neg : (39453 / 250000000) ≤ -Real.log (4999211 / 5000000) ∧
    -Real.log (4999211 / 5000000) ≤ (157813 / 1000000000) := by
  have h := checkLog_sound (w := (789 / 9999211)) (n := 12)
    (lo := (39453 / 250000000)) (hi := (157813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999211) = 1/(4999211 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1052 : Bounds (-157813 / 1000000000) (-39453 / 250000000) (Real.log (4999211 / 5000000)) := by
  have h := reflection_log_1052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1053_neg : (3807619 / 50000000) ≤ -Real.log (1000000 / 1079127) ∧
    -Real.log (1000000 / 1079127) ≤ (76152381 / 1000000000) := by
  have h := checkLog_sound (w := (79127 / 2079127)) (n := 12)
    (lo := (3807619 / 50000000)) (hi := (76152381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079127 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079127 / 1000000) = 1/(1000000 / 1079127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1053 : Bounds (3807619 / 50000000) (76152381 / 1000000000) (Real.log (1079127 / 1000000)) := by
  have h := reflection_log_1053_neg
  have he : Real.log (1079127 / 1000000) = -Real.log (1000000 / 1079127) := by
    rw [show ((1079127 / 1000000) : ℝ) = ((1000000 / 1079127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1054_neg : (16486629 / 200000000) ≤ -Real.log (920873 / 1000000) ∧
    -Real.log (920873 / 1000000) ≤ (41216573 / 500000000) := by
  have h := checkLog_sound (w := (79127 / 1920873)) (n := 12)
    (lo := (16486629 / 200000000)) (hi := (41216573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920873) = 1/(920873 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1054 : Bounds (-41216573 / 500000000) (-16486629 / 200000000) (Real.log (920873 / 1000000)) := by
  have h := reflection_log_1054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1055_neg : (76346037 / 1000000000) ≤ -Real.log (125000 / 134917) ∧
    -Real.log (125000 / 134917) ≤ (38173019 / 500000000) := by
  have h := checkLog_sound (w := (9917 / 259917)) (n := 12)
    (lo := (76346037 / 1000000000)) (hi := (38173019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134917 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134917 / 125000) = 1/(125000 / 134917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1055 : Bounds (76346037 / 1000000000) (38173019 / 500000000) (Real.log (134917 / 125000)) := by
  have h := reflection_log_1055_neg
  have he : Real.log (134917 / 125000) = -Real.log (125000 / 134917) := by
    rw [show ((134917 / 125000) : ℝ) = ((125000 / 134917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1056_neg : (8266013 / 100000000) ≤ -Real.log (115083 / 125000) ∧
    -Real.log (115083 / 125000) ≤ (82660131 / 1000000000) := by
  have h := checkLog_sound (w := (9917 / 240083)) (n := 12)
    (lo := (8266013 / 100000000)) (hi := (82660131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115083) = 1/(115083 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1056 : Bounds (-82660131 / 1000000000) (-8266013 / 100000000) (Real.log (115083 / 125000)) := by
  have h := reflection_log_1056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1057_neg : (1578523 / 250000000) ≤ -Real.log (15526653111 / 15625000000) ∧
    -Real.log (15526653111 / 15625000000) ≤ (6314093 / 1000000000) := by
  have h := checkLog_sound (w := (98346889 / 31151653111)) (n := 12)
    (lo := (1578523 / 250000000)) (hi := (6314093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15526653111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15526653111) = 1/(15526653111 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1057 : Bounds (-6314093 / 1000000000) (-1578523 / 250000000) (Real.log (15526653111 / 15625000000)) := by
  have h := reflection_log_1057_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1058_neg : (1570191 / 250000000) ≤ -Real.log (993738917871 / 1000000000000) ∧
    -Real.log (993738917871 / 1000000000000) ≤ (1256153 / 200000000) := by
  have h := checkLog_sound (w := (6261082129 / 1993738917871)) (n := 12)
    (lo := (1570191 / 250000000)) (hi := (1256153 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993738917871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993738917871) = 1/(993738917871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1058 : Bounds (-1256153 / 200000000) (-1570191 / 250000000) (Real.log (993738917871 / 1000000000000)) := by
  have h := reflection_log_1058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1059_neg : (79292763 / 500000000) ≤ -Real.log (125000000000 / 146481518081) ∧
    -Real.log (125000000000 / 146481518081) ≤ (158585527 / 1000000000) := by
  have h := checkLog_sound (w := (21481518081 / 271481518081)) (n := 12)
    (lo := (79292763 / 500000000)) (hi := (158585527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146481518081 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146481518081 / 125000000000) = 1/(125000000000 / 146481518081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1059 : Bounds (79292763 / 500000000) (158585527 / 1000000000) (Real.log (146481518081 / 125000000000)) := by
  have h := reflection_log_1059_neg
  have he : Real.log (146481518081 / 125000000000) = -Real.log (125000000000 / 146481518081) := by
    rw [show ((146481518081 / 125000000000) : ℝ) = ((125000000000 / 146481518081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1060_neg : (159006167 / 1000000000) ≤ -Real.log (1562500000 / 1831789339) ∧
    -Real.log (1562500000 / 1831789339) ≤ (19875771 / 125000000) := by
  have h := checkLog_sound (w := (269289339 / 3394289339)) (n := 12)
    (lo := (159006167 / 1000000000)) (hi := (19875771 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1831789339 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1831789339 / 1562500000) = 1/(1562500000 / 1831789339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1060 : Bounds (159006167 / 1000000000) (19875771 / 125000000) (Real.log (1831789339 / 1562500000)) := by
  have h := reflection_log_1060_neg
  have he : Real.log (1831789339 / 1562500000) = -Real.log (1562500000 / 1831789339) := by
    rw [show ((1831789339 / 1562500000) : ℝ) = ((1562500000 / 1831789339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1061_neg : (318054311 / 1000000000) ≤ -Real.log (500000000000 / 687225454113) ∧
    -Real.log (500000000000 / 687225454113) ≤ (39756789 / 125000000) := by
  have h := checkLog_sound (w := (187225454113 / 1187225454113)) (n := 12)
    (lo := (318054311 / 1000000000)) (hi := (39756789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687225454113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687225454113 / 500000000000) = 1/(500000000000 / 687225454113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1061 : Bounds (318054311 / 1000000000) (39756789 / 125000000) (Real.log (687225454113 / 500000000000)) := by
  have h := reflection_log_1061_neg
  have he : Real.log (687225454113 / 500000000000) = -Real.log (500000000000 / 687225454113) := by
    rw [show ((687225454113 / 500000000000) : ℝ) = ((500000000000 / 687225454113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1062_neg : (63651883 / 200000000) ≤ -Real.log (250000000000 / 343683210639) ∧
    -Real.log (250000000000 / 343683210639) ≤ (39782427 / 125000000) := by
  have h := checkLog_sound (w := (93683210639 / 593683210639)) (n := 12)
    (lo := (63651883 / 200000000)) (hi := (39782427 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343683210639 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343683210639 / 250000000000) = 1/(250000000000 / 343683210639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1062 : Bounds (63651883 / 200000000) (39782427 / 125000000) (Real.log (343683210639 / 250000000000)) := by
  have h := reflection_log_1062_neg
  have he : Real.log (343683210639 / 250000000000) = -Real.log (250000000000 / 343683210639) := by
    rw [show ((343683210639 / 250000000000) : ℝ) = ((250000000000 / 343683210639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1063_neg : (146608019 / 1000000000) ≤ -Real.log (10000 / 11579) ∧
    -Real.log (10000 / 11579) ≤ (7330401 / 50000000) := by
  have h := checkLog_sound (w := (1579 / 21579)) (n := 12)
    (lo := (146608019 / 1000000000)) (hi := (7330401 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11579 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11579 / 10000) = 1/(10000 / 11579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1063 : Bounds (146608019 / 1000000000) (7330401 / 50000000) (Real.log (11579 / 10000)) := by
  have h := reflection_log_1063_neg
  have he : Real.log (11579 / 10000) = -Real.log (10000 / 11579) := by
    rw [show ((11579 / 10000) : ℝ) = ((10000 / 11579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1064_neg : (85928253 / 500000000) ≤ -Real.log (8421 / 10000) ∧
    -Real.log (8421 / 10000) ≤ (171856507 / 1000000000) := by
  have h := checkLog_sound (w := (1579 / 18421)) (n := 12)
    (lo := (85928253 / 500000000)) (hi := (171856507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8421) = 1/(8421 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1064 : Bounds (-171856507 / 1000000000) (-85928253 / 500000000) (Real.log (8421 / 10000)) := by
  have h := reflection_log_1064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1065_neg : (157887 / 1000000000) ≤ -Real.log (10000000 / 10001579) ∧
    -Real.log (10000000 / 10001579) ≤ (2467 / 15625000) := by
  have h := checkLog_sound (w := (1579 / 20001579)) (n := 12)
    (lo := (157887 / 1000000000)) (hi := (2467 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001579 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001579 / 10000000) = 1/(10000000 / 10001579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1065 : Bounds (157887 / 1000000000) (2467 / 15625000) (Real.log (10001579 / 10000000)) := by
  have h := reflection_log_1065_neg
  have he : Real.log (10001579 / 10000000) = -Real.log (10000000 / 10001579) := by
    rw [show ((10001579 / 10000000) : ℝ) = ((10000000 / 10001579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1066_neg : (19739 / 125000000) ≤ -Real.log (9998421 / 10000000) ∧
    -Real.log (9998421 / 10000000) ≤ (157913 / 1000000000) := by
  have h := checkLog_sound (w := (1579 / 19998421)) (n := 12)
    (lo := (19739 / 125000000)) (hi := (157913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998421) = 1/(9998421 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1066 : Bounds (-157913 / 1000000000) (-19739 / 125000000) (Real.log (9998421 / 10000000)) := by
  have h := reflection_log_1066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1067_neg : (1904991 / 25000000) ≤ -Real.log (500000 / 539589) ∧
    -Real.log (500000 / 539589) ≤ (76199641 / 1000000000) := by
  have h := checkLog_sound (w := (39589 / 1039589)) (n := 12)
    (lo := (1904991 / 25000000)) (hi := (76199641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539589 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539589 / 500000) = 1/(500000 / 539589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1067 : Bounds (1904991 / 25000000) (76199641 / 1000000000) (Real.log (539589 / 500000)) := by
  have h := reflection_log_1067_neg
  have he : Real.log (539589 / 500000) = -Real.log (500000 / 539589) := by
    rw [show ((539589 / 500000) : ℝ) = ((500000 / 539589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1068_neg : (82488529 / 1000000000) ≤ -Real.log (460411 / 500000) ∧
    -Real.log (460411 / 500000) ≤ (8248853 / 100000000) := by
  have h := checkLog_sound (w := (39589 / 960411)) (n := 12)
    (lo := (82488529 / 1000000000)) (hi := (8248853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460411) = 1/(460411 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1068 : Bounds (-8248853 / 100000000) (-82488529 / 1000000000) (Real.log (460411 / 500000)) := by
  have h := reflection_log_1068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1069_neg : (76393287 / 1000000000) ≤ -Real.log (1000000 / 1079387) ∧
    -Real.log (1000000 / 1079387) ≤ (9549161 / 125000000) := by
  have h := checkLog_sound (w := (79387 / 2079387)) (n := 12)
    (lo := (76393287 / 1000000000)) (hi := (9549161 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079387 / 1000000) = 1/(1000000 / 1079387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1069 : Bounds (76393287 / 1000000000) (9549161 / 125000000) (Real.log (1079387 / 1000000)) := by
  have h := reflection_log_1069_neg
  have he : Real.log (1079387 / 1000000) = -Real.log (1000000 / 1079387) := by
    rw [show ((1079387 / 1000000) : ℝ) = ((1000000 / 1079387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1070_neg : (41357763 / 500000000) ≤ -Real.log (920613 / 1000000) ∧
    -Real.log (920613 / 1000000) ≤ (82715527 / 1000000000) := by
  have h := checkLog_sound (w := (79387 / 1920613)) (n := 12)
    (lo := (41357763 / 500000000)) (hi := (82715527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920613) = 1/(920613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1070 : Bounds (-82715527 / 1000000000) (-41357763 / 500000000) (Real.log (920613 / 1000000)) := by
  have h := reflection_log_1070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1071_neg : (6322239 / 1000000000) ≤ -Real.log (993697704231 / 1000000000000) ∧
    -Real.log (993697704231 / 1000000000000) ≤ (19757 / 3125000) := by
  have h := checkLog_sound (w := (6302295769 / 1993697704231)) (n := 12)
    (lo := (6322239 / 1000000000)) (hi := (19757 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993697704231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993697704231) = 1/(993697704231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1071 : Bounds (-19757 / 3125000) (-6322239 / 1000000000) (Real.log (993697704231 / 1000000000000)) := by
  have h := reflection_log_1071_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1072_neg : (6288889 / 1000000000) ≤ -Real.log (248432711079 / 250000000000) ∧
    -Real.log (248432711079 / 250000000000) ≤ (628889 / 100000000) := by
  have h := checkLog_sound (w := (1567288921 / 498432711079)) (n := 12)
    (lo := (6288889 / 1000000000)) (hi := (628889 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248432711079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248432711079) = 1/(248432711079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1072 : Bounds (-628889 / 100000000) (-6288889 / 1000000000) (Real.log (248432711079 / 250000000000)) := by
  have h := reflection_log_1072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1073_neg : (158688169 / 1000000000) ≤ -Real.log (250000000000 / 292993108331) ∧
    -Real.log (250000000000 / 292993108331) ≤ (15868817 / 100000000) := by
  have h := checkLog_sound (w := (42993108331 / 542993108331)) (n := 12)
    (lo := (158688169 / 1000000000)) (hi := (15868817 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292993108331 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292993108331 / 250000000000) = 1/(250000000000 / 292993108331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1073 : Bounds (158688169 / 1000000000) (15868817 / 100000000) (Real.log (292993108331 / 250000000000)) := by
  have h := reflection_log_1073_neg
  have he : Real.log (292993108331 / 250000000000) = -Real.log (250000000000 / 292993108331) := by
    rw [show ((292993108331 / 250000000000) : ℝ) = ((250000000000 / 292993108331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1074_neg : (159108813 / 1000000000) ≤ -Real.log (500000000000 / 586232760129) ∧
    -Real.log (500000000000 / 586232760129) ≤ (79554407 / 500000000) := by
  have h := checkLog_sound (w := (86232760129 / 1086232760129)) (n := 12)
    (lo := (159108813 / 1000000000)) (hi := (79554407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586232760129 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586232760129 / 500000000000) = 1/(500000000000 / 586232760129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1074 : Bounds (159108813 / 1000000000) (79554407 / 500000000) (Real.log (586232760129 / 500000000000)) := by
  have h := reflection_log_1074_neg
  have he : Real.log (586232760129 / 500000000000) = -Real.log (500000000000 / 586232760129) := by
    rw [show ((586232760129 / 500000000000) : ℝ) = ((500000000000 / 586232760129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1075_neg : (63651883 / 200000000) ≤ -Real.log (500000000000 / 687366421277) ∧
    -Real.log (500000000000 / 687366421277) ≤ (39782427 / 125000000) := by
  have h := checkLog_sound (w := (187366421277 / 1187366421277)) (n := 12)
    (lo := (63651883 / 200000000)) (hi := (39782427 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687366421277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687366421277 / 500000000000) = 1/(500000000000 / 687366421277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1075 : Bounds (63651883 / 200000000) (39782427 / 125000000) (Real.log (687366421277 / 500000000000)) := by
  have h := reflection_log_1075_neg
  have he : Real.log (687366421277 / 500000000000) = -Real.log (500000000000 / 687366421277) := by
    rw [show ((687366421277 / 500000000000) : ℝ) = ((500000000000 / 687366421277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1076_neg : (159232263 / 500000000) ≤ -Real.log (250000000000 / 343753710961) ∧
    -Real.log (250000000000 / 343753710961) ≤ (318464527 / 1000000000) := by
  have h := checkLog_sound (w := (93753710961 / 593753710961)) (n := 12)
    (lo := (159232263 / 500000000)) (hi := (318464527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343753710961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343753710961 / 250000000000) = 1/(250000000000 / 343753710961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1076 : Bounds (159232263 / 500000000) (318464527 / 1000000000) (Real.log (343753710961 / 250000000000)) := by
  have h := reflection_log_1076_neg
  have he : Real.log (343753710961 / 250000000000) = -Real.log (250000000000 / 343753710961) := by
    rw [show ((343753710961 / 250000000000) : ℝ) = ((250000000000 / 343753710961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1077_neg : (146694379 / 1000000000) ≤ -Real.log (500 / 579) ∧
    -Real.log (500 / 579) ≤ (7334719 / 50000000) := by
  have h := checkLog_sound (w := (79 / 1079)) (n := 12)
    (lo := (146694379 / 1000000000)) (hi := (7334719 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579 / 500) = 1/(500 / 579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1077 : Bounds (146694379 / 1000000000) (7334719 / 50000000) (Real.log (579 / 500)) := by
  have h := reflection_log_1077_neg
  have he : Real.log (579 / 500) = -Real.log (500 / 579) := by
    rw [show ((579 / 500) : ℝ) = ((500 / 579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1078_neg : (5374227 / 31250000) ≤ -Real.log (421 / 500) ∧
    -Real.log (421 / 500) ≤ (34395053 / 200000000) := by
  have h := checkLog_sound (w := (79 / 921)) (n := 12)
    (lo := (5374227 / 31250000)) (hi := (34395053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 421) = 1/(421 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1078 : Bounds (-34395053 / 200000000) (-5374227 / 31250000) (Real.log (421 / 500)) := by
  have h := reflection_log_1078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1079_neg : (157987 / 1000000000) ≤ -Real.log (500000 / 500079) ∧
    -Real.log (500000 / 500079) ≤ (39497 / 250000000) := by
  have h := checkLog_sound (w := (79 / 1000079)) (n := 12)
    (lo := (157987 / 1000000000)) (hi := (39497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500079 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500079 / 500000) = 1/(500000 / 500079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1079 : Bounds (157987 / 1000000000) (39497 / 250000000) (Real.log (500079 / 500000)) := by
  have h := reflection_log_1079_neg
  have he : Real.log (500079 / 500000) = -Real.log (500000 / 500079) := by
    rw [show ((500079 / 500000) : ℝ) = ((500000 / 500079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1080_neg : (39503 / 250000000) ≤ -Real.log (499921 / 500000) ∧
    -Real.log (499921 / 500000) ≤ (158013 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 999921)) (n := 12)
    (lo := (39503 / 250000000)) (hi := (158013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499921) = 1/(499921 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1080 : Bounds (-158013 / 1000000000) (-39503 / 250000000) (Real.log (499921 / 500000)) := by
  have h := reflection_log_1080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1081_neg : (7624597 / 100000000) ≤ -Real.log (250000 / 269807) ∧
    -Real.log (250000 / 269807) ≤ (76245971 / 1000000000) := by
  have h := checkLog_sound (w := (19807 / 519807)) (n := 12)
    (lo := (7624597 / 100000000)) (hi := (76245971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269807 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269807 / 250000) = 1/(250000 / 269807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1081 : Bounds (7624597 / 100000000) (76245971 / 1000000000) (Real.log (269807 / 250000)) := by
  have h := reflection_log_1081_neg
  have he : Real.log (269807 / 250000) = -Real.log (250000 / 269807) := by
    rw [show ((269807 / 250000) : ℝ) = ((250000 / 269807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1082_neg : (8254283 / 100000000) ≤ -Real.log (230193 / 250000) ∧
    -Real.log (230193 / 250000) ≤ (82542831 / 1000000000) := by
  have h := checkLog_sound (w := (19807 / 480193)) (n := 12)
    (lo := (8254283 / 100000000)) (hi := (82542831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230193) = 1/(230193 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1082 : Bounds (-82542831 / 1000000000) (-8254283 / 100000000) (Real.log (230193 / 250000)) := by
  have h := reflection_log_1082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1083_neg : (9554951 / 125000000) ≤ -Real.log (1000000 / 1079437) ∧
    -Real.log (1000000 / 1079437) ≤ (76439609 / 1000000000) := by
  have h := checkLog_sound (w := (79437 / 2079437)) (n := 12)
    (lo := (9554951 / 125000000)) (hi := (76439609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079437 / 1000000) = 1/(1000000 / 1079437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1083 : Bounds (9554951 / 125000000) (76439609 / 1000000000) (Real.log (1079437 / 1000000)) := by
  have h := reflection_log_1083_neg
  have he : Real.log (1079437 / 1000000) = -Real.log (1000000 / 1079437) := by
    rw [show ((1079437 / 1000000) : ℝ) = ((1000000 / 1079437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1084_neg : (82769839 / 1000000000) ≤ -Real.log (920563 / 1000000) ∧
    -Real.log (920563 / 1000000) ≤ (1034623 / 12500000) := by
  have h := checkLog_sound (w := (79437 / 1920563)) (n := 12)
    (lo := (82769839 / 1000000000)) (hi := (1034623 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920563) = 1/(920563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1084 : Bounds (-1034623 / 12500000) (-82769839 / 1000000000) (Real.log (920563 / 1000000)) := by
  have h := reflection_log_1084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1085_neg : (633023 / 100000000) ≤ -Real.log (993689763031 / 1000000000000) ∧
    -Real.log (993689763031 / 1000000000000) ≤ (6330231 / 1000000000) := by
  have h := checkLog_sound (w := (6310236969 / 1993689763031)) (n := 12)
    (lo := (633023 / 100000000)) (hi := (6330231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993689763031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993689763031) = 1/(993689763031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1085 : Bounds (-6330231 / 1000000000) (-633023 / 100000000) (Real.log (993689763031 / 1000000000000)) := by
  have h := reflection_log_1085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1086_neg : (6296859 / 1000000000) ≤ -Real.log (62107682751 / 62500000000) ∧
    -Real.log (62107682751 / 62500000000) ≤ (314843 / 50000000) := by
  have h := checkLog_sound (w := (392317249 / 124607682751)) (n := 12)
    (lo := (6296859 / 1000000000)) (hi := (314843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62107682751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62107682751) = 1/(62107682751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1086 : Bounds (-314843 / 50000000) (-6296859 / 1000000000) (Real.log (62107682751 / 62500000000)) := by
  have h := reflection_log_1086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1087_neg : (158788801 / 1000000000) ≤ -Real.log (62500000000 / 73255648521) ∧
    -Real.log (62500000000 / 73255648521) ≤ (79394401 / 500000000) := by
  have h := checkLog_sound (w := (10755648521 / 135755648521)) (n := 12)
    (lo := (158788801 / 1000000000)) (hi := (79394401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73255648521 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73255648521 / 62500000000) = 1/(62500000000 / 73255648521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1087 : Bounds (158788801 / 1000000000) (79394401 / 500000000) (Real.log (73255648521 / 62500000000)) := by
  have h := reflection_log_1087_neg
  have he : Real.log (73255648521 / 62500000000) = -Real.log (62500000000 / 73255648521) := by
    rw [show ((73255648521 / 62500000000) : ℝ) = ((62500000000 / 73255648521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0017 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1088_neg : (19901181 / 125000000) ≤ -Real.log (250000000000 / 293145879207) ∧
    -Real.log (250000000000 / 293145879207) ≤ (159209449 / 1000000000) := by
  have h := checkLog_sound (w := (43145879207 / 543145879207)) (n := 12)
    (lo := (19901181 / 125000000)) (hi := (159209449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293145879207 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293145879207 / 250000000000) = 1/(250000000000 / 293145879207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1088 : Bounds (19901181 / 125000000) (159209449 / 1000000000) (Real.log (293145879207 / 250000000000)) := by
  have h := reflection_log_1088_neg
  have he : Real.log (293145879207 / 250000000000) = -Real.log (250000000000 / 293145879207) := by
    rw [show ((293145879207 / 250000000000) : ℝ) = ((250000000000 / 293145879207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1089_neg : (159232263 / 500000000) ≤ -Real.log (500000000000 / 687507421921) ∧
    -Real.log (500000000000 / 687507421921) ≤ (318464527 / 1000000000) := by
  have h := checkLog_sound (w := (187507421921 / 1187507421921)) (n := 12)
    (lo := (159232263 / 500000000)) (hi := (318464527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687507421921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687507421921 / 500000000000) = 1/(500000000000 / 687507421921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1089 : Bounds (159232263 / 500000000) (318464527 / 1000000000) (Real.log (687507421921 / 500000000000)) := by
  have h := reflection_log_1089_neg
  have he : Real.log (687507421921 / 500000000000) = -Real.log (500000000000 / 687507421921) := by
    rw [show ((687507421921 / 500000000000) : ℝ) = ((500000000000 / 687507421921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1090_neg : (318669643 / 1000000000) ≤ -Real.log (250000000000 / 343824228029) ∧
    -Real.log (250000000000 / 343824228029) ≤ (79667411 / 250000000) := by
  have h := checkLog_sound (w := (93824228029 / 593824228029)) (n := 12)
    (lo := (318669643 / 1000000000)) (hi := (79667411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343824228029 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343824228029 / 250000000000) = 1/(250000000000 / 343824228029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1090 : Bounds (318669643 / 1000000000) (79667411 / 250000000) (Real.log (343824228029 / 250000000000)) := by
  have h := reflection_log_1090_neg
  have he : Real.log (343824228029 / 250000000000) = -Real.log (250000000000 / 343824228029) := by
    rw [show ((343824228029 / 250000000000) : ℝ) = ((250000000000 / 343824228029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1091_neg : (146780731 / 1000000000) ≤ -Real.log (10000 / 11581) ∧
    -Real.log (10000 / 11581) ≤ (36695183 / 250000000) := by
  have h := checkLog_sound (w := (1581 / 21581)) (n := 12)
    (lo := (146780731 / 1000000000)) (hi := (36695183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11581 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11581 / 10000) = 1/(10000 / 11581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1091 : Bounds (146780731 / 1000000000) (36695183 / 250000000) (Real.log (11581 / 10000)) := by
  have h := reflection_log_1091_neg
  have he : Real.log (11581 / 10000) = -Real.log (10000 / 11581) := by
    rw [show ((11581 / 10000) : ℝ) = ((10000 / 11581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1092_neg : (43023509 / 250000000) ≤ -Real.log (8419 / 10000) ∧
    -Real.log (8419 / 10000) ≤ (172094037 / 1000000000) := by
  have h := checkLog_sound (w := (1581 / 18419)) (n := 12)
    (lo := (43023509 / 250000000)) (hi := (172094037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8419) = 1/(8419 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1092 : Bounds (-172094037 / 1000000000) (-43023509 / 250000000) (Real.log (8419 / 10000)) := by
  have h := reflection_log_1092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1093_neg : (158087 / 1000000000) ≤ -Real.log (10000000 / 10001581) ∧
    -Real.log (10000000 / 10001581) ≤ (19761 / 125000000) := by
  have h := checkLog_sound (w := (1581 / 20001581)) (n := 12)
    (lo := (158087 / 1000000000)) (hi := (19761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001581 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001581 / 10000000) = 1/(10000000 / 10001581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1093 : Bounds (158087 / 1000000000) (19761 / 125000000) (Real.log (10001581 / 10000000)) := by
  have h := reflection_log_1093_neg
  have he : Real.log (10001581 / 10000000) = -Real.log (10000000 / 10001581) := by
    rw [show ((10001581 / 10000000) : ℝ) = ((10000000 / 10001581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1094_neg : (4941 / 31250000) ≤ -Real.log (9998419 / 10000000) ∧
    -Real.log (9998419 / 10000000) ≤ (158113 / 1000000000) := by
  have h := checkLog_sound (w := (1581 / 19998419)) (n := 12)
    (lo := (4941 / 31250000)) (hi := (158113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998419) = 1/(9998419 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1094 : Bounds (-158113 / 1000000000) (-4941 / 31250000) (Real.log (9998419 / 10000000)) := by
  have h := reflection_log_1094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1095_neg : (3051729 / 40000000) ≤ -Real.log (1000000 / 1079279) ∧
    -Real.log (1000000 / 1079279) ≤ (38146613 / 500000000) := by
  have h := checkLog_sound (w := (79279 / 2079279)) (n := 12)
    (lo := (3051729 / 40000000)) (hi := (38146613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079279 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079279 / 1000000) = 1/(1000000 / 1079279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1095 : Bounds (3051729 / 40000000) (38146613 / 500000000) (Real.log (1079279 / 1000000)) := by
  have h := reflection_log_1095_neg
  have he : Real.log (1079279 / 1000000) = -Real.log (1000000 / 1079279) := by
    rw [show ((1079279 / 1000000) : ℝ) = ((1000000 / 1079279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1096_neg : (4129911 / 50000000) ≤ -Real.log (920721 / 1000000) ∧
    -Real.log (920721 / 1000000) ≤ (82598221 / 1000000000) := by
  have h := checkLog_sound (w := (79279 / 1920721)) (n := 12)
    (lo := (4129911 / 50000000)) (hi := (82598221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920721) = 1/(920721 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1096 : Bounds (-82598221 / 1000000000) (-4129911 / 50000000) (Real.log (920721 / 1000000)) := by
  have h := reflection_log_1096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1097_neg : (38243427 / 500000000) ≤ -Real.log (15625 / 16867) ∧
    -Real.log (15625 / 16867) ≤ (15297371 / 200000000) := by
  have h := checkLog_sound (w := (621 / 16246)) (n := 12)
    (lo := (38243427 / 500000000)) (hi := (15297371 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16867 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16867 / 15625) = 1/(15625 / 16867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1097 : Bounds (38243427 / 500000000) (15297371 / 200000000) (Real.log (16867 / 15625)) := by
  have h := reflection_log_1097_neg
  have he : Real.log (16867 / 15625) = -Real.log (15625 / 16867) := by
    rw [show ((16867 / 15625) : ℝ) = ((15625 / 16867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1098_neg : (41412621 / 500000000) ≤ -Real.log (14383 / 15625) ∧
    -Real.log (14383 / 15625) ≤ (82825243 / 1000000000) := by
  have h := checkLog_sound (w := (621 / 15004)) (n := 12)
    (lo := (41412621 / 500000000)) (hi := (82825243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14383) = 1/(14383 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1098 : Bounds (-82825243 / 1000000000) (-41412621 / 500000000) (Real.log (14383 / 15625)) := by
  have h := reflection_log_1098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1099_neg : (6338387 / 1000000000) ≤ -Real.log (242598061 / 244140625) ∧
    -Real.log (242598061 / 244140625) ≤ (1584597 / 250000000) := by
  have h := checkLog_sound (w := (771282 / 243369343)) (n := 12)
    (lo := (6338387 / 1000000000)) (hi := (1584597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242598061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242598061) = 1/(242598061 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1099 : Bounds (-1584597 / 250000000) (-6338387 / 1000000000) (Real.log (242598061 / 244140625)) := by
  have h := reflection_log_1099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1100_neg : (3152497 / 500000000) ≤ -Real.log (993714840159 / 1000000000000) ∧
    -Real.log (993714840159 / 1000000000000) ≤ (1260999 / 200000000) := by
  have h := checkLog_sound (w := (6285159841 / 1993714840159)) (n := 12)
    (lo := (3152497 / 500000000)) (hi := (1260999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993714840159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993714840159) = 1/(993714840159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1100 : Bounds (-1260999 / 200000000) (-3152497 / 500000000) (Real.log (993714840159 / 1000000000000)) := by
  have h := reflection_log_1100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1101_neg : (31778289 / 200000000) ≤ -Real.log (500000000000 / 586105345701) ∧
    -Real.log (500000000000 / 586105345701) ≤ (79445723 / 500000000) := by
  have h := checkLog_sound (w := (86105345701 / 1086105345701)) (n := 12)
    (lo := (31778289 / 200000000)) (hi := (79445723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586105345701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586105345701 / 500000000000) = 1/(500000000000 / 586105345701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1101 : Bounds (31778289 / 200000000) (79445723 / 500000000) (Real.log (586105345701 / 500000000000)) := by
  have h := reflection_log_1101_neg
  have he : Real.log (586105345701 / 500000000000) = -Real.log (500000000000 / 586105345701) := by
    rw [show ((586105345701 / 500000000000) : ℝ) = ((500000000000 / 586105345701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1102_neg : (4978503 / 31250000) ≤ -Real.log (500000000000 / 586351943267) ∧
    -Real.log (500000000000 / 586351943267) ≤ (159312097 / 1000000000) := by
  have h := checkLog_sound (w := (86351943267 / 1086351943267)) (n := 12)
    (lo := (4978503 / 31250000)) (hi := (159312097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586351943267 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586351943267 / 500000000000) = 1/(500000000000 / 586351943267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1102 : Bounds (4978503 / 31250000) (159312097 / 1000000000) (Real.log (586351943267 / 500000000000)) := by
  have h := reflection_log_1102_neg
  have he : Real.log (586351943267 / 500000000000) = -Real.log (500000000000 / 586351943267) := by
    rw [show ((586351943267 / 500000000000) : ℝ) = ((500000000000 / 586351943267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1103_neg : (318669643 / 1000000000) ≤ -Real.log (500000000000 / 687648456057) ∧
    -Real.log (500000000000 / 687648456057) ≤ (79667411 / 250000000) := by
  have h := checkLog_sound (w := (187648456057 / 1187648456057)) (n := 12)
    (lo := (318669643 / 1000000000)) (hi := (79667411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687648456057 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687648456057 / 500000000000) = 1/(500000000000 / 687648456057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1103 : Bounds (318669643 / 1000000000) (79667411 / 250000000) (Real.log (687648456057 / 500000000000)) := by
  have h := reflection_log_1103_neg
  have he : Real.log (687648456057 / 500000000000) = -Real.log (500000000000 / 687648456057) := by
    rw [show ((687648456057 / 500000000000) : ℝ) = ((500000000000 / 687648456057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1104_neg : (318874767 / 1000000000) ≤ -Real.log (500000000000 / 687789523697) ∧
    -Real.log (500000000000 / 687789523697) ≤ (19929673 / 62500000) := by
  have h := checkLog_sound (w := (187789523697 / 1187789523697)) (n := 12)
    (lo := (318874767 / 1000000000)) (hi := (19929673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687789523697 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687789523697 / 500000000000) = 1/(500000000000 / 687789523697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1104 : Bounds (318874767 / 1000000000) (19929673 / 62500000) (Real.log (687789523697 / 500000000000)) := by
  have h := reflection_log_1104_neg
  have he : Real.log (687789523697 / 500000000000) = -Real.log (500000000000 / 687789523697) := by
    rw [show ((687789523697 / 500000000000) : ℝ) = ((500000000000 / 687789523697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1105_neg : (5874683 / 40000000) ≤ -Real.log (5000 / 5791) ∧
    -Real.log (5000 / 5791) ≤ (36716769 / 250000000) := by
  have h := checkLog_sound (w := (791 / 10791)) (n := 12)
    (lo := (5874683 / 40000000)) (hi := (36716769 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5791 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5791 / 5000) = 1/(5000 / 5791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1105 : Bounds (5874683 / 40000000) (36716769 / 250000000) (Real.log (5791 / 5000)) := by
  have h := reflection_log_1105_neg
  have he : Real.log (5791 / 5000) = -Real.log (5000 / 5791) := by
    rw [show ((5791 / 5000) : ℝ) = ((5000 / 5791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1106_neg : (86106411 / 500000000) ≤ -Real.log (4209 / 5000) ∧
    -Real.log (4209 / 5000) ≤ (172212823 / 1000000000) := by
  have h := checkLog_sound (w := (791 / 9209)) (n := 12)
    (lo := (86106411 / 500000000)) (hi := (172212823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4209) = 1/(4209 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1106 : Bounds (-172212823 / 1000000000) (-86106411 / 500000000) (Real.log (4209 / 5000)) := by
  have h := reflection_log_1106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1107_neg : (158187 / 1000000000) ≤ -Real.log (5000000 / 5000791) ∧
    -Real.log (5000000 / 5000791) ≤ (39547 / 250000000) := by
  have h := checkLog_sound (w := (791 / 10000791)) (n := 12)
    (lo := (158187 / 1000000000)) (hi := (39547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000791 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000791 / 5000000) = 1/(5000000 / 5000791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1107 : Bounds (158187 / 1000000000) (39547 / 250000000) (Real.log (5000791 / 5000000)) := by
  have h := reflection_log_1107_neg
  have he : Real.log (5000791 / 5000000) = -Real.log (5000000 / 5000791) := by
    rw [show ((5000791 / 5000000) : ℝ) = ((5000000 / 5000791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1108_neg : (39553 / 250000000) ≤ -Real.log (4999209 / 5000000) ∧
    -Real.log (4999209 / 5000000) ≤ (158213 / 1000000000) := by
  have h := checkLog_sound (w := (791 / 9999209)) (n := 12)
    (lo := (39553 / 250000000)) (hi := (158213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999209) = 1/(4999209 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1108 : Bounds (-158213 / 1000000000) (-39553 / 250000000) (Real.log (4999209 / 5000000)) := by
  have h := reflection_log_1108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1109_neg : (38170239 / 500000000) ≤ -Real.log (100000 / 107933) ∧
    -Real.log (100000 / 107933) ≤ (76340479 / 1000000000) := by
  have h := checkLog_sound (w := (7933 / 207933)) (n := 12)
    (lo := (38170239 / 500000000)) (hi := (76340479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107933 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107933 / 100000) = 1/(100000 / 107933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1109 : Bounds (38170239 / 500000000) (76340479 / 1000000000) (Real.log (107933 / 100000)) := by
  have h := reflection_log_1109_neg
  have he : Real.log (107933 / 100000) = -Real.log (100000 / 107933) := by
    rw [show ((107933 / 100000) : ℝ) = ((100000 / 107933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1110_neg : (82653613 / 1000000000) ≤ -Real.log (92067 / 100000) ∧
    -Real.log (92067 / 100000) ≤ (41326807 / 500000000) := by
  have h := checkLog_sound (w := (7933 / 192067)) (n := 12)
    (lo := (82653613 / 1000000000)) (hi := (41326807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92067) = 1/(92067 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1110 : Bounds (-41326807 / 500000000) (-82653613 / 1000000000) (Real.log (92067 / 100000)) := by
  have h := reflection_log_1110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1111_neg : (38267049 / 500000000) ≤ -Real.log (1000000 / 1079539) ∧
    -Real.log (1000000 / 1079539) ≤ (76534099 / 1000000000) := by
  have h := checkLog_sound (w := (79539 / 2079539)) (n := 12)
    (lo := (38267049 / 500000000)) (hi := (76534099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079539 / 1000000) = 1/(1000000 / 1079539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1111 : Bounds (38267049 / 500000000) (76534099 / 1000000000) (Real.log (1079539 / 1000000)) := by
  have h := reflection_log_1111_neg
  have he : Real.log (1079539 / 1000000) = -Real.log (1000000 / 1079539) := by
    rw [show ((1079539 / 1000000) : ℝ) = ((1000000 / 1079539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1112_neg : (82880647 / 1000000000) ≤ -Real.log (920461 / 1000000) ∧
    -Real.log (920461 / 1000000) ≤ (10360081 / 125000000) := by
  have h := checkLog_sound (w := (79539 / 1920461)) (n := 12)
    (lo := (82880647 / 1000000000)) (hi := (10360081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920461) = 1/(920461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1112 : Bounds (-10360081 / 125000000) (-82880647 / 1000000000) (Real.log (920461 / 1000000)) := by
  have h := reflection_log_1112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1113_neg : (6346549 / 1000000000) ≤ -Real.log (993673547479 / 1000000000000) ∧
    -Real.log (993673547479 / 1000000000000) ≤ (126931 / 20000000) := by
  have h := checkLog_sound (w := (6326452521 / 1993673547479)) (n := 12)
    (lo := (6346549 / 1000000000)) (hi := (126931 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993673547479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993673547479) = 1/(993673547479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1113 : Bounds (-126931 / 20000000) (-6346549 / 1000000000) (Real.log (993673547479 / 1000000000000)) := by
  have h := reflection_log_1113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1114_neg : (3156567 / 500000000) ≤ -Real.log (9937067511 / 10000000000) ∧
    -Real.log (9937067511 / 10000000000) ≤ (1262627 / 200000000) := by
  have h := checkLog_sound (w := (62932489 / 19937067511)) (n := 12)
    (lo := (3156567 / 500000000)) (hi := (1262627 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9937067511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9937067511) = 1/(9937067511 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1114 : Bounds (-1262627 / 200000000) (-3156567 / 500000000) (Real.log (9937067511 / 10000000000)) := by
  have h := reflection_log_1114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1115_neg : (158994091 / 1000000000) ≤ -Real.log (5000000000 / 5861655099) ∧
    -Real.log (5000000000 / 5861655099) ≤ (39748523 / 250000000) := by
  have h := checkLog_sound (w := (861655099 / 10861655099)) (n := 12)
    (lo := (158994091 / 1000000000)) (hi := (39748523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5861655099 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5861655099 / 5000000000) = 1/(5000000000 / 5861655099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1115 : Bounds (158994091 / 1000000000) (39748523 / 250000000) (Real.log (5861655099 / 5000000000)) := by
  have h := reflection_log_1115_neg
  have he : Real.log (5861655099 / 5000000000) = -Real.log (5000000000 / 5861655099) := by
    rw [show ((5861655099 / 5000000000) : ℝ) = ((5000000000 / 5861655099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1116_neg : (31882949 / 200000000) ≤ -Real.log (500000000000 / 586412134789) ∧
    -Real.log (500000000000 / 586412134789) ≤ (79707373 / 500000000) := by
  have h := checkLog_sound (w := (86412134789 / 1086412134789)) (n := 12)
    (lo := (31882949 / 200000000)) (hi := (79707373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586412134789 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586412134789 / 500000000000) = 1/(500000000000 / 586412134789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1116 : Bounds (31882949 / 200000000) (79707373 / 500000000) (Real.log (586412134789 / 500000000000)) := by
  have h := reflection_log_1116_neg
  have he : Real.log (586412134789 / 500000000000) = -Real.log (500000000000 / 586412134789) := by
    rw [show ((586412134789 / 500000000000) : ℝ) = ((500000000000 / 586412134789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1117_neg : (318874767 / 1000000000) ≤ -Real.log (31250000000 / 42986845231) ∧
    -Real.log (31250000000 / 42986845231) ≤ (19929673 / 62500000) := by
  have h := checkLog_sound (w := (11736845231 / 74236845231)) (n := 12)
    (lo := (318874767 / 1000000000)) (hi := (19929673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42986845231 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42986845231 / 31250000000) = 1/(31250000000 / 42986845231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1117 : Bounds (318874767 / 1000000000) (19929673 / 62500000) (Real.log (42986845231 / 31250000000)) := by
  have h := reflection_log_1117_neg
  have he : Real.log (42986845231 / 31250000000) = -Real.log (31250000000 / 42986845231) := by
    rw [show ((42986845231 / 31250000000) : ℝ) = ((31250000000 / 42986845231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1118_neg : (159539949 / 500000000) ≤ -Real.log (125000000000 / 171982656213) ∧
    -Real.log (125000000000 / 171982656213) ≤ (319079899 / 1000000000) := by
  have h := checkLog_sound (w := (46982656213 / 296982656213)) (n := 12)
    (lo := (159539949 / 500000000)) (hi := (319079899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171982656213 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171982656213 / 125000000000) = 1/(125000000000 / 171982656213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1118 : Bounds (159539949 / 500000000) (319079899 / 1000000000) (Real.log (171982656213 / 125000000000)) := by
  have h := reflection_log_1118_neg
  have he : Real.log (171982656213 / 125000000000) = -Real.log (125000000000 / 171982656213) := by
    rw [show ((171982656213 / 125000000000) : ℝ) = ((125000000000 / 171982656213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1119_neg : (36738353 / 250000000) ≤ -Real.log (10000 / 11583) ∧
    -Real.log (10000 / 11583) ≤ (146953413 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 21583)) (n := 12)
    (lo := (36738353 / 250000000)) (hi := (146953413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11583 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11583 / 10000) = 1/(10000 / 11583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1119 : Bounds (36738353 / 250000000) (146953413 / 1000000000) (Real.log (11583 / 10000)) := by
  have h := reflection_log_1119_neg
  have he : Real.log (11583 / 10000) = -Real.log (10000 / 11583) := by
    rw [show ((11583 / 10000) : ℝ) = ((10000 / 11583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1120_neg : (86165811 / 500000000) ≤ -Real.log (8417 / 10000) ∧
    -Real.log (8417 / 10000) ≤ (172331623 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 18417)) (n := 12)
    (lo := (86165811 / 500000000)) (hi := (172331623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8417) = 1/(8417 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1120 : Bounds (-172331623 / 1000000000) (-86165811 / 500000000) (Real.log (8417 / 10000)) := by
  have h := reflection_log_1120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1121_neg : (158287 / 1000000000) ≤ -Real.log (10000000 / 10001583) ∧
    -Real.log (10000000 / 10001583) ≤ (9893 / 62500000) := by
  have h := checkLog_sound (w := (1583 / 20001583)) (n := 12)
    (lo := (158287 / 1000000000)) (hi := (9893 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001583 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001583 / 10000000) = 1/(10000000 / 10001583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1121 : Bounds (158287 / 1000000000) (9893 / 62500000) (Real.log (10001583 / 10000000)) := by
  have h := reflection_log_1121_neg
  have he : Real.log (10001583 / 10000000) = -Real.log (10000000 / 10001583) := by
    rw [show ((10001583 / 10000000) : ℝ) = ((10000000 / 10001583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1122_neg : (19789 / 125000000) ≤ -Real.log (9998417 / 10000000) ∧
    -Real.log (9998417 / 10000000) ≤ (158313 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 19998417)) (n := 12)
    (lo := (19789 / 125000000)) (hi := (158313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998417) = 1/(9998417 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1122 : Bounds (-158313 / 1000000000) (-19789 / 125000000) (Real.log (9998417 / 10000000)) := by
  have h := reflection_log_1122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1123_neg : (38193401 / 500000000) ≤ -Real.log (50000 / 53969) ∧
    -Real.log (50000 / 53969) ≤ (76386803 / 1000000000) := by
  have h := checkLog_sound (w := (3969 / 103969)) (n := 12)
    (lo := (38193401 / 500000000)) (hi := (76386803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53969 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53969 / 50000) = 1/(50000 / 53969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1123 : Bounds (38193401 / 500000000) (76386803 / 1000000000) (Real.log (53969 / 50000)) := by
  have h := reflection_log_1123_neg
  have he : Real.log (53969 / 50000) = -Real.log (50000 / 53969) := by
    rw [show ((53969 / 50000) : ℝ) = ((50000 / 53969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1124_neg : (41353961 / 500000000) ≤ -Real.log (46031 / 50000) ∧
    -Real.log (46031 / 50000) ≤ (82707923 / 1000000000) := by
  have h := checkLog_sound (w := (3969 / 96031)) (n := 12)
    (lo := (41353961 / 500000000)) (hi := (82707923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 46031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 46031) = 1/(46031 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1124 : Bounds (-82707923 / 1000000000) (-41353961 / 500000000) (Real.log (46031 / 50000)) := by
  have h := reflection_log_1124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1125_neg : (76581339 / 1000000000) ≤ -Real.log (100000 / 107959) ∧
    -Real.log (100000 / 107959) ≤ (3829067 / 50000000) := by
  have h := checkLog_sound (w := (7959 / 207959)) (n := 12)
    (lo := (76581339 / 1000000000)) (hi := (3829067 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107959 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107959 / 100000) = 1/(100000 / 107959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1125 : Bounds (76581339 / 1000000000) (3829067 / 50000000) (Real.log (107959 / 100000)) := by
  have h := reflection_log_1125_neg
  have he : Real.log (107959 / 100000) = -Real.log (100000 / 107959) := by
    rw [show ((107959 / 100000) : ℝ) = ((100000 / 107959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1126_neg : (10367007 / 125000000) ≤ -Real.log (92041 / 100000) ∧
    -Real.log (92041 / 100000) ≤ (82936057 / 1000000000) := by
  have h := checkLog_sound (w := (7959 / 192041)) (n := 12)
    (lo := (10367007 / 125000000)) (hi := (82936057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92041) = 1/(92041 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1126 : Bounds (-82936057 / 1000000000) (-10367007 / 125000000) (Real.log (92041 / 100000)) := by
  have h := reflection_log_1126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1127_neg : (1588679 / 250000000) ≤ -Real.log (9936654319 / 10000000000) ∧
    -Real.log (9936654319 / 10000000000) ≤ (6354717 / 1000000000) := by
  have h := checkLog_sound (w := (63345681 / 19936654319)) (n := 12)
    (lo := (1588679 / 250000000)) (hi := (6354717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9936654319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9936654319) = 1/(9936654319 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1127 : Bounds (-6354717 / 1000000000) (-1588679 / 250000000) (Real.log (9936654319 / 10000000000)) := by
  have h := reflection_log_1127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1128_neg : (39507 / 6250000) ≤ -Real.log (2484247039 / 2500000000) ∧
    -Real.log (2484247039 / 2500000000) ≤ (6321121 / 1000000000) := by
  have h := checkLog_sound (w := (15752961 / 4984247039)) (n := 12)
    (lo := (39507 / 6250000)) (hi := (6321121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2484247039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2484247039) = 1/(2484247039 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1128 : Bounds (-6321121 / 1000000000) (-39507 / 6250000) (Real.log (2484247039 / 2500000000)) := by
  have h := reflection_log_1128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1129_neg : (6363789 / 40000000) ≤ -Real.log (500000000000 / 586224500879) ∧
    -Real.log (500000000000 / 586224500879) ≤ (79547363 / 500000000) := by
  have h := checkLog_sound (w := (86224500879 / 1086224500879)) (n := 12)
    (lo := (6363789 / 40000000)) (hi := (79547363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586224500879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586224500879 / 500000000000) = 1/(500000000000 / 586224500879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1129 : Bounds (6363789 / 40000000) (79547363 / 500000000) (Real.log (586224500879 / 500000000000)) := by
  have h := reflection_log_1129_neg
  have he : Real.log (586224500879 / 500000000000) = -Real.log (500000000000 / 586224500879) := by
    rw [show ((586224500879 / 500000000000) : ℝ) = ((500000000000 / 586224500879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1130_neg : (31903479 / 200000000) ≤ -Real.log (500000000000 / 586472332983) ∧
    -Real.log (500000000000 / 586472332983) ≤ (39879349 / 250000000) := by
  have h := checkLog_sound (w := (86472332983 / 1086472332983)) (n := 12)
    (lo := (31903479 / 200000000)) (hi := (39879349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586472332983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586472332983 / 500000000000) = 1/(500000000000 / 586472332983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1130 : Bounds (31903479 / 200000000) (39879349 / 250000000) (Real.log (586472332983 / 500000000000)) := by
  have h := reflection_log_1130_neg
  have he : Real.log (586472332983 / 500000000000) = -Real.log (500000000000 / 586472332983) := by
    rw [show ((586472332983 / 500000000000) : ℝ) = ((500000000000 / 586472332983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1131_neg : (159539949 / 500000000) ≤ -Real.log (500000000000 / 687930624851) ∧
    -Real.log (500000000000 / 687930624851) ≤ (319079899 / 1000000000) := by
  have h := checkLog_sound (w := (187930624851 / 1187930624851)) (n := 12)
    (lo := (159539949 / 500000000)) (hi := (319079899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687930624851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687930624851 / 500000000000) = 1/(500000000000 / 687930624851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1131 : Bounds (159539949 / 500000000) (319079899 / 1000000000) (Real.log (687930624851 / 500000000000)) := by
  have h := reflection_log_1131_neg
  have he : Real.log (687930624851 / 500000000000) = -Real.log (500000000000 / 687930624851) := by
    rw [show ((687930624851 / 500000000000) : ℝ) = ((500000000000 / 687930624851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1132_neg : (63857007 / 200000000) ≤ -Real.log (100000000000 / 137614351907) ∧
    -Real.log (100000000000 / 137614351907) ≤ (79821259 / 250000000) := by
  have h := checkLog_sound (w := (37614351907 / 237614351907)) (n := 12)
    (lo := (63857007 / 200000000)) (hi := (79821259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137614351907 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137614351907 / 100000000000) = 1/(100000000000 / 137614351907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1132 : Bounds (63857007 / 200000000) (79821259 / 250000000) (Real.log (137614351907 / 100000000000)) := by
  have h := reflection_log_1132_neg
  have he : Real.log (137614351907 / 100000000000) = -Real.log (100000000000 / 137614351907) := by
    rw [show ((137614351907 / 100000000000) : ℝ) = ((100000000000 / 137614351907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1133_neg : (73519871 / 500000000) ≤ -Real.log (625 / 724) ∧
    -Real.log (625 / 724) ≤ (147039743 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 1349)) (n := 12)
    (lo := (73519871 / 500000000)) (hi := (147039743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724 / 625) = 1/(625 / 724) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1133 : Bounds (73519871 / 500000000) (147039743 / 1000000000) (Real.log (724 / 625)) := by
  have h := reflection_log_1133_neg
  have he : Real.log (724 / 625) = -Real.log (625 / 724) := by
    rw [show ((724 / 625) : ℝ) = ((625 / 724) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1134_neg : (43112609 / 250000000) ≤ -Real.log (526 / 625) ∧
    -Real.log (526 / 625) ≤ (172450437 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 1151)) (n := 12)
    (lo := (43112609 / 250000000)) (hi := (172450437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 526) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 526) = 1/(526 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1134 : Bounds (-172450437 / 1000000000) (-43112609 / 250000000) (Real.log (526 / 625)) := by
  have h := reflection_log_1134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1135_neg : (158387 / 1000000000) ≤ -Real.log (625000 / 625099) ∧
    -Real.log (625000 / 625099) ≤ (39597 / 250000000) := by
  have h := checkLog_sound (w := (99 / 1250099)) (n := 12)
    (lo := (158387 / 1000000000)) (hi := (39597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625099 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625099 / 625000) = 1/(625000 / 625099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1135 : Bounds (158387 / 1000000000) (39597 / 250000000) (Real.log (625099 / 625000)) := by
  have h := reflection_log_1135_neg
  have he : Real.log (625099 / 625000) = -Real.log (625000 / 625099) := by
    rw [show ((625099 / 625000) : ℝ) = ((625000 / 625099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1136_neg : (39603 / 250000000) ≤ -Real.log (624901 / 625000) ∧
    -Real.log (624901 / 625000) ≤ (158413 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 1249901)) (n := 12)
    (lo := (39603 / 250000000)) (hi := (158413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624901) = 1/(624901 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1136 : Bounds (-158413 / 1000000000) (-39603 / 250000000) (Real.log (624901 / 625000)) := by
  have h := reflection_log_1136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1137_neg : (1528681 / 20000000) ≤ -Real.log (1000000 / 1079431) ∧
    -Real.log (1000000 / 1079431) ≤ (76434051 / 1000000000) := by
  have h := checkLog_sound (w := (79431 / 2079431)) (n := 12)
    (lo := (1528681 / 20000000)) (hi := (76434051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079431 / 1000000) = 1/(1000000 / 1079431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1137 : Bounds (1528681 / 20000000) (76434051 / 1000000000) (Real.log (1079431 / 1000000)) := by
  have h := reflection_log_1137_neg
  have he : Real.log (1079431 / 1000000) = -Real.log (1000000 / 1079431) := by
    rw [show ((1079431 / 1000000) : ℝ) = ((1000000 / 1079431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1138_neg : (82763321 / 1000000000) ≤ -Real.log (920569 / 1000000) ∧
    -Real.log (920569 / 1000000) ≤ (41381661 / 500000000) := by
  have h := checkLog_sound (w := (79431 / 1920569)) (n := 12)
    (lo := (82763321 / 1000000000)) (hi := (41381661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920569) = 1/(920569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1138 : Bounds (-41381661 / 500000000) (-82763321 / 1000000000) (Real.log (920569 / 1000000)) := by
  have h := reflection_log_1138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1139_neg : (19156913 / 250000000) ≤ -Real.log (25000 / 26991) ∧
    -Real.log (25000 / 26991) ≤ (76627653 / 1000000000) := by
  have h := checkLog_sound (w := (1991 / 51991)) (n := 12)
    (lo := (19156913 / 250000000)) (hi := (76627653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26991 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26991 / 25000) = 1/(25000 / 26991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1139 : Bounds (19156913 / 250000000) (76627653 / 1000000000) (Real.log (26991 / 25000)) := by
  have h := reflection_log_1139_neg
  have he : Real.log (26991 / 25000) = -Real.log (25000 / 26991) := by
    rw [show ((26991 / 25000) : ℝ) = ((25000 / 26991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1140_neg : (82990381 / 1000000000) ≤ -Real.log (23009 / 25000) ∧
    -Real.log (23009 / 25000) ≤ (41495191 / 500000000) := by
  have h := checkLog_sound (w := (1991 / 48009)) (n := 12)
    (lo := (82990381 / 1000000000)) (hi := (41495191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 23009) = 1/(23009 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1140 : Bounds (-41495191 / 500000000) (-82990381 / 1000000000) (Real.log (23009 / 25000)) := by
  have h := reflection_log_1140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1141_neg : (795341 / 125000000) ≤ -Real.log (621035919 / 625000000) ∧
    -Real.log (621035919 / 625000000) ≤ (6362729 / 1000000000) := by
  have h := checkLog_sound (w := (3964081 / 1246035919)) (n := 12)
    (lo := (795341 / 125000000)) (hi := (6362729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 621035919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 621035919) = 1/(621035919 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1141 : Bounds (-6362729 / 1000000000) (-795341 / 125000000) (Real.log (621035919 / 625000000)) := by
  have h := reflection_log_1141_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1142_neg : (6329271 / 1000000000) ≤ -Real.log (993690716239 / 1000000000000) ∧
    -Real.log (993690716239 / 1000000000000) ≤ (791159 / 125000000) := by
  have h := checkLog_sound (w := (6309283761 / 1993690716239)) (n := 12)
    (lo := (6329271 / 1000000000)) (hi := (791159 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993690716239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993690716239) = 1/(993690716239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1142 : Bounds (-791159 / 125000000) (-6329271 / 1000000000) (Real.log (993690716239 / 1000000000000)) := by
  have h := reflection_log_1142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1143_neg : (39799343 / 250000000) ≤ -Real.log (12500000000 / 14657116957) ∧
    -Real.log (12500000000 / 14657116957) ≤ (159197373 / 1000000000) := by
  have h := checkLog_sound (w := (2157116957 / 27157116957)) (n := 12)
    (lo := (39799343 / 250000000)) (hi := (159197373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14657116957 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14657116957 / 12500000000) = 1/(12500000000 / 14657116957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1143 : Bounds (39799343 / 250000000) (159197373 / 1000000000) (Real.log (14657116957 / 12500000000)) := by
  have h := reflection_log_1143_neg
  have he : Real.log (14657116957 / 12500000000) = -Real.log (12500000000 / 14657116957) := by
    rw [show ((14657116957 / 12500000000) : ℝ) = ((12500000000 / 14657116957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1144_neg : (159618033 / 1000000000) ≤ -Real.log (100000000000 / 117306271459) ∧
    -Real.log (100000000000 / 117306271459) ≤ (79809017 / 500000000) := by
  have h := checkLog_sound (w := (17306271459 / 217306271459)) (n := 12)
    (lo := (159618033 / 1000000000)) (hi := (79809017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117306271459 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117306271459 / 100000000000) = 1/(100000000000 / 117306271459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1144 : Bounds (159618033 / 1000000000) (79809017 / 500000000) (Real.log (117306271459 / 100000000000)) := by
  have h := reflection_log_1144_neg
  have he : Real.log (117306271459 / 100000000000) = -Real.log (100000000000 / 117306271459) := by
    rw [show ((117306271459 / 100000000000) : ℝ) = ((100000000000 / 117306271459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1145_neg : (63857007 / 200000000) ≤ -Real.log (250000000000 / 344035879767) ∧
    -Real.log (250000000000 / 344035879767) ≤ (79821259 / 250000000) := by
  have h := checkLog_sound (w := (94035879767 / 594035879767)) (n := 12)
    (lo := (63857007 / 200000000)) (hi := (79821259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344035879767 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344035879767 / 250000000000) = 1/(250000000000 / 344035879767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1145 : Bounds (63857007 / 200000000) (79821259 / 250000000) (Real.log (344035879767 / 250000000000)) := by
  have h := reflection_log_1145_neg
  have he : Real.log (344035879767 / 250000000000) = -Real.log (250000000000 / 344035879767) := by
    rw [show ((344035879767 / 250000000000) : ℝ) = ((250000000000 / 344035879767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1146_neg : (319490179 / 1000000000) ≤ -Real.log (500000000000 / 688212927757) ∧
    -Real.log (500000000000 / 688212927757) ≤ (15974509 / 50000000) := by
  have h := checkLog_sound (w := (188212927757 / 1188212927757)) (n := 12)
    (lo := (319490179 / 1000000000)) (hi := (15974509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688212927757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688212927757 / 500000000000) = 1/(500000000000 / 688212927757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1146 : Bounds (319490179 / 1000000000) (15974509 / 50000000) (Real.log (688212927757 / 500000000000)) := by
  have h := reflection_log_1146_neg
  have he : Real.log (688212927757 / 500000000000) = -Real.log (500000000000 / 688212927757) := by
    rw [show ((688212927757 / 500000000000) : ℝ) = ((500000000000 / 688212927757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1147_neg : (9195379 / 62500000) ≤ -Real.log (2000 / 2317) ∧
    -Real.log (2000 / 2317) ≤ (29425213 / 200000000) := by
  have h := checkLog_sound (w := (317 / 4317)) (n := 12)
    (lo := (9195379 / 62500000)) (hi := (29425213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2317 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2317 / 2000) = 1/(2000 / 2317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1147 : Bounds (9195379 / 62500000) (29425213 / 200000000) (Real.log (2317 / 2000)) := by
  have h := reflection_log_1147_neg
  have he : Real.log (2317 / 2000) = -Real.log (2000 / 2317) := by
    rw [show ((2317 / 2000) : ℝ) = ((2000 / 2317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1148_neg : (34513853 / 200000000) ≤ -Real.log (1683 / 2000) ∧
    -Real.log (1683 / 2000) ≤ (86284633 / 500000000) := by
  have h := checkLog_sound (w := (317 / 3683)) (n := 12)
    (lo := (34513853 / 200000000)) (hi := (86284633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1683) = 1/(1683 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1148 : Bounds (-86284633 / 500000000) (-34513853 / 200000000) (Real.log (1683 / 2000)) := by
  have h := reflection_log_1148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1149_neg : (158487 / 1000000000) ≤ -Real.log (2000000 / 2000317) ∧
    -Real.log (2000000 / 2000317) ≤ (19811 / 125000000) := by
  have h := checkLog_sound (w := (317 / 4000317)) (n := 12)
    (lo := (158487 / 1000000000)) (hi := (19811 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000317 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000317 / 2000000) = 1/(2000000 / 2000317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1149 : Bounds (158487 / 1000000000) (19811 / 125000000) (Real.log (2000317 / 2000000)) := by
  have h := reflection_log_1149_neg
  have he : Real.log (2000317 / 2000000) = -Real.log (2000000 / 2000317) := by
    rw [show ((2000317 / 2000000) : ℝ) = ((2000000 / 2000317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1150_neg : (9907 / 62500000) ≤ -Real.log (1999683 / 2000000) ∧
    -Real.log (1999683 / 2000000) ≤ (158513 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 3999683)) (n := 12)
    (lo := (9907 / 62500000)) (hi := (158513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999683) = 1/(1999683 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1150 : Bounds (-158513 / 1000000000) (-9907 / 62500000) (Real.log (1999683 / 2000000)) := by
  have h := reflection_log_1150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1151_neg : (4780081 / 62500000) ≤ -Real.log (500000 / 539741) ∧
    -Real.log (500000 / 539741) ≤ (76481297 / 1000000000) := by
  have h := checkLog_sound (w := (39741 / 1039741)) (n := 12)
    (lo := (4780081 / 62500000)) (hi := (76481297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539741 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539741 / 500000) = 1/(500000 / 539741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1151 : Bounds (4780081 / 62500000) (76481297 / 1000000000) (Real.log (539741 / 500000)) := by
  have h := reflection_log_1151_neg
  have he : Real.log (539741 / 500000) = -Real.log (500000 / 539741) := by
    rw [show ((539741 / 500000) : ℝ) = ((500000 / 539741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


