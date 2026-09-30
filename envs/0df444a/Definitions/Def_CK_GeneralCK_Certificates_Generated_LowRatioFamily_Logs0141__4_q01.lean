-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:55:23.593074+00:00
-- url     : https://prove2.me/theorems/f18c145c-2483-414f-a7a6-f71edb31b16c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0141 (+3 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0142, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0143, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0144) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4_q00

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9088_neg : (17625387 / 62500000) ≤ -Real.log (125000000000 / 165723366251) ∧
    -Real.log (125000000000 / 165723366251) ≤ (282006193 / 1000000000) := by
  have h := checkLog_sound (w := (40723366251 / 290723366251)) (n := 12)
    (lo := (17625387 / 62500000)) (hi := (282006193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165723366251 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165723366251 / 125000000000) = 1/(125000000000 / 165723366251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9088 : Bounds (17625387 / 62500000) (282006193 / 1000000000) (Real.log (165723366251 / 125000000000)) := by
  have h := reflection_log_9088_neg
  have he : Real.log (165723366251 / 125000000000) = -Real.log (125000000000 / 165723366251) := by
    rw [show ((165723366251 / 125000000000) : ℝ) = ((125000000000 / 165723366251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9089_neg : (22624471 / 40000000) ≤ -Real.log (500000000000 / 880262249827) ∧
    -Real.log (500000000000 / 880262249827) ≤ (2209421 / 3906250) := by
  have h := checkLog_sound (w := (380262249827 / 1380262249827)) (n := 12)
    (lo := (22624471 / 40000000)) (hi := (2209421 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((880262249827 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(880262249827 / 500000000000) = 1/(500000000000 / 880262249827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9089 : Bounds (22624471 / 40000000) (2209421 / 3906250) (Real.log (880262249827 / 500000000000)) := by
  have h := reflection_log_9089_neg
  have he : Real.log (880262249827 / 500000000000) = -Real.log (500000000000 / 880262249827) := by
    rw [show ((880262249827 / 500000000000) : ℝ) = ((500000000000 / 880262249827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9090_neg : (566694071 / 1000000000) ≤ -Real.log (250000000000 / 440607734807) ∧
    -Real.log (250000000000 / 440607734807) ≤ (70836759 / 125000000) := by
  have h := checkLog_sound (w := (190607734807 / 690607734807)) (n := 12)
    (lo := (566694071 / 1000000000)) (hi := (70836759 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((440607734807 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(440607734807 / 250000000000) = 1/(250000000000 / 440607734807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9090 : Bounds (566694071 / 1000000000) (70836759 / 125000000) (Real.log (440607734807 / 250000000000)) := by
  have h := reflection_log_9090_neg
  have he : Real.log (440607734807 / 250000000000) = -Real.log (250000000000 / 440607734807) := by
    rw [show ((440607734807 / 250000000000) : ℝ) = ((250000000000 / 440607734807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9091_neg : (244121957 / 1000000000) ≤ -Real.log (2000 / 2553) ∧
    -Real.log (2000 / 2553) ≤ (122060979 / 500000000) := by
  have h := checkLog_sound (w := (553 / 4553)) (n := 12)
    (lo := (244121957 / 1000000000)) (hi := (122060979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2553 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2553 / 2000) = 1/(2000 / 2553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9091 : Bounds (244121957 / 1000000000) (122060979 / 500000000) (Real.log (2553 / 2000)) := by
  have h := reflection_log_9091_neg
  have he : Real.log (2553 / 2000) = -Real.log (2000 / 2553) := by
    rw [show ((2553 / 2000) : ℝ) = ((2000 / 2553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9092_neg : (80913683 / 250000000) ≤ -Real.log (1447 / 2000) ∧
    -Real.log (1447 / 2000) ≤ (323654733 / 1000000000) := by
  have h := checkLog_sound (w := (553 / 3447)) (n := 12)
    (lo := (80913683 / 250000000)) (hi := (323654733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1447) = 1/(1447 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9092 : Bounds (-323654733 / 1000000000) (-80913683 / 250000000) (Real.log (1447 / 2000)) := by
  have h := reflection_log_9092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9093_neg : (276461 / 1000000000) ≤ -Real.log (2000000 / 2000553) ∧
    -Real.log (2000000 / 2000553) ≤ (138231 / 500000000) := by
  have h := checkLog_sound (w := (553 / 4000553)) (n := 12)
    (lo := (276461 / 1000000000)) (hi := (138231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000553 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000553 / 2000000) = 1/(2000000 / 2000553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9093 : Bounds (276461 / 1000000000) (138231 / 500000000) (Real.log (2000553 / 2000000)) := by
  have h := reflection_log_9093_neg
  have he : Real.log (2000553 / 2000000) = -Real.log (2000000 / 2000553) := by
    rw [show ((2000553 / 2000000) : ℝ) = ((2000000 / 2000553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9094_neg : (138269 / 500000000) ≤ -Real.log (1999447 / 2000000) ∧
    -Real.log (1999447 / 2000000) ≤ (276539 / 1000000000) := by
  have h := checkLog_sound (w := (553 / 3999447)) (n := 12)
    (lo := (138269 / 500000000)) (hi := (276539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999447) = 1/(1999447 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9094 : Bounds (-276539 / 1000000000) (-138269 / 500000000) (Real.log (1999447 / 2000000)) := by
  have h := reflection_log_9094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9095_neg : (1635693 / 12500000) ≤ -Real.log (1000000 / 1139803) ∧
    -Real.log (1000000 / 1139803) ≤ (130855441 / 1000000000) := by
  have h := checkLog_sound (w := (139803 / 2139803)) (n := 12)
    (lo := (1635693 / 12500000)) (hi := (130855441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1139803 / 1000000) = 1/(1000000 / 1139803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9095 : Bounds (1635693 / 12500000) (130855441 / 1000000000) (Real.log (1139803 / 1000000)) := by
  have h := reflection_log_9095_neg
  have he : Real.log (1139803 / 1000000) = -Real.log (1000000 / 1139803) := by
    rw [show ((1139803 / 1000000) : ℝ) = ((1000000 / 1139803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9096_neg : (75296923 / 500000000) ≤ -Real.log (860197 / 1000000) ∧
    -Real.log (860197 / 1000000) ≤ (150593847 / 1000000000) := by
  have h := checkLog_sound (w := (139803 / 1860197)) (n := 12)
    (lo := (75296923 / 500000000)) (hi := (150593847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 860197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 860197) = 1/(860197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9096 : Bounds (-150593847 / 1000000000) (-75296923 / 500000000) (Real.log (860197 / 1000000)) := by
  have h := reflection_log_9096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9097_neg : (16415479 / 125000000) ≤ -Real.log (1000000 / 1140337) ∧
    -Real.log (1000000 / 1140337) ≤ (131323833 / 1000000000) := by
  have h := checkLog_sound (w := (140337 / 2140337)) (n := 12)
    (lo := (16415479 / 125000000)) (hi := (131323833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1140337 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1140337 / 1000000) = 1/(1000000 / 1140337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9097 : Bounds (16415479 / 125000000) (131323833 / 1000000000) (Real.log (1140337 / 1000000)) := by
  have h := reflection_log_9097_neg
  have he : Real.log (1140337 / 1000000) = -Real.log (1000000 / 1140337) := by
    rw [show ((1140337 / 1000000) : ℝ) = ((1000000 / 1140337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9098_neg : (75607413 / 500000000) ≤ -Real.log (859663 / 1000000) ∧
    -Real.log (859663 / 1000000) ≤ (151214827 / 1000000000) := by
  have h := checkLog_sound (w := (140337 / 1859663)) (n := 12)
    (lo := (75607413 / 500000000)) (hi := (151214827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 859663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 859663) = 1/(859663 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9098 : Bounds (-151214827 / 1000000000) (-75607413 / 500000000) (Real.log (859663 / 1000000)) := by
  have h := reflection_log_9098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9099_neg : (9945497 / 500000000) ≤ -Real.log (980305526431 / 1000000000000) ∧
    -Real.log (980305526431 / 1000000000000) ≤ (3978199 / 200000000) := by
  have h := checkLog_sound (w := (19694473569 / 1980305526431)) (n := 12)
    (lo := (9945497 / 500000000)) (hi := (3978199 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980305526431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980305526431) = 1/(980305526431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9099 : Bounds (-3978199 / 200000000) (-9945497 / 500000000) (Real.log (980305526431 / 1000000000000)) := by
  have h := reflection_log_9099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9100_neg : (3947681 / 200000000) ≤ -Real.log (980455121191 / 1000000000000) ∧
    -Real.log (980455121191 / 1000000000000) ≤ (9869203 / 500000000) := by
  have h := checkLog_sound (w := (19544878809 / 1980455121191)) (n := 12)
    (lo := (3947681 / 200000000)) (hi := (9869203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980455121191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980455121191) = 1/(980455121191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9100 : Bounds (-9869203 / 500000000) (-3947681 / 200000000) (Real.log (980455121191 / 1000000000000)) := by
  have h := reflection_log_9100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9101_neg : (140724643 / 500000000) ≤ -Real.log (6250000000 / 8281554981) ∧
    -Real.log (6250000000 / 8281554981) ≤ (281449287 / 1000000000) := by
  have h := checkLog_sound (w := (2031554981 / 14531554981)) (n := 12)
    (lo := (140724643 / 500000000)) (hi := (281449287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8281554981 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8281554981 / 6250000000) = 1/(6250000000 / 8281554981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9101 : Bounds (140724643 / 500000000) (281449287 / 1000000000) (Real.log (8281554981 / 6250000000)) := by
  have h := reflection_log_9101_neg
  have he : Real.log (8281554981 / 6250000000) = -Real.log (6250000000 / 8281554981) := by
    rw [show ((8281554981 / 6250000000) : ℝ) = ((6250000000 / 8281554981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9102_neg : (282538659 / 1000000000) ≤ -Real.log (7812500 / 10363227) ∧
    -Real.log (7812500 / 10363227) ≤ (14126933 / 50000000) := by
  have h := checkLog_sound (w := (2550727 / 18175727)) (n := 12)
    (lo := (282538659 / 1000000000)) (hi := (14126933 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10363227 / 7812500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10363227 / 7812500) = 1/(7812500 / 10363227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9102 : Bounds (282538659 / 1000000000) (14126933 / 50000000) (Real.log (10363227 / 7812500)) := by
  have h := reflection_log_9102_neg
  have he : Real.log (10363227 / 7812500) = -Real.log (7812500 / 10363227) := by
    rw [show ((10363227 / 7812500) : ℝ) = ((7812500 / 10363227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9103_neg : (566694071 / 1000000000) ≤ -Real.log (500000000000 / 881215469613) ∧
    -Real.log (500000000000 / 881215469613) ≤ (70836759 / 125000000) := by
  have h := checkLog_sound (w := (381215469613 / 1381215469613)) (n := 12)
    (lo := (566694071 / 1000000000)) (hi := (70836759 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881215469613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881215469613 / 500000000000) = 1/(500000000000 / 881215469613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9103 : Bounds (566694071 / 1000000000) (70836759 / 125000000) (Real.log (881215469613 / 500000000000)) := by
  have h := reflection_log_9103_neg
  have he : Real.log (881215469613 / 500000000000) = -Real.log (500000000000 / 881215469613) := by
    rw [show ((881215469613 / 500000000000) : ℝ) = ((500000000000 / 881215469613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9104_neg : (56777669 / 100000000) ≤ -Real.log (500000000000 / 882170006911) ∧
    -Real.log (500000000000 / 882170006911) ≤ (567776691 / 1000000000) := by
  have h := checkLog_sound (w := (382170006911 / 1382170006911)) (n := 12)
    (lo := (56777669 / 100000000)) (hi := (567776691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((882170006911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(882170006911 / 500000000000) = 1/(500000000000 / 882170006911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9104 : Bounds (56777669 / 100000000) (567776691 / 1000000000) (Real.log (882170006911 / 500000000000)) := by
  have h := reflection_log_9104_neg
  have he : Real.log (882170006911 / 500000000000) = -Real.log (500000000000 / 882170006911) := by
    rw [show ((882170006911 / 500000000000) : ℝ) = ((500000000000 / 882170006911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9105_neg : (244513577 / 1000000000) ≤ -Real.log (1000 / 1277) ∧
    -Real.log (1000 / 1277) ≤ (122256789 / 500000000) := by
  have h := checkLog_sound (w := (277 / 2277)) (n := 12)
    (lo := (244513577 / 1000000000)) (hi := (122256789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1277 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1277 / 1000) = 1/(1000 / 1277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9105 : Bounds (244513577 / 1000000000) (122256789 / 500000000) (Real.log (1277 / 1000)) := by
  have h := reflection_log_9105_neg
  have he : Real.log (1277 / 1000) = -Real.log (1000 / 1277) := by
    rw [show ((1277 / 1000) : ℝ) = ((1000 / 1277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9106_neg : (40543257 / 125000000) ≤ -Real.log (723 / 1000) ∧
    -Real.log (723 / 1000) ≤ (324346057 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1723)) (n := 12)
    (lo := (40543257 / 125000000)) (hi := (324346057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 723) = 1/(723 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9106 : Bounds (-324346057 / 1000000000) (-40543257 / 125000000) (Real.log (723 / 1000)) := by
  have h := reflection_log_9106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9107_neg : (276961 / 1000000000) ≤ -Real.log (1000000 / 1000277) ∧
    -Real.log (1000000 / 1000277) ≤ (138481 / 500000000) := by
  have h := checkLog_sound (w := (277 / 2000277)) (n := 12)
    (lo := (276961 / 1000000000)) (hi := (138481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000277 / 1000000) = 1/(1000000 / 1000277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9107 : Bounds (276961 / 1000000000) (138481 / 500000000) (Real.log (1000277 / 1000000)) := by
  have h := reflection_log_9107_neg
  have he : Real.log (1000277 / 1000000) = -Real.log (1000000 / 1000277) := by
    rw [show ((1000277 / 1000000) : ℝ) = ((1000000 / 1000277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9108_neg : (138519 / 500000000) ≤ -Real.log (999723 / 1000000) ∧
    -Real.log (999723 / 1000000) ≤ (277039 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1999723)) (n := 12)
    (lo := (138519 / 500000000)) (hi := (277039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999723) = 1/(999723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9108 : Bounds (-277039 / 1000000000) (-138519 / 500000000) (Real.log (999723 / 1000000)) := by
  have h := reflection_log_9108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9109_neg : (32770881 / 250000000) ≤ -Real.log (1000000 / 1140063) ∧
    -Real.log (1000000 / 1140063) ≤ (5243341 / 40000000) := by
  have h := checkLog_sound (w := (140063 / 2140063)) (n := 12)
    (lo := (32770881 / 250000000)) (hi := (5243341 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1140063 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1140063 / 1000000) = 1/(1000000 / 1140063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9109 : Bounds (32770881 / 250000000) (5243341 / 40000000) (Real.log (1140063 / 1000000)) := by
  have h := reflection_log_9109_neg
  have he : Real.log (1140063 / 1000000) = -Real.log (1000000 / 1140063) := by
    rw [show ((1140063 / 1000000) : ℝ) = ((1000000 / 1140063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9110_neg : (37724037 / 250000000) ≤ -Real.log (859937 / 1000000) ∧
    -Real.log (859937 / 1000000) ≤ (150896149 / 1000000000) := by
  have h := checkLog_sound (w := (140063 / 1859937)) (n := 12)
    (lo := (37724037 / 250000000)) (hi := (150896149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 859937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 859937) = 1/(859937 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9110 : Bounds (-150896149 / 1000000000) (-37724037 / 250000000) (Real.log (859937 / 1000000)) := by
  have h := reflection_log_9110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9111_neg : (65776343 / 500000000) ≤ -Real.log (500000 / 570299) ∧
    -Real.log (500000 / 570299) ≤ (131552687 / 1000000000) := by
  have h := checkLog_sound (w := (70299 / 1070299)) (n := 12)
    (lo := (65776343 / 500000000)) (hi := (131552687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570299 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(570299 / 500000) = 1/(500000 / 570299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9111 : Bounds (65776343 / 500000000) (131552687 / 1000000000) (Real.log (570299 / 500000)) := by
  have h := reflection_log_9111_neg
  have he : Real.log (570299 / 500000) = -Real.log (500000 / 570299) := by
    rw [show ((570299 / 500000) : ℝ) = ((500000 / 570299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9112_neg : (1893981 / 12500000) ≤ -Real.log (429701 / 500000) ∧
    -Real.log (429701 / 500000) ≤ (151518481 / 1000000000) := by
  have h := checkLog_sound (w := (70299 / 929701)) (n := 12)
    (lo := (1893981 / 12500000)) (hi := (151518481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 429701) = 1/(429701 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9112 : Bounds (-151518481 / 1000000000) (-1893981 / 12500000) (Real.log (429701 / 500000)) := by
  have h := reflection_log_9112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9113_neg : (9982897 / 500000000) ≤ -Real.log (245058050599 / 250000000000) ∧
    -Real.log (245058050599 / 250000000000) ≤ (3993159 / 200000000) := by
  have h := checkLog_sound (w := (4941949401 / 495058050599)) (n := 12)
    (lo := (9982897 / 500000000)) (hi := (3993159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245058050599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245058050599) = 1/(245058050599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9113 : Bounds (-3993159 / 200000000) (-9982897 / 500000000) (Real.log (245058050599 / 250000000000)) := by
  have h := reflection_log_9113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9114_neg : (1238289 / 62500000) ≤ -Real.log (980382356031 / 1000000000000) ∧
    -Real.log (980382356031 / 1000000000000) ≤ (158501 / 8000000) := by
  have h := checkLog_sound (w := (19617643969 / 1980382356031)) (n := 12)
    (lo := (1238289 / 62500000)) (hi := (158501 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980382356031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980382356031) = 1/(980382356031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9114 : Bounds (-158501 / 8000000) (-1238289 / 62500000) (Real.log (980382356031 / 1000000000000)) := by
  have h := reflection_log_9114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9115_neg : (35247459 / 125000000) ≤ -Real.log (500000000000 / 662875885093) ∧
    -Real.log (500000000000 / 662875885093) ≤ (281979673 / 1000000000) := by
  have h := checkLog_sound (w := (162875885093 / 1162875885093)) (n := 12)
    (lo := (35247459 / 125000000)) (hi := (281979673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((662875885093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(662875885093 / 500000000000) = 1/(500000000000 / 662875885093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9115 : Bounds (35247459 / 125000000) (281979673 / 1000000000) (Real.log (662875885093 / 500000000000)) := by
  have h := reflection_log_9115_neg
  have he : Real.log (662875885093 / 500000000000) = -Real.log (500000000000 / 662875885093) := by
    rw [show ((662875885093 / 500000000000) : ℝ) = ((500000000000 / 662875885093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9116_neg : (141535583 / 500000000) ≤ -Real.log (500000000000 / 663599805447) ∧
    -Real.log (500000000000 / 663599805447) ≤ (283071167 / 1000000000) := by
  have h := checkLog_sound (w := (163599805447 / 1163599805447)) (n := 12)
    (lo := (141535583 / 500000000)) (hi := (283071167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663599805447 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663599805447 / 500000000000) = 1/(500000000000 / 663599805447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9116 : Bounds (141535583 / 500000000) (283071167 / 1000000000) (Real.log (663599805447 / 500000000000)) := by
  have h := reflection_log_9116_neg
  have he : Real.log (663599805447 / 500000000000) = -Real.log (500000000000 / 663599805447) := by
    rw [show ((663599805447 / 500000000000) : ℝ) = ((500000000000 / 663599805447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9117_neg : (56777669 / 100000000) ≤ -Real.log (50000000000 / 88217000691) ∧
    -Real.log (50000000000 / 88217000691) ≤ (567776691 / 1000000000) := by
  have h := checkLog_sound (w := (38217000691 / 138217000691)) (n := 12)
    (lo := (56777669 / 100000000)) (hi := (567776691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88217000691 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88217000691 / 50000000000) = 1/(50000000000 / 88217000691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9117 : Bounds (56777669 / 100000000) (567776691 / 1000000000) (Real.log (88217000691 / 50000000000)) := by
  have h := reflection_log_9117_neg
  have he : Real.log (88217000691 / 50000000000) = -Real.log (50000000000 / 88217000691) := by
    rw [show ((88217000691 / 50000000000) : ℝ) = ((50000000000 / 88217000691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9118_neg : (568859633 / 1000000000) ≤ -Real.log (250000000000 / 441562932227) ∧
    -Real.log (250000000000 / 441562932227) ≤ (284429817 / 500000000) := by
  have h := checkLog_sound (w := (191562932227 / 691562932227)) (n := 12)
    (lo := (568859633 / 1000000000)) (hi := (284429817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441562932227 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441562932227 / 250000000000) = 1/(250000000000 / 441562932227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9118 : Bounds (568859633 / 1000000000) (284429817 / 500000000) (Real.log (441562932227 / 250000000000)) := by
  have h := reflection_log_9118_neg
  have he : Real.log (441562932227 / 250000000000) = -Real.log (250000000000 / 441562932227) := by
    rw [show ((441562932227 / 250000000000) : ℝ) = ((250000000000 / 441562932227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9119_neg : (244905043 / 1000000000) ≤ -Real.log (400 / 511) ∧
    -Real.log (400 / 511) ≤ (61226261 / 250000000) := by
  have h := checkLog_sound (w := (111 / 911)) (n := 12)
    (lo := (244905043 / 1000000000)) (hi := (61226261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(511 / 400) = 1/(400 / 511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9119 : Bounds (244905043 / 1000000000) (61226261 / 250000000) (Real.log (511 / 400)) := by
  have h := reflection_log_9119_neg
  have he : Real.log (511 / 400) = -Real.log (400 / 511) := by
    rw [show ((511 / 400) : ℝ) = ((400 / 511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9120_neg : (162518929 / 500000000) ≤ -Real.log (289 / 400) ∧
    -Real.log (289 / 400) ≤ (325037859 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 689)) (n := 12)
    (lo := (162518929 / 500000000)) (hi := (325037859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 289) = 1/(289 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9120 : Bounds (-325037859 / 1000000000) (-162518929 / 500000000) (Real.log (289 / 400)) := by
  have h := reflection_log_9120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9121_neg : (277461 / 1000000000) ≤ -Real.log (400000 / 400111) ∧
    -Real.log (400000 / 400111) ≤ (138731 / 500000000) := by
  have h := checkLog_sound (w := (111 / 800111)) (n := 12)
    (lo := (277461 / 1000000000)) (hi := (138731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400111 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400111 / 400000) = 1/(400000 / 400111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9121 : Bounds (277461 / 1000000000) (138731 / 500000000) (Real.log (400111 / 400000)) := by
  have h := reflection_log_9121_neg
  have he : Real.log (400111 / 400000) = -Real.log (400000 / 400111) := by
    rw [show ((400111 / 400000) : ℝ) = ((400000 / 400111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9122_neg : (138769 / 500000000) ≤ -Real.log (399889 / 400000) ∧
    -Real.log (399889 / 400000) ≤ (277539 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 799889)) (n := 12)
    (lo := (138769 / 500000000)) (hi := (277539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399889) = 1/(399889 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9122 : Bounds (-277539 / 1000000000) (-138769 / 500000000) (Real.log (399889 / 400000)) := by
  have h := reflection_log_9122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9123_neg : (8207027 / 62500000) ≤ -Real.log (250000 / 285081) ∧
    -Real.log (250000 / 285081) ≤ (131312433 / 1000000000) := by
  have h := checkLog_sound (w := (35081 / 535081)) (n := 12)
    (lo := (8207027 / 62500000)) (hi := (131312433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((285081 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(285081 / 250000) = 1/(250000 / 285081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9123 : Bounds (8207027 / 62500000) (131312433 / 1000000000) (Real.log (285081 / 250000)) := by
  have h := reflection_log_9123_neg
  have he : Real.log (285081 / 250000) = -Real.log (250000 / 285081) := by
    rw [show ((285081 / 250000) : ℝ) = ((250000 / 285081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9124_neg : (18899963 / 125000000) ≤ -Real.log (214919 / 250000) ∧
    -Real.log (214919 / 250000) ≤ (30239941 / 200000000) := by
  have h := checkLog_sound (w := (35081 / 464919)) (n := 12)
    (lo := (18899963 / 125000000)) (hi := (30239941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 214919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 214919) = 1/(214919 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9124 : Bounds (-30239941 / 200000000) (-18899963 / 125000000) (Real.log (214919 / 250000)) := by
  have h := reflection_log_9124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9125_neg : (131781487 / 1000000000) ≤ -Real.log (1000000 / 1140859) ∧
    -Real.log (1000000 / 1140859) ≤ (8236343 / 62500000) := by
  have h := checkLog_sound (w := (140859 / 2140859)) (n := 12)
    (lo := (131781487 / 1000000000)) (hi := (8236343 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1140859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1140859 / 1000000) = 1/(1000000 / 1140859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9125 : Bounds (131781487 / 1000000000) (8236343 / 62500000) (Real.log (1140859 / 1000000)) := by
  have h := reflection_log_9125_neg
  have he : Real.log (1140859 / 1000000) = -Real.log (1000000 / 1140859) := by
    rw [show ((1140859 / 1000000) : ℝ) = ((1000000 / 1140859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9126_neg : (75911113 / 500000000) ≤ -Real.log (859141 / 1000000) ∧
    -Real.log (859141 / 1000000) ≤ (151822227 / 1000000000) := by
  have h := checkLog_sound (w := (140859 / 1859141)) (n := 12)
    (lo := (75911113 / 500000000)) (hi := (151822227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 859141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 859141) = 1/(859141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9126 : Bounds (-151822227 / 1000000000) (-75911113 / 500000000) (Real.log (859141 / 1000000)) := by
  have h := reflection_log_9126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9127_neg : (10020369 / 500000000) ≤ -Real.log (980158742119 / 1000000000000) ∧
    -Real.log (980158742119 / 1000000000000) ≤ (20040739 / 1000000000) := by
  have h := checkLog_sound (w := (19841257881 / 1980158742119)) (n := 12)
    (lo := (10020369 / 500000000)) (hi := (20040739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980158742119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980158742119) = 1/(980158742119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9127 : Bounds (-20040739 / 1000000000) (-10020369 / 500000000) (Real.log (980158742119 / 1000000000000)) := by
  have h := reflection_log_9127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9128_neg : (2485909 / 125000000) ≤ -Real.log (61269323439 / 62500000000) ∧
    -Real.log (61269323439 / 62500000000) ≤ (19887273 / 1000000000) := by
  have h := checkLog_sound (w := (1230676561 / 123769323439)) (n := 12)
    (lo := (2485909 / 125000000)) (hi := (19887273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61269323439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61269323439) = 1/(61269323439 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9128 : Bounds (-19887273 / 1000000000) (-2485909 / 125000000) (Real.log (61269323439 / 62500000000)) := by
  have h := reflection_log_9128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9129_neg : (282512137 / 1000000000) ≤ -Real.log (500000000000 / 663228937413) ∧
    -Real.log (500000000000 / 663228937413) ≤ (141256069 / 500000000) := by
  have h := checkLog_sound (w := (163228937413 / 1163228937413)) (n := 12)
    (lo := (282512137 / 1000000000)) (hi := (141256069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663228937413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663228937413 / 500000000000) = 1/(500000000000 / 663228937413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9129 : Bounds (282512137 / 1000000000) (141256069 / 500000000) (Real.log (663228937413 / 500000000000)) := by
  have h := reflection_log_9129_neg
  have he : Real.log (663228937413 / 500000000000) = -Real.log (500000000000 / 663228937413) := by
    rw [show ((663228937413 / 500000000000) : ℝ) = ((500000000000 / 663228937413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9130_neg : (283603713 / 1000000000) ≤ -Real.log (250000000000 / 331976648769) ∧
    -Real.log (250000000000 / 331976648769) ≤ (141801857 / 500000000) := by
  have h := checkLog_sound (w := (81976648769 / 581976648769)) (n := 12)
    (lo := (283603713 / 1000000000)) (hi := (141801857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331976648769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331976648769 / 250000000000) = 1/(250000000000 / 331976648769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9130 : Bounds (283603713 / 1000000000) (141801857 / 500000000) (Real.log (331976648769 / 250000000000)) := by
  have h := reflection_log_9130_neg
  have he : Real.log (331976648769 / 250000000000) = -Real.log (250000000000 / 331976648769) := by
    rw [show ((331976648769 / 250000000000) : ℝ) = ((250000000000 / 331976648769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9131_neg : (568859633 / 1000000000) ≤ -Real.log (500000000000 / 883125864453) ∧
    -Real.log (500000000000 / 883125864453) ≤ (284429817 / 500000000) := by
  have h := checkLog_sound (w := (383125864453 / 1383125864453)) (n := 12)
    (lo := (568859633 / 1000000000)) (hi := (284429817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((883125864453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(883125864453 / 500000000000) = 1/(500000000000 / 883125864453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9131 : Bounds (568859633 / 1000000000) (284429817 / 500000000) (Real.log (883125864453 / 500000000000)) := by
  have h := reflection_log_9131_neg
  have he : Real.log (883125864453 / 500000000000) = -Real.log (500000000000 / 883125864453) := by
    rw [show ((883125864453 / 500000000000) : ℝ) = ((500000000000 / 883125864453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9132_neg : (284971451 / 500000000) ≤ -Real.log (500000000000 / 884083044983) ∧
    -Real.log (500000000000 / 884083044983) ≤ (569942903 / 1000000000) := by
  have h := checkLog_sound (w := (384083044983 / 1384083044983)) (n := 12)
    (lo := (284971451 / 500000000)) (hi := (569942903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884083044983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884083044983 / 500000000000) = 1/(500000000000 / 884083044983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9132 : Bounds (284971451 / 500000000) (569942903 / 1000000000) (Real.log (884083044983 / 500000000000)) := by
  have h := reflection_log_9132_neg
  have he : Real.log (884083044983 / 500000000000) = -Real.log (500000000000 / 884083044983) := by
    rw [show ((884083044983 / 500000000000) : ℝ) = ((500000000000 / 884083044983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9133_neg : (49059271 / 200000000) ≤ -Real.log (500 / 639) ∧
    -Real.log (500 / 639) ≤ (61324089 / 250000000) := by
  have h := checkLog_sound (w := (139 / 1139)) (n := 12)
    (lo := (49059271 / 200000000)) (hi := (61324089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639 / 500) = 1/(500 / 639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9133 : Bounds (49059271 / 200000000) (61324089 / 250000000) (Real.log (639 / 500)) := by
  have h := reflection_log_9133_neg
  have he : Real.log (639 / 500) = -Real.log (500 / 639) := by
    rw [show ((639 / 500) : ℝ) = ((500 / 639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9134_neg : (16286507 / 50000000) ≤ -Real.log (361 / 500) ∧
    -Real.log (361 / 500) ≤ (325730141 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 861)) (n := 12)
    (lo := (16286507 / 50000000)) (hi := (325730141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 361) = 1/(361 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9134 : Bounds (-325730141 / 1000000000) (-16286507 / 50000000) (Real.log (361 / 500)) := by
  have h := reflection_log_9134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9135_neg : (277961 / 1000000000) ≤ -Real.log (500000 / 500139) ∧
    -Real.log (500000 / 500139) ≤ (138981 / 500000000) := by
  have h := checkLog_sound (w := (139 / 1000139)) (n := 12)
    (lo := (277961 / 1000000000)) (hi := (138981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500139 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500139 / 500000) = 1/(500000 / 500139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9135 : Bounds (277961 / 1000000000) (138981 / 500000000) (Real.log (500139 / 500000)) := by
  have h := reflection_log_9135_neg
  have he : Real.log (500139 / 500000) = -Real.log (500000 / 500139) := by
    rw [show ((500139 / 500000) : ℝ) = ((500000 / 500139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9136_neg : (139019 / 500000000) ≤ -Real.log (499861 / 500000) ∧
    -Real.log (499861 / 500000) ≤ (278039 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 999861)) (n := 12)
    (lo := (139019 / 500000000)) (hi := (278039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499861) = 1/(499861 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9136 : Bounds (-278039 / 1000000000) (-139019 / 500000000) (Real.log (499861 / 500000)) := by
  have h := reflection_log_9136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9137_neg : (131540411 / 1000000000) ≤ -Real.log (125000 / 142573) ∧
    -Real.log (125000 / 142573) ≤ (32885103 / 250000000) := by
  have h := checkLog_sound (w := (17573 / 267573)) (n := 12)
    (lo := (131540411 / 1000000000)) (hi := (32885103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142573 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142573 / 125000) = 1/(125000 / 142573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9137 : Bounds (131540411 / 1000000000) (32885103 / 250000000) (Real.log (142573 / 125000)) := by
  have h := reflection_log_9137_neg
  have he : Real.log (142573 / 125000) = -Real.log (125000 / 142573) := by
    rw [show ((142573 / 125000) : ℝ) = ((125000 / 142573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9138_neg : (15150219 / 100000000) ≤ -Real.log (107427 / 125000) ∧
    -Real.log (107427 / 125000) ≤ (151502191 / 1000000000) := by
  have h := checkLog_sound (w := (17573 / 232427)) (n := 12)
    (lo := (15150219 / 100000000)) (hi := (151502191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107427) = 1/(107427 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9138 : Bounds (-151502191 / 1000000000) (-15150219 / 100000000) (Real.log (107427 / 125000)) := by
  have h := reflection_log_9138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9139_neg : (33002559 / 250000000) ≤ -Real.log (3125 / 3566) ∧
    -Real.log (3125 / 3566) ≤ (132010237 / 1000000000) := by
  have h := checkLog_sound (w := (441 / 6691)) (n := 12)
    (lo := (33002559 / 250000000)) (hi := (132010237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3566 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3566 / 3125) = 1/(3125 / 3566) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9139 : Bounds (33002559 / 250000000) (132010237 / 1000000000) (Real.log (3566 / 3125)) := by
  have h := reflection_log_9139_neg
  have he : Real.log (3566 / 3125) = -Real.log (3125 / 3566) := by
    rw [show ((3566 / 3125) : ℝ) = ((3125 / 3566) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9140_neg : (9507879 / 62500000) ≤ -Real.log (2684 / 3125) ∧
    -Real.log (2684 / 3125) ≤ (30425213 / 200000000) := by
  have h := checkLog_sound (w := (441 / 5809)) (n := 12)
    (lo := (9507879 / 62500000)) (hi := (30425213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2684) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2684) = 1/(2684 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9140 : Bounds (-30425213 / 200000000) (-9507879 / 62500000) (Real.log (2684 / 3125)) := by
  have h := reflection_log_9140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9141_neg : (20115827 / 1000000000) ≤ -Real.log (9571144 / 9765625) ∧
    -Real.log (9571144 / 9765625) ≤ (5028957 / 250000000) := by
  have h := checkLog_sound (w := (194481 / 19336769)) (n := 12)
    (lo := (20115827 / 1000000000)) (hi := (5028957 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9571144) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9571144) = 1/(9571144 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9141 : Bounds (-5028957 / 250000000) (-20115827 / 1000000000) (Real.log (9571144 / 9765625)) := by
  have h := reflection_log_9141_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9142_neg : (9980889 / 500000000) ≤ -Real.log (15316189671 / 15625000000) ∧
    -Real.log (15316189671 / 15625000000) ≤ (19961779 / 1000000000) := by
  have h := checkLog_sound (w := (308810329 / 30941189671)) (n := 12)
    (lo := (9980889 / 500000000)) (hi := (19961779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15316189671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15316189671) = 1/(15316189671 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9142 : Bounds (-19961779 / 1000000000) (-9980889 / 500000000) (Real.log (15316189671 / 15625000000)) := by
  have h := reflection_log_9142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9143_neg : (141521301 / 500000000) ≤ -Real.log (500000000000 / 663580850251) ∧
    -Real.log (500000000000 / 663580850251) ≤ (283042603 / 1000000000) := by
  have h := checkLog_sound (w := (163580850251 / 1163580850251)) (n := 12)
    (lo := (141521301 / 500000000)) (hi := (283042603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663580850251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663580850251 / 500000000000) = 1/(500000000000 / 663580850251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9143 : Bounds (141521301 / 500000000) (283042603 / 1000000000) (Real.log (663580850251 / 500000000000)) := by
  have h := reflection_log_9143_neg
  have he : Real.log (663580850251 / 500000000000) = -Real.log (500000000000 / 663580850251) := by
    rw [show ((663580850251 / 500000000000) : ℝ) = ((500000000000 / 663580850251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9144_neg : (2841363 / 10000000) ≤ -Real.log (500000000000 / 664307004471) ∧
    -Real.log (500000000000 / 664307004471) ≤ (284136301 / 1000000000) := by
  have h := checkLog_sound (w := (164307004471 / 1164307004471)) (n := 12)
    (lo := (2841363 / 10000000)) (hi := (284136301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664307004471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664307004471 / 500000000000) = 1/(500000000000 / 664307004471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9144 : Bounds (2841363 / 10000000) (284136301 / 1000000000) (Real.log (664307004471 / 500000000000)) := by
  have h := reflection_log_9144_neg
  have he : Real.log (664307004471 / 500000000000) = -Real.log (500000000000 / 664307004471) := by
    rw [show ((664307004471 / 500000000000) : ℝ) = ((500000000000 / 664307004471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9145_neg : (284971451 / 500000000) ≤ -Real.log (250000000000 / 442041522491) ∧
    -Real.log (250000000000 / 442041522491) ≤ (569942903 / 1000000000) := by
  have h := checkLog_sound (w := (192041522491 / 692041522491)) (n := 12)
    (lo := (284971451 / 500000000)) (hi := (569942903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((442041522491 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(442041522491 / 250000000000) = 1/(250000000000 / 442041522491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9145 : Bounds (284971451 / 500000000) (569942903 / 1000000000) (Real.log (442041522491 / 250000000000)) := by
  have h := reflection_log_9145_neg
  have he : Real.log (442041522491 / 250000000000) = -Real.log (250000000000 / 442041522491) := by
    rw [show ((442041522491 / 250000000000) : ℝ) = ((250000000000 / 442041522491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9146_neg : (8922289 / 15625000) ≤ -Real.log (500000000000 / 885041551247) ∧
    -Real.log (500000000000 / 885041551247) ≤ (571026497 / 1000000000) := by
  have h := checkLog_sound (w := (385041551247 / 1385041551247)) (n := 12)
    (lo := (8922289 / 15625000)) (hi := (571026497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885041551247 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885041551247 / 500000000000) = 1/(500000000000 / 885041551247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9146 : Bounds (8922289 / 15625000) (571026497 / 1000000000) (Real.log (885041551247 / 500000000000)) := by
  have h := reflection_log_9146_neg
  have he : Real.log (885041551247 / 500000000000) = -Real.log (500000000000 / 885041551247) := by
    rw [show ((885041551247 / 500000000000) : ℝ) = ((500000000000 / 885041551247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9147_neg : (49137503 / 200000000) ≤ -Real.log (2000 / 2557) ∧
    -Real.log (2000 / 2557) ≤ (61421879 / 250000000) := by
  have h := checkLog_sound (w := (557 / 4557)) (n := 12)
    (lo := (49137503 / 200000000)) (hi := (61421879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2557 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2557 / 2000) = 1/(2000 / 2557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9147 : Bounds (49137503 / 200000000) (61421879 / 250000000) (Real.log (2557 / 2000)) := by
  have h := reflection_log_9147_neg
  have he : Real.log (2557 / 2000) = -Real.log (2000 / 2557) := by
    rw [show ((2557 / 2000) : ℝ) = ((2000 / 2557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9148_neg : (3264229 / 10000000) ≤ -Real.log (1443 / 2000) ∧
    -Real.log (1443 / 2000) ≤ (326422901 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 3443)) (n := 12)
    (lo := (3264229 / 10000000)) (hi := (326422901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1443) = 1/(1443 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9148 : Bounds (-326422901 / 1000000000) (-3264229 / 10000000) (Real.log (1443 / 2000)) := by
  have h := reflection_log_9148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9149_neg : (278461 / 1000000000) ≤ -Real.log (2000000 / 2000557) ∧
    -Real.log (2000000 / 2000557) ≤ (139231 / 500000000) := by
  have h := checkLog_sound (w := (557 / 4000557)) (n := 12)
    (lo := (278461 / 1000000000)) (hi := (139231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000557 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000557 / 2000000) = 1/(2000000 / 2000557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9149 : Bounds (278461 / 1000000000) (139231 / 500000000) (Real.log (2000557 / 2000000)) := by
  have h := reflection_log_9149_neg
  have he : Real.log (2000557 / 2000000) = -Real.log (2000000 / 2000557) := by
    rw [show ((2000557 / 2000000) : ℝ) = ((2000000 / 2000557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9150_neg : (139269 / 500000000) ≤ -Real.log (1999443 / 2000000) ∧
    -Real.log (1999443 / 2000000) ≤ (278539 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 3999443)) (n := 12)
    (lo := (139269 / 500000000)) (hi := (278539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999443) = 1/(1999443 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9150 : Bounds (-278539 / 1000000000) (-139269 / 500000000) (Real.log (1999443 / 2000000)) := by
  have h := reflection_log_9150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9151_neg : (26353843 / 200000000) ≤ -Real.log (200000 / 228169) ∧
    -Real.log (200000 / 228169) ≤ (1029447 / 7812500) := by
  have h := checkLog_sound (w := (28169 / 428169)) (n := 12)
    (lo := (26353843 / 200000000)) (hi := (1029447 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228169 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228169 / 200000) = 1/(200000 / 228169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9151 : Bounds (26353843 / 200000000) (1029447 / 7812500) (Real.log (228169 / 200000)) := by
  have h := reflection_log_9151_neg
  have he : Real.log (228169 / 200000) = -Real.log (200000 / 228169) := by
    rw [show ((228169 / 200000) : ℝ) = ((200000 / 228169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


