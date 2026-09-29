-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0123__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0123__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:36:34.890591+00:00
-- url     : https://prove2.me/theorems/30cf463e-38f6-46a1-ab1f-7d27da5e453c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0123 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0124, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0123 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0124, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0125)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0123 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0124, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0125)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0123 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0124, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0125) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0123 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0124, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0125).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0123 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7872_neg : (125015753 / 1000000000) ≤ -Real.log (882483 / 1000000) ∧
    -Real.log (882483 / 1000000) ≤ (62507877 / 500000000) := by
  have h := checkLog_sound (w := (117517 / 1882483)) (n := 12)
    (lo := (125015753 / 1000000000)) (hi := (62507877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 882483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 882483) = 1/(882483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7872 : Bounds (-62507877 / 500000000) (-125015753 / 1000000000) (Real.log (882483 / 1000000)) := by
  have h := reflection_log_7872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7873_neg : (13906493 / 1000000000) ≤ -Real.log (986189754711 / 1000000000000) ∧
    -Real.log (986189754711 / 1000000000000) ≤ (6953247 / 500000000) := by
  have h := checkLog_sound (w := (13810245289 / 1986189754711)) (n := 12)
    (lo := (13906493 / 1000000000)) (hi := (6953247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986189754711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986189754711) = 1/(986189754711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7873 : Bounds (-6953247 / 500000000) (-13906493 / 1000000000) (Real.log (986189754711 / 1000000000000)) := by
  have h := reflection_log_7873_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7874_neg : (13790439 / 1000000000) ≤ -Real.log (986304213159 / 1000000000000) ∧
    -Real.log (986304213159 / 1000000000000) ≤ (344761 / 25000000) := by
  have h := checkLog_sound (w := (13695786841 / 1986304213159)) (n := 12)
    (lo := (13790439 / 1000000000)) (hi := (344761 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986304213159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986304213159) = 1/(986304213159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7874 : Bounds (-344761 / 25000000) (-13790439 / 1000000000) (Real.log (986304213159 / 1000000000000)) := by
  have h := reflection_log_7874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7875_neg : (235135403 / 1000000000) ≤ -Real.log (100000000000 / 126508005359) ∧
    -Real.log (100000000000 / 126508005359) ≤ (58783851 / 250000000) := by
  have h := checkLog_sound (w := (26508005359 / 226508005359)) (n := 12)
    (lo := (235135403 / 1000000000)) (hi := (58783851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126508005359 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126508005359 / 100000000000) = 1/(100000000000 / 126508005359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7875 : Bounds (235135403 / 1000000000) (58783851 / 250000000) (Real.log (126508005359 / 100000000000)) := by
  have h := reflection_log_7875_neg
  have he : Real.log (126508005359 / 100000000000) = -Real.log (100000000000 / 126508005359) := by
    rw [show ((126508005359 / 100000000000) : ℝ) = ((100000000000 / 126508005359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7876_neg : (236125013 / 1000000000) ≤ -Real.log (500000000000 / 633166304621) ∧
    -Real.log (500000000000 / 633166304621) ≤ (118062507 / 500000000) := by
  have h := checkLog_sound (w := (133166304621 / 1133166304621)) (n := 12)
    (lo := (236125013 / 1000000000)) (hi := (118062507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633166304621 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633166304621 / 500000000000) = 1/(500000000000 / 633166304621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7876 : Bounds (236125013 / 1000000000) (118062507 / 500000000) (Real.log (633166304621 / 500000000000)) := by
  have h := reflection_log_7876_neg
  have he : Real.log (633166304621 / 500000000000) = -Real.log (500000000000 / 633166304621) := by
    rw [show ((633166304621 / 500000000000) : ℝ) = ((500000000000 / 633166304621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7877_neg : (47260441 / 100000000) ≤ -Real.log (500000000000 / 802083333333) ∧
    -Real.log (500000000000 / 802083333333) ≤ (472604411 / 1000000000) := by
  have h := checkLog_sound (w := (302083333333 / 1302083333333)) (n := 12)
    (lo := (47260441 / 100000000)) (hi := (472604411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802083333333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802083333333 / 500000000000) = 1/(500000000000 / 802083333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7877 : Bounds (47260441 / 100000000) (472604411 / 1000000000) (Real.log (802083333333 / 500000000000)) := by
  have h := reflection_log_7877_neg
  have he : Real.log (802083333333 / 500000000000) = -Real.log (500000000000 / 802083333333) := by
    rw [show ((802083333333 / 500000000000) : ℝ) = ((500000000000 / 802083333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7878_neg : (236830713 / 500000000) ≤ -Real.log (125000000000 / 200732899023) ∧
    -Real.log (125000000000 / 200732899023) ≤ (473661427 / 1000000000) := by
  have h := checkLog_sound (w := (75732899023 / 325732899023)) (n := 12)
    (lo := (236830713 / 500000000)) (hi := (473661427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200732899023 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200732899023 / 125000000000) = 1/(125000000000 / 200732899023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7878 : Bounds (236830713 / 500000000) (473661427 / 1000000000) (Real.log (200732899023 / 125000000000)) := by
  have h := reflection_log_7878_neg
  have he : Real.log (200732899023 / 125000000000) = -Real.log (125000000000 / 200732899023) := by
    rw [show ((200732899023 / 125000000000) : ℝ) = ((125000000000 / 200732899023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7879_neg : (13090639 / 62500000) ≤ -Real.log (1000 / 1233) ∧
    -Real.log (1000 / 1233) ≤ (8378009 / 40000000) := by
  have h := checkLog_sound (w := (233 / 2233)) (n := 12)
    (lo := (13090639 / 62500000)) (hi := (8378009 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233 / 1000) = 1/(1000 / 1233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7879 : Bounds (13090639 / 62500000) (8378009 / 40000000) (Real.log (1233 / 1000)) := by
  have h := reflection_log_7879_neg
  have he : Real.log (1233 / 1000) = -Real.log (1000 / 1233) := by
    rw [show ((1233 / 1000) : ℝ) = ((1000 / 1233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7880_neg : (265268477 / 1000000000) ≤ -Real.log (767 / 1000) ∧
    -Real.log (767 / 1000) ≤ (132634239 / 500000000) := by
  have h := checkLog_sound (w := (233 / 1767)) (n := 12)
    (lo := (265268477 / 1000000000)) (hi := (132634239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 767) = 1/(767 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7880 : Bounds (-132634239 / 500000000) (-265268477 / 1000000000) (Real.log (767 / 1000)) := by
  have h := reflection_log_7880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7881_neg : (58243 / 250000000) ≤ -Real.log (1000000 / 1000233) ∧
    -Real.log (1000000 / 1000233) ≤ (232973 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 2000233)) (n := 12)
    (lo := (58243 / 250000000)) (hi := (232973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000233 / 1000000) = 1/(1000000 / 1000233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7881 : Bounds (58243 / 250000000) (232973 / 1000000000) (Real.log (1000233 / 1000000)) := by
  have h := reflection_log_7881_neg
  have he : Real.log (1000233 / 1000000) = -Real.log (1000000 / 1000233) := by
    rw [show ((1000233 / 1000000) : ℝ) = ((1000000 / 1000233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7882_neg : (233027 / 1000000000) ≤ -Real.log (999767 / 1000000) ∧
    -Real.log (999767 / 1000000) ≤ (58257 / 250000000) := by
  have h := checkLog_sound (w := (233 / 1999767)) (n := 12)
    (lo := (233027 / 1000000000)) (hi := (58257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999767) = 1/(999767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7882 : Bounds (-58257 / 250000000) (-233027 / 1000000000) (Real.log (999767 / 1000000)) := by
  have h := reflection_log_7882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7883_neg : (11090253 / 100000000) ≤ -Real.log (500000 / 558643) ∧
    -Real.log (500000 / 558643) ≤ (110902531 / 1000000000) := by
  have h := checkLog_sound (w := (58643 / 1058643)) (n := 12)
    (lo := (11090253 / 100000000)) (hi := (110902531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558643 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(558643 / 500000) = 1/(500000 / 558643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7883 : Bounds (11090253 / 100000000) (110902531 / 1000000000) (Real.log (558643 / 500000)) := by
  have h := reflection_log_7883_neg
  have he : Real.log (558643 / 500000) = -Real.log (500000 / 558643) := by
    rw [show ((558643 / 500000) : ℝ) = ((500000 / 558643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7884_neg : (62377013 / 500000000) ≤ -Real.log (441357 / 500000) ∧
    -Real.log (441357 / 500000) ≤ (124754027 / 1000000000) := by
  have h := checkLog_sound (w := (58643 / 941357)) (n := 12)
    (lo := (62377013 / 500000000)) (hi := (124754027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 441357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 441357) = 1/(441357 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7884 : Bounds (-124754027 / 1000000000) (-62377013 / 500000000) (Real.log (441357 / 500000)) := by
  have h := reflection_log_7884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7885_neg : (55670051 / 500000000) ≤ -Real.log (40000 / 44711) ∧
    -Real.log (40000 / 44711) ≤ (111340103 / 1000000000) := by
  have h := checkLog_sound (w := (4711 / 84711)) (n := 12)
    (lo := (55670051 / 500000000)) (hi := (111340103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44711 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44711 / 40000) = 1/(40000 / 44711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7885 : Bounds (55670051 / 500000000) (111340103 / 1000000000) (Real.log (44711 / 40000)) := by
  have h := reflection_log_7885_neg
  have he : Real.log (44711 / 40000) = -Real.log (40000 / 44711) := by
    rw [show ((44711 / 40000) : ℝ) = ((40000 / 44711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7886_neg : (125308153 / 1000000000) ≤ -Real.log (35289 / 40000) ∧
    -Real.log (35289 / 40000) ≤ (62654077 / 500000000) := by
  have h := checkLog_sound (w := (4711 / 75289)) (n := 12)
    (lo := (125308153 / 1000000000)) (hi := (62654077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 35289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 35289) = 1/(35289 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7886 : Bounds (-62654077 / 500000000) (-125308153 / 1000000000) (Real.log (35289 / 40000)) := by
  have h := reflection_log_7886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7887_neg : (13968051 / 1000000000) ≤ -Real.log (1577806479 / 1600000000) ∧
    -Real.log (1577806479 / 1600000000) ≤ (3492013 / 250000000) := by
  have h := checkLog_sound (w := (22193521 / 3177806479)) (n := 12)
    (lo := (13968051 / 1000000000)) (hi := (3492013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1577806479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1577806479) = 1/(1577806479 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7887 : Bounds (-3492013 / 250000000) (-13968051 / 1000000000) (Real.log (1577806479 / 1600000000)) := by
  have h := reflection_log_7887_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7888_neg : (1731437 / 125000000) ≤ -Real.log (246560998551 / 250000000000) ∧
    -Real.log (246560998551 / 250000000000) ≤ (13851497 / 1000000000) := by
  have h := checkLog_sound (w := (3439001449 / 496560998551)) (n := 12)
    (lo := (1731437 / 125000000)) (hi := (13851497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246560998551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246560998551) = 1/(246560998551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7888 : Bounds (-13851497 / 1000000000) (-1731437 / 125000000) (Real.log (246560998551 / 250000000000)) := by
  have h := reflection_log_7888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7889_neg : (58914139 / 250000000) ≤ -Real.log (250000000000 / 316434881513) ∧
    -Real.log (250000000000 / 316434881513) ≤ (235656557 / 1000000000) := by
  have h := checkLog_sound (w := (66434881513 / 566434881513)) (n := 12)
    (lo := (58914139 / 250000000)) (hi := (235656557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316434881513 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316434881513 / 250000000000) = 1/(250000000000 / 316434881513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7889 : Bounds (58914139 / 250000000) (235656557 / 1000000000) (Real.log (316434881513 / 250000000000)) := by
  have h := reflection_log_7889_neg
  have he : Real.log (316434881513 / 250000000000) = -Real.log (250000000000 / 316434881513) := by
    rw [show ((316434881513 / 250000000000) : ℝ) = ((250000000000 / 316434881513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7890_neg : (47329651 / 200000000) ≤ -Real.log (500000000000 / 633497690499) ∧
    -Real.log (500000000000 / 633497690499) ≤ (3697629 / 15625000) := by
  have h := checkLog_sound (w := (133497690499 / 1133497690499)) (n := 12)
    (lo := (47329651 / 200000000)) (hi := (3697629 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633497690499 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633497690499 / 500000000000) = 1/(500000000000 / 633497690499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7890 : Bounds (47329651 / 200000000) (3697629 / 15625000) (Real.log (633497690499 / 500000000000)) := by
  have h := reflection_log_7890_neg
  have he : Real.log (633497690499 / 500000000000) = -Real.log (500000000000 / 633497690499) := by
    rw [show ((633497690499 / 500000000000) : ℝ) = ((500000000000 / 633497690499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7891_neg : (236830713 / 500000000) ≤ -Real.log (500000000000 / 802931596091) ∧
    -Real.log (500000000000 / 802931596091) ≤ (473661427 / 1000000000) := by
  have h := checkLog_sound (w := (302931596091 / 1302931596091)) (n := 12)
    (lo := (236830713 / 500000000)) (hi := (473661427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802931596091 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802931596091 / 500000000000) = 1/(500000000000 / 802931596091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7891 : Bounds (236830713 / 500000000) (473661427 / 1000000000) (Real.log (802931596091 / 500000000000)) := by
  have h := reflection_log_7891_neg
  have he : Real.log (802931596091 / 500000000000) = -Real.log (500000000000 / 802931596091) := by
    rw [show ((802931596091 / 500000000000) : ℝ) = ((500000000000 / 802931596091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7892_neg : (474718701 / 1000000000) ≤ -Real.log (250000000000 / 401890482399) ∧
    -Real.log (250000000000 / 401890482399) ≤ (237359351 / 500000000) := by
  have h := checkLog_sound (w := (151890482399 / 651890482399)) (n := 12)
    (lo := (474718701 / 1000000000)) (hi := (237359351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401890482399 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401890482399 / 250000000000) = 1/(250000000000 / 401890482399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7892 : Bounds (474718701 / 1000000000) (237359351 / 500000000) (Real.log (401890482399 / 250000000000)) := by
  have h := reflection_log_7892_neg
  have he : Real.log (401890482399 / 250000000000) = -Real.log (250000000000 / 401890482399) := by
    rw [show ((401890482399 / 250000000000) : ℝ) = ((250000000000 / 401890482399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7893_neg : (26231957 / 125000000) ≤ -Real.log (2000 / 2467) ∧
    -Real.log (2000 / 2467) ≤ (209855657 / 1000000000) := by
  have h := checkLog_sound (w := (467 / 4467)) (n := 12)
    (lo := (26231957 / 125000000)) (hi := (209855657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2467 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2467 / 2000) = 1/(2000 / 2467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7893 : Bounds (26231957 / 125000000) (209855657 / 1000000000) (Real.log (2467 / 2000)) := by
  have h := reflection_log_7893_neg
  have he : Real.log (2467 / 2000) = -Real.log (2000 / 2467) := by
    rw [show ((2467 / 2000) : ℝ) = ((2000 / 2467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7894_neg : (13296029 / 50000000) ≤ -Real.log (1533 / 2000) ∧
    -Real.log (1533 / 2000) ≤ (265920581 / 1000000000) := by
  have h := checkLog_sound (w := (467 / 3533)) (n := 12)
    (lo := (13296029 / 50000000)) (hi := (265920581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1533) = 1/(1533 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7894 : Bounds (-265920581 / 1000000000) (-13296029 / 50000000) (Real.log (1533 / 2000)) := by
  have h := reflection_log_7894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7895_neg : (456 / 1953125) ≤ -Real.log (2000000 / 2000467) ∧
    -Real.log (2000000 / 2000467) ≤ (233473 / 1000000000) := by
  have h := checkLog_sound (w := (467 / 4000467)) (n := 12)
    (lo := (456 / 1953125)) (hi := (233473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000467 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000467 / 2000000) = 1/(2000000 / 2000467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7895 : Bounds (456 / 1953125) (233473 / 1000000000) (Real.log (2000467 / 2000000)) := by
  have h := reflection_log_7895_neg
  have he : Real.log (2000467 / 2000000) = -Real.log (2000000 / 2000467) := by
    rw [show ((2000467 / 2000000) : ℝ) = ((2000000 / 2000467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7896_neg : (233527 / 1000000000) ≤ -Real.log (1999533 / 2000000) ∧
    -Real.log (1999533 / 2000000) ≤ (29191 / 125000000) := by
  have h := checkLog_sound (w := (467 / 3999533)) (n := 12)
    (lo := (233527 / 1000000000)) (hi := (29191 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999533) = 1/(1999533 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7896 : Bounds (-29191 / 125000000) (-233527 / 1000000000) (Real.log (1999533 / 2000000)) := by
  have h := reflection_log_7896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7897_neg : (4445301 / 40000000) ≤ -Real.log (1000000 / 1117543) ∧
    -Real.log (1000000 / 1117543) ≤ (55566263 / 500000000) := by
  have h := checkLog_sound (w := (117543 / 2117543)) (n := 12)
    (lo := (4445301 / 40000000)) (hi := (55566263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1117543 / 1000000) = 1/(1000000 / 1117543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7897 : Bounds (4445301 / 40000000) (55566263 / 500000000) (Real.log (1117543 / 1000000)) := by
  have h := reflection_log_7897_neg
  have he : Real.log (1117543 / 1000000) = -Real.log (1000000 / 1117543) := by
    rw [show ((1117543 / 1000000) : ℝ) = ((1000000 / 1117543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7898_neg : (3907663 / 31250000) ≤ -Real.log (882457 / 1000000) ∧
    -Real.log (882457 / 1000000) ≤ (125045217 / 1000000000) := by
  have h := checkLog_sound (w := (117543 / 1882457)) (n := 12)
    (lo := (3907663 / 31250000)) (hi := (125045217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 882457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 882457) = 1/(882457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7898 : Bounds (-125045217 / 1000000000) (-3907663 / 31250000) (Real.log (882457 / 1000000)) := by
  have h := reflection_log_7898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7899_neg : (111570891 / 1000000000) ≤ -Real.log (1000000 / 1118033) ∧
    -Real.log (1000000 / 1118033) ≤ (27892723 / 250000000) := by
  have h := checkLog_sound (w := (118033 / 2118033)) (n := 12)
    (lo := (111570891 / 1000000000)) (hi := (27892723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1118033 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1118033 / 1000000) = 1/(1000000 / 1118033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7899 : Bounds (111570891 / 1000000000) (27892723 / 250000000) (Real.log (1118033 / 1000000)) := by
  have h := reflection_log_7899_neg
  have he : Real.log (1118033 / 1000000) = -Real.log (1000000 / 1118033) := by
    rw [show ((1118033 / 1000000) : ℝ) = ((1000000 / 1118033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7900_neg : (62800319 / 500000000) ≤ -Real.log (881967 / 1000000) ∧
    -Real.log (881967 / 1000000) ≤ (125600639 / 1000000000) := by
  have h := checkLog_sound (w := (118033 / 1881967)) (n := 12)
    (lo := (62800319 / 500000000)) (hi := (125600639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 881967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 881967) = 1/(881967 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7900 : Bounds (-125600639 / 1000000000) (-62800319 / 500000000) (Real.log (881967 / 1000000)) := by
  have h := reflection_log_7900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7901_neg : (14029747 / 1000000000) ≤ -Real.log (986068210911 / 1000000000000) ∧
    -Real.log (986068210911 / 1000000000000) ≤ (3507437 / 250000000) := by
  have h := checkLog_sound (w := (13931789089 / 1986068210911)) (n := 12)
    (lo := (14029747 / 1000000000)) (hi := (3507437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986068210911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986068210911) = 1/(986068210911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7901 : Bounds (-3507437 / 250000000) (-14029747 / 1000000000) (Real.log (986068210911 / 1000000000000)) := by
  have h := reflection_log_7901_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7902_neg : (13912691 / 1000000000) ≤ -Real.log (986183643151 / 1000000000000) ∧
    -Real.log (986183643151 / 1000000000000) ≤ (3478173 / 250000000) := by
  have h := checkLog_sound (w := (13816356849 / 1986183643151)) (n := 12)
    (lo := (13912691 / 1000000000)) (hi := (3478173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986183643151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986183643151) = 1/(986183643151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7902 : Bounds (-3478173 / 250000000) (-13912691 / 1000000000) (Real.log (986183643151 / 1000000000000)) := by
  have h := reflection_log_7902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7903_neg : (118088871 / 500000000) ≤ -Real.log (125000000000 / 158299922829) ∧
    -Real.log (125000000000 / 158299922829) ≤ (236177743 / 1000000000) := by
  have h := checkLog_sound (w := (33299922829 / 283299922829)) (n := 12)
    (lo := (118088871 / 500000000)) (hi := (236177743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158299922829 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158299922829 / 125000000000) = 1/(125000000000 / 158299922829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7903 : Bounds (118088871 / 500000000) (236177743 / 1000000000) (Real.log (158299922829 / 125000000000)) := by
  have h := reflection_log_7903_neg
  have he : Real.log (158299922829 / 125000000000) = -Real.log (125000000000 / 158299922829) := by
    rw [show ((158299922829 / 125000000000) : ℝ) = ((125000000000 / 158299922829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7904_neg : (237171529 / 1000000000) ≤ -Real.log (500000000000 / 633829270257) ∧
    -Real.log (500000000000 / 633829270257) ≤ (23717153 / 100000000) := by
  have h := checkLog_sound (w := (133829270257 / 1133829270257)) (n := 12)
    (lo := (237171529 / 1000000000)) (hi := (23717153 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633829270257 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633829270257 / 500000000000) = 1/(500000000000 / 633829270257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7904 : Bounds (237171529 / 1000000000) (23717153 / 100000000) (Real.log (633829270257 / 500000000000)) := by
  have h := reflection_log_7904_neg
  have he : Real.log (633829270257 / 500000000000) = -Real.log (500000000000 / 633829270257) := by
    rw [show ((633829270257 / 500000000000) : ℝ) = ((500000000000 / 633829270257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7905_neg : (474718701 / 1000000000) ≤ -Real.log (500000000000 / 803780964797) ∧
    -Real.log (500000000000 / 803780964797) ≤ (237359351 / 500000000) := by
  have h := checkLog_sound (w := (303780964797 / 1303780964797)) (n := 12)
    (lo := (474718701 / 1000000000)) (hi := (237359351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803780964797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803780964797 / 500000000000) = 1/(500000000000 / 803780964797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7905 : Bounds (474718701 / 1000000000) (237359351 / 500000000) (Real.log (803780964797 / 500000000000)) := by
  have h := reflection_log_7905_neg
  have he : Real.log (803780964797 / 500000000000) = -Real.log (500000000000 / 803780964797) := by
    rw [show ((803780964797 / 500000000000) : ℝ) = ((500000000000 / 803780964797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7906_neg : (475776237 / 1000000000) ≤ -Real.log (250000000000 / 402315720809) ∧
    -Real.log (250000000000 / 402315720809) ≤ (237888119 / 500000000) := by
  have h := checkLog_sound (w := (152315720809 / 652315720809)) (n := 12)
    (lo := (475776237 / 1000000000)) (hi := (237888119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((402315720809 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(402315720809 / 250000000000) = 1/(250000000000 / 402315720809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7906 : Bounds (475776237 / 1000000000) (237888119 / 500000000) (Real.log (402315720809 / 250000000000)) := by
  have h := reflection_log_7906_neg
  have he : Real.log (402315720809 / 250000000000) = -Real.log (250000000000 / 402315720809) := by
    rw [show ((402315720809 / 250000000000) : ℝ) = ((250000000000 / 402315720809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7907_neg : (8410437 / 40000000) ≤ -Real.log (500 / 617) ∧
    -Real.log (500 / 617) ≤ (105130463 / 500000000) := by
  have h := checkLog_sound (w := (117 / 1117)) (n := 12)
    (lo := (8410437 / 40000000)) (hi := (105130463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(617 / 500) = 1/(500 / 617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7907 : Bounds (8410437 / 40000000) (105130463 / 500000000) (Real.log (617 / 500)) := by
  have h := reflection_log_7907_neg
  have he : Real.log (617 / 500) = -Real.log (500 / 617) := by
    rw [show ((617 / 500) : ℝ) = ((500 / 617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7908_neg : (266573109 / 1000000000) ≤ -Real.log (383 / 500) ∧
    -Real.log (383 / 500) ≤ (26657311 / 100000000) := by
  have h := checkLog_sound (w := (117 / 883)) (n := 12)
    (lo := (266573109 / 1000000000)) (hi := (26657311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 383) = 1/(383 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7908 : Bounds (-26657311 / 100000000) (-266573109 / 1000000000) (Real.log (383 / 500)) := by
  have h := reflection_log_7908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7909_neg : (58493 / 250000000) ≤ -Real.log (500000 / 500117) ∧
    -Real.log (500000 / 500117) ≤ (233973 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 1000117)) (n := 12)
    (lo := (58493 / 250000000)) (hi := (233973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500117 / 500000) = 1/(500000 / 500117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7909 : Bounds (58493 / 250000000) (233973 / 1000000000) (Real.log (500117 / 500000)) := by
  have h := reflection_log_7909_neg
  have he : Real.log (500117 / 500000) = -Real.log (500000 / 500117) := by
    rw [show ((500117 / 500000) : ℝ) = ((500000 / 500117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7910_neg : (234027 / 1000000000) ≤ -Real.log (499883 / 500000) ∧
    -Real.log (499883 / 500000) ≤ (58507 / 250000000) := by
  have h := checkLog_sound (w := (117 / 999883)) (n := 12)
    (lo := (234027 / 1000000000)) (hi := (58507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499883) = 1/(499883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7910 : Bounds (-58507 / 250000000) (-234027 / 1000000000) (Real.log (499883 / 500000)) := by
  have h := reflection_log_7910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7911_neg : (55681681 / 500000000) ≤ -Real.log (1000000 / 1117801) ∧
    -Real.log (1000000 / 1117801) ≤ (111363363 / 1000000000) := by
  have h := checkLog_sound (w := (117801 / 2117801)) (n := 12)
    (lo := (55681681 / 500000000)) (hi := (111363363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1117801 / 1000000) = 1/(1000000 / 1117801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7911 : Bounds (55681681 / 500000000) (111363363 / 1000000000) (Real.log (1117801 / 1000000)) := by
  have h := reflection_log_7911_neg
  have he : Real.log (1117801 / 1000000) = -Real.log (1000000 / 1117801) := by
    rw [show ((1117801 / 1000000) : ℝ) = ((1000000 / 1117801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7912_neg : (15667203 / 125000000) ≤ -Real.log (882199 / 1000000) ∧
    -Real.log (882199 / 1000000) ≤ (1002701 / 8000000) := by
  have h := checkLog_sound (w := (117801 / 1882199)) (n := 12)
    (lo := (15667203 / 125000000)) (hi := (1002701 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 882199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 882199) = 1/(882199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7912 : Bounds (-1002701 / 8000000) (-15667203 / 125000000) (Real.log (882199 / 1000000)) := by
  have h := reflection_log_7912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7913_neg : (111801627 / 1000000000) ≤ -Real.log (1000000 / 1118291) ∧
    -Real.log (1000000 / 1118291) ≤ (27950407 / 250000000) := by
  have h := checkLog_sound (w := (118291 / 2118291)) (n := 12)
    (lo := (111801627 / 1000000000)) (hi := (27950407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1118291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1118291 / 1000000) = 1/(1000000 / 1118291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7913 : Bounds (111801627 / 1000000000) (27950407 / 250000000) (Real.log (1118291 / 1000000)) := by
  have h := reflection_log_7913_neg
  have he : Real.log (1118291 / 1000000) = -Real.log (1000000 / 1118291) := by
    rw [show ((1118291 / 1000000) : ℝ) = ((1000000 / 1118291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7914_neg : (125893209 / 1000000000) ≤ -Real.log (881709 / 1000000) ∧
    -Real.log (881709 / 1000000) ≤ (12589321 / 100000000) := by
  have h := checkLog_sound (w := (118291 / 1881709)) (n := 12)
    (lo := (125893209 / 1000000000)) (hi := (12589321 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 881709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 881709) = 1/(881709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7914 : Bounds (-12589321 / 100000000) (-125893209 / 1000000000) (Real.log (881709 / 1000000)) := by
  have h := reflection_log_7914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7915_neg : (7045791 / 500000000) ≤ -Real.log (986007239319 / 1000000000000) ∧
    -Real.log (986007239319 / 1000000000000) ≤ (14091583 / 1000000000) := by
  have h := checkLog_sound (w := (13992760681 / 1986007239319)) (n := 12)
    (lo := (7045791 / 500000000)) (hi := (14091583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986007239319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986007239319) = 1/(986007239319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7915 : Bounds (-14091583 / 1000000000) (-7045791 / 500000000) (Real.log (986007239319 / 1000000000000)) := by
  have h := reflection_log_7915_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7916_neg : (6987131 / 500000000) ≤ -Real.log (986122924399 / 1000000000000) ∧
    -Real.log (986122924399 / 1000000000000) ≤ (13974263 / 1000000000) := by
  have h := checkLog_sound (w := (13877075601 / 1986122924399)) (n := 12)
    (lo := (6987131 / 500000000)) (hi := (13974263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986122924399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986122924399) = 1/(986122924399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7916 : Bounds (-13974263 / 1000000000) (-6987131 / 500000000) (Real.log (986122924399 / 1000000000000)) := by
  have h := reflection_log_7916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7917_neg : (236700987 / 1000000000) ≤ -Real.log (20000000000 / 25341243869) ∧
    -Real.log (20000000000 / 25341243869) ≤ (59175247 / 250000000) := by
  have h := checkLog_sound (w := (5341243869 / 45341243869)) (n := 12)
    (lo := (236700987 / 1000000000)) (hi := (59175247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25341243869 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25341243869 / 20000000000) = 1/(20000000000 / 25341243869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7917 : Bounds (236700987 / 1000000000) (59175247 / 250000000) (Real.log (25341243869 / 20000000000)) := by
  have h := reflection_log_7917_neg
  have he : Real.log (25341243869 / 20000000000) = -Real.log (20000000000 / 25341243869) := by
    rw [show ((25341243869 / 20000000000) : ℝ) = ((20000000000 / 25341243869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7918_neg : (59423709 / 250000000) ≤ -Real.log (15625000000 / 19817532627) ∧
    -Real.log (15625000000 / 19817532627) ≤ (237694837 / 1000000000) := by
  have h := checkLog_sound (w := (4192532627 / 35442532627)) (n := 12)
    (lo := (59423709 / 250000000)) (hi := (237694837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19817532627 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19817532627 / 15625000000) = 1/(15625000000 / 19817532627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7918 : Bounds (59423709 / 250000000) (237694837 / 1000000000) (Real.log (19817532627 / 15625000000)) := by
  have h := reflection_log_7918_neg
  have he : Real.log (19817532627 / 15625000000) = -Real.log (15625000000 / 19817532627) := by
    rw [show ((19817532627 / 15625000000) : ℝ) = ((15625000000 / 19817532627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7919_neg : (475776237 / 1000000000) ≤ -Real.log (500000000000 / 804631441617) ∧
    -Real.log (500000000000 / 804631441617) ≤ (237888119 / 500000000) := by
  have h := checkLog_sound (w := (304631441617 / 1304631441617)) (n := 12)
    (lo := (475776237 / 1000000000)) (hi := (237888119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804631441617 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804631441617 / 500000000000) = 1/(500000000000 / 804631441617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7919 : Bounds (475776237 / 1000000000) (237888119 / 500000000) (Real.log (804631441617 / 500000000000)) := by
  have h := reflection_log_7919_neg
  have he : Real.log (804631441617 / 500000000000) = -Real.log (500000000000 / 804631441617) := by
    rw [show ((804631441617 / 500000000000) : ℝ) = ((500000000000 / 804631441617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7920_neg : (238417017 / 500000000) ≤ -Real.log (500000000000 / 805483028721) ∧
    -Real.log (500000000000 / 805483028721) ≤ (95366807 / 200000000) := by
  have h := checkLog_sound (w := (305483028721 / 1305483028721)) (n := 12)
    (lo := (238417017 / 500000000)) (hi := (95366807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805483028721 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805483028721 / 500000000000) = 1/(500000000000 / 805483028721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7920 : Bounds (238417017 / 500000000) (95366807 / 200000000) (Real.log (805483028721 / 500000000000)) := by
  have h := reflection_log_7920_neg
  have he : Real.log (805483028721 / 500000000000) = -Real.log (500000000000 / 805483028721) := by
    rw [show ((805483028721 / 500000000000) : ℝ) = ((500000000000 / 805483028721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7921_neg : (210666029 / 1000000000) ≤ -Real.log (2000 / 2469) ∧
    -Real.log (2000 / 2469) ≤ (21066603 / 100000000) := by
  have h := checkLog_sound (w := (469 / 4469)) (n := 12)
    (lo := (210666029 / 1000000000)) (hi := (21066603 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2469 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2469 / 2000) = 1/(2000 / 2469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7921 : Bounds (210666029 / 1000000000) (21066603 / 100000000) (Real.log (2469 / 2000)) := by
  have h := reflection_log_7921_neg
  have he : Real.log (2469 / 2000) = -Real.log (2000 / 2469) := by
    rw [show ((2469 / 2000) : ℝ) = ((2000 / 2469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7922_neg : (267226063 / 1000000000) ≤ -Real.log (1531 / 2000) ∧
    -Real.log (1531 / 2000) ≤ (16701629 / 62500000) := by
  have h := checkLog_sound (w := (469 / 3531)) (n := 12)
    (lo := (267226063 / 1000000000)) (hi := (16701629 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1531) = 1/(1531 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7922 : Bounds (-16701629 / 62500000) (-267226063 / 1000000000) (Real.log (1531 / 2000)) := by
  have h := reflection_log_7922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7923_neg : (29309 / 125000000) ≤ -Real.log (2000000 / 2000469) ∧
    -Real.log (2000000 / 2000469) ≤ (234473 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 4000469)) (n := 12)
    (lo := (29309 / 125000000)) (hi := (234473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000469 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000469 / 2000000) = 1/(2000000 / 2000469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7923 : Bounds (29309 / 125000000) (234473 / 1000000000) (Real.log (2000469 / 2000000)) := by
  have h := reflection_log_7923_neg
  have he : Real.log (2000469 / 2000000) = -Real.log (2000000 / 2000469) := by
    rw [show ((2000469 / 2000000) : ℝ) = ((2000000 / 2000469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7924_neg : (234527 / 1000000000) ≤ -Real.log (1999531 / 2000000) ∧
    -Real.log (1999531 / 2000000) ≤ (7329 / 31250000) := by
  have h := checkLog_sound (w := (469 / 3999531)) (n := 12)
    (lo := (234527 / 1000000000)) (hi := (7329 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999531) = 1/(1999531 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7924 : Bounds (-7329 / 31250000) (-234527 / 1000000000) (Real.log (1999531 / 2000000)) := by
  have h := reflection_log_7924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7925_neg : (111593251 / 1000000000) ≤ -Real.log (500000 / 559029) ∧
    -Real.log (500000 / 559029) ≤ (27898313 / 250000000) := by
  have h := checkLog_sound (w := (59029 / 1059029)) (n := 12)
    (lo := (111593251 / 1000000000)) (hi := (27898313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559029 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559029 / 500000) = 1/(500000 / 559029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7925 : Bounds (111593251 / 1000000000) (27898313 / 250000000) (Real.log (559029 / 500000)) := by
  have h := reflection_log_7925_neg
  have he : Real.log (559029 / 500000) = -Real.log (500000 / 559029) := by
    rw [show ((559029 / 500000) : ℝ) = ((500000 / 559029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7926_neg : (15703623 / 125000000) ≤ -Real.log (440971 / 500000) ∧
    -Real.log (440971 / 500000) ≤ (25125797 / 200000000) := by
  have h := checkLog_sound (w := (59029 / 940971)) (n := 12)
    (lo := (15703623 / 125000000)) (hi := (25125797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 440971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 440971) = 1/(440971 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7926 : Bounds (-25125797 / 200000000) (-15703623 / 125000000) (Real.log (440971 / 500000)) := by
  have h := reflection_log_7926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7927_neg : (22406283 / 200000000) ≤ -Real.log (250000 / 279637) ∧
    -Real.log (250000 / 279637) ≤ (14003927 / 125000000) := by
  have h := checkLog_sound (w := (29637 / 529637)) (n := 12)
    (lo := (22406283 / 200000000)) (hi := (14003927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279637 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279637 / 250000) = 1/(250000 / 279637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7927 : Bounds (22406283 / 200000000) (14003927 / 125000000) (Real.log (279637 / 250000)) := by
  have h := reflection_log_7927_neg
  have he : Real.log (279637 / 250000) = -Real.log (250000 / 279637) := by
    rw [show ((279637 / 250000) : ℝ) = ((250000 / 279637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7928_neg : (126184731 / 1000000000) ≤ -Real.log (220363 / 250000) ∧
    -Real.log (220363 / 250000) ≤ (31546183 / 250000000) := by
  have h := checkLog_sound (w := (29637 / 470363)) (n := 12)
    (lo := (126184731 / 1000000000)) (hi := (31546183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 220363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 220363) = 1/(220363 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7928 : Bounds (-31546183 / 250000000) (-126184731 / 1000000000) (Real.log (220363 / 250000)) := by
  have h := reflection_log_7928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7929_neg : (2830663 / 200000000) ≤ -Real.log (61621648231 / 62500000000) ∧
    -Real.log (61621648231 / 62500000000) ≤ (3538329 / 250000000) := by
  have h := checkLog_sound (w := (878351769 / 124121648231)) (n := 12)
    (lo := (2830663 / 200000000)) (hi := (3538329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61621648231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61621648231) = 1/(61621648231 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7929 : Bounds (-3538329 / 250000000) (-2830663 / 200000000) (Real.log (61621648231 / 62500000000)) := by
  have h := reflection_log_7929_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7930_neg : (14035733 / 1000000000) ≤ -Real.log (246515577159 / 250000000000) ∧
    -Real.log (246515577159 / 250000000000) ≤ (7017867 / 500000000) := by
  have h := checkLog_sound (w := (3484422841 / 496515577159)) (n := 12)
    (lo := (14035733 / 1000000000)) (hi := (7017867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246515577159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246515577159) = 1/(246515577159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7930 : Bounds (-7017867 / 500000000) (-14035733 / 1000000000) (Real.log (246515577159 / 250000000000)) := by
  have h := reflection_log_7930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7931_neg : (59305559 / 250000000) ≤ -Real.log (500000000000 / 633861410387) ∧
    -Real.log (500000000000 / 633861410387) ≤ (237222237 / 1000000000) := by
  have h := checkLog_sound (w := (133861410387 / 1133861410387)) (n := 12)
    (lo := (59305559 / 250000000)) (hi := (237222237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633861410387 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633861410387 / 500000000000) = 1/(500000000000 / 633861410387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7931 : Bounds (59305559 / 250000000) (237222237 / 1000000000) (Real.log (633861410387 / 500000000000)) := by
  have h := reflection_log_7931_neg
  have he : Real.log (633861410387 / 500000000000) = -Real.log (500000000000 / 633861410387) := by
    rw [show ((633861410387 / 500000000000) : ℝ) = ((500000000000 / 633861410387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7932_neg : (119108073 / 500000000) ≤ -Real.log (250000000000 / 317245862509) ∧
    -Real.log (250000000000 / 317245862509) ≤ (238216147 / 1000000000) := by
  have h := checkLog_sound (w := (67245862509 / 567245862509)) (n := 12)
    (lo := (119108073 / 500000000)) (hi := (238216147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317245862509 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317245862509 / 250000000000) = 1/(250000000000 / 317245862509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7932 : Bounds (119108073 / 500000000) (238216147 / 1000000000) (Real.log (317245862509 / 250000000000)) := by
  have h := reflection_log_7932_neg
  have he : Real.log (317245862509 / 250000000000) = -Real.log (250000000000 / 317245862509) := by
    rw [show ((317245862509 / 250000000000) : ℝ) = ((250000000000 / 317245862509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7933_neg : (238417017 / 500000000) ≤ -Real.log (6250000000 / 10068537859) ∧
    -Real.log (6250000000 / 10068537859) ≤ (95366807 / 200000000) := by
  have h := checkLog_sound (w := (3818537859 / 16318537859)) (n := 12)
    (lo := (238417017 / 500000000)) (hi := (95366807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10068537859 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10068537859 / 6250000000) = 1/(6250000000 / 10068537859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7933 : Bounds (238417017 / 500000000) (95366807 / 200000000) (Real.log (10068537859 / 6250000000)) := by
  have h := reflection_log_7933_neg
  have he : Real.log (10068537859 / 6250000000) = -Real.log (6250000000 / 10068537859) := by
    rw [show ((10068537859 / 6250000000) : ℝ) = ((6250000000 / 10068537859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7934_neg : (477892093 / 1000000000) ≤ -Real.log (500000000000 / 806335728283) ∧
    -Real.log (500000000000 / 806335728283) ≤ (238946047 / 500000000) := by
  have h := checkLog_sound (w := (306335728283 / 1306335728283)) (n := 12)
    (lo := (477892093 / 1000000000)) (hi := (238946047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((806335728283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(806335728283 / 500000000000) = 1/(500000000000 / 806335728283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7934 : Bounds (477892093 / 1000000000) (238946047 / 500000000) (Real.log (806335728283 / 500000000000)) := by
  have h := reflection_log_7934_neg
  have he : Real.log (806335728283 / 500000000000) = -Real.log (500000000000 / 806335728283) := by
    rw [show ((806335728283 / 500000000000) : ℝ) = ((500000000000 / 806335728283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7935_neg : (21107097 / 100000000) ≤ -Real.log (200 / 247) ∧
    -Real.log (200 / 247) ≤ (211070971 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 447)) (n := 12)
    (lo := (21107097 / 100000000)) (hi := (211070971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247 / 200) = 1/(200 / 247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7935 : Bounds (21107097 / 100000000) (211070971 / 1000000000) (Real.log (247 / 200)) := by
  have h := reflection_log_7935_neg
  have he : Real.log (247 / 200) = -Real.log (200 / 247) := by
    rw [show ((247 / 200) : ℝ) = ((200 / 247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0124 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7936_neg : (53575889 / 200000000) ≤ -Real.log (153 / 200) ∧
    -Real.log (153 / 200) ≤ (133939723 / 500000000) := by
  have h := checkLog_sound (w := (47 / 353)) (n := 12)
    (lo := (53575889 / 200000000)) (hi := (133939723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 153) = 1/(153 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7936 : Bounds (-133939723 / 500000000) (-53575889 / 200000000) (Real.log (153 / 200)) := by
  have h := reflection_log_7936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7937_neg : (58743 / 250000000) ≤ -Real.log (200000 / 200047) ∧
    -Real.log (200000 / 200047) ≤ (234973 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 400047)) (n := 12)
    (lo := (58743 / 250000000)) (hi := (234973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200047 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200047 / 200000) = 1/(200000 / 200047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7937 : Bounds (58743 / 250000000) (234973 / 1000000000) (Real.log (200047 / 200000)) := by
  have h := reflection_log_7937_neg
  have he : Real.log (200047 / 200000) = -Real.log (200000 / 200047) := by
    rw [show ((200047 / 200000) : ℝ) = ((200000 / 200047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7938_neg : (235027 / 1000000000) ≤ -Real.log (199953 / 200000) ∧
    -Real.log (199953 / 200000) ≤ (58757 / 250000000) := by
  have h := checkLog_sound (w := (47 / 399953)) (n := 12)
    (lo := (235027 / 1000000000)) (hi := (58757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199953) = 1/(199953 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7938 : Bounds (-58757 / 250000000) (-235027 / 1000000000) (Real.log (199953 / 200000)) := by
  have h := reflection_log_7938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7939_neg : (6988943 / 62500000) ≤ -Real.log (200000 / 223663) ∧
    -Real.log (200000 / 223663) ≤ (111823089 / 1000000000) := by
  have h := checkLog_sound (w := (23663 / 423663)) (n := 12)
    (lo := (6988943 / 62500000)) (hi := (111823089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223663 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223663 / 200000) = 1/(200000 / 223663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7939 : Bounds (6988943 / 62500000) (111823089 / 1000000000) (Real.log (223663 / 200000)) := by
  have h := reflection_log_7939_neg
  have he : Real.log (223663 / 200000) = -Real.log (200000 / 223663) := by
    rw [show ((223663 / 200000) : ℝ) = ((200000 / 223663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7940_neg : (125920429 / 1000000000) ≤ -Real.log (176337 / 200000) ∧
    -Real.log (176337 / 200000) ≤ (12592043 / 100000000) := by
  have h := checkLog_sound (w := (23663 / 376337)) (n := 12)
    (lo := (125920429 / 1000000000)) (hi := (12592043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 176337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 176337) = 1/(176337 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7940 : Bounds (-12592043 / 100000000) (-125920429 / 1000000000) (Real.log (176337 / 200000)) := by
  have h := reflection_log_7940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7941_neg : (22452409 / 200000000) ≤ -Real.log (500000 / 559403) ∧
    -Real.log (500000 / 559403) ≤ (56131023 / 500000000) := by
  have h := checkLog_sound (w := (59403 / 1059403)) (n := 12)
    (lo := (22452409 / 200000000)) (hi := (56131023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559403 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559403 / 500000) = 1/(500000 / 559403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7941 : Bounds (22452409 / 200000000) (56131023 / 500000000) (Real.log (559403 / 500000)) := by
  have h := reflection_log_7941_neg
  have he : Real.log (559403 / 500000) = -Real.log (500000 / 559403) := by
    rw [show ((559403 / 500000) : ℝ) = ((500000 / 559403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7942_neg : (3952421 / 31250000) ≤ -Real.log (440597 / 500000) ∧
    -Real.log (440597 / 500000) ≤ (126477473 / 1000000000) := by
  have h := checkLog_sound (w := (59403 / 940597)) (n := 12)
    (lo := (3952421 / 31250000)) (hi := (126477473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 440597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 440597) = 1/(440597 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7942 : Bounds (-126477473 / 1000000000) (-3952421 / 31250000) (Real.log (440597 / 500000)) := by
  have h := reflection_log_7942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7943_neg : (14215427 / 1000000000) ≤ -Real.log (246471283591 / 250000000000) ∧
    -Real.log (246471283591 / 250000000000) ≤ (3553857 / 250000000) := by
  have h := checkLog_sound (w := (3528716409 / 496471283591)) (n := 12)
    (lo := (14215427 / 1000000000)) (hi := (3553857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246471283591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246471283591) = 1/(246471283591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7943 : Bounds (-3553857 / 250000000) (-14215427 / 1000000000) (Real.log (246471283591 / 250000000000)) := by
  have h := reflection_log_7943_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7944_neg : (14097341 / 1000000000) ≤ -Real.log (39440062431 / 40000000000) ∧
    -Real.log (39440062431 / 40000000000) ≤ (7048671 / 500000000) := by
  have h := checkLog_sound (w := (559937569 / 79440062431)) (n := 12)
    (lo := (14097341 / 1000000000)) (hi := (7048671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39440062431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39440062431) = 1/(39440062431 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7944 : Bounds (-7048671 / 500000000) (-14097341 / 1000000000) (Real.log (39440062431 / 40000000000)) := by
  have h := reflection_log_7944_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7945_neg : (237743517 / 1000000000) ≤ -Real.log (250000000000 / 317095958307) ∧
    -Real.log (250000000000 / 317095958307) ≤ (118871759 / 500000000) := by
  have h := checkLog_sound (w := (67095958307 / 567095958307)) (n := 12)
    (lo := (237743517 / 1000000000)) (hi := (118871759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317095958307 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317095958307 / 250000000000) = 1/(250000000000 / 317095958307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7945 : Bounds (237743517 / 1000000000) (118871759 / 500000000) (Real.log (317095958307 / 250000000000)) := by
  have h := reflection_log_7945_neg
  have he : Real.log (317095958307 / 250000000000) = -Real.log (250000000000 / 317095958307) := by
    rw [show ((317095958307 / 250000000000) : ℝ) = ((250000000000 / 317095958307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7946_neg : (119369759 / 500000000) ≤ -Real.log (250000000000 / 317411943341) ∧
    -Real.log (250000000000 / 317411943341) ≤ (238739519 / 1000000000) := by
  have h := checkLog_sound (w := (67411943341 / 567411943341)) (n := 12)
    (lo := (119369759 / 500000000)) (hi := (238739519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317411943341 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317411943341 / 250000000000) = 1/(250000000000 / 317411943341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7946 : Bounds (119369759 / 500000000) (238739519 / 1000000000) (Real.log (317411943341 / 250000000000)) := by
  have h := reflection_log_7946_neg
  have he : Real.log (317411943341 / 250000000000) = -Real.log (250000000000 / 317411943341) := by
    rw [show ((317411943341 / 250000000000) : ℝ) = ((250000000000 / 317411943341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7947_neg : (477892093 / 1000000000) ≤ -Real.log (250000000000 / 403167864141) ∧
    -Real.log (250000000000 / 403167864141) ≤ (238946047 / 500000000) := by
  have h := checkLog_sound (w := (153167864141 / 653167864141)) (n := 12)
    (lo := (477892093 / 1000000000)) (hi := (238946047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403167864141 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403167864141 / 250000000000) = 1/(250000000000 / 403167864141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7947 : Bounds (477892093 / 1000000000) (238946047 / 500000000) (Real.log (403167864141 / 250000000000)) := by
  have h := reflection_log_7947_neg
  have he : Real.log (403167864141 / 250000000000) = -Real.log (250000000000 / 403167864141) := by
    rw [show ((403167864141 / 250000000000) : ℝ) = ((250000000000 / 403167864141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7948_neg : (95790083 / 200000000) ≤ -Real.log (125000000000 / 201797385621) ∧
    -Real.log (125000000000 / 201797385621) ≤ (29934401 / 62500000) := by
  have h := checkLog_sound (w := (76797385621 / 326797385621)) (n := 12)
    (lo := (95790083 / 200000000)) (hi := (29934401 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201797385621 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201797385621 / 125000000000) = 1/(125000000000 / 201797385621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7948 : Bounds (95790083 / 200000000) (29934401 / 62500000) (Real.log (201797385621 / 125000000000)) := by
  have h := reflection_log_7948_neg
  have he : Real.log (201797385621 / 125000000000) = -Real.log (125000000000 / 201797385621) := by
    rw [show ((201797385621 / 125000000000) : ℝ) = ((125000000000 / 201797385621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7949_neg : (105737873 / 500000000) ≤ -Real.log (2000 / 2471) ∧
    -Real.log (2000 / 2471) ≤ (211475747 / 1000000000) := by
  have h := checkLog_sound (w := (471 / 4471)) (n := 12)
    (lo := (105737873 / 500000000)) (hi := (211475747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2471 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2471 / 2000) = 1/(2000 / 2471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7949 : Bounds (105737873 / 500000000) (211475747 / 1000000000) (Real.log (2471 / 2000)) := by
  have h := reflection_log_7949_neg
  have he : Real.log (2471 / 2000) = -Real.log (2000 / 2471) := by
    rw [show ((2471 / 2000) : ℝ) = ((2000 / 2471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7950_neg : (268533253 / 1000000000) ≤ -Real.log (1529 / 2000) ∧
    -Real.log (1529 / 2000) ≤ (134266627 / 500000000) := by
  have h := checkLog_sound (w := (471 / 3529)) (n := 12)
    (lo := (268533253 / 1000000000)) (hi := (134266627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1529) = 1/(1529 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7950 : Bounds (-134266627 / 500000000) (-268533253 / 1000000000) (Real.log (1529 / 2000)) := by
  have h := reflection_log_7950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7951_neg : (14717 / 62500000) ≤ -Real.log (2000000 / 2000471) ∧
    -Real.log (2000000 / 2000471) ≤ (235473 / 1000000000) := by
  have h := checkLog_sound (w := (471 / 4000471)) (n := 12)
    (lo := (14717 / 62500000)) (hi := (235473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000471 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000471 / 2000000) = 1/(2000000 / 2000471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7951 : Bounds (14717 / 62500000) (235473 / 1000000000) (Real.log (2000471 / 2000000)) := by
  have h := reflection_log_7951_neg
  have he : Real.log (2000471 / 2000000) = -Real.log (2000000 / 2000471) := by
    rw [show ((2000471 / 2000000) : ℝ) = ((2000000 / 2000471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7952_neg : (235527 / 1000000000) ≤ -Real.log (1999529 / 2000000) ∧
    -Real.log (1999529 / 2000000) ≤ (29441 / 125000000) := by
  have h := checkLog_sound (w := (471 / 3999529)) (n := 12)
    (lo := (235527 / 1000000000)) (hi := (29441 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999529) = 1/(1999529 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7952 : Bounds (-29441 / 125000000) (-235527 / 1000000000) (Real.log (1999529 / 2000000)) := by
  have h := reflection_log_7952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7953_neg : (22410753 / 200000000) ≤ -Real.log (1000000 / 1118573) ∧
    -Real.log (1000000 / 1118573) ≤ (56026883 / 500000000) := by
  have h := checkLog_sound (w := (118573 / 2118573)) (n := 12)
    (lo := (22410753 / 200000000)) (hi := (56026883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1118573 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1118573 / 1000000) = 1/(1000000 / 1118573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7953 : Bounds (22410753 / 200000000) (56026883 / 500000000) (Real.log (1118573 / 1000000)) := by
  have h := reflection_log_7953_neg
  have he : Real.log (1118573 / 1000000) = -Real.log (1000000 / 1118573) := by
    rw [show ((1118573 / 1000000) : ℝ) = ((1000000 / 1118573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7954_neg : (126213093 / 1000000000) ≤ -Real.log (881427 / 1000000) ∧
    -Real.log (881427 / 1000000) ≤ (63106547 / 500000000) := by
  have h := checkLog_sound (w := (118573 / 1881427)) (n := 12)
    (lo := (126213093 / 1000000000)) (hi := (63106547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 881427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 881427) = 1/(881427 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7954 : Bounds (-63106547 / 500000000) (-126213093 / 1000000000) (Real.log (881427 / 1000000)) := by
  have h := reflection_log_7954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7955_neg : (112492621 / 1000000000) ≤ -Real.log (125000 / 139883) ∧
    -Real.log (125000 / 139883) ≤ (56246311 / 500000000) := by
  have h := checkLog_sound (w := (14883 / 264883)) (n := 12)
    (lo := (112492621 / 1000000000)) (hi := (56246311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139883 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139883 / 125000) = 1/(125000 / 139883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7955 : Bounds (112492621 / 1000000000) (56246311 / 500000000) (Real.log (139883 / 125000)) := by
  have h := reflection_log_7955_neg
  have he : Real.log (139883 / 125000) = -Real.log (125000 / 139883) := by
    rw [show ((139883 / 125000) : ℝ) = ((125000 / 139883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7956_neg : (1267703 / 10000000) ≤ -Real.log (110117 / 125000) ∧
    -Real.log (110117 / 125000) ≤ (126770301 / 1000000000) := by
  have h := checkLog_sound (w := (14883 / 235117)) (n := 12)
    (lo := (1267703 / 10000000)) (hi := (126770301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 110117) = 1/(110117 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7956 : Bounds (-126770301 / 1000000000) (-1267703 / 10000000) (Real.log (110117 / 125000)) := by
  have h := reflection_log_7956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7957_neg : (7138839 / 500000000) ≤ -Real.log (15403496311 / 15625000000) ∧
    -Real.log (15403496311 / 15625000000) ≤ (14277679 / 1000000000) := by
  have h := checkLog_sound (w := (221503689 / 31028496311)) (n := 12)
    (lo := (7138839 / 500000000)) (hi := (14277679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15403496311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15403496311) = 1/(15403496311 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7957 : Bounds (-14277679 / 1000000000) (-7138839 / 500000000) (Real.log (15403496311 / 15625000000)) := by
  have h := reflection_log_7957_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7958_neg : (442479 / 31250000) ≤ -Real.log (985940443671 / 1000000000000) ∧
    -Real.log (985940443671 / 1000000000000) ≤ (14159329 / 1000000000) := by
  have h := checkLog_sound (w := (14059556329 / 1985940443671)) (n := 12)
    (lo := (442479 / 31250000)) (hi := (14159329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985940443671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985940443671) = 1/(985940443671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7958 : Bounds (-14159329 / 1000000000) (-442479 / 31250000) (Real.log (985940443671 / 1000000000000)) := by
  have h := reflection_log_7958_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7959_neg : (238266859 / 1000000000) ≤ -Real.log (125000000000 / 158630975679) ∧
    -Real.log (125000000000 / 158630975679) ≤ (11913343 / 50000000) := by
  have h := checkLog_sound (w := (33630975679 / 283630975679)) (n := 12)
    (lo := (238266859 / 1000000000)) (hi := (11913343 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158630975679 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158630975679 / 125000000000) = 1/(125000000000 / 158630975679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7959 : Bounds (238266859 / 1000000000) (11913343 / 50000000) (Real.log (158630975679 / 125000000000)) := by
  have h := reflection_log_7959_neg
  have he : Real.log (158630975679 / 125000000000) = -Real.log (125000000000 / 158630975679) := by
    rw [show ((158630975679 / 125000000000) : ℝ) = ((125000000000 / 158630975679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7960_neg : (119631461 / 500000000) ≤ -Real.log (250000000000 / 317578121453) ∧
    -Real.log (250000000000 / 317578121453) ≤ (239262923 / 1000000000) := by
  have h := checkLog_sound (w := (67578121453 / 567578121453)) (n := 12)
    (lo := (119631461 / 500000000)) (hi := (239262923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317578121453 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317578121453 / 250000000000) = 1/(250000000000 / 317578121453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7960 : Bounds (119631461 / 500000000) (239262923 / 1000000000) (Real.log (317578121453 / 250000000000)) := by
  have h := reflection_log_7960_neg
  have he : Real.log (317578121453 / 250000000000) = -Real.log (250000000000 / 317578121453) := by
    rw [show ((317578121453 / 250000000000) : ℝ) = ((250000000000 / 317578121453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7961_neg : (95790083 / 200000000) ≤ -Real.log (500000000000 / 807189542483) ∧
    -Real.log (500000000000 / 807189542483) ≤ (29934401 / 62500000) := by
  have h := checkLog_sound (w := (307189542483 / 1307189542483)) (n := 12)
    (lo := (95790083 / 200000000)) (hi := (29934401 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807189542483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807189542483 / 500000000000) = 1/(500000000000 / 807189542483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7961 : Bounds (95790083 / 200000000) (29934401 / 62500000) (Real.log (807189542483 / 500000000000)) := by
  have h := reflection_log_7961_neg
  have he : Real.log (807189542483 / 500000000000) = -Real.log (500000000000 / 807189542483) := by
    rw [show ((807189542483 / 500000000000) : ℝ) = ((500000000000 / 807189542483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7962_neg : (480009 / 1000000) ≤ -Real.log (500000000000 / 808044473513) ∧
    -Real.log (500000000000 / 808044473513) ≤ (480009001 / 1000000000) := by
  have h := checkLog_sound (w := (308044473513 / 1308044473513)) (n := 12)
    (lo := (480009 / 1000000)) (hi := (480009001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808044473513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808044473513 / 500000000000) = 1/(500000000000 / 808044473513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7962 : Bounds (480009 / 1000000) (480009001 / 1000000000) (Real.log (808044473513 / 500000000000)) := by
  have h := reflection_log_7962_neg
  have he : Real.log (808044473513 / 500000000000) = -Real.log (500000000000 / 808044473513) := by
    rw [show ((808044473513 / 500000000000) : ℝ) = ((500000000000 / 808044473513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7963_neg : (211880359 / 1000000000) ≤ -Real.log (250 / 309) ∧
    -Real.log (250 / 309) ≤ (5297009 / 25000000) := by
  have h := checkLog_sound (w := (59 / 559)) (n := 12)
    (lo := (211880359 / 1000000000)) (hi := (5297009 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309 / 250) = 1/(250 / 309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7963 : Bounds (211880359 / 1000000000) (5297009 / 25000000) (Real.log (309 / 250)) := by
  have h := reflection_log_7963_neg
  have he : Real.log (309 / 250) = -Real.log (250 / 309) := by
    rw [show ((309 / 250) : ℝ) = ((250 / 309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7964_neg : (269187489 / 1000000000) ≤ -Real.log (191 / 250) ∧
    -Real.log (191 / 250) ≤ (26918749 / 100000000) := by
  have h := checkLog_sound (w := (59 / 441)) (n := 12)
    (lo := (269187489 / 1000000000)) (hi := (26918749 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 191) = 1/(191 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7964 : Bounds (-26918749 / 100000000) (-269187489 / 1000000000) (Real.log (191 / 250)) := by
  have h := reflection_log_7964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7965_neg : (58993 / 250000000) ≤ -Real.log (250000 / 250059) ∧
    -Real.log (250000 / 250059) ≤ (235973 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 500059)) (n := 12)
    (lo := (58993 / 250000000)) (hi := (235973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250059 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250059 / 250000) = 1/(250000 / 250059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7965 : Bounds (58993 / 250000000) (235973 / 1000000000) (Real.log (250059 / 250000)) := by
  have h := reflection_log_7965_neg
  have he : Real.log (250059 / 250000) = -Real.log (250000 / 250059) := by
    rw [show ((250059 / 250000) : ℝ) = ((250000 / 250059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7966_neg : (236027 / 1000000000) ≤ -Real.log (249941 / 250000) ∧
    -Real.log (249941 / 250000) ≤ (59007 / 250000000) := by
  have h := checkLog_sound (w := (59 / 499941)) (n := 12)
    (lo := (236027 / 1000000000)) (hi := (59007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249941) = 1/(249941 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7966 : Bounds (-59007 / 250000000) (-236027 / 1000000000) (Real.log (249941 / 250000)) := by
  have h := reflection_log_7966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7967_neg : (14035437 / 125000000) ≤ -Real.log (100000 / 111883) ∧
    -Real.log (100000 / 111883) ≤ (112283497 / 1000000000) := by
  have h := checkLog_sound (w := (11883 / 211883)) (n := 12)
    (lo := (14035437 / 125000000)) (hi := (112283497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111883 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111883 / 100000) = 1/(100000 / 111883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7967 : Bounds (14035437 / 125000000) (112283497 / 1000000000) (Real.log (111883 / 100000)) := by
  have h := reflection_log_7967_neg
  have he : Real.log (111883 / 100000) = -Real.log (100000 / 111883) := by
    rw [show ((111883 / 100000) : ℝ) = ((100000 / 111883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7968_neg : (126504709 / 1000000000) ≤ -Real.log (88117 / 100000) ∧
    -Real.log (88117 / 100000) ≤ (12650471 / 100000000) := by
  have h := checkLog_sound (w := (11883 / 188117)) (n := 12)
    (lo := (126504709 / 1000000000)) (hi := (12650471 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 88117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 88117) = 1/(88117 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7968 : Bounds (-12650471 / 100000000) (-126504709 / 1000000000) (Real.log (88117 / 100000)) := by
  have h := reflection_log_7968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7969_neg : (14090393 / 125000000) ≤ -Real.log (500000 / 559661) ∧
    -Real.log (500000 / 559661) ≤ (22544629 / 200000000) := by
  have h := checkLog_sound (w := (59661 / 1059661)) (n := 12)
    (lo := (14090393 / 125000000)) (hi := (22544629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559661 / 500000) = 1/(500000 / 559661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7969 : Bounds (14090393 / 125000000) (22544629 / 200000000) (Real.log (559661 / 500000)) := by
  have h := reflection_log_7969_neg
  have he : Real.log (559661 / 500000) = -Real.log (500000 / 559661) := by
    rw [show ((559661 / 500000) : ℝ) = ((500000 / 559661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7970_neg : (127063213 / 1000000000) ≤ -Real.log (440339 / 500000) ∧
    -Real.log (440339 / 500000) ≤ (63531607 / 500000000) := by
  have h := checkLog_sound (w := (59661 / 940339)) (n := 12)
    (lo := (127063213 / 1000000000)) (hi := (63531607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 440339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 440339) = 1/(440339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7970 : Bounds (-63531607 / 500000000) (-127063213 / 1000000000) (Real.log (440339 / 500000)) := by
  have h := reflection_log_7970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7971_neg : (3585017 / 250000000) ≤ -Real.log (246440565079 / 250000000000) ∧
    -Real.log (246440565079 / 250000000000) ≤ (14340069 / 1000000000) := by
  have h := checkLog_sound (w := (3559434921 / 496440565079)) (n := 12)
    (lo := (3585017 / 250000000)) (hi := (14340069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246440565079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246440565079) = 1/(246440565079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7971 : Bounds (-14340069 / 1000000000) (-3585017 / 250000000) (Real.log (246440565079 / 250000000000)) := by
  have h := reflection_log_7971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7972_neg : (3555303 / 250000000) ≤ -Real.log (9858794311 / 10000000000) ∧
    -Real.log (9858794311 / 10000000000) ≤ (14221213 / 1000000000) := by
  have h := checkLog_sound (w := (141205689 / 19858794311)) (n := 12)
    (lo := (3555303 / 250000000)) (hi := (14221213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9858794311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9858794311) = 1/(9858794311 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7972 : Bounds (-14221213 / 1000000000) (-3555303 / 250000000) (Real.log (9858794311 / 10000000000)) := by
  have h := reflection_log_7972_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7973_neg : (47757641 / 200000000) ≤ -Real.log (7812500000 / 9919606177) ∧
    -Real.log (7812500000 / 9919606177) ≤ (119394103 / 500000000) := by
  have h := checkLog_sound (w := (2107106177 / 17732106177)) (n := 12)
    (lo := (47757641 / 200000000)) (hi := (119394103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9919606177 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9919606177 / 7812500000) = 1/(7812500000 / 9919606177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7973 : Bounds (47757641 / 200000000) (119394103 / 500000000) (Real.log (9919606177 / 7812500000)) := by
  have h := reflection_log_7973_neg
  have he : Real.log (9919606177 / 7812500000) = -Real.log (7812500000 / 9919606177) := by
    rw [show ((9919606177 / 7812500000) : ℝ) = ((7812500000 / 9919606177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7974_neg : (119893179 / 500000000) ≤ -Real.log (250000000000 / 317744396931) ∧
    -Real.log (250000000000 / 317744396931) ≤ (239786359 / 1000000000) := by
  have h := checkLog_sound (w := (67744396931 / 567744396931)) (n := 12)
    (lo := (119893179 / 500000000)) (hi := (239786359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317744396931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317744396931 / 250000000000) = 1/(250000000000 / 317744396931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7974 : Bounds (119893179 / 500000000) (239786359 / 1000000000) (Real.log (317744396931 / 250000000000)) := by
  have h := reflection_log_7974_neg
  have he : Real.log (317744396931 / 250000000000) = -Real.log (250000000000 / 317744396931) := by
    rw [show ((317744396931 / 250000000000) : ℝ) = ((250000000000 / 317744396931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7975_neg : (480009 / 1000000) ≤ -Real.log (62500000000 / 101005559189) ∧
    -Real.log (62500000000 / 101005559189) ≤ (480009001 / 1000000000) := by
  have h := checkLog_sound (w := (38505559189 / 163505559189)) (n := 12)
    (lo := (480009 / 1000000)) (hi := (480009001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101005559189 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101005559189 / 62500000000) = 1/(62500000000 / 101005559189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7975 : Bounds (480009 / 1000000) (480009001 / 1000000000) (Real.log (101005559189 / 62500000000)) := by
  have h := reflection_log_7975_neg
  have he : Real.log (101005559189 / 62500000000) = -Real.log (62500000000 / 101005559189) := by
    rw [show ((101005559189 / 62500000000) : ℝ) = ((62500000000 / 101005559189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7976_neg : (60133481 / 125000000) ≤ -Real.log (500000000000 / 808900523561) ∧
    -Real.log (500000000000 / 808900523561) ≤ (481067849 / 1000000000) := by
  have h := checkLog_sound (w := (308900523561 / 1308900523561)) (n := 12)
    (lo := (60133481 / 125000000)) (hi := (481067849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808900523561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808900523561 / 500000000000) = 1/(500000000000 / 808900523561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7976 : Bounds (60133481 / 125000000) (481067849 / 1000000000) (Real.log (808900523561 / 500000000000)) := by
  have h := reflection_log_7976_neg
  have he : Real.log (808900523561 / 500000000000) = -Real.log (500000000000 / 808900523561) := by
    rw [show ((808900523561 / 500000000000) : ℝ) = ((500000000000 / 808900523561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7977_neg : (212284807 / 1000000000) ≤ -Real.log (2000 / 2473) ∧
    -Real.log (2000 / 2473) ≤ (26535601 / 125000000) := by
  have h := checkLog_sound (w := (473 / 4473)) (n := 12)
    (lo := (212284807 / 1000000000)) (hi := (26535601 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2473 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2473 / 2000) = 1/(2000 / 2473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7977 : Bounds (212284807 / 1000000000) (26535601 / 125000000) (Real.log (2473 / 2000)) := by
  have h := reflection_log_7977_neg
  have he : Real.log (2473 / 2000) = -Real.log (2000 / 2473) := by
    rw [show ((2473 / 2000) : ℝ) = ((2000 / 2473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7978_neg : (134921077 / 500000000) ≤ -Real.log (1527 / 2000) ∧
    -Real.log (1527 / 2000) ≤ (53968431 / 200000000) := by
  have h := checkLog_sound (w := (473 / 3527)) (n := 12)
    (lo := (134921077 / 500000000)) (hi := (53968431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1527) = 1/(1527 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7978 : Bounds (-53968431 / 200000000) (-134921077 / 500000000) (Real.log (1527 / 2000)) := by
  have h := reflection_log_7978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7979_neg : (29559 / 125000000) ≤ -Real.log (2000000 / 2000473) ∧
    -Real.log (2000000 / 2000473) ≤ (236473 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 4000473)) (n := 12)
    (lo := (29559 / 125000000)) (hi := (236473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000473 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000473 / 2000000) = 1/(2000000 / 2000473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7979 : Bounds (29559 / 125000000) (236473 / 1000000000) (Real.log (2000473 / 2000000)) := by
  have h := reflection_log_7979_neg
  have he : Real.log (2000473 / 2000000) = -Real.log (2000000 / 2000473) := by
    rw [show ((2000473 / 2000000) : ℝ) = ((2000000 / 2000473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7980_neg : (236527 / 1000000000) ≤ -Real.log (1999527 / 2000000) ∧
    -Real.log (1999527 / 2000000) ≤ (14783 / 62500000) := by
  have h := checkLog_sound (w := (473 / 3999527)) (n := 12)
    (lo := (236527 / 1000000000)) (hi := (14783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999527) = 1/(1999527 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7980 : Bounds (-14783 / 62500000) (-236527 / 1000000000) (Real.log (1999527 / 2000000)) := by
  have h := reflection_log_7980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7981_neg : (112514067 / 1000000000) ≤ -Real.log (62500 / 69943) ∧
    -Real.log (62500 / 69943) ≤ (28128517 / 250000000) := by
  have h := checkLog_sound (w := (7443 / 132443)) (n := 12)
    (lo := (112514067 / 1000000000)) (hi := (28128517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69943 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69943 / 62500) = 1/(62500 / 69943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7981 : Bounds (112514067 / 1000000000) (28128517 / 250000000) (Real.log (69943 / 62500)) := by
  have h := reflection_log_7981_neg
  have he : Real.log (69943 / 62500) = -Real.log (62500 / 69943) := by
    rw [show ((69943 / 62500) : ℝ) = ((62500 / 69943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7982_neg : (15849693 / 125000000) ≤ -Real.log (55057 / 62500) ∧
    -Real.log (55057 / 62500) ≤ (25359509 / 200000000) := by
  have h := checkLog_sound (w := (7443 / 117557)) (n := 12)
    (lo := (15849693 / 125000000)) (hi := (25359509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 55057) = 1/(55057 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7982 : Bounds (-25359509 / 200000000) (-15849693 / 125000000) (Real.log (55057 / 62500)) := by
  have h := reflection_log_7982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7983_neg : (56476807 / 500000000) ≤ -Real.log (50000 / 55979) ∧
    -Real.log (50000 / 55979) ≤ (22590723 / 200000000) := by
  have h := checkLog_sound (w := (5979 / 105979)) (n := 12)
    (lo := (56476807 / 500000000)) (hi := (22590723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55979 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55979 / 50000) = 1/(50000 / 55979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7983 : Bounds (56476807 / 500000000) (22590723 / 200000000) (Real.log (55979 / 50000)) := by
  have h := reflection_log_7983_neg
  have he : Real.log (55979 / 50000) = -Real.log (50000 / 55979) := by
    rw [show ((55979 / 50000) : ℝ) = ((50000 / 55979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7984_neg : (31839053 / 250000000) ≤ -Real.log (44021 / 50000) ∧
    -Real.log (44021 / 50000) ≤ (127356213 / 1000000000) := by
  have h := checkLog_sound (w := (5979 / 94021)) (n := 12)
    (lo := (31839053 / 250000000)) (hi := (127356213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44021) = 1/(44021 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7984 : Bounds (-127356213 / 1000000000) (-31839053 / 250000000) (Real.log (44021 / 50000)) := by
  have h := reflection_log_7984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7985_neg : (14402597 / 1000000000) ≤ -Real.log (2464251559 / 2500000000) ∧
    -Real.log (2464251559 / 2500000000) ≤ (7201299 / 500000000) := by
  have h := checkLog_sound (w := (35748441 / 4964251559)) (n := 12)
    (lo := (14402597 / 1000000000)) (hi := (7201299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2464251559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2464251559) = 1/(2464251559 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7985 : Bounds (-7201299 / 500000000) (-14402597 / 1000000000) (Real.log (2464251559 / 2500000000)) := by
  have h := reflection_log_7985_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7986_neg : (3570869 / 250000000) ≤ -Real.log (3850851751 / 3906250000) ∧
    -Real.log (3850851751 / 3906250000) ≤ (14283477 / 1000000000) := by
  have h := checkLog_sound (w := (55398249 / 7757101751)) (n := 12)
    (lo := (3570869 / 250000000)) (hi := (14283477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3850851751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3850851751) = 1/(3850851751 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7986 : Bounds (-14283477 / 1000000000) (-3570869 / 250000000) (Real.log (3850851751 / 3906250000)) := by
  have h := reflection_log_7986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7987_neg : (59827903 / 250000000) ≤ -Real.log (25000000000 / 31759358483) ∧
    -Real.log (25000000000 / 31759358483) ≤ (239311613 / 1000000000) := by
  have h := checkLog_sound (w := (6759358483 / 56759358483)) (n := 12)
    (lo := (59827903 / 250000000)) (hi := (239311613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31759358483 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31759358483 / 25000000000) = 1/(25000000000 / 31759358483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7987 : Bounds (59827903 / 250000000) (239311613 / 1000000000) (Real.log (31759358483 / 25000000000)) := by
  have h := reflection_log_7987_neg
  have he : Real.log (31759358483 / 25000000000) = -Real.log (25000000000 / 31759358483) := by
    rw [show ((31759358483 / 25000000000) : ℝ) = ((25000000000 / 31759358483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7988_neg : (240309827 / 1000000000) ≤ -Real.log (12500000000 / 15895538493) ∧
    -Real.log (12500000000 / 15895538493) ≤ (60077457 / 250000000) := by
  have h := checkLog_sound (w := (3395538493 / 28395538493)) (n := 12)
    (lo := (240309827 / 1000000000)) (hi := (60077457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15895538493 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15895538493 / 12500000000) = 1/(12500000000 / 15895538493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7988 : Bounds (240309827 / 1000000000) (60077457 / 250000000) (Real.log (15895538493 / 12500000000)) := by
  have h := reflection_log_7988_neg
  have he : Real.log (15895538493 / 12500000000) = -Real.log (12500000000 / 15895538493) := by
    rw [show ((15895538493 / 12500000000) : ℝ) = ((12500000000 / 15895538493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7989_neg : (60133481 / 125000000) ≤ -Real.log (12500000000 / 20222513089) ∧
    -Real.log (12500000000 / 20222513089) ≤ (481067849 / 1000000000) := by
  have h := checkLog_sound (w := (7722513089 / 32722513089)) (n := 12)
    (lo := (60133481 / 125000000)) (hi := (481067849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20222513089 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20222513089 / 12500000000) = 1/(12500000000 / 20222513089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7989 : Bounds (60133481 / 125000000) (481067849 / 1000000000) (Real.log (20222513089 / 12500000000)) := by
  have h := reflection_log_7989_neg
  have he : Real.log (20222513089 / 12500000000) = -Real.log (12500000000 / 20222513089) := by
    rw [show ((20222513089 / 12500000000) : ℝ) = ((12500000000 / 20222513089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7990_neg : (241063481 / 500000000) ≤ -Real.log (500000000000 / 809757694827) ∧
    -Real.log (500000000000 / 809757694827) ≤ (482126963 / 1000000000) := by
  have h := checkLog_sound (w := (309757694827 / 1309757694827)) (n := 12)
    (lo := (241063481 / 500000000)) (hi := (482126963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809757694827 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(809757694827 / 500000000000) = 1/(500000000000 / 809757694827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7990 : Bounds (241063481 / 500000000) (482126963 / 1000000000) (Real.log (809757694827 / 500000000000)) := by
  have h := reflection_log_7990_neg
  have he : Real.log (809757694827 / 500000000000) = -Real.log (500000000000 / 809757694827) := by
    rw [show ((809757694827 / 500000000000) : ℝ) = ((500000000000 / 809757694827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7991_neg : (212689093 / 1000000000) ≤ -Real.log (1000 / 1237) ∧
    -Real.log (1000 / 1237) ≤ (106344547 / 500000000) := by
  have h := checkLog_sound (w := (237 / 2237)) (n := 12)
    (lo := (212689093 / 1000000000)) (hi := (106344547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1237 / 1000) = 1/(1000 / 1237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7991 : Bounds (212689093 / 1000000000) (106344547 / 500000000) (Real.log (1237 / 1000)) := by
  have h := reflection_log_7991_neg
  have he : Real.log (1237 / 1000) = -Real.log (1000 / 1237) := by
    rw [show ((1237 / 1000) : ℝ) = ((1000 / 1237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7992_neg : (270497247 / 1000000000) ≤ -Real.log (763 / 1000) ∧
    -Real.log (763 / 1000) ≤ (8453039 / 31250000) := by
  have h := checkLog_sound (w := (237 / 1763)) (n := 12)
    (lo := (270497247 / 1000000000)) (hi := (8453039 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 763) = 1/(763 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7992 : Bounds (-8453039 / 31250000) (-270497247 / 1000000000) (Real.log (763 / 1000)) := by
  have h := reflection_log_7992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7993_neg : (236971 / 1000000000) ≤ -Real.log (1000000 / 1000237) ∧
    -Real.log (1000000 / 1000237) ≤ (59243 / 250000000) := by
  have h := checkLog_sound (w := (237 / 2000237)) (n := 12)
    (lo := (236971 / 1000000000)) (hi := (59243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000237 / 1000000) = 1/(1000000 / 1000237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7993 : Bounds (236971 / 1000000000) (59243 / 250000000) (Real.log (1000237 / 1000000)) := by
  have h := reflection_log_7993_neg
  have he : Real.log (1000237 / 1000000) = -Real.log (1000000 / 1000237) := by
    rw [show ((1000237 / 1000000) : ℝ) = ((1000000 / 1000237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7994_neg : (59257 / 250000000) ≤ -Real.log (999763 / 1000000) ∧
    -Real.log (999763 / 1000000) ≤ (237029 / 1000000000) := by
  have h := checkLog_sound (w := (237 / 1999763)) (n := 12)
    (lo := (59257 / 250000000)) (hi := (237029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999763) = 1/(999763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7994 : Bounds (-237029 / 1000000000) (-59257 / 250000000) (Real.log (999763 / 1000000)) := by
  have h := reflection_log_7994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7995_neg : (28185923 / 250000000) ≤ -Real.log (200000 / 223869) ∧
    -Real.log (200000 / 223869) ≤ (112743693 / 1000000000) := by
  have h := checkLog_sound (w := (23869 / 423869)) (n := 12)
    (lo := (28185923 / 250000000)) (hi := (112743693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223869 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223869 / 200000) = 1/(200000 / 223869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7995 : Bounds (28185923 / 250000000) (112743693 / 1000000000) (Real.log (223869 / 200000)) := by
  have h := reflection_log_7995_neg
  have he : Real.log (223869 / 200000) = -Real.log (200000 / 223869) := by
    rw [show ((223869 / 200000) : ℝ) = ((200000 / 223869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7996_neg : (12708933 / 100000000) ≤ -Real.log (176131 / 200000) ∧
    -Real.log (176131 / 200000) ≤ (127089331 / 1000000000) := by
  have h := checkLog_sound (w := (23869 / 376131)) (n := 12)
    (lo := (12708933 / 100000000)) (hi := (127089331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 176131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 176131) = 1/(176131 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7996 : Bounds (-127089331 / 1000000000) (-12708933 / 100000000) (Real.log (176131 / 200000)) := by
  have h := reflection_log_7996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7997_neg : (113184031 / 1000000000) ≤ -Real.log (500000 / 559919) ∧
    -Real.log (500000 / 559919) ≤ (3537001 / 31250000) := by
  have h := checkLog_sound (w := (59919 / 1059919)) (n := 12)
    (lo := (113184031 / 1000000000)) (hi := (3537001 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559919 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559919 / 500000) = 1/(500000 / 559919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7997 : Bounds (113184031 / 1000000000) (3537001 / 31250000) (Real.log (559919 / 500000)) := by
  have h := reflection_log_7997_neg
  have he : Real.log (559919 / 500000) = -Real.log (500000 / 559919) := by
    rw [show ((559919 / 500000) : ℝ) = ((500000 / 559919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7998_neg : (127649297 / 1000000000) ≤ -Real.log (440081 / 500000) ∧
    -Real.log (440081 / 500000) ≤ (63824649 / 500000000) := by
  have h := checkLog_sound (w := (59919 / 940081)) (n := 12)
    (lo := (127649297 / 1000000000)) (hi := (63824649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 440081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 440081) = 1/(440081 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7998 : Bounds (-63824649 / 500000000) (-127649297 / 1000000000) (Real.log (440081 / 500000)) := by
  have h := reflection_log_7998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7999_neg : (2893053 / 200000000) ≤ -Real.log (246409713439 / 250000000000) ∧
    -Real.log (246409713439 / 250000000000) ≤ (7232633 / 500000000) := by
  have h := checkLog_sound (w := (3590286561 / 496409713439)) (n := 12)
    (lo := (2893053 / 200000000)) (hi := (7232633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246409713439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246409713439) = 1/(246409713439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7999 : Bounds (-7232633 / 500000000) (-2893053 / 200000000) (Real.log (246409713439 / 250000000000)) := by
  have h := reflection_log_7999_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0125 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8000_neg : (14345637 / 1000000000) ≤ -Real.log (39430270839 / 40000000000) ∧
    -Real.log (39430270839 / 40000000000) ≤ (7172819 / 500000000) := by
  have h := checkLog_sound (w := (569729161 / 79430270839)) (n := 12)
    (lo := (14345637 / 1000000000)) (hi := (7172819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39430270839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39430270839) = 1/(39430270839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8000 : Bounds (-7172819 / 500000000) (-14345637 / 1000000000) (Real.log (39430270839 / 40000000000)) := by
  have h := reflection_log_8000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8001_neg : (119916511 / 500000000) ≤ -Real.log (62500000000 / 79439806167) ∧
    -Real.log (62500000000 / 79439806167) ≤ (239833023 / 1000000000) := by
  have h := checkLog_sound (w := (16939806167 / 141939806167)) (n := 12)
    (lo := (119916511 / 500000000)) (hi := (239833023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79439806167 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79439806167 / 62500000000) = 1/(62500000000 / 79439806167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8001 : Bounds (119916511 / 500000000) (239833023 / 1000000000) (Real.log (79439806167 / 62500000000)) := by
  have h := reflection_log_8001_neg
  have he : Real.log (79439806167 / 62500000000) = -Real.log (62500000000 / 79439806167) := by
    rw [show ((79439806167 / 62500000000) : ℝ) = ((62500000000 / 79439806167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8002_neg : (240833329 / 1000000000) ≤ -Real.log (500000000000 / 636154480653) ∧
    -Real.log (500000000000 / 636154480653) ≤ (24083333 / 100000000) := by
  have h := checkLog_sound (w := (136154480653 / 1136154480653)) (n := 12)
    (lo := (240833329 / 1000000000)) (hi := (24083333 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636154480653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636154480653 / 500000000000) = 1/(500000000000 / 636154480653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8002 : Bounds (240833329 / 1000000000) (24083333 / 100000000) (Real.log (636154480653 / 500000000000)) := by
  have h := reflection_log_8002_neg
  have he : Real.log (636154480653 / 500000000000) = -Real.log (500000000000 / 636154480653) := by
    rw [show ((636154480653 / 500000000000) : ℝ) = ((500000000000 / 636154480653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8003_neg : (241063481 / 500000000) ≤ -Real.log (250000000000 / 404878847413) ∧
    -Real.log (250000000000 / 404878847413) ≤ (482126963 / 1000000000) := by
  have h := checkLog_sound (w := (154878847413 / 654878847413)) (n := 12)
    (lo := (241063481 / 500000000)) (hi := (482126963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((404878847413 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(404878847413 / 250000000000) = 1/(250000000000 / 404878847413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8003 : Bounds (241063481 / 500000000) (482126963 / 1000000000) (Real.log (404878847413 / 250000000000)) := by
  have h := reflection_log_8003_neg
  have he : Real.log (404878847413 / 250000000000) = -Real.log (250000000000 / 404878847413) := by
    rw [show ((404878847413 / 250000000000) : ℝ) = ((250000000000 / 404878847413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8004_neg : (483186341 / 1000000000) ≤ -Real.log (125000000000 / 202653997379) ∧
    -Real.log (125000000000 / 202653997379) ≤ (241593171 / 500000000) := by
  have h := checkLog_sound (w := (77653997379 / 327653997379)) (n := 12)
    (lo := (483186341 / 1000000000)) (hi := (241593171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202653997379 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202653997379 / 125000000000) = 1/(125000000000 / 202653997379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8004 : Bounds (483186341 / 1000000000) (241593171 / 500000000) (Real.log (202653997379 / 125000000000)) := by
  have h := reflection_log_8004_neg
  have he : Real.log (202653997379 / 125000000000) = -Real.log (125000000000 / 202653997379) := by
    rw [show ((202653997379 / 125000000000) : ℝ) = ((125000000000 / 202653997379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8005_neg : (42618643 / 200000000) ≤ -Real.log (80 / 99) ∧
    -Real.log (80 / 99) ≤ (6659163 / 31250000) := by
  have h := checkLog_sound (w := (19 / 179)) (n := 12)
    (lo := (42618643 / 200000000)) (hi := (6659163 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99 / 80) = 1/(80 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8005 : Bounds (42618643 / 200000000) (6659163 / 31250000) (Real.log (99 / 80)) := by
  have h := reflection_log_8005_neg
  have he : Real.log (99 / 80) = -Real.log (80 / 99) := by
    rw [show ((99 / 80) : ℝ) = ((80 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8006_neg : (27115277 / 100000000) ≤ -Real.log (61 / 80) ∧
    -Real.log (61 / 80) ≤ (271152771 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 141)) (n := 12)
    (lo := (27115277 / 100000000)) (hi := (271152771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 61) = 1/(61 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8006 : Bounds (-271152771 / 1000000000) (-27115277 / 100000000) (Real.log (61 / 80)) := by
  have h := reflection_log_8006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8007_neg : (237471 / 1000000000) ≤ -Real.log (80000 / 80019) ∧
    -Real.log (80000 / 80019) ≤ (7421 / 31250000) := by
  have h := checkLog_sound (w := (19 / 160019)) (n := 12)
    (lo := (237471 / 1000000000)) (hi := (7421 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80019 / 80000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80019 / 80000) = 1/(80000 / 80019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8007 : Bounds (237471 / 1000000000) (7421 / 31250000) (Real.log (80019 / 80000)) := by
  have h := reflection_log_8007_neg
  have he : Real.log (80019 / 80000) = -Real.log (80000 / 80019) := by
    rw [show ((80019 / 80000) : ℝ) = ((80000 / 80019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8008_neg : (29691 / 125000000) ≤ -Real.log (79981 / 80000) ∧
    -Real.log (79981 / 80000) ≤ (237529 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 159981)) (n := 12)
    (lo := (29691 / 125000000)) (hi := (237529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80000 / 79981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80000 / 79981) = 1/(79981 / 80000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8008 : Bounds (-237529 / 1000000000) (-29691 / 125000000) (Real.log (79981 / 80000)) := by
  have h := reflection_log_8008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8009_neg : (56487079 / 500000000) ≤ -Real.log (1000000 / 1119603) ∧
    -Real.log (1000000 / 1119603) ≤ (112974159 / 1000000000) := by
  have h := checkLog_sound (w := (119603 / 2119603)) (n := 12)
    (lo := (56487079 / 500000000)) (hi := (112974159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1119603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1119603 / 1000000) = 1/(1000000 / 1119603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8009 : Bounds (56487079 / 500000000) (112974159 / 1000000000) (Real.log (1119603 / 1000000)) := by
  have h := reflection_log_8009_neg
  have he : Real.log (1119603 / 1000000) = -Real.log (1000000 / 1119603) := by
    rw [show ((1119603 / 1000000) : ℝ) = ((1000000 / 1119603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8010_neg : (1990349 / 15625000) ≤ -Real.log (880397 / 1000000) ∧
    -Real.log (880397 / 1000000) ≤ (127382337 / 1000000000) := by
  have h := checkLog_sound (w := (119603 / 1880397)) (n := 12)
    (lo := (1990349 / 15625000)) (hi := (127382337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 880397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 880397) = 1/(880397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8010 : Bounds (-127382337 / 1000000000) (-1990349 / 15625000) (Real.log (880397 / 1000000)) := by
  have h := reflection_log_8010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8011_neg : (22682879 / 200000000) ≤ -Real.log (31250 / 35003) ∧
    -Real.log (31250 / 35003) ≤ (28353599 / 250000000) := by
  have h := checkLog_sound (w := (3753 / 66253)) (n := 12)
    (lo := (22682879 / 200000000)) (hi := (28353599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35003 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35003 / 31250) = 1/(31250 / 35003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8011 : Bounds (22682879 / 200000000) (28353599 / 250000000) (Real.log (35003 / 31250)) := by
  have h := reflection_log_8011_neg
  have he : Real.log (35003 / 31250) = -Real.log (31250 / 35003) := by
    rw [show ((35003 / 31250) : ℝ) = ((31250 / 35003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8012_neg : (31985617 / 250000000) ≤ -Real.log (27497 / 31250) ∧
    -Real.log (27497 / 31250) ≤ (127942469 / 1000000000) := by
  have h := checkLog_sound (w := (3753 / 58747)) (n := 12)
    (lo := (31985617 / 250000000)) (hi := (127942469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27497) = 1/(27497 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8012 : Bounds (-127942469 / 1000000000) (-31985617 / 250000000) (Real.log (27497 / 31250)) := by
  have h := reflection_log_8012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8013_neg : (1816009 / 125000000) ≤ -Real.log (962477491 / 976562500) ∧
    -Real.log (962477491 / 976562500) ≤ (14528073 / 1000000000) := by
  have h := checkLog_sound (w := (14085009 / 1939039991)) (n := 12)
    (lo := (1816009 / 125000000)) (hi := (14528073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 962477491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 962477491) = 1/(962477491 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8013 : Bounds (-14528073 / 1000000000) (-1816009 / 125000000) (Real.log (962477491 / 976562500)) := by
  have h := reflection_log_8013_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8014_neg : (7204089 / 500000000) ≤ -Real.log (985695122391 / 1000000000000) ∧
    -Real.log (985695122391 / 1000000000000) ≤ (14408179 / 1000000000) := by
  have h := checkLog_sound (w := (14304877609 / 1985695122391)) (n := 12)
    (lo := (7204089 / 500000000)) (hi := (14408179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985695122391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985695122391) = 1/(985695122391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8014 : Bounds (-14408179 / 1000000000) (-7204089 / 500000000) (Real.log (985695122391 / 1000000000000)) := by
  have h := reflection_log_8014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8015_neg : (48071299 / 200000000) ≤ -Real.log (500000000000 / 635851212577) ∧
    -Real.log (500000000000 / 635851212577) ≤ (15022281 / 62500000) := by
  have h := checkLog_sound (w := (135851212577 / 1135851212577)) (n := 12)
    (lo := (48071299 / 200000000)) (hi := (15022281 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635851212577 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635851212577 / 500000000000) = 1/(500000000000 / 635851212577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8015 : Bounds (48071299 / 200000000) (15022281 / 62500000) (Real.log (635851212577 / 500000000000)) := by
  have h := reflection_log_8015_neg
  have he : Real.log (635851212577 / 500000000000) = -Real.log (500000000000 / 635851212577) := by
    rw [show ((635851212577 / 500000000000) : ℝ) = ((500000000000 / 635851212577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8016_neg : (3771201 / 15625000) ≤ -Real.log (500000000000 / 636487616831) ∧
    -Real.log (500000000000 / 636487616831) ≤ (48271373 / 200000000) := by
  have h := checkLog_sound (w := (136487616831 / 1136487616831)) (n := 12)
    (lo := (3771201 / 15625000)) (hi := (48271373 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636487616831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636487616831 / 500000000000) = 1/(500000000000 / 636487616831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8016 : Bounds (3771201 / 15625000) (48271373 / 200000000) (Real.log (636487616831 / 500000000000)) := by
  have h := reflection_log_8016_neg
  have he : Real.log (636487616831 / 500000000000) = -Real.log (500000000000 / 636487616831) := by
    rw [show ((636487616831 / 500000000000) : ℝ) = ((500000000000 / 636487616831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8017_neg : (483186341 / 1000000000) ≤ -Real.log (100000000000 / 162123197903) ∧
    -Real.log (100000000000 / 162123197903) ≤ (241593171 / 500000000) := by
  have h := checkLog_sound (w := (62123197903 / 262123197903)) (n := 12)
    (lo := (483186341 / 1000000000)) (hi := (241593171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162123197903 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162123197903 / 100000000000) = 1/(100000000000 / 162123197903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8017 : Bounds (483186341 / 1000000000) (241593171 / 500000000) (Real.log (162123197903 / 100000000000)) := by
  have h := reflection_log_8017_neg
  have he : Real.log (162123197903 / 100000000000) = -Real.log (100000000000 / 162123197903) := by
    rw [show ((162123197903 / 100000000000) : ℝ) = ((100000000000 / 162123197903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8018_neg : (96849197 / 200000000) ≤ -Real.log (500000000000 / 811475409837) ∧
    -Real.log (500000000000 / 811475409837) ≤ (242122993 / 500000000) := by
  have h := checkLog_sound (w := (311475409837 / 1311475409837)) (n := 12)
    (lo := (96849197 / 200000000)) (hi := (242122993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811475409837 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811475409837 / 500000000000) = 1/(500000000000 / 811475409837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8018 : Bounds (96849197 / 200000000) (242122993 / 500000000) (Real.log (811475409837 / 500000000000)) := by
  have h := reflection_log_8018_neg
  have he : Real.log (811475409837 / 500000000000) = -Real.log (500000000000 / 811475409837) := by
    rw [show ((811475409837 / 500000000000) : ℝ) = ((500000000000 / 811475409837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8019_neg : (106748587 / 500000000) ≤ -Real.log (500 / 619) ∧
    -Real.log (500 / 619) ≤ (8539887 / 40000000) := by
  have h := checkLog_sound (w := (119 / 1119)) (n := 12)
    (lo := (106748587 / 500000000)) (hi := (8539887 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619 / 500) = 1/(500 / 619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8019 : Bounds (106748587 / 500000000) (8539887 / 40000000) (Real.log (619 / 500)) := by
  have h := reflection_log_8019_neg
  have he : Real.log (619 / 500) = -Real.log (500 / 619) := by
    rw [show ((619 / 500) : ℝ) = ((500 / 619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8020_neg : (271808723 / 1000000000) ≤ -Real.log (381 / 500) ∧
    -Real.log (381 / 500) ≤ (67952181 / 250000000) := by
  have h := checkLog_sound (w := (119 / 881)) (n := 12)
    (lo := (271808723 / 1000000000)) (hi := (67952181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 381) = 1/(381 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8020 : Bounds (-67952181 / 250000000) (-271808723 / 1000000000) (Real.log (381 / 500)) := by
  have h := reflection_log_8020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8021_neg : (237971 / 1000000000) ≤ -Real.log (500000 / 500119) ∧
    -Real.log (500000 / 500119) ≤ (59493 / 250000000) := by
  have h := checkLog_sound (w := (119 / 1000119)) (n := 12)
    (lo := (237971 / 1000000000)) (hi := (59493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500119 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500119 / 500000) = 1/(500000 / 500119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8021 : Bounds (237971 / 1000000000) (59493 / 250000000) (Real.log (500119 / 500000)) := by
  have h := reflection_log_8021_neg
  have he : Real.log (500119 / 500000) = -Real.log (500000 / 500119) := by
    rw [show ((500119 / 500000) : ℝ) = ((500000 / 500119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8022_neg : (59507 / 250000000) ≤ -Real.log (499881 / 500000) ∧
    -Real.log (499881 / 500000) ≤ (238029 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 999881)) (n := 12)
    (lo := (59507 / 250000000)) (hi := (238029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499881) = 1/(499881 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8022 : Bounds (-238029 / 1000000000) (-59507 / 250000000) (Real.log (499881 / 500000)) := by
  have h := reflection_log_8022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8023_neg : (113203677 / 1000000000) ≤ -Real.log (50000 / 55993) ∧
    -Real.log (50000 / 55993) ≤ (56601839 / 500000000) := by
  have h := checkLog_sound (w := (5993 / 105993)) (n := 12)
    (lo := (113203677 / 1000000000)) (hi := (56601839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55993 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55993 / 50000) = 1/(50000 / 55993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8023 : Bounds (113203677 / 1000000000) (56601839 / 500000000) (Real.log (55993 / 50000)) := by
  have h := reflection_log_8023_neg
  have he : Real.log (55993 / 50000) = -Real.log (50000 / 55993) := by
    rw [show ((55993 / 50000) : ℝ) = ((50000 / 55993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8024_neg : (127674293 / 1000000000) ≤ -Real.log (44007 / 50000) ∧
    -Real.log (44007 / 50000) ≤ (63837147 / 500000000) := by
  have h := checkLog_sound (w := (5993 / 94007)) (n := 12)
    (lo := (127674293 / 1000000000)) (hi := (63837147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44007) = 1/(44007 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8024 : Bounds (-63837147 / 500000000) (-127674293 / 1000000000) (Real.log (44007 / 50000)) := by
  have h := reflection_log_8024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8025_neg : (56822353 / 500000000) ≤ -Real.log (500000 / 560177) ∧
    -Real.log (500000 / 560177) ≤ (113644707 / 1000000000) := by
  have h := checkLog_sound (w := (60177 / 1060177)) (n := 12)
    (lo := (56822353 / 500000000)) (hi := (113644707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((560177 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(560177 / 500000) = 1/(500000 / 560177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8025 : Bounds (56822353 / 500000000) (113644707 / 1000000000) (Real.log (560177 / 500000)) := by
  have h := reflection_log_8025_neg
  have he : Real.log (560177 / 500000) = -Real.log (500000 / 560177) := by
    rw [show ((560177 / 500000) : ℝ) = ((500000 / 560177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8026_neg : (5129429 / 40000000) ≤ -Real.log (439823 / 500000) ∧
    -Real.log (439823 / 500000) ≤ (64117863 / 500000000) := by
  have h := checkLog_sound (w := (60177 / 939823)) (n := 12)
    (lo := (5129429 / 40000000)) (hi := (64117863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 439823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 439823) = 1/(439823 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8026 : Bounds (-64117863 / 500000000) (-5129429 / 40000000) (Real.log (439823 / 500000)) := by
  have h := reflection_log_8026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8027_neg : (7295509 / 500000000) ≤ -Real.log (246378728671 / 250000000000) ∧
    -Real.log (246378728671 / 250000000000) ≤ (14591019 / 1000000000) := by
  have h := checkLog_sound (w := (3621271329 / 496378728671)) (n := 12)
    (lo := (7295509 / 500000000)) (hi := (14591019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246378728671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246378728671) = 1/(246378728671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8027 : Bounds (-14591019 / 1000000000) (-7295509 / 500000000) (Real.log (246378728671 / 250000000000)) := by
  have h := reflection_log_8027_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8028_neg : (2894123 / 200000000) ≤ -Real.log (2464083951 / 2500000000) ∧
    -Real.log (2464083951 / 2500000000) ≤ (1808827 / 125000000) := by
  have h := checkLog_sound (w := (35916049 / 4964083951)) (n := 12)
    (lo := (2894123 / 200000000)) (hi := (1808827 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2464083951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2464083951) = 1/(2464083951 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8028 : Bounds (-1808827 / 125000000) (-2894123 / 200000000) (Real.log (2464083951 / 2500000000)) := by
  have h := reflection_log_8028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8029_neg : (24087797 / 100000000) ≤ -Real.log (125000000000 / 159045719999) ∧
    -Real.log (125000000000 / 159045719999) ≤ (240877971 / 1000000000) := by
  have h := checkLog_sound (w := (34045719999 / 284045719999)) (n := 12)
    (lo := (24087797 / 100000000)) (hi := (240877971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159045719999 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159045719999 / 125000000000) = 1/(125000000000 / 159045719999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8029 : Bounds (24087797 / 100000000) (240877971 / 1000000000) (Real.log (159045719999 / 125000000000)) := by
  have h := reflection_log_8029_neg
  have he : Real.log (159045719999 / 125000000000) = -Real.log (125000000000 / 159045719999) := by
    rw [show ((159045719999 / 125000000000) : ℝ) = ((125000000000 / 159045719999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8030_neg : (241880431 / 1000000000) ≤ -Real.log (500000000000 / 636820948427) ∧
    -Real.log (500000000000 / 636820948427) ≤ (15117527 / 62500000) := by
  have h := checkLog_sound (w := (136820948427 / 1136820948427)) (n := 12)
    (lo := (241880431 / 1000000000)) (hi := (15117527 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636820948427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636820948427 / 500000000000) = 1/(500000000000 / 636820948427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8030 : Bounds (241880431 / 1000000000) (15117527 / 62500000) (Real.log (636820948427 / 500000000000)) := by
  have h := reflection_log_8030_neg
  have he : Real.log (636820948427 / 500000000000) = -Real.log (500000000000 / 636820948427) := by
    rw [show ((636820948427 / 500000000000) : ℝ) = ((500000000000 / 636820948427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8031_neg : (96849197 / 200000000) ≤ -Real.log (125000000000 / 202868852459) ∧
    -Real.log (125000000000 / 202868852459) ≤ (242122993 / 500000000) := by
  have h := checkLog_sound (w := (77868852459 / 327868852459)) (n := 12)
    (lo := (96849197 / 200000000)) (hi := (242122993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202868852459 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202868852459 / 125000000000) = 1/(125000000000 / 202868852459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8031 : Bounds (96849197 / 200000000) (242122993 / 500000000) (Real.log (202868852459 / 125000000000)) := by
  have h := reflection_log_8031_neg
  have he : Real.log (202868852459 / 125000000000) = -Real.log (125000000000 / 202868852459) := by
    rw [show ((202868852459 / 125000000000) : ℝ) = ((125000000000 / 202868852459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8032_neg : (485305897 / 1000000000) ≤ -Real.log (250000000000 / 406167979003) ∧
    -Real.log (250000000000 / 406167979003) ≤ (242652949 / 500000000) := by
  have h := checkLog_sound (w := (156167979003 / 656167979003)) (n := 12)
    (lo := (485305897 / 1000000000)) (hi := (242652949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406167979003 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406167979003 / 250000000000) = 1/(250000000000 / 406167979003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8032 : Bounds (485305897 / 1000000000) (242652949 / 500000000) (Real.log (406167979003 / 250000000000)) := by
  have h := reflection_log_8032_neg
  have he : Real.log (406167979003 / 250000000000) = -Real.log (250000000000 / 406167979003) := by
    rw [show ((406167979003 / 250000000000) : ℝ) = ((250000000000 / 406167979003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8033_neg : (213900969 / 1000000000) ≤ -Real.log (2000 / 2477) ∧
    -Real.log (2000 / 2477) ≤ (21390097 / 100000000) := by
  have h := checkLog_sound (w := (477 / 4477)) (n := 12)
    (lo := (213900969 / 1000000000)) (hi := (21390097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2477 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2477 / 2000) = 1/(2000 / 2477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8033 : Bounds (213900969 / 1000000000) (21390097 / 100000000) (Real.log (2477 / 2000)) := by
  have h := reflection_log_8033_neg
  have he : Real.log (2477 / 2000) = -Real.log (2000 / 2477) := by
    rw [show ((2477 / 2000) : ℝ) = ((2000 / 2477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8034_neg : (136232553 / 500000000) ≤ -Real.log (1523 / 2000) ∧
    -Real.log (1523 / 2000) ≤ (272465107 / 1000000000) := by
  have h := checkLog_sound (w := (477 / 3523)) (n := 12)
    (lo := (136232553 / 500000000)) (hi := (272465107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1523) = 1/(1523 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8034 : Bounds (-272465107 / 1000000000) (-136232553 / 500000000) (Real.log (1523 / 2000)) := by
  have h := reflection_log_8034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8035_neg : (238471 / 1000000000) ≤ -Real.log (2000000 / 2000477) ∧
    -Real.log (2000000 / 2000477) ≤ (29809 / 125000000) := by
  have h := checkLog_sound (w := (477 / 4000477)) (n := 12)
    (lo := (238471 / 1000000000)) (hi := (29809 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000477 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000477 / 2000000) = 1/(2000000 / 2000477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8035 : Bounds (238471 / 1000000000) (29809 / 125000000) (Real.log (2000477 / 2000000)) := by
  have h := reflection_log_8035_neg
  have he : Real.log (2000477 / 2000000) = -Real.log (2000000 / 2000477) := by
    rw [show ((2000477 / 2000000) : ℝ) = ((2000000 / 2000477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8036_neg : (3727 / 15625000) ≤ -Real.log (1999523 / 2000000) ∧
    -Real.log (1999523 / 2000000) ≤ (238529 / 1000000000) := by
  have h := checkLog_sound (w := (477 / 3999523)) (n := 12)
    (lo := (3727 / 15625000)) (hi := (238529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999523) = 1/(1999523 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8036 : Bounds (-238529 / 1000000000) (-3727 / 15625000) (Real.log (1999523 / 2000000)) := by
  have h := reflection_log_8036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8037_neg : (28358509 / 250000000) ≤ -Real.log (500000 / 560059) ∧
    -Real.log (500000 / 560059) ≤ (113434037 / 1000000000) := by
  have h := checkLog_sound (w := (60059 / 1060059)) (n := 12)
    (lo := (28358509 / 250000000)) (hi := (113434037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((560059 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(560059 / 500000) = 1/(500000 / 560059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8037 : Bounds (28358509 / 250000000) (113434037 / 1000000000) (Real.log (560059 / 500000)) := by
  have h := reflection_log_8037_neg
  have he : Real.log (560059 / 500000) = -Real.log (500000 / 560059) := by
    rw [show ((560059 / 500000) : ℝ) = ((500000 / 560059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8038_neg : (127967471 / 1000000000) ≤ -Real.log (439941 / 500000) ∧
    -Real.log (439941 / 500000) ≤ (7997967 / 62500000) := by
  have h := checkLog_sound (w := (60059 / 939941)) (n := 12)
    (lo := (127967471 / 1000000000)) (hi := (7997967 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 439941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 439941) = 1/(439941 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8038 : Bounds (-7997967 / 62500000) (-127967471 / 1000000000) (Real.log (439941 / 500000)) := by
  have h := reflection_log_8038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8039_neg : (113875857 / 1000000000) ≤ -Real.log (1000000 / 1120613) ∧
    -Real.log (1000000 / 1120613) ≤ (56937929 / 500000000) := by
  have h := checkLog_sound (w := (120613 / 2120613)) (n := 12)
    (lo := (113875857 / 1000000000)) (hi := (56937929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1120613 / 1000000) = 1/(1000000 / 1120613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8039 : Bounds (113875857 / 1000000000) (56937929 / 500000000) (Real.log (1120613 / 1000000)) := by
  have h := reflection_log_8039_neg
  have he : Real.log (1120613 / 1000000) = -Real.log (1000000 / 1120613) := by
    rw [show ((1120613 / 1000000) : ℝ) = ((1000000 / 1120613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8040_neg : (25706041 / 200000000) ≤ -Real.log (879387 / 1000000) ∧
    -Real.log (879387 / 1000000) ≤ (64265103 / 500000000) := by
  have h := checkLog_sound (w := (120613 / 1879387)) (n := 12)
    (lo := (25706041 / 200000000)) (hi := (64265103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 879387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 879387) = 1/(879387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8040 : Bounds (-64265103 / 500000000) (-25706041 / 200000000) (Real.log (879387 / 1000000)) := by
  have h := reflection_log_8040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8041_neg : (3663587 / 250000000) ≤ -Real.log (985452504231 / 1000000000000) ∧
    -Real.log (985452504231 / 1000000000000) ≤ (14654349 / 1000000000) := by
  have h := checkLog_sound (w := (14547495769 / 1985452504231)) (n := 12)
    (lo := (3663587 / 250000000)) (hi := (14654349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985452504231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985452504231) = 1/(985452504231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8041 : Bounds (-14654349 / 1000000000) (-3663587 / 250000000) (Real.log (985452504231 / 1000000000000)) := by
  have h := reflection_log_8041_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8042_neg : (7266717 / 500000000) ≤ -Real.log (246392916519 / 250000000000) ∧
    -Real.log (246392916519 / 250000000000) ≤ (2906687 / 200000000) := by
  have h := checkLog_sound (w := (3607083481 / 496392916519)) (n := 12)
    (lo := (7266717 / 500000000)) (hi := (2906687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246392916519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246392916519) = 1/(246392916519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8042 : Bounds (-2906687 / 200000000) (-7266717 / 500000000) (Real.log (246392916519 / 250000000000)) := by
  have h := reflection_log_8042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8043_neg : (60350377 / 250000000) ≤ -Real.log (500000000000 / 636516032831) ∧
    -Real.log (500000000000 / 636516032831) ≤ (241401509 / 1000000000) := by
  have h := checkLog_sound (w := (136516032831 / 1136516032831)) (n := 12)
    (lo := (60350377 / 250000000)) (hi := (241401509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636516032831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636516032831 / 500000000000) = 1/(500000000000 / 636516032831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8043 : Bounds (60350377 / 250000000) (241401509 / 1000000000) (Real.log (636516032831 / 500000000000)) := by
  have h := reflection_log_8043_neg
  have he : Real.log (636516032831 / 500000000000) = -Real.log (500000000000 / 636516032831) := by
    rw [show ((636516032831 / 500000000000) : ℝ) = ((500000000000 / 636516032831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8044_neg : (121203031 / 500000000) ≤ -Real.log (100000000000 / 127431153747) ∧
    -Real.log (100000000000 / 127431153747) ≤ (242406063 / 1000000000) := by
  have h := checkLog_sound (w := (27431153747 / 227431153747)) (n := 12)
    (lo := (121203031 / 500000000)) (hi := (242406063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127431153747 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127431153747 / 100000000000) = 1/(100000000000 / 127431153747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8044 : Bounds (121203031 / 500000000) (242406063 / 1000000000) (Real.log (127431153747 / 100000000000)) := by
  have h := reflection_log_8044_neg
  have he : Real.log (127431153747 / 100000000000) = -Real.log (100000000000 / 127431153747) := by
    rw [show ((127431153747 / 100000000000) : ℝ) = ((100000000000 / 127431153747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8045_neg : (485305897 / 1000000000) ≤ -Real.log (100000000000 / 162467191601) ∧
    -Real.log (100000000000 / 162467191601) ≤ (242652949 / 500000000) := by
  have h := checkLog_sound (w := (62467191601 / 262467191601)) (n := 12)
    (lo := (485305897 / 1000000000)) (hi := (242652949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162467191601 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162467191601 / 100000000000) = 1/(100000000000 / 162467191601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8045 : Bounds (485305897 / 1000000000) (242652949 / 500000000) (Real.log (162467191601 / 100000000000)) := by
  have h := reflection_log_8045_neg
  have he : Real.log (162467191601 / 100000000000) = -Real.log (100000000000 / 162467191601) := by
    rw [show ((162467191601 / 100000000000) : ℝ) = ((100000000000 / 162467191601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8046_neg : (121591519 / 250000000) ≤ -Real.log (100000000000 / 162639527249) ∧
    -Real.log (100000000000 / 162639527249) ≤ (486366077 / 1000000000) := by
  have h := checkLog_sound (w := (62639527249 / 262639527249)) (n := 12)
    (lo := (121591519 / 250000000)) (hi := (486366077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162639527249 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162639527249 / 100000000000) = 1/(100000000000 / 162639527249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8046 : Bounds (121591519 / 250000000) (486366077 / 1000000000) (Real.log (162639527249 / 100000000000)) := by
  have h := reflection_log_8046_neg
  have he : Real.log (162639527249 / 100000000000) = -Real.log (100000000000 / 162639527249) := by
    rw [show ((162639527249 / 100000000000) : ℝ) = ((100000000000 / 162639527249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8047_neg : (107152301 / 500000000) ≤ -Real.log (1000 / 1239) ∧
    -Real.log (1000 / 1239) ≤ (214304603 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 2239)) (n := 12)
    (lo := (107152301 / 500000000)) (hi := (214304603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239 / 1000) = 1/(1000 / 1239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8047 : Bounds (107152301 / 500000000) (214304603 / 1000000000) (Real.log (1239 / 1000)) := by
  have h := reflection_log_8047_neg
  have he : Real.log (1239 / 1000) = -Real.log (1000 / 1239) := by
    rw [show ((1239 / 1000) : ℝ) = ((1000 / 1239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8048_neg : (273121921 / 1000000000) ≤ -Real.log (761 / 1000) ∧
    -Real.log (761 / 1000) ≤ (136560961 / 500000000) := by
  have h := checkLog_sound (w := (239 / 1761)) (n := 12)
    (lo := (273121921 / 1000000000)) (hi := (136560961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 761) = 1/(761 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8048 : Bounds (-136560961 / 500000000) (-273121921 / 1000000000) (Real.log (761 / 1000)) := by
  have h := reflection_log_8048_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8049_neg : (238971 / 1000000000) ≤ -Real.log (1000000 / 1000239) ∧
    -Real.log (1000000 / 1000239) ≤ (59743 / 250000000) := by
  have h := checkLog_sound (w := (239 / 2000239)) (n := 12)
    (lo := (238971 / 1000000000)) (hi := (59743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000239 / 1000000) = 1/(1000000 / 1000239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8049 : Bounds (238971 / 1000000000) (59743 / 250000000) (Real.log (1000239 / 1000000)) := by
  have h := reflection_log_8049_neg
  have he : Real.log (1000239 / 1000000) = -Real.log (1000000 / 1000239) := by
    rw [show ((1000239 / 1000000) : ℝ) = ((1000000 / 1000239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8050_neg : (59757 / 250000000) ≤ -Real.log (999761 / 1000000) ∧
    -Real.log (999761 / 1000000) ≤ (239029 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 1999761)) (n := 12)
    (lo := (59757 / 250000000)) (hi := (239029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999761) = 1/(999761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8050 : Bounds (-239029 / 1000000000) (-59757 / 250000000) (Real.log (999761 / 1000000)) := by
  have h := reflection_log_8050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8051_neg : (113664343 / 1000000000) ≤ -Real.log (125000 / 140047) ∧
    -Real.log (125000 / 140047) ≤ (14208043 / 125000000) := by
  have h := checkLog_sound (w := (15047 / 265047)) (n := 12)
    (lo := (113664343 / 1000000000)) (hi := (14208043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140047 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140047 / 125000) = 1/(125000 / 140047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8051 : Bounds (113664343 / 1000000000) (14208043 / 125000000) (Real.log (140047 / 125000)) := by
  have h := reflection_log_8051_neg
  have he : Real.log (140047 / 125000) = -Real.log (125000 / 140047) := by
    rw [show ((140047 / 125000) : ℝ) = ((125000 / 140047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8052_neg : (25652147 / 200000000) ≤ -Real.log (109953 / 125000) ∧
    -Real.log (109953 / 125000) ≤ (1002037 / 7812500) := by
  have h := checkLog_sound (w := (15047 / 234953)) (n := 12)
    (lo := (25652147 / 200000000)) (hi := (1002037 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 109953) = 1/(109953 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8052 : Bounds (-1002037 / 7812500) (-25652147 / 200000000) (Real.log (109953 / 125000)) := by
  have h := reflection_log_8052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8053_neg : (114106061 / 1000000000) ≤ -Real.log (1000000 / 1120871) ∧
    -Real.log (1000000 / 1120871) ≤ (57053031 / 500000000) := by
  have h := checkLog_sound (w := (120871 / 2120871)) (n := 12)
    (lo := (114106061 / 1000000000)) (hi := (57053031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1120871 / 1000000) = 1/(1000000 / 1120871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8053 : Bounds (114106061 / 1000000000) (57053031 / 500000000) (Real.log (1120871 / 1000000)) := by
  have h := reflection_log_8053_neg
  have he : Real.log (1120871 / 1000000) = -Real.log (1000000 / 1120871) := by
    rw [show ((1120871 / 1000000) : ℝ) = ((1000000 / 1120871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8054_neg : (64411817 / 500000000) ≤ -Real.log (879129 / 1000000) ∧
    -Real.log (879129 / 1000000) ≤ (25764727 / 200000000) := by
  have h := checkLog_sound (w := (120871 / 1879129)) (n := 12)
    (lo := (64411817 / 500000000)) (hi := (25764727 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 879129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 879129) = 1/(879129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8054 : Bounds (-25764727 / 200000000) (-64411817 / 500000000) (Real.log (879129 / 1000000)) := by
  have h := reflection_log_8054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8055_neg : (3679393 / 250000000) ≤ -Real.log (985390201359 / 1000000000000) ∧
    -Real.log (985390201359 / 1000000000000) ≤ (14717573 / 1000000000) := by
  have h := checkLog_sound (w := (14609798641 / 1985390201359)) (n := 12)
    (lo := (3679393 / 250000000)) (hi := (14717573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985390201359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985390201359) = 1/(985390201359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8055 : Bounds (-14717573 / 1000000000) (-3679393 / 250000000) (Real.log (985390201359 / 1000000000000)) := by
  have h := reflection_log_8055_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8056_neg : (1824549 / 125000000) ≤ -Real.log (15398587791 / 15625000000) ∧
    -Real.log (15398587791 / 15625000000) ≤ (14596393 / 1000000000) := by
  have h := checkLog_sound (w := (226412209 / 31023587791)) (n := 12)
    (lo := (1824549 / 125000000)) (hi := (14596393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15398587791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15398587791) = 1/(15398587791 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8056 : Bounds (-14596393 / 1000000000) (-1824549 / 125000000) (Real.log (15398587791 / 15625000000)) := by
  have h := reflection_log_8056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8057_neg : (120962539 / 500000000) ≤ -Real.log (500000000000 / 636849381099) ∧
    -Real.log (500000000000 / 636849381099) ≤ (241925079 / 1000000000) := by
  have h := checkLog_sound (w := (136849381099 / 1136849381099)) (n := 12)
    (lo := (120962539 / 500000000)) (hi := (241925079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636849381099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636849381099 / 500000000000) = 1/(500000000000 / 636849381099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8057 : Bounds (120962539 / 500000000) (241925079 / 1000000000) (Real.log (636849381099 / 500000000000)) := by
  have h := reflection_log_8057_neg
  have he : Real.log (636849381099 / 500000000000) = -Real.log (500000000000 / 636849381099) := by
    rw [show ((636849381099 / 500000000000) : ℝ) = ((500000000000 / 636849381099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8058_neg : (7591553 / 31250000) ≤ -Real.log (500000000000 / 637489492441) ∧
    -Real.log (500000000000 / 637489492441) ≤ (242929697 / 1000000000) := by
  have h := checkLog_sound (w := (137489492441 / 1137489492441)) (n := 12)
    (lo := (7591553 / 31250000)) (hi := (242929697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637489492441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637489492441 / 500000000000) = 1/(500000000000 / 637489492441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8058 : Bounds (7591553 / 31250000) (242929697 / 1000000000) (Real.log (637489492441 / 500000000000)) := by
  have h := reflection_log_8058_neg
  have he : Real.log (637489492441 / 500000000000) = -Real.log (500000000000 / 637489492441) := by
    rw [show ((637489492441 / 500000000000) : ℝ) = ((500000000000 / 637489492441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8059_neg : (121591519 / 250000000) ≤ -Real.log (125000000000 / 203299409061) ∧
    -Real.log (125000000000 / 203299409061) ≤ (486366077 / 1000000000) := by
  have h := checkLog_sound (w := (78299409061 / 328299409061)) (n := 12)
    (lo := (121591519 / 250000000)) (hi := (486366077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203299409061 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203299409061 / 125000000000) = 1/(125000000000 / 203299409061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8059 : Bounds (121591519 / 250000000) (486366077 / 1000000000) (Real.log (203299409061 / 125000000000)) := by
  have h := reflection_log_8059_neg
  have he : Real.log (203299409061 / 125000000000) = -Real.log (125000000000 / 203299409061) := by
    rw [show ((203299409061 / 125000000000) : ℝ) = ((125000000000 / 203299409061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8060_neg : (487426523 / 1000000000) ≤ -Real.log (500000000000 / 814060446781) ∧
    -Real.log (500000000000 / 814060446781) ≤ (121856631 / 250000000) := by
  have h := checkLog_sound (w := (314060446781 / 1314060446781)) (n := 12)
    (lo := (487426523 / 1000000000)) (hi := (121856631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814060446781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814060446781 / 500000000000) = 1/(500000000000 / 814060446781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8060 : Bounds (487426523 / 1000000000) (121856631 / 250000000) (Real.log (814060446781 / 500000000000)) := by
  have h := reflection_log_8060_neg
  have he : Real.log (814060446781 / 500000000000) = -Real.log (500000000000 / 814060446781) := by
    rw [show ((814060446781 / 500000000000) : ℝ) = ((500000000000 / 814060446781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8061_neg : (26838509 / 125000000) ≤ -Real.log (2000 / 2479) ∧
    -Real.log (2000 / 2479) ≤ (214708073 / 1000000000) := by
  have h := checkLog_sound (w := (479 / 4479)) (n := 12)
    (lo := (26838509 / 125000000)) (hi := (214708073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2479 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2479 / 2000) = 1/(2000 / 2479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8061 : Bounds (26838509 / 125000000) (214708073 / 1000000000) (Real.log (2479 / 2000)) := by
  have h := reflection_log_8061_neg
  have he : Real.log (2479 / 2000) = -Real.log (2000 / 2479) := by
    rw [show ((2479 / 2000) : ℝ) = ((2000 / 2479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8062_neg : (273779167 / 1000000000) ≤ -Real.log (1521 / 2000) ∧
    -Real.log (1521 / 2000) ≤ (8555599 / 31250000) := by
  have h := checkLog_sound (w := (479 / 3521)) (n := 12)
    (lo := (273779167 / 1000000000)) (hi := (8555599 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1521) = 1/(1521 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8062 : Bounds (-8555599 / 31250000) (-273779167 / 1000000000) (Real.log (1521 / 2000)) := by
  have h := reflection_log_8062_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8063_neg : (239471 / 1000000000) ≤ -Real.log (2000000 / 2000479) ∧
    -Real.log (2000000 / 2000479) ≤ (14967 / 62500000) := by
  have h := checkLog_sound (w := (479 / 4000479)) (n := 12)
    (lo := (239471 / 1000000000)) (hi := (14967 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000479 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000479 / 2000000) = 1/(2000000 / 2000479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8063 : Bounds (239471 / 1000000000) (14967 / 62500000) (Real.log (2000479 / 2000000)) := by
  have h := reflection_log_8063_neg
  have he : Real.log (2000479 / 2000000) = -Real.log (2000000 / 2000479) := by
    rw [show ((2000479 / 2000000) : ℝ) = ((2000000 / 2000479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


