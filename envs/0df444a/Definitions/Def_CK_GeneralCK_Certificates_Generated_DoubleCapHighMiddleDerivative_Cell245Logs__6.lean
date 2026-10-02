-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell245Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell245Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:29:07.760171+00:00
-- url     : https://prove2.me/theorems/3760c9c9-be91-4433-9725-e4490a4c2d1e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell245Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell246…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell245Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell246Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell247Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell248Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell249Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell250Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell245Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell246Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell247Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell248Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell249Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell250Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell245Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell246Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell247Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell248Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell249Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell250Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell245Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell246Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell247Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell248Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell249Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell250Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell245Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell245
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (166139093 / 500000000) ≤ -Real.log (2560 / 3569) ∧
    -Real.log (2560 / 3569) ≤ (332278187 / 1000000000) := by
  have h := checkLog_sound (w := (1009 / 6129)) (n := 12)
    (lo := (166139093 / 500000000)) (hi := (332278187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3569 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3569 / 2560) = 1/(2560 / 3569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (166139093 / 500000000) (332278187 / 1000000000) (Real.log (3569 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3569 / 2560) = -Real.log (2560 / 3569) := by
    rw [show ((3569 / 2560) : ℝ) = ((2560 / 3569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (250553687 / 500000000) ≤ -Real.log (1551 / 2560) ∧
    -Real.log (1551 / 2560) ≤ (4008859 / 8000000) := by
  have h := checkLog_sound (w := (1009 / 4111)) (n := 12)
    (lo := (250553687 / 500000000)) (hi := (4008859 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1551) = 1/(1551 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4008859 / 8000000) (-250553687 / 500000000) (Real.log (1551 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331857811 / 1000000000) ≤ -Real.log (1024 / 1427) ∧
    -Real.log (1024 / 1427) ≤ (82964453 / 250000000) := by
  have h := checkLog_sound (w := (403 / 2451)) (n := 12)
    (lo := (331857811 / 1000000000)) (hi := (82964453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1427 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1427 / 1024) = 1/(1024 / 1427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331857811 / 1000000000) (82964453 / 250000000) (Real.log (1427 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1427 / 1024) = -Real.log (1024 / 1427) := by
    rw [show ((1427 / 1024) : ℝ) = ((1024 / 1427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (500140723 / 1000000000) ≤ -Real.log (621 / 1024) ∧
    -Real.log (621 / 1024) ≤ (125035181 / 250000000) := by
  have h := checkLog_sound (w := (403 / 1645)) (n := 12)
    (lo := (500140723 / 1000000000)) (hi := (125035181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 621) = 1/(621 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-125035181 / 250000000) (-500140723 / 1000000000) (Real.log (621 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (123510501 / 500000000) ≤ -Real.log (500000 / 640103) ∧
    -Real.log (500000 / 640103) ≤ (247021003 / 1000000000) := by
  have h := checkLog_sound (w := (140103 / 1140103)) (n := 12)
    (lo := (123510501 / 500000000)) (hi := (247021003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640103 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640103 / 500000) = 1/(500000 / 640103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (123510501 / 500000000) (247021003 / 1000000000) (Real.log (640103 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (640103 / 500000) = -Real.log (500000 / 640103) := by
    rw [show ((640103 / 500000) : ℝ) = ((500000 / 640103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (328790219 / 1000000000) ≤ -Real.log (359897 / 500000) ∧
    -Real.log (359897 / 500000) ≤ (16439511 / 50000000) := by
  have h := checkLog_sound (w := (140103 / 859897)) (n := 12)
    (lo := (328790219 / 1000000000)) (hi := (16439511 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 359897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 359897) = 1/(359897 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-16439511 / 50000000) (-328790219 / 1000000000) (Real.log (359897 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (9894117 / 40000000) ≤ -Real.log (1000000 / 1280631) ∧
    -Real.log (1000000 / 1280631) ≤ (123676463 / 500000000) := by
  have h := checkLog_sound (w := (280631 / 2280631)) (n := 12)
    (lo := (9894117 / 40000000)) (hi := (123676463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280631 / 1000000) = 1/(1000000 / 1280631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (9894117 / 40000000) (123676463 / 500000000) (Real.log (1280631 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1280631 / 1000000) = -Real.log (1000000 / 1280631) := by
    rw [show ((1280631 / 1000000) : ℝ) = ((1000000 / 1280631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (8234521 / 25000000) ≤ -Real.log (719369 / 1000000) ∧
    -Real.log (719369 / 1000000) ≤ (329380841 / 1000000000) := by
  have h := checkLog_sound (w := (280631 / 1719369)) (n := 12)
    (lo := (8234521 / 25000000)) (hi := (329380841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 719369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 719369) = 1/(719369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-329380841 / 1000000000) (-8234521 / 25000000) (Real.log (719369 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (92217993 / 500000000) ≤ -Real.log (50000 / 60127) ∧
    -Real.log (50000 / 60127) ≤ (184435987 / 1000000000) := by
  have h := checkLog_sound (w := (10127 / 110127)) (n := 12)
    (lo := (92217993 / 500000000)) (hi := (184435987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60127 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60127 / 50000) = 1/(50000 / 60127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (92217993 / 500000000) (184435987 / 1000000000) (Real.log (60127 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (60127 / 50000) = -Real.log (50000 / 60127) := by
    rw [show ((60127 / 50000) : ℝ) = ((50000 / 60127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (113161801 / 500000000) ≤ -Real.log (39873 / 50000) ∧
    -Real.log (39873 / 50000) ≤ (226323603 / 1000000000) := by
  have h := checkLog_sound (w := (10127 / 89873)) (n := 12)
    (lo := (113161801 / 500000000)) (hi := (226323603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39873) = 1/(39873 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-226323603 / 1000000000) (-113161801 / 500000000) (Real.log (39873 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (92351027 / 500000000) ≤ -Real.log (50000 / 60143) ∧
    -Real.log (50000 / 60143) ≤ (36940411 / 200000000) := by
  have h := checkLog_sound (w := (10143 / 110143)) (n := 12)
    (lo := (92351027 / 500000000)) (hi := (36940411 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60143 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60143 / 50000) = 1/(50000 / 60143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (92351027 / 500000000) (36940411 / 200000000) (Real.log (60143 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60143 / 50000) = -Real.log (50000 / 60143) := by
    rw [show ((60143 / 50000) : ℝ) = ((50000 / 60143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (56681239 / 250000000) ≤ -Real.log (39857 / 50000) ∧
    -Real.log (39857 / 50000) ≤ (226724957 / 1000000000) := by
  have h := checkLog_sound (w := (10143 / 89857)) (n := 12)
    (lo := (56681239 / 250000000)) (hi := (226724957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39857) = 1/(39857 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-226724957 / 1000000000) (-56681239 / 250000000) (Real.log (39857 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (415999267 / 500000000) ≤ -Real.log (500000000000 / 1148953301127) ∧
    -Real.log (500000000000 / 1148953301127) ≤ (103999817 / 125000000) := by
  have h := checkLog_sound (w := (148953301127 / 2148953301127)) (n := 12)
    (lo := (69425677 / 500000000)) (hi := (27770271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148953301127 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1148953301127 / 1000000000000) = 1/(500000000000 / 1148953301127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (415999267 / 500000000) (103999817 / 125000000) (Real.log (1148953301127 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1148953301127 / 500000000000) = -Real.log (500000000000 / 1148953301127) := by
    rw [show ((1148953301127 / 500000000000) : ℝ) = ((500000000000 / 1148953301127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (833385559 / 1000000000) ≤ -Real.log (500000000000 / 1150548033527) ∧
    -Real.log (500000000000 / 1150548033527) ≤ (833385561 / 1000000000) := by
  have h := checkLog_sound (w := (150548033527 / 2150548033527)) (n := 12)
    (lo := (140238379 / 1000000000)) (hi := (7011919 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150548033527 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1150548033527 / 1000000000000) = 1/(500000000000 / 1150548033527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (833385559 / 1000000000) (833385561 / 1000000000) (Real.log (1150548033527 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1150548033527 / 500000000000) = -Real.log (500000000000 / 1150548033527) := by
    rw [show ((1150548033527 / 500000000000) : ℝ) = ((500000000000 / 1150548033527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (575811221 / 1000000000) ≤ -Real.log (250000000000 / 444643189579) ∧
    -Real.log (250000000000 / 444643189579) ≤ (287905611 / 500000000) := by
  have h := checkLog_sound (w := (194643189579 / 694643189579)) (n := 12)
    (lo := (575811221 / 1000000000)) (hi := (287905611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444643189579 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444643189579 / 250000000000) = 1/(250000000000 / 444643189579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (575811221 / 1000000000) (287905611 / 500000000) (Real.log (444643189579 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (444643189579 / 250000000000) = -Real.log (250000000000 / 444643189579) := by
    rw [show ((444643189579 / 250000000000) : ℝ) = ((250000000000 / 444643189579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (115346753 / 200000000) ≤ -Real.log (250000000000 / 445053581681) ∧
    -Real.log (250000000000 / 445053581681) ≤ (288366883 / 500000000) := by
  have h := checkLog_sound (w := (195053581681 / 695053581681)) (n := 12)
    (lo := (115346753 / 200000000)) (hi := (288366883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((445053581681 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(445053581681 / 250000000000) = 1/(250000000000 / 445053581681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (115346753 / 200000000) (288366883 / 500000000) (Real.log (445053581681 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (445053581681 / 250000000000) = -Real.log (250000000000 / 445053581681) := by
    rw [show ((445053581681 / 250000000000) : ℝ) = ((250000000000 / 445053581681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (102689897 / 250000000) ≤ -Real.log (125000000000 / 188495347729) ∧
    -Real.log (125000000000 / 188495347729) ≤ (410759589 / 1000000000) := by
  have h := checkLog_sound (w := (63495347729 / 313495347729)) (n := 12)
    (lo := (102689897 / 250000000)) (hi := (410759589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188495347729 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188495347729 / 125000000000) = 1/(125000000000 / 188495347729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (102689897 / 250000000) (410759589 / 1000000000) (Real.log (188495347729 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (188495347729 / 125000000000) = -Real.log (125000000000 / 188495347729) := by
    rw [show ((188495347729 / 125000000000) : ℝ) = ((125000000000 / 188495347729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (411427011 / 1000000000) ≤ -Real.log (5000000000 / 7544847831) ∧
    -Real.log (5000000000 / 7544847831) ≤ (102856753 / 250000000) := by
  have h := checkLog_sound (w := (2544847831 / 12544847831)) (n := 12)
    (lo := (411427011 / 1000000000)) (hi := (102856753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7544847831 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7544847831 / 5000000000) = 1/(5000000000 / 7544847831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (411427011 / 1000000000) (102856753 / 250000000) (Real.log (7544847831 / 5000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7544847831 / 5000000000) = -Real.log (5000000000 / 7544847831) := by
    rw [show ((7544847831 / 5000000000) : ℝ) = ((5000000000 / 7544847831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21011451 / 500000000) ≤ -Real.log (2397119551 / 2500000000) ∧
    -Real.log (2397119551 / 2500000000) ≤ (42022903 / 1000000000) := by
  have h := checkLog_sound (w := (102880449 / 4897119551)) (n := 12)
    (lo := (21011451 / 500000000)) (hi := (42022903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2397119551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2397119551) = 1/(2397119551 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-42022903 / 1000000000) (-21011451 / 500000000) (Real.log (2397119551 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8377523 / 200000000) ≤ -Real.log (2397443871 / 2500000000) ∧
    -Real.log (2397443871 / 2500000000) ≤ (327247 / 7812500) := by
  have h := checkLog_sound (w := (102556129 / 4897443871)) (n := 12)
    (lo := (8377523 / 200000000)) (hi := (327247 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2397443871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2397443871) = 1/(2397443871 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-327247 / 7812500) (-8377523 / 200000000) (Real.log (2397443871 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell245

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell246Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell246
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (332698383 / 1000000000) ≤ -Real.log (5120 / 7141) ∧
    -Real.log (5120 / 7141) ≤ (20793649 / 62500000) := by
  have h := checkLog_sound (w := (2021 / 12261)) (n := 12)
    (lo := (332698383 / 1000000000)) (hi := (20793649 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7141 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7141 / 5120) = 1/(5120 / 7141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (332698383 / 1000000000) (20793649 / 62500000) (Real.log (7141 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7141 / 5120) = -Real.log (5120 / 7141) := by
    rw [show ((7141 / 5120) : ℝ) = ((5120 / 7141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (6275937 / 12500000) ≤ -Real.log (3099 / 5120) ∧
    -Real.log (3099 / 5120) ≤ (502074961 / 1000000000) := by
  have h := checkLog_sound (w := (2021 / 8219)) (n := 12)
    (lo := (6275937 / 12500000)) (hi := (502074961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3099) = 1/(3099 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-502074961 / 1000000000) (-6275937 / 12500000) (Real.log (3099 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (166139093 / 500000000) ≤ -Real.log (2560 / 3569) ∧
    -Real.log (2560 / 3569) ≤ (332278187 / 1000000000) := by
  have h := checkLog_sound (w := (1009 / 6129)) (n := 12)
    (lo := (166139093 / 500000000)) (hi := (332278187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3569 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3569 / 2560) = 1/(2560 / 3569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (166139093 / 500000000) (332278187 / 1000000000) (Real.log (3569 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3569 / 2560) = -Real.log (2560 / 3569) := by
    rw [show ((3569 / 2560) : ℝ) = ((2560 / 3569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (250553687 / 500000000) ≤ -Real.log (1551 / 2560) ∧
    -Real.log (1551 / 2560) ≤ (4008859 / 8000000) := by
  have h := checkLog_sound (w := (1009 / 4111)) (n := 12)
    (lo := (250553687 / 500000000)) (hi := (4008859 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1551) = 1/(1551 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4008859 / 8000000) (-250553687 / 500000000) (Real.log (1551 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15459509 / 62500000) ≤ -Real.log (100000 / 128063) ∧
    -Real.log (100000 / 128063) ≤ (49470429 / 200000000) := by
  have h := checkLog_sound (w := (28063 / 228063)) (n := 12)
    (lo := (15459509 / 62500000)) (hi := (49470429 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128063 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128063 / 100000) = 1/(100000 / 128063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15459509 / 62500000) (49470429 / 200000000) (Real.log (128063 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (128063 / 100000) = -Real.log (100000 / 128063) := by
    rw [show ((128063 / 100000) : ℝ) = ((100000 / 128063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6587589 / 20000000) ≤ -Real.log (71937 / 100000) ∧
    -Real.log (71937 / 100000) ≤ (329379451 / 1000000000) := by
  have h := checkLog_sound (w := (28063 / 171937)) (n := 12)
    (lo := (6587589 / 20000000)) (hi := (329379451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 71937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 71937) = 1/(71937 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-329379451 / 1000000000) (-6587589 / 20000000) (Real.log (71937 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (30960397 / 125000000) ≤ -Real.log (500000 / 640527) ∧
    -Real.log (500000 / 640527) ≤ (247683177 / 1000000000) := by
  have h := checkLog_sound (w := (140527 / 1140527)) (n := 12)
    (lo := (30960397 / 125000000)) (hi := (247683177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640527 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640527 / 500000) = 1/(500000 / 640527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (30960397 / 125000000) (247683177 / 1000000000) (Real.log (640527 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (640527 / 500000) = -Real.log (500000 / 640527) := by
    rw [show ((640527 / 500000) : ℝ) = ((500000 / 640527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (82492257 / 250000000) ≤ -Real.log (359473 / 500000) ∧
    -Real.log (359473 / 500000) ≤ (329969029 / 1000000000) := by
  have h := checkLog_sound (w := (140527 / 859473)) (n := 12)
    (lo := (82492257 / 250000000)) (hi := (329969029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 359473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 359473) = 1/(359473 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-329969029 / 1000000000) (-82492257 / 250000000) (Real.log (359473 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (184701223 / 1000000000) ≤ -Real.log (1000000 / 1202859) ∧
    -Real.log (1000000 / 1202859) ≤ (23087653 / 125000000) := by
  have h := checkLog_sound (w := (202859 / 2202859)) (n := 12)
    (lo := (184701223 / 1000000000)) (hi := (23087653 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202859 / 1000000) = 1/(1000000 / 1202859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (184701223 / 1000000000) (23087653 / 125000000) (Real.log (1202859 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1202859 / 1000000) = -Real.log (1000000 / 1202859) := by
    rw [show ((1202859 / 1000000) : ℝ) = ((1000000 / 1202859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (113361851 / 500000000) ≤ -Real.log (797141 / 1000000) ∧
    -Real.log (797141 / 1000000) ≤ (226723703 / 1000000000) := by
  have h := checkLog_sound (w := (202859 / 1797141)) (n := 12)
    (lo := (113361851 / 500000000)) (hi := (226723703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797141) = 1/(797141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-226723703 / 1000000000) (-113361851 / 500000000) (Real.log (797141 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (184968051 / 1000000000) ≤ -Real.log (50000 / 60159) ∧
    -Real.log (50000 / 60159) ≤ (46242013 / 250000000) := by
  have h := checkLog_sound (w := (10159 / 110159)) (n := 12)
    (lo := (184968051 / 1000000000)) (hi := (46242013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60159 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60159 / 50000) = 1/(50000 / 60159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (184968051 / 1000000000) (46242013 / 250000000) (Real.log (60159 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60159 / 50000) = -Real.log (50000 / 60159) := by
    rw [show ((60159 / 50000) : ℝ) = ((50000 / 60159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28390809 / 125000000) ≤ -Real.log (39841 / 50000) ∧
    -Real.log (39841 / 50000) ≤ (227126473 / 1000000000) := by
  have h := checkLog_sound (w := (10159 / 89841)) (n := 12)
    (lo := (28390809 / 125000000)) (hi := (227126473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39841) = 1/(39841 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-227126473 / 1000000000) (-28390809 / 125000000) (Real.log (39841 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (833385559 / 1000000000) ≤ -Real.log (250000000000 / 575274016763) ∧
    -Real.log (250000000000 / 575274016763) ≤ (833385561 / 1000000000) := by
  have h := checkLog_sound (w := (75274016763 / 1075274016763)) (n := 12)
    (lo := (140238379 / 1000000000)) (hi := (7011919 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575274016763 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(575274016763 / 500000000000) = 1/(250000000000 / 575274016763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (833385559 / 1000000000) (833385561 / 1000000000) (Real.log (575274016763 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (575274016763 / 250000000000) = -Real.log (250000000000 / 575274016763) := by
    rw [show ((575274016763 / 250000000000) : ℝ) = ((250000000000 / 575274016763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (834773343 / 1000000000) ≤ -Real.log (250000000000 / 576072926751) ∧
    -Real.log (250000000000 / 576072926751) ≤ (166954669 / 200000000) := by
  have h := checkLog_sound (w := (76072926751 / 1076072926751)) (n := 12)
    (lo := (141626163 / 1000000000)) (hi := (35406541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576072926751 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(576072926751 / 500000000000) = 1/(250000000000 / 576072926751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (834773343 / 1000000000) (166954669 / 200000000) (Real.log (576072926751 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (576072926751 / 250000000000) = -Real.log (250000000000 / 576072926751) := by
    rw [show ((576072926751 / 250000000000) : ℝ) = ((250000000000 / 576072926751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (288365797 / 500000000) ≤ -Real.log (100000000000 / 178021046193) ∧
    -Real.log (100000000000 / 178021046193) ≤ (115346319 / 200000000) := by
  have h := checkLog_sound (w := (78021046193 / 278021046193)) (n := 12)
    (lo := (288365797 / 500000000)) (hi := (115346319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178021046193 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178021046193 / 100000000000) = 1/(100000000000 / 178021046193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (288365797 / 500000000) (115346319 / 200000000) (Real.log (178021046193 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (178021046193 / 100000000000) = -Real.log (100000000000 / 178021046193) := by
    rw [show ((178021046193 / 100000000000) : ℝ) = ((100000000000 / 178021046193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (144413051 / 250000000) ≤ -Real.log (500000000000 / 890925048613) ∧
    -Real.log (500000000000 / 890925048613) ≤ (115530441 / 200000000) := by
  have h := checkLog_sound (w := (390925048613 / 1390925048613)) (n := 12)
    (lo := (144413051 / 250000000)) (hi := (115530441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((890925048613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(890925048613 / 500000000000) = 1/(500000000000 / 890925048613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (144413051 / 250000000) (115530441 / 200000000) (Real.log (890925048613 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (890925048613 / 500000000000) = -Real.log (500000000000 / 890925048613) := by
    rw [show ((890925048613 / 500000000000) : ℝ) = ((500000000000 / 890925048613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (16456997 / 40000000) ≤ -Real.log (500000000000 / 754483209369) ∧
    -Real.log (500000000000 / 754483209369) ≤ (205712463 / 500000000) := by
  have h := checkLog_sound (w := (254483209369 / 1254483209369)) (n := 12)
    (lo := (16456997 / 40000000)) (hi := (205712463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754483209369 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754483209369 / 500000000000) = 1/(500000000000 / 754483209369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (16456997 / 40000000) (205712463 / 500000000) (Real.log (754483209369 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (754483209369 / 500000000000) = -Real.log (500000000000 / 754483209369) := by
    rw [show ((754483209369 / 500000000000) : ℝ) = ((500000000000 / 754483209369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (103023631 / 250000000) ≤ -Real.log (125000000000 / 188747144901) ∧
    -Real.log (125000000000 / 188747144901) ≤ (16483781 / 40000000) := by
  have h := checkLog_sound (w := (63747144901 / 313747144901)) (n := 12)
    (lo := (103023631 / 250000000)) (hi := (16483781 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188747144901 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188747144901 / 125000000000) = 1/(125000000000 / 188747144901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (103023631 / 250000000) (16483781 / 40000000) (Real.log (188747144901 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (188747144901 / 125000000000) = -Real.log (125000000000 / 188747144901) := by
    rw [show ((188747144901 / 125000000000) : ℝ) = ((125000000000 / 188747144901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2107921 / 50000000) ≤ -Real.log (2396794719 / 2500000000) ∧
    -Real.log (2396794719 / 2500000000) ≤ (42158421 / 1000000000) := by
  have h := checkLog_sound (w := (103205281 / 4896794719)) (n := 12)
    (lo := (2107921 / 50000000)) (hi := (42158421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2396794719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2396794719) = 1/(2396794719 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-42158421 / 1000000000) (-2107921 / 50000000) (Real.log (2396794719 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (42022479 / 1000000000) ≤ -Real.log (958848226119 / 1000000000000) ∧
    -Real.log (958848226119 / 1000000000000) ≤ (525281 / 12500000) := by
  have h := checkLog_sound (w := (41151773881 / 1958848226119)) (n := 12)
    (lo := (42022479 / 1000000000)) (hi := (525281 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958848226119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958848226119) = 1/(958848226119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-525281 / 12500000) (-42022479 / 1000000000) (Real.log (958848226119 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell246

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell247Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell247
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (83279601 / 250000000) ≤ -Real.log (640 / 893) ∧
    -Real.log (640 / 893) ≤ (66623681 / 200000000) := by
  have h := checkLog_sound (w := (253 / 1533)) (n := 12)
    (lo := (83279601 / 250000000)) (hi := (66623681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((893 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(893 / 640) = 1/(640 / 893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (83279601 / 250000000) (66623681 / 200000000) (Real.log (893 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (893 / 640) = -Real.log (640 / 893) := by
    rw [show ((893 / 640) : ℝ) = ((640 / 893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (503043483 / 1000000000) ≤ -Real.log (387 / 640) ∧
    -Real.log (387 / 640) ≤ (125760871 / 250000000) := by
  have h := checkLog_sound (w := (253 / 1027)) (n := 12)
    (lo := (503043483 / 1000000000)) (hi := (125760871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 387) = 1/(387 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-125760871 / 250000000) (-503043483 / 1000000000) (Real.log (387 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (332698383 / 1000000000) ≤ -Real.log (5120 / 7141) ∧
    -Real.log (5120 / 7141) ≤ (20793649 / 62500000) := by
  have h := checkLog_sound (w := (2021 / 12261)) (n := 12)
    (lo := (332698383 / 1000000000)) (hi := (20793649 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7141 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7141 / 5120) = 1/(5120 / 7141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (332698383 / 1000000000) (20793649 / 62500000) (Real.log (7141 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7141 / 5120) = -Real.log (5120 / 7141) := by
    rw [show ((7141 / 5120) : ℝ) = ((5120 / 7141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (6275937 / 12500000) ≤ -Real.log (3099 / 5120) ∧
    -Real.log (3099 / 5120) ≤ (502074961 / 1000000000) := by
  have h := checkLog_sound (w := (2021 / 8219)) (n := 12)
    (lo := (6275937 / 12500000)) (hi := (502074961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3099) = 1/(3099 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-502074961 / 1000000000) (-6275937 / 12500000) (Real.log (3099 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (49536479 / 200000000) ≤ -Real.log (1000000 / 1281053) ∧
    -Real.log (1000000 / 1281053) ≤ (61920599 / 250000000) := by
  have h := checkLog_sound (w := (281053 / 2281053)) (n := 12)
    (lo := (49536479 / 200000000)) (hi := (61920599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281053 / 1000000) = 1/(1000000 / 1281053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (49536479 / 200000000) (61920599 / 250000000) (Real.log (1281053 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1281053 / 1000000) = -Real.log (1000000 / 1281053) := by
    rw [show ((1281053 / 1000000) : ℝ) = ((1000000 / 1281053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (329967637 / 1000000000) ≤ -Real.log (718947 / 1000000) ∧
    -Real.log (718947 / 1000000) ≤ (164983819 / 500000000) := by
  have h := checkLog_sound (w := (281053 / 1718947)) (n := 12)
    (lo := (329967637 / 1000000000)) (hi := (164983819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718947) = 1/(718947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-164983819 / 500000000) (-329967637 / 1000000000) (Real.log (718947 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (124006659 / 500000000) ≤ -Real.log (1000000 / 1281477) ∧
    -Real.log (1000000 / 1281477) ≤ (248013319 / 1000000000) := by
  have h := checkLog_sound (w := (281477 / 2281477)) (n := 12)
    (lo := (124006659 / 500000000)) (hi := (248013319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281477 / 1000000) = 1/(1000000 / 1281477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (124006659 / 500000000) (248013319 / 1000000000) (Real.log (1281477 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1281477 / 1000000) = -Real.log (1000000 / 1281477) := by
    rw [show ((1281477 / 1000000) : ℝ) = ((1000000 / 1281477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (165278781 / 500000000) ≤ -Real.log (718523 / 1000000) ∧
    -Real.log (718523 / 1000000) ≤ (330557563 / 1000000000) := by
  have h := checkLog_sound (w := (281477 / 1718523)) (n := 12)
    (lo := (165278781 / 500000000)) (hi := (330557563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718523) = 1/(718523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-330557563 / 1000000000) (-165278781 / 500000000) (Real.log (718523 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9248361 / 50000000) ≤ -Real.log (1000000 / 1203179) ∧
    -Real.log (1000000 / 1203179) ≤ (184967221 / 1000000000) := by
  have h := checkLog_sound (w := (203179 / 2203179)) (n := 12)
    (lo := (9248361 / 50000000)) (hi := (184967221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203179 / 1000000) = 1/(1000000 / 1203179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9248361 / 50000000) (184967221 / 1000000000) (Real.log (1203179 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1203179 / 1000000) = -Real.log (1000000 / 1203179) := by
    rw [show ((1203179 / 1000000) : ℝ) = ((1000000 / 1203179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (227125217 / 1000000000) ≤ -Real.log (796821 / 1000000) ∧
    -Real.log (796821 / 1000000) ≤ (113562609 / 500000000) := by
  have h := checkLog_sound (w := (203179 / 1796821)) (n := 12)
    (lo := (227125217 / 1000000000)) (hi := (113562609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796821) = 1/(796821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-113562609 / 500000000) (-227125217 / 1000000000) (Real.log (796821 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (92616989 / 500000000) ≤ -Real.log (2000 / 2407) ∧
    -Real.log (2000 / 2407) ≤ (185233979 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 4407)) (n := 12)
    (lo := (92616989 / 500000000)) (hi := (185233979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2407 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2407 / 2000) = 1/(2000 / 2407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (92616989 / 500000000) (185233979 / 1000000000) (Real.log (2407 / 2000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (2407 / 2000) = -Real.log (2000 / 2407) := by
    rw [show ((2407 / 2000) : ℝ) = ((2000 / 2407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (227528149 / 1000000000) ≤ -Real.log (1593 / 2000) ∧
    -Real.log (1593 / 2000) ≤ (4550563 / 20000000) := by
  have h := checkLog_sound (w := (407 / 3593)) (n := 12)
    (lo := (227528149 / 1000000000)) (hi := (4550563 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1593) = 1/(1593 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4550563 / 20000000) (-227528149 / 1000000000) (Real.log (1593 / 2000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (834773343 / 1000000000) ≤ -Real.log (500000000000 / 1152145853501) ∧
    -Real.log (500000000000 / 1152145853501) ≤ (166954669 / 200000000) := by
  have h := checkLog_sound (w := (152145853501 / 2152145853501)) (n := 12)
    (lo := (141626163 / 1000000000)) (hi := (35406541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152145853501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1152145853501 / 1000000000000) = 1/(500000000000 / 1152145853501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (834773343 / 1000000000) (166954669 / 200000000) (Real.log (1152145853501 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1152145853501 / 500000000000) = -Real.log (500000000000 / 1152145853501) := by
    rw [show ((1152145853501 / 500000000000) : ℝ) = ((500000000000 / 1152145853501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (836161887 / 1000000000) ≤ -Real.log (250000000000 / 576873385013) ∧
    -Real.log (250000000000 / 576873385013) ≤ (836161889 / 1000000000) := by
  have h := checkLog_sound (w := (76873385013 / 1076873385013)) (n := 12)
    (lo := (143014707 / 1000000000)) (hi := (35753677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576873385013 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(576873385013 / 500000000000) = 1/(250000000000 / 576873385013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (836161887 / 1000000000) (836161889 / 1000000000) (Real.log (576873385013 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (576873385013 / 250000000000) = -Real.log (250000000000 / 576873385013) := by
    rw [show ((576873385013 / 250000000000) : ℝ) = ((250000000000 / 576873385013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (577650033 / 1000000000) ≤ -Real.log (500000000000 / 890923113943) ∧
    -Real.log (500000000000 / 890923113943) ≤ (288825017 / 500000000) := by
  have h := checkLog_sound (w := (390923113943 / 1390923113943)) (n := 12)
    (lo := (577650033 / 1000000000)) (hi := (288825017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((890923113943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(890923113943 / 500000000000) = 1/(500000000000 / 890923113943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (577650033 / 1000000000) (288825017 / 500000000) (Real.log (890923113943 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (890923113943 / 500000000000) = -Real.log (500000000000 / 890923113943) := by
    rw [show ((890923113943 / 500000000000) : ℝ) = ((500000000000 / 890923113943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (578570881 / 1000000000) ≤ -Real.log (62500000000 / 111467987107) ∧
    -Real.log (62500000000 / 111467987107) ≤ (289285441 / 500000000) := by
  have h := checkLog_sound (w := (48967987107 / 173967987107)) (n := 12)
    (lo := (578570881 / 1000000000)) (hi := (289285441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111467987107 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111467987107 / 62500000000) = 1/(62500000000 / 111467987107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (578570881 / 1000000000) (289285441 / 500000000) (Real.log (111467987107 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (111467987107 / 62500000000) = -Real.log (62500000000 / 111467987107) := by
    rw [show ((111467987107 / 62500000000) : ℝ) = ((62500000000 / 111467987107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (206046219 / 500000000) ≤ -Real.log (500000000000 / 754987004609) ∧
    -Real.log (500000000000 / 754987004609) ≤ (412092439 / 1000000000) := by
  have h := checkLog_sound (w := (254987004609 / 1254987004609)) (n := 12)
    (lo := (206046219 / 500000000)) (hi := (412092439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754987004609 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754987004609 / 500000000000) = 1/(500000000000 / 754987004609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (206046219 / 500000000) (412092439 / 1000000000) (Real.log (754987004609 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (754987004609 / 500000000000) = -Real.log (500000000000 / 754987004609) := by
    rw [show ((754987004609 / 500000000000) : ℝ) = ((500000000000 / 754987004609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (412762127 / 1000000000) ≤ -Real.log (500000000000 / 755492780917) ∧
    -Real.log (500000000000 / 755492780917) ≤ (25797633 / 62500000) := by
  have h := checkLog_sound (w := (255492780917 / 1255492780917)) (n := 12)
    (lo := (412762127 / 1000000000)) (hi := (25797633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755492780917 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755492780917 / 500000000000) = 1/(500000000000 / 755492780917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (412762127 / 1000000000) (25797633 / 62500000) (Real.log (755492780917 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (755492780917 / 500000000000) = -Real.log (500000000000 / 755492780917) := by
    rw [show ((755492780917 / 500000000000) : ℝ) = ((500000000000 / 755492780917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (42294171 / 1000000000) ≤ -Real.log (3834351 / 4000000) ∧
    -Real.log (3834351 / 4000000) ≤ (10573543 / 250000000) := by
  have h := checkLog_sound (w := (165649 / 7834351)) (n := 12)
    (lo := (42294171 / 1000000000)) (hi := (10573543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000000 / 3834351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000000 / 3834351) = 1/(3834351 / 4000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-10573543 / 250000000) (-42294171 / 1000000000) (Real.log (3834351 / 4000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (42157997 / 1000000000) ≤ -Real.log (958718293959 / 1000000000000) ∧
    -Real.log (958718293959 / 1000000000000) ≤ (21078999 / 500000000) := by
  have h := checkLog_sound (w := (41281706041 / 1958718293959)) (n := 12)
    (lo := (42157997 / 1000000000)) (hi := (21078999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958718293959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958718293959) = 1/(958718293959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21078999 / 500000000) (-42157997 / 1000000000) (Real.log (958718293959 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell247

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell248Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell248
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (333538249 / 1000000000) ≤ -Real.log (5120 / 7147) ∧
    -Real.log (5120 / 7147) ≤ (1334153 / 4000000) := by
  have h := checkLog_sound (w := (2027 / 12267)) (n := 12)
    (lo := (333538249 / 1000000000)) (hi := (1334153 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7147 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7147 / 5120) = 1/(5120 / 7147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (333538249 / 1000000000) (1334153 / 4000000) (Real.log (7147 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7147 / 5120) = -Real.log (5120 / 7147) := by
    rw [show ((7147 / 5120) : ℝ) = ((5120 / 7147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (100802589 / 200000000) ≤ -Real.log (3093 / 5120) ∧
    -Real.log (3093 / 5120) ≤ (252006473 / 500000000) := by
  have h := checkLog_sound (w := (2027 / 8213)) (n := 12)
    (lo := (100802589 / 200000000)) (hi := (252006473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3093) = 1/(3093 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-252006473 / 500000000) (-100802589 / 200000000) (Real.log (3093 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (83279601 / 250000000) ≤ -Real.log (640 / 893) ∧
    -Real.log (640 / 893) ≤ (66623681 / 200000000) := by
  have h := checkLog_sound (w := (253 / 1533)) (n := 12)
    (lo := (83279601 / 250000000)) (hi := (66623681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((893 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(893 / 640) = 1/(640 / 893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (83279601 / 250000000) (66623681 / 200000000) (Real.log (893 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (893 / 640) = -Real.log (640 / 893) := by
    rw [show ((893 / 640) : ℝ) = ((640 / 893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (503043483 / 1000000000) ≤ -Real.log (387 / 640) ∧
    -Real.log (387 / 640) ≤ (125760871 / 250000000) := by
  have h := checkLog_sound (w := (253 / 1027)) (n := 12)
    (lo := (503043483 / 1000000000)) (hi := (125760871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 387) = 1/(387 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-125760871 / 250000000) (-503043483 / 1000000000) (Real.log (387 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (124006269 / 500000000) ≤ -Real.log (250000 / 320369) ∧
    -Real.log (250000 / 320369) ≤ (248012539 / 1000000000) := by
  have h := checkLog_sound (w := (70369 / 570369)) (n := 12)
    (lo := (124006269 / 500000000)) (hi := (248012539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320369 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320369 / 250000) = 1/(250000 / 320369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (124006269 / 500000000) (248012539 / 1000000000) (Real.log (320369 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (320369 / 250000) = -Real.log (250000 / 320369) := by
    rw [show ((320369 / 250000) : ℝ) = ((250000 / 320369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (330556171 / 1000000000) ≤ -Real.log (179631 / 250000) ∧
    -Real.log (179631 / 250000) ≤ (82639043 / 250000000) := by
  have h := checkLog_sound (w := (70369 / 429631)) (n := 12)
    (lo := (330556171 / 1000000000)) (hi := (82639043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 179631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 179631) = 1/(179631 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-82639043 / 250000000) (-330556171 / 1000000000) (Real.log (179631 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (62086033 / 250000000) ≤ -Real.log (1000000 / 1281901) ∧
    -Real.log (1000000 / 1281901) ≤ (248344133 / 1000000000) := by
  have h := checkLog_sound (w := (281901 / 2281901)) (n := 12)
    (lo := (62086033 / 250000000)) (hi := (248344133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281901 / 1000000) = 1/(1000000 / 1281901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (62086033 / 250000000) (248344133 / 1000000000) (Real.log (1281901 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1281901 / 1000000) = -Real.log (1000000 / 1281901) := by
    rw [show ((1281901 / 1000000) : ℝ) = ((1000000 / 1281901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (82786959 / 250000000) ≤ -Real.log (718099 / 1000000) ∧
    -Real.log (718099 / 1000000) ≤ (331147837 / 1000000000) := by
  have h := checkLog_sound (w := (281901 / 1718099)) (n := 12)
    (lo := (82786959 / 250000000)) (hi := (331147837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718099) = 1/(718099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-331147837 / 1000000000) (-82786959 / 250000000) (Real.log (718099 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (185233147 / 1000000000) ≤ -Real.log (1000000 / 1203499) ∧
    -Real.log (1000000 / 1203499) ≤ (46308287 / 250000000) := by
  have h := checkLog_sound (w := (203499 / 2203499)) (n := 12)
    (lo := (185233147 / 1000000000)) (hi := (46308287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203499 / 1000000) = 1/(1000000 / 1203499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (185233147 / 1000000000) (46308287 / 250000000) (Real.log (1203499 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1203499 / 1000000) = -Real.log (1000000 / 1203499) := by
    rw [show ((1203499 / 1000000) : ℝ) = ((1000000 / 1203499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (113763447 / 500000000) ≤ -Real.log (796501 / 1000000) ∧
    -Real.log (796501 / 1000000) ≤ (45505379 / 200000000) := by
  have h := checkLog_sound (w := (203499 / 1796501)) (n := 12)
    (lo := (113763447 / 500000000)) (hi := (45505379 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796501) = 1/(796501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-45505379 / 200000000) (-113763447 / 500000000) (Real.log (796501 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (92749917 / 500000000) ≤ -Real.log (50000 / 60191) ∧
    -Real.log (50000 / 60191) ≤ (37099967 / 200000000) := by
  have h := checkLog_sound (w := (10191 / 110191)) (n := 12)
    (lo := (92749917 / 500000000)) (hi := (37099967 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60191 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60191 / 50000) = 1/(50000 / 60191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (92749917 / 500000000) (37099967 / 200000000) (Real.log (60191 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60191 / 50000) = -Real.log (50000 / 60191) := by
    rw [show ((60191 / 50000) : ℝ) = ((50000 / 60191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (56982497 / 250000000) ≤ -Real.log (39809 / 50000) ∧
    -Real.log (39809 / 50000) ≤ (227929989 / 1000000000) := by
  have h := checkLog_sound (w := (10191 / 89809)) (n := 12)
    (lo := (56982497 / 250000000)) (hi := (227929989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39809) = 1/(39809 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-227929989 / 1000000000) (-56982497 / 250000000) (Real.log (39809 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (836161887 / 1000000000) ≤ -Real.log (20000000000 / 46149870801) ∧
    -Real.log (20000000000 / 46149870801) ≤ (836161889 / 1000000000) := by
  have h := checkLog_sound (w := (6149870801 / 86149870801)) (n := 12)
    (lo := (143014707 / 1000000000)) (hi := (35753677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46149870801 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(46149870801 / 40000000000) = 1/(20000000000 / 46149870801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (836161887 / 1000000000) (836161889 / 1000000000) (Real.log (46149870801 / 20000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (46149870801 / 20000000000) = -Real.log (20000000000 / 46149870801) := by
    rw [show ((46149870801 / 20000000000) : ℝ) = ((20000000000 / 46149870801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (837551193 / 1000000000) ≤ -Real.log (31250000000 / 72209424507) ∧
    -Real.log (31250000000 / 72209424507) ≤ (167510239 / 200000000) := by
  have h := checkLog_sound (w := (9709424507 / 134709424507)) (n := 12)
    (lo := (144404013 / 1000000000)) (hi := (72202007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72209424507 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(72209424507 / 62500000000) = 1/(31250000000 / 72209424507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (837551193 / 1000000000) (167510239 / 200000000) (Real.log (72209424507 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (72209424507 / 31250000000) = -Real.log (31250000000 / 72209424507) := by
    rw [show ((72209424507 / 31250000000) : ℝ) = ((31250000000 / 72209424507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (578568709 / 1000000000) ≤ -Real.log (250000000000 / 445870979953) ∧
    -Real.log (250000000000 / 445870979953) ≤ (57856871 / 100000000) := by
  have h := checkLog_sound (w := (195870979953 / 695870979953)) (n := 12)
    (lo := (578568709 / 1000000000)) (hi := (57856871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((445870979953 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(445870979953 / 250000000000) = 1/(250000000000 / 445870979953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (578568709 / 1000000000) (57856871 / 100000000) (Real.log (445870979953 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (445870979953 / 250000000000) = -Real.log (250000000000 / 445870979953) := by
    rw [show ((445870979953 / 250000000000) : ℝ) = ((250000000000 / 445870979953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4527281 / 7812500) ≤ -Real.log (500000000000 / 892565649027) ∧
    -Real.log (500000000000 / 892565649027) ≤ (579491969 / 1000000000) := by
  have h := checkLog_sound (w := (392565649027 / 1392565649027)) (n := 12)
    (lo := (4527281 / 7812500)) (hi := (579491969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((892565649027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(892565649027 / 500000000000) = 1/(500000000000 / 892565649027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (4527281 / 7812500) (579491969 / 1000000000) (Real.log (892565649027 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (892565649027 / 500000000000) = -Real.log (500000000000 / 892565649027) := by
    rw [show ((892565649027 / 500000000000) : ℝ) = ((500000000000 / 892565649027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (412760041 / 1000000000) ≤ -Real.log (31250000000 / 47218200291) ∧
    -Real.log (31250000000 / 47218200291) ≤ (206380021 / 500000000) := by
  have h := checkLog_sound (w := (15968200291 / 78468200291)) (n := 12)
    (lo := (412760041 / 1000000000)) (hi := (206380021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47218200291 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47218200291 / 31250000000) = 1/(31250000000 / 47218200291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (412760041 / 1000000000) (206380021 / 500000000) (Real.log (47218200291 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (47218200291 / 31250000000) = -Real.log (31250000000 / 47218200291) := by
    rw [show ((47218200291 / 31250000000) : ℝ) = ((31250000000 / 47218200291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (206714911 / 500000000) ≤ -Real.log (250000000000 / 377998693763) ∧
    -Real.log (250000000000 / 377998693763) ≤ (413429823 / 1000000000) := by
  have h := checkLog_sound (w := (127998693763 / 627998693763)) (n := 12)
    (lo := (206714911 / 500000000)) (hi := (413429823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377998693763 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377998693763 / 250000000000) = 1/(250000000000 / 377998693763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (206714911 / 500000000) (413429823 / 1000000000) (Real.log (377998693763 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (377998693763 / 250000000000) = -Real.log (250000000000 / 377998693763) := by
    rw [show ((377998693763 / 250000000000) : ℝ) = ((250000000000 / 377998693763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (42430153 / 1000000000) ≤ -Real.log (2396143519 / 2500000000) ∧
    -Real.log (2396143519 / 2500000000) ≤ (21215077 / 500000000) := by
  have h := checkLog_sound (w := (103856481 / 4896143519)) (n := 12)
    (lo := (42430153 / 1000000000)) (hi := (21215077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2396143519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2396143519) = 1/(2396143519 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21215077 / 500000000) (-42430153 / 1000000000) (Real.log (2396143519 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21146873 / 500000000) ≤ -Real.log (958588156999 / 1000000000000) ∧
    -Real.log (958588156999 / 1000000000000) ≤ (42293747 / 1000000000) := by
  have h := checkLog_sound (w := (41411843001 / 1958588156999)) (n := 12)
    (lo := (21146873 / 500000000)) (hi := (42293747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958588156999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958588156999) = 1/(958588156999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-42293747 / 1000000000) (-21146873 / 500000000) (Real.log (958588156999 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell248

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell249Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell249
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (333957917 / 1000000000) ≤ -Real.log (512 / 715) ∧
    -Real.log (512 / 715) ≤ (166978959 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1227)) (n := 12)
    (lo := (333957917 / 1000000000)) (hi := (166978959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715 / 512) = 1/(512 / 715) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (333957917 / 1000000000) (166978959 / 500000000) (Real.log (715 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (715 / 512) = -Real.log (512 / 715) := by
    rw [show ((715 / 512) : ℝ) = ((512 / 715) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (126245837 / 250000000) ≤ -Real.log (309 / 512) ∧
    -Real.log (309 / 512) ≤ (504983349 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 821)) (n := 12)
    (lo := (126245837 / 250000000)) (hi := (504983349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 309) = 1/(309 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-504983349 / 1000000000) (-126245837 / 250000000) (Real.log (309 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (333538249 / 1000000000) ≤ -Real.log (5120 / 7147) ∧
    -Real.log (5120 / 7147) ≤ (1334153 / 4000000) := by
  have h := checkLog_sound (w := (2027 / 12267)) (n := 12)
    (lo := (333538249 / 1000000000)) (hi := (1334153 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7147 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7147 / 5120) = 1/(5120 / 7147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (333538249 / 1000000000) (1334153 / 4000000) (Real.log (7147 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7147 / 5120) = -Real.log (5120 / 7147) := by
    rw [show ((7147 / 5120) : ℝ) = ((5120 / 7147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (100802589 / 200000000) ≤ -Real.log (3093 / 5120) ∧
    -Real.log (3093 / 5120) ≤ (252006473 / 500000000) := by
  have h := checkLog_sound (w := (2027 / 8213)) (n := 12)
    (lo := (100802589 / 200000000)) (hi := (252006473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3093) = 1/(3093 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-252006473 / 500000000) (-100802589 / 200000000) (Real.log (3093 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (31042919 / 125000000) ≤ -Real.log (10000 / 12819) ∧
    -Real.log (10000 / 12819) ≤ (248343353 / 1000000000) := by
  have h := checkLog_sound (w := (2819 / 22819)) (n := 12)
    (lo := (31042919 / 125000000)) (hi := (248343353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12819 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12819 / 10000) = 1/(10000 / 12819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (31042919 / 125000000) (248343353 / 1000000000) (Real.log (12819 / 10000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12819 / 10000) = -Real.log (10000 / 12819) := by
    rw [show ((12819 / 10000) : ℝ) = ((10000 / 12819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (331146443 / 1000000000) ≤ -Real.log (7181 / 10000) ∧
    -Real.log (7181 / 10000) ≤ (82786611 / 250000000) := by
  have h := checkLog_sound (w := (2819 / 17181)) (n := 12)
    (lo := (331146443 / 1000000000)) (hi := (82786611 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 7181) = 1/(7181 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-82786611 / 250000000) (-331146443 / 1000000000) (Real.log (7181 / 10000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (31084257 / 125000000) ≤ -Real.log (250000 / 320581) ∧
    -Real.log (250000 / 320581) ≤ (248674057 / 1000000000) := by
  have h := checkLog_sound (w := (70581 / 570581)) (n := 12)
    (lo := (31084257 / 125000000)) (hi := (248674057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320581 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320581 / 250000) = 1/(250000 / 320581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (31084257 / 125000000) (248674057 / 1000000000) (Real.log (320581 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (320581 / 250000) = -Real.log (250000 / 320581) := by
    rw [show ((320581 / 250000) : ℝ) = ((250000 / 320581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (66347413 / 200000000) ≤ -Real.log (179419 / 250000) ∧
    -Real.log (179419 / 250000) ≤ (165868533 / 500000000) := by
  have h := checkLog_sound (w := (70581 / 429419)) (n := 12)
    (lo := (66347413 / 200000000)) (hi := (165868533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 179419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 179419) = 1/(179419 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-165868533 / 500000000) (-66347413 / 200000000) (Real.log (179419 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (185499003 / 1000000000) ≤ -Real.log (1000000 / 1203819) ∧
    -Real.log (1000000 / 1203819) ≤ (46374751 / 250000000) := by
  have h := checkLog_sound (w := (203819 / 2203819)) (n := 12)
    (lo := (185499003 / 1000000000)) (hi := (46374751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203819 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203819 / 1000000) = 1/(1000000 / 1203819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (185499003 / 1000000000) (46374751 / 250000000) (Real.log (1203819 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1203819 / 1000000) = -Real.log (1000000 / 1203819) := by
    rw [show ((1203819 / 1000000) : ℝ) = ((1000000 / 1203819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (56982183 / 250000000) ≤ -Real.log (796181 / 1000000) ∧
    -Real.log (796181 / 1000000) ≤ (227928733 / 1000000000) := by
  have h := checkLog_sound (w := (203819 / 1796181)) (n := 12)
    (lo := (56982183 / 250000000)) (hi := (227928733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796181) = 1/(796181 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-227928733 / 1000000000) (-56982183 / 250000000) (Real.log (796181 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (185765619 / 1000000000) ≤ -Real.log (50000 / 60207) ∧
    -Real.log (50000 / 60207) ≤ (9288281 / 50000000) := by
  have h := checkLog_sound (w := (10207 / 110207)) (n := 12)
    (lo := (185765619 / 1000000000)) (hi := (9288281 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60207 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60207 / 50000) = 1/(50000 / 60207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (185765619 / 1000000000) (9288281 / 50000000) (Real.log (60207 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60207 / 50000) = -Real.log (50000 / 60207) := by
    rw [show ((60207 / 50000) : ℝ) = ((50000 / 60207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (57082997 / 250000000) ≤ -Real.log (39793 / 50000) ∧
    -Real.log (39793 / 50000) ≤ (228331989 / 1000000000) := by
  have h := checkLog_sound (w := (10207 / 89793)) (n := 12)
    (lo := (57082997 / 250000000)) (hi := (228331989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39793) = 1/(39793 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-228331989 / 1000000000) (-57082997 / 250000000) (Real.log (39793 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (837551193 / 1000000000) ≤ -Real.log (500000000000 / 1155350792111) ∧
    -Real.log (500000000000 / 1155350792111) ≤ (167510239 / 200000000) := by
  have h := checkLog_sound (w := (155350792111 / 2155350792111)) (n := 12)
    (lo := (144404013 / 1000000000)) (hi := (72202007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155350792111 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1155350792111 / 1000000000000) = 1/(500000000000 / 1155350792111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (837551193 / 1000000000) (167510239 / 200000000) (Real.log (1155350792111 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1155350792111 / 500000000000) = -Real.log (500000000000 / 1155350792111) := by
    rw [show ((1155350792111 / 500000000000) : ℝ) = ((500000000000 / 1155350792111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (167788253 / 200000000) ≤ -Real.log (500000000000 / 1156957928803) ∧
    -Real.log (500000000000 / 1156957928803) ≤ (838941267 / 1000000000) := by
  have h := checkLog_sound (w := (156957928803 / 2156957928803)) (n := 12)
    (lo := (29158817 / 200000000)) (hi := (72897043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156957928803 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1156957928803 / 1000000000000) = 1/(500000000000 / 1156957928803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (167788253 / 200000000) (838941267 / 1000000000) (Real.log (1156957928803 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1156957928803 / 500000000000) = -Real.log (500000000000 / 1156957928803) := by
    rw [show ((1156957928803 / 500000000000) : ℝ) = ((500000000000 / 1156957928803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (144872449 / 250000000) ≤ -Real.log (500000000000 / 892563709789) ∧
    -Real.log (500000000000 / 892563709789) ≤ (579489797 / 1000000000) := by
  have h := checkLog_sound (w := (392563709789 / 1392563709789)) (n := 12)
    (lo := (144872449 / 250000000)) (hi := (579489797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((892563709789 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(892563709789 / 500000000000) = 1/(500000000000 / 892563709789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (144872449 / 250000000) (579489797 / 1000000000) (Real.log (892563709789 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (892563709789 / 500000000000) = -Real.log (500000000000 / 892563709789) := by
    rw [show ((892563709789 / 500000000000) : ℝ) = ((500000000000 / 892563709789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (580411121 / 1000000000) ≤ -Real.log (250000000000 / 446693215323) ∧
    -Real.log (250000000000 / 446693215323) ≤ (290205561 / 500000000) := by
  have h := checkLog_sound (w := (196693215323 / 696693215323)) (n := 12)
    (lo := (580411121 / 1000000000)) (hi := (290205561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((446693215323 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(446693215323 / 250000000000) = 1/(250000000000 / 446693215323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (580411121 / 1000000000) (290205561 / 500000000) (Real.log (446693215323 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (446693215323 / 250000000000) = -Real.log (250000000000 / 446693215323) := by
    rw [show ((446693215323 / 250000000000) : ℝ) = ((250000000000 / 446693215323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (82685547 / 200000000) ≤ -Real.log (500000000000 / 755995809997) ∧
    -Real.log (500000000000 / 755995809997) ≤ (51678467 / 125000000) := by
  have h := checkLog_sound (w := (255995809997 / 1255995809997)) (n := 12)
    (lo := (82685547 / 200000000)) (hi := (51678467 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755995809997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755995809997 / 500000000000) = 1/(500000000000 / 755995809997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (82685547 / 200000000) (51678467 / 125000000) (Real.log (755995809997 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (755995809997 / 500000000000) = -Real.log (500000000000 / 755995809997) := by
    rw [show ((755995809997 / 500000000000) : ℝ) = ((500000000000 / 755995809997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (414097607 / 1000000000) ≤ -Real.log (6250000000 / 9456279999) ∧
    -Real.log (6250000000 / 9456279999) ≤ (51762201 / 125000000) := by
  have h := checkLog_sound (w := (3206279999 / 15706279999)) (n := 12)
    (lo := (414097607 / 1000000000)) (hi := (51762201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9456279999 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9456279999 / 6250000000) = 1/(6250000000 / 9456279999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (414097607 / 1000000000) (51762201 / 125000000) (Real.log (9456279999 / 6250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9456279999 / 6250000000) = -Real.log (6250000000 / 9456279999) := by
    rw [show ((9456279999 / 6250000000) : ℝ) = ((6250000000 / 9456279999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1330199 / 31250000) ≤ -Real.log (2395817151 / 2500000000) ∧
    -Real.log (2395817151 / 2500000000) ≤ (42566369 / 1000000000) := by
  have h := checkLog_sound (w := (104182849 / 4895817151)) (n := 12)
    (lo := (1330199 / 31250000)) (hi := (42566369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2395817151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2395817151) = 1/(2395817151 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-42566369 / 1000000000) (-1330199 / 31250000) (Real.log (2395817151 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1325929 / 31250000) ≤ -Real.log (958457815239 / 1000000000000) ∧
    -Real.log (958457815239 / 1000000000000) ≤ (42429729 / 1000000000) := by
  have h := checkLog_sound (w := (41542184761 / 1958457815239)) (n := 12)
    (lo := (1325929 / 31250000)) (hi := (42429729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958457815239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958457815239) = 1/(958457815239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-42429729 / 1000000000) (-1325929 / 31250000) (Real.log (958457815239 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell249

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell250Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell250
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (33437741 / 100000000) ≤ -Real.log (5120 / 7153) ∧
    -Real.log (5120 / 7153) ≤ (334377411 / 1000000000) := by
  have h := checkLog_sound (w := (2033 / 12273)) (n := 12)
    (lo := (33437741 / 100000000)) (hi := (334377411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7153 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7153 / 5120) = 1/(5120 / 7153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33437741 / 100000000) (334377411 / 1000000000) (Real.log (7153 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7153 / 5120) = -Real.log (5120 / 7153) := by
    rw [show ((7153 / 5120) : ℝ) = ((5120 / 7153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (505954693 / 1000000000) ≤ -Real.log (3087 / 5120) ∧
    -Real.log (3087 / 5120) ≤ (252977347 / 500000000) := by
  have h := checkLog_sound (w := (2033 / 8207)) (n := 12)
    (lo := (505954693 / 1000000000)) (hi := (252977347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3087) = 1/(3087 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-252977347 / 500000000) (-505954693 / 1000000000) (Real.log (3087 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (333957917 / 1000000000) ≤ -Real.log (512 / 715) ∧
    -Real.log (512 / 715) ≤ (166978959 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1227)) (n := 12)
    (lo := (333957917 / 1000000000)) (hi := (166978959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715 / 512) = 1/(512 / 715) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (333957917 / 1000000000) (166978959 / 500000000) (Real.log (715 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (715 / 512) = -Real.log (512 / 715) := by
    rw [show ((715 / 512) : ℝ) = ((512 / 715) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (126245837 / 250000000) ≤ -Real.log (309 / 512) ∧
    -Real.log (309 / 512) ≤ (504983349 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 821)) (n := 12)
    (lo := (126245837 / 250000000)) (hi := (504983349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 309) = 1/(309 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-504983349 / 1000000000) (-126245837 / 250000000) (Real.log (309 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (62168319 / 250000000) ≤ -Real.log (1000000 / 1282323) ∧
    -Real.log (1000000 / 1282323) ≤ (248673277 / 1000000000) := by
  have h := checkLog_sound (w := (282323 / 2282323)) (n := 12)
    (lo := (62168319 / 250000000)) (hi := (248673277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1282323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1282323 / 1000000) = 1/(1000000 / 1282323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (62168319 / 250000000) (248673277 / 1000000000) (Real.log (1282323 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1282323 / 1000000) = -Real.log (1000000 / 1282323) := by
    rw [show ((1282323 / 1000000) : ℝ) = ((1000000 / 1282323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (331735671 / 1000000000) ≤ -Real.log (717677 / 1000000) ∧
    -Real.log (717677 / 1000000) ≤ (41466959 / 125000000) := by
  have h := checkLog_sound (w := (282323 / 1717677)) (n := 12)
    (lo := (331735671 / 1000000000)) (hi := (41466959 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 717677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 717677) = 1/(717677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-41466959 / 125000000) (-331735671 / 1000000000) (Real.log (717677 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (249004651 / 1000000000) ≤ -Real.log (250000 / 320687) ∧
    -Real.log (250000 / 320687) ≤ (62251163 / 250000000) := by
  have h := checkLog_sound (w := (70687 / 570687)) (n := 12)
    (lo := (249004651 / 1000000000)) (hi := (62251163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320687 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320687 / 250000) = 1/(250000 / 320687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (249004651 / 1000000000) (62251163 / 250000000) (Real.log (320687 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (320687 / 250000) = -Real.log (250000 / 320687) := by
    rw [show ((320687 / 250000) : ℝ) = ((250000 / 320687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (66465607 / 200000000) ≤ -Real.log (179313 / 250000) ∧
    -Real.log (179313 / 250000) ≤ (83082009 / 250000000) := by
  have h := checkLog_sound (w := (70687 / 429313)) (n := 12)
    (lo := (66465607 / 200000000)) (hi := (83082009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 179313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 179313) = 1/(179313 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-83082009 / 250000000) (-66465607 / 200000000) (Real.log (179313 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (46441197 / 250000000) ≤ -Real.log (1000000 / 1204139) ∧
    -Real.log (1000000 / 1204139) ≤ (185764789 / 1000000000) := by
  have h := checkLog_sound (w := (204139 / 2204139)) (n := 12)
    (lo := (46441197 / 250000000)) (hi := (185764789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204139 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204139 / 1000000) = 1/(1000000 / 1204139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (46441197 / 250000000) (185764789 / 1000000000) (Real.log (1204139 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1204139 / 1000000) = -Real.log (1000000 / 1204139) := by
    rw [show ((1204139 / 1000000) : ℝ) = ((1000000 / 1204139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (228330731 / 1000000000) ≤ -Real.log (795861 / 1000000) ∧
    -Real.log (795861 / 1000000) ≤ (57082683 / 250000000) := by
  have h := checkLog_sound (w := (204139 / 1795861)) (n := 12)
    (lo := (228330731 / 1000000000)) (hi := (57082683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795861) = 1/(795861 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-57082683 / 250000000) (-228330731 / 1000000000) (Real.log (795861 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (186031333 / 1000000000) ≤ -Real.log (50000 / 60223) ∧
    -Real.log (50000 / 60223) ≤ (93015667 / 500000000) := by
  have h := checkLog_sound (w := (10223 / 110223)) (n := 12)
    (lo := (186031333 / 1000000000)) (hi := (93015667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60223 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60223 / 50000) = 1/(50000 / 60223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (186031333 / 1000000000) (93015667 / 500000000) (Real.log (60223 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60223 / 50000) = -Real.log (50000 / 60223) := by
    rw [show ((60223 / 50000) : ℝ) = ((50000 / 60223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (228734149 / 1000000000) ≤ -Real.log (39777 / 50000) ∧
    -Real.log (39777 / 50000) ≤ (4574683 / 20000000) := by
  have h := checkLog_sound (w := (10223 / 89777)) (n := 12)
    (lo := (228734149 / 1000000000)) (hi := (4574683 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39777) = 1/(39777 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4574683 / 20000000) (-228734149 / 1000000000) (Real.log (39777 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (167788253 / 200000000) ≤ -Real.log (250000000000 / 578478964401) ∧
    -Real.log (250000000000 / 578478964401) ≤ (838941267 / 1000000000) := by
  have h := checkLog_sound (w := (78478964401 / 1078478964401)) (n := 12)
    (lo := (29158817 / 200000000)) (hi := (72897043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578478964401 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(578478964401 / 500000000000) = 1/(250000000000 / 578478964401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (167788253 / 200000000) (838941267 / 1000000000) (Real.log (578478964401 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (578478964401 / 250000000000) = -Real.log (250000000000 / 578478964401) := by
    rw [show ((578478964401 / 250000000000) : ℝ) = ((250000000000 / 578478964401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (840332103 / 1000000000) ≤ -Real.log (500000000000 / 1158568189181) ∧
    -Real.log (500000000000 / 1158568189181) ≤ (168066421 / 200000000) := by
  have h := checkLog_sound (w := (158568189181 / 2158568189181)) (n := 12)
    (lo := (147184923 / 1000000000)) (hi := (36796231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158568189181 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1158568189181 / 1000000000000) = 1/(500000000000 / 1158568189181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (840332103 / 1000000000) (168066421 / 200000000) (Real.log (1158568189181 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1158568189181 / 500000000000) = -Real.log (500000000000 / 1158568189181) := by
    rw [show ((1158568189181 / 500000000000) : ℝ) = ((500000000000 / 1158568189181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (145102237 / 250000000) ≤ -Real.log (250000000000 / 446692244561) ∧
    -Real.log (250000000000 / 446692244561) ≤ (580408949 / 1000000000) := by
  have h := checkLog_sound (w := (196692244561 / 696692244561)) (n := 12)
    (lo := (145102237 / 250000000)) (hi := (580408949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((446692244561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(446692244561 / 250000000000) = 1/(250000000000 / 446692244561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (145102237 / 250000000) (580408949 / 1000000000) (Real.log (446692244561 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (446692244561 / 250000000000) = -Real.log (250000000000 / 446692244561) := by
    rw [show ((446692244561 / 250000000000) : ℝ) = ((250000000000 / 446692244561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (581332687 / 1000000000) ≤ -Real.log (500000000000 / 894210124197) ∧
    -Real.log (500000000000 / 894210124197) ≤ (36333293 / 62500000) := by
  have h := checkLog_sound (w := (394210124197 / 1394210124197)) (n := 12)
    (lo := (581332687 / 1000000000)) (hi := (36333293 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((894210124197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(894210124197 / 500000000000) = 1/(500000000000 / 894210124197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (581332687 / 1000000000) (36333293 / 62500000) (Real.log (894210124197 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (894210124197 / 500000000000) = -Real.log (500000000000 / 894210124197) := by
    rw [show ((894210124197 / 500000000000) : ℝ) = ((500000000000 / 894210124197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (2588097 / 6250000) ≤ -Real.log (500000000000 / 756500821123) ∧
    -Real.log (500000000000 / 756500821123) ≤ (414095521 / 1000000000) := by
  have h := checkLog_sound (w := (256500821123 / 1256500821123)) (n := 12)
    (lo := (2588097 / 6250000)) (hi := (414095521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((756500821123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(756500821123 / 500000000000) = 1/(500000000000 / 756500821123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2588097 / 6250000) (414095521 / 1000000000) (Real.log (756500821123 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (756500821123 / 500000000000) = -Real.log (500000000000 / 756500821123) := by
    rw [show ((756500821123 / 500000000000) : ℝ) = ((500000000000 / 756500821123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (414765483 / 1000000000) ≤ -Real.log (500000000000 / 757007818589) ∧
    -Real.log (500000000000 / 757007818589) ≤ (103691371 / 250000000) := by
  have h := checkLog_sound (w := (257007818589 / 1257007818589)) (n := 12)
    (lo := (414765483 / 1000000000)) (hi := (103691371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757007818589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757007818589 / 500000000000) = 1/(500000000000 / 757007818589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (414765483 / 1000000000) (103691371 / 250000000) (Real.log (757007818589 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (757007818589 / 500000000000) = -Real.log (500000000000 / 757007818589) := by
    rw [show ((757007818589 / 500000000000) : ℝ) = ((500000000000 / 757007818589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8540563 / 200000000) ≤ -Real.log (2395490271 / 2500000000) ∧
    -Real.log (2395490271 / 2500000000) ≤ (1334463 / 31250000) := by
  have h := checkLog_sound (w := (104509729 / 4895490271)) (n := 12)
    (lo := (8540563 / 200000000)) (hi := (1334463 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2395490271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2395490271) = 1/(2395490271 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1334463 / 31250000) (-8540563 / 200000000) (Real.log (2395490271 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21282971 / 500000000) ≤ -Real.log (958327268679 / 1000000000000) ∧
    -Real.log (958327268679 / 1000000000000) ≤ (42565943 / 1000000000) := by
  have h := checkLog_sound (w := (41672731321 / 1958327268679)) (n := 12)
    (lo := (21282971 / 500000000)) (hi := (42565943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958327268679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958327268679) = 1/(958327268679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-42565943 / 1000000000) (-21282971 / 500000000) (Real.log (958327268679 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell250

end


