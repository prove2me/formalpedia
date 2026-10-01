-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0205Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0205Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:01:37.71967+00:00
-- url     : https://prove2.me/theorems/baba57d7-ebc4-48d5-b305-2076b416a479
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0205Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0206Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0205Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0206Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0207Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0208Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0209Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0210Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0211Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0205Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0206Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0207Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0208Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0209Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0210Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0211Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0205Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0206Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0207Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0208Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0209Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0210Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0211Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0205Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0206Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0207Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0208Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0209Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0210Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0211Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0205Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0205
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (131707697 / 500000000) ≤ -Real.log (5120 / 6663) ∧
    -Real.log (5120 / 6663) ≤ (52683079 / 200000000) := by
  have h := checkLog_sound (w := (1543 / 11783)) (n := 12)
    (lo := (131707697 / 500000000)) (hi := (52683079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6663 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6663 / 5120) = 1/(5120 / 6663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (131707697 / 500000000) (52683079 / 200000000) (Real.log (6663 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6663 / 5120) = -Real.log (5120 / 6663) := by
    rw [show ((6663 / 5120) : ℝ) = ((5120 / 6663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (179314989 / 500000000) ≤ -Real.log (3577 / 5120) ∧
    -Real.log (3577 / 5120) ≤ (358629979 / 1000000000) := by
  have h := checkLog_sound (w := (1543 / 8697)) (n := 12)
    (lo := (179314989 / 500000000)) (hi := (358629979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3577) = 1/(3577 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-358629979 / 1000000000) (-179314989 / 500000000) (Real.log (3577 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (52593009 / 200000000) ≤ -Real.log (256 / 333) ∧
    -Real.log (256 / 333) ≤ (131482523 / 500000000) := by
  have h := checkLog_sound (w := (77 / 589)) (n := 12)
    (lo := (52593009 / 200000000)) (hi := (131482523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333 / 256) = 1/(256 / 333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (52593009 / 200000000) (131482523 / 500000000) (Real.log (333 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (333 / 256) = -Real.log (256 / 333) := by
    rw [show ((333 / 256) : ℝ) = ((256 / 333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (178895819 / 500000000) ≤ -Real.log (179 / 256) ∧
    -Real.log (179 / 256) ≤ (357791639 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 435)) (n := 12)
    (lo := (178895819 / 500000000)) (hi := (357791639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 179) = 1/(179 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-357791639 / 1000000000) (-178895819 / 500000000) (Real.log (179 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (235855577 / 500000000) ≤ -Real.log (2560 / 4103) ∧
    -Real.log (2560 / 4103) ≤ (94342231 / 200000000) := by
  have h := checkLog_sound (w := (1543 / 6663)) (n := 12)
    (lo := (235855577 / 500000000)) (hi := (94342231 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4103 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4103 / 2560) = 1/(2560 / 4103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (235855577 / 500000000) (94342231 / 200000000) (Real.log (4103 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4103 / 2560) = -Real.log (2560 / 4103) := by
    rw [show ((4103 / 2560) : ℝ) = ((2560 / 4103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (46157507 / 50000000) ≤ -Real.log (1017 / 2560) ∧
    -Real.log (1017 / 2560) ≤ (461575071 / 500000000) := by
  have h := checkLog_sound (w := (263 / 2297)) (n := 12)
    (lo := (2875037 / 12500000)) (hi := (230002961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1017) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1017) = 1/(1017 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-461575071 / 500000000) (-46157507 / 50000000) (Real.log (1017 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (94195943 / 200000000) ≤ -Real.log (128 / 205) ∧
    -Real.log (128 / 205) ≤ (117744929 / 250000000) := by
  have h := checkLog_sound (w := (77 / 333)) (n := 12)
    (lo := (94195943 / 200000000)) (hi := (117744929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205 / 128) = 1/(128 / 205) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (94195943 / 200000000) (117744929 / 250000000) (Real.log (205 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (205 / 128) = -Real.log (128 / 205) := by
    rw [show ((205 / 128) : ℝ) = ((128 / 205) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (92020463 / 100000000) ≤ -Real.log (51 / 128) ∧
    -Real.log (51 / 128) ≤ (115025579 / 125000000) := by
  have h := checkLog_sound (w := (13 / 115)) (n := 12)
    (lo := (4541149 / 20000000)) (hi := (227057451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 51) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 51) = 1/(51 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115025579 / 125000000) (-92020463 / 100000000) (Real.log (51 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (179882283 / 500000000) ≤ -Real.log (31250 / 44781) ∧
    -Real.log (31250 / 44781) ≤ (359764567 / 1000000000) := by
  have h := checkLog_sound (w := (13531 / 76031)) (n := 12)
    (lo := (179882283 / 500000000)) (hi := (359764567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44781 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44781 / 31250) = 1/(31250 / 44781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (179882283 / 500000000) (359764567 / 1000000000) (Real.log (44781 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (44781 / 31250) = -Real.log (31250 / 44781) := by
    rw [show ((44781 / 31250) : ℝ) = ((31250 / 44781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (283690933 / 500000000) ≤ -Real.log (17719 / 31250) ∧
    -Real.log (17719 / 31250) ≤ (567381867 / 1000000000) := by
  have h := checkLog_sound (w := (13531 / 48969)) (n := 12)
    (lo := (283690933 / 500000000)) (hi := (567381867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 17719) = 1/(17719 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-567381867 / 1000000000) (-283690933 / 500000000) (Real.log (17719 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (360378477 / 1000000000) ≤ -Real.log (62500 / 89617) ∧
    -Real.log (62500 / 89617) ≤ (180189239 / 500000000) := by
  have h := checkLog_sound (w := (27117 / 152117)) (n := 12)
    (lo := (360378477 / 1000000000)) (hi := (180189239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89617 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89617 / 62500) = 1/(62500 / 89617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (360378477 / 1000000000) (180189239 / 500000000) (Real.log (89617 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (89617 / 62500) = -Real.log (62500 / 89617) := by
    rw [show ((89617 / 62500) : ℝ) = ((62500 / 89617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (568935077 / 1000000000) ≤ -Real.log (35383 / 62500) ∧
    -Real.log (35383 / 62500) ≤ (284467539 / 500000000) := by
  have h := checkLog_sound (w := (27117 / 97883)) (n := 12)
    (lo := (568935077 / 1000000000)) (hi := (284467539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 35383) = 1/(35383 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-284467539 / 500000000) (-568935077 / 1000000000) (Real.log (35383 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (34977909 / 125000000) ≤ -Real.log (62500 / 82681) ∧
    -Real.log (62500 / 82681) ≤ (279823273 / 1000000000) := by
  have h := checkLog_sound (w := (20181 / 145181)) (n := 12)
    (lo := (34977909 / 125000000)) (hi := (279823273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82681 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82681 / 62500) = 1/(62500 / 82681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (34977909 / 125000000) (279823273 / 1000000000) (Real.log (82681 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (82681 / 62500) = -Real.log (62500 / 82681) := by
    rw [show ((82681 / 62500) : ℝ) = ((62500 / 82681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (194965199 / 500000000) ≤ -Real.log (42319 / 62500) ∧
    -Real.log (42319 / 62500) ≤ (389930399 / 1000000000) := by
  have h := checkLog_sound (w := (20181 / 104819)) (n := 12)
    (lo := (194965199 / 500000000)) (hi := (389930399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42319) = 1/(42319 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-389930399 / 1000000000) (-194965199 / 500000000) (Real.log (42319 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (280373429 / 1000000000) ≤ -Real.log (125000 / 165453) ∧
    -Real.log (125000 / 165453) ≤ (28037343 / 100000000) := by
  have h := checkLog_sound (w := (40453 / 290453)) (n := 12)
    (lo := (280373429 / 1000000000)) (hi := (28037343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165453 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165453 / 125000) = 1/(125000 / 165453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (280373429 / 1000000000) (28037343 / 100000000) (Real.log (165453 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (165453 / 125000) = -Real.log (125000 / 165453) := by
    rw [show ((165453 / 125000) : ℝ) = ((125000 / 165453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (6109471 / 15625000) ≤ -Real.log (84547 / 125000) ∧
    -Real.log (84547 / 125000) ≤ (78201229 / 200000000) := by
  have h := checkLog_sound (w := (40453 / 209547)) (n := 12)
    (lo := (6109471 / 15625000)) (hi := (78201229 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84547) = 1/(84547 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-78201229 / 200000000) (-6109471 / 15625000) (Real.log (84547 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (927146431 / 1000000000) ≤ -Real.log (20000000000 / 50545741859) ∧
    -Real.log (20000000000 / 50545741859) ≤ (927146433 / 1000000000) := by
  have h := checkLog_sound (w := (10545741859 / 90545741859)) (n := 12)
    (lo := (233999251 / 1000000000)) (hi := (58499813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50545741859 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50545741859 / 40000000000) = 1/(20000000000 / 50545741859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (927146431 / 1000000000) (927146433 / 1000000000) (Real.log (50545741859 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (50545741859 / 20000000000) = -Real.log (20000000000 / 50545741859) := by
    rw [show ((50545741859 / 20000000000) : ℝ) = ((20000000000 / 50545741859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (464656777 / 500000000) ≤ -Real.log (500000000000 / 1266384987141) ∧
    -Real.log (500000000000 / 1266384987141) ≤ (232328389 / 250000000) := by
  have h := checkLog_sound (w := (266384987141 / 2266384987141)) (n := 12)
    (lo := (118083187 / 500000000)) (hi := (1889331 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266384987141 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1266384987141 / 1000000000000) = 1/(500000000000 / 1266384987141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (464656777 / 500000000) (232328389 / 250000000) (Real.log (1266384987141 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1266384987141 / 500000000000) = -Real.log (500000000000 / 1266384987141) := by
    rw [show ((1266384987141 / 500000000000) : ℝ) = ((500000000000 / 1266384987141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (669753671 / 1000000000) ≤ -Real.log (250000000000 / 488438999031) ∧
    -Real.log (250000000000 / 488438999031) ≤ (83719209 / 125000000) := by
  have h := checkLog_sound (w := (238438999031 / 738438999031)) (n := 12)
    (lo := (669753671 / 1000000000)) (hi := (83719209 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488438999031 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488438999031 / 250000000000) = 1/(250000000000 / 488438999031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (669753671 / 1000000000) (83719209 / 125000000) (Real.log (488438999031 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (488438999031 / 250000000000) = -Real.log (250000000000 / 488438999031) := by
    rw [show ((488438999031 / 250000000000) : ℝ) = ((250000000000 / 488438999031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (671379573 / 1000000000) ≤ -Real.log (100000000000 / 195693519581) ∧
    -Real.log (100000000000 / 195693519581) ≤ (335689787 / 500000000) := by
  have h := checkLog_sound (w := (95693519581 / 295693519581)) (n := 12)
    (lo := (671379573 / 1000000000)) (hi := (335689787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195693519581 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195693519581 / 100000000000) = 1/(100000000000 / 195693519581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (671379573 / 1000000000) (335689787 / 500000000) (Real.log (195693519581 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (195693519581 / 100000000000) = -Real.log (100000000000 / 195693519581) := by
    rw [show ((195693519581 / 100000000000) : ℝ) = ((100000000000 / 195693519581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0205

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0206Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0206
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (52593009 / 200000000) ≤ -Real.log (256 / 333) ∧
    -Real.log (256 / 333) ≤ (131482523 / 500000000) := by
  have h := checkLog_sound (w := (77 / 589)) (n := 12)
    (lo := (52593009 / 200000000)) (hi := (131482523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333 / 256) = 1/(256 / 333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (52593009 / 200000000) (131482523 / 500000000) (Real.log (333 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (333 / 256) = -Real.log (256 / 333) := by
    rw [show ((333 / 256) : ℝ) = ((256 / 333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (178895819 / 500000000) ≤ -Real.log (179 / 256) ∧
    -Real.log (179 / 256) ≤ (357791639 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 435)) (n := 12)
    (lo := (178895819 / 500000000)) (hi := (357791639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 179) = 1/(179 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-357791639 / 1000000000) (-178895819 / 500000000) (Real.log (179 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (262514493 / 1000000000) ≤ -Real.log (5120 / 6657) ∧
    -Real.log (5120 / 6657) ≤ (131257247 / 500000000) := by
  have h := checkLog_sound (w := (1537 / 11777)) (n := 12)
    (lo := (262514493 / 1000000000)) (hi := (131257247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6657 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6657 / 5120) = 1/(5120 / 6657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (262514493 / 1000000000) (131257247 / 500000000) (Real.log (6657 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6657 / 5120) = -Real.log (5120 / 6657) := by
    rw [show ((6657 / 5120) : ℝ) = ((5120 / 6657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (178477 / 500000) ≤ -Real.log (3583 / 5120) ∧
    -Real.log (3583 / 5120) ≤ (356954001 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 8703)) (n := 12)
    (lo := (178477 / 500000)) (hi := (356954001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3583) = 1/(3583 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-356954001 / 1000000000) (-178477 / 500000) (Real.log (3583 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (94195943 / 200000000) ≤ -Real.log (128 / 205) ∧
    -Real.log (128 / 205) ≤ (117744929 / 250000000) := by
  have h := checkLog_sound (w := (77 / 333)) (n := 12)
    (lo := (94195943 / 200000000)) (hi := (117744929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205 / 128) = 1/(128 / 205) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (94195943 / 200000000) (117744929 / 250000000) (Real.log (205 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (205 / 128) = -Real.log (128 / 205) := by
    rw [show ((205 / 128) : ℝ) = ((128 / 205) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (92020463 / 100000000) ≤ -Real.log (51 / 128) ∧
    -Real.log (51 / 128) ≤ (115025579 / 125000000) := by
  have h := checkLog_sound (w := (13 / 115)) (n := 12)
    (lo := (4541149 / 20000000)) (hi := (227057451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 51) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 51) = 1/(51 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-115025579 / 125000000) (-92020463 / 100000000) (Real.log (51 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23512387 / 50000000) ≤ -Real.log (2560 / 4097) ∧
    -Real.log (2560 / 4097) ≤ (470247741 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 6657)) (n := 12)
    (lo := (23512387 / 50000000)) (hi := (470247741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4097 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4097 / 2560) = 1/(2560 / 4097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23512387 / 50000000) (470247741 / 1000000000) (Real.log (4097 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4097 / 2560) = -Real.log (2560 / 4097) := by
    rw [show ((4097 / 2560) : ℝ) = ((2560 / 4097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (91726777 / 100000000) ≤ -Real.log (1023 / 2560) ∧
    -Real.log (1023 / 2560) ≤ (229316943 / 250000000) := by
  have h := checkLog_sound (w := (257 / 2303)) (n := 12)
    (lo := (22412059 / 100000000)) (hi := (224120591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1023) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1023) = 1/(1023 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-229316943 / 250000000) (-91726777 / 100000000) (Real.log (1023 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (359150277 / 1000000000) ≤ -Real.log (62500 / 89507) ∧
    -Real.log (62500 / 89507) ≤ (179575139 / 500000000) := by
  have h := checkLog_sound (w := (27007 / 152007)) (n := 12)
    (lo := (359150277 / 1000000000)) (hi := (179575139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89507 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89507 / 62500) = 1/(62500 / 89507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (359150277 / 1000000000) (179575139 / 500000000) (Real.log (89507 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (89507 / 62500) = -Real.log (62500 / 89507) := by
    rw [show ((89507 / 62500) : ℝ) = ((62500 / 89507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (282915531 / 500000000) ≤ -Real.log (35493 / 62500) ∧
    -Real.log (35493 / 62500) ≤ (565831063 / 1000000000) := by
  have h := checkLog_sound (w := (27007 / 97993)) (n := 12)
    (lo := (282915531 / 500000000)) (hi := (565831063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 35493) = 1/(35493 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-565831063 / 1000000000) (-282915531 / 500000000) (Real.log (35493 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (359765263 / 1000000000) ≤ -Real.log (1000000 / 1432993) ∧
    -Real.log (1000000 / 1432993) ≤ (22485329 / 62500000) := by
  have h := checkLog_sound (w := (432993 / 2432993)) (n := 12)
    (lo := (359765263 / 1000000000)) (hi := (22485329 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1432993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1432993 / 1000000) = 1/(1000000 / 1432993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (359765263 / 1000000000) (22485329 / 62500000) (Real.log (1432993 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1432993 / 1000000) = -Real.log (1000000 / 1432993) := by
    rw [show ((1432993 / 1000000) : ℝ) = ((1000000 / 1432993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (567383629 / 1000000000) ≤ -Real.log (567007 / 1000000) ∧
    -Real.log (567007 / 1000000) ≤ (56738363 / 100000000) := by
  have h := checkLog_sound (w := (432993 / 1567007)) (n := 12)
    (lo := (567383629 / 1000000000)) (hi := (56738363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 567007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 567007) = 1/(567007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-56738363 / 100000000) (-567383629 / 1000000000) (Real.log (567007 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (279273569 / 1000000000) ≤ -Real.log (1000000 / 1322169) ∧
    -Real.log (1000000 / 1322169) ≤ (27927357 / 100000000) := by
  have h := checkLog_sound (w := (322169 / 2322169)) (n := 12)
    (lo := (279273569 / 1000000000)) (hi := (27927357 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1322169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1322169 / 1000000) = 1/(1000000 / 1322169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (279273569 / 1000000000) (27927357 / 100000000) (Real.log (1322169 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1322169 / 1000000) = -Real.log (1000000 / 1322169) := by
    rw [show ((1322169 / 1000000) : ℝ) = ((1000000 / 1322169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (97214321 / 250000000) ≤ -Real.log (677831 / 1000000) ∧
    -Real.log (677831 / 1000000) ≤ (77771457 / 200000000) := by
  have h := checkLog_sound (w := (322169 / 1677831)) (n := 12)
    (lo := (97214321 / 250000000)) (hi := (77771457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 677831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 677831) = 1/(677831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-77771457 / 200000000) (-97214321 / 250000000) (Real.log (677831 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (69956007 / 250000000) ≤ -Real.log (1000000 / 1322897) ∧
    -Real.log (1000000 / 1322897) ≤ (279824029 / 1000000000) := by
  have h := checkLog_sound (w := (322897 / 2322897)) (n := 12)
    (lo := (69956007 / 250000000)) (hi := (279824029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1322897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1322897 / 1000000) = 1/(1000000 / 1322897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (69956007 / 250000000) (279824029 / 1000000000) (Real.log (1322897 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1322897 / 1000000) = -Real.log (1000000 / 1322897) := by
    rw [show ((1322897 / 1000000) : ℝ) = ((1000000 / 1322897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (623891 / 1600000) ≤ -Real.log (677103 / 1000000) ∧
    -Real.log (677103 / 1000000) ≤ (97482969 / 250000000) := by
  have h := checkLog_sound (w := (322897 / 1677103)) (n := 12)
    (lo := (623891 / 1600000)) (hi := (97482969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 677103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 677103) = 1/(677103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-97482969 / 250000000) (-623891 / 1600000) (Real.log (677103 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (46249067 / 50000000) ≤ -Real.log (50000000000 / 126091060209) ∧
    -Real.log (50000000000 / 126091060209) ≤ (462490671 / 500000000) := by
  have h := checkLog_sound (w := (26091060209 / 226091060209)) (n := 12)
    (lo := (2897927 / 12500000)) (hi := (231834161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126091060209 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126091060209 / 100000000000) = 1/(50000000000 / 126091060209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (46249067 / 50000000) (462490671 / 500000000) (Real.log (126091060209 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (126091060209 / 50000000000) = -Real.log (50000000000 / 126091060209) := by
    rw [show ((126091060209 / 50000000000) : ℝ) = ((50000000000 / 126091060209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (927148893 / 1000000000) ≤ -Real.log (12500000000 / 31591166423) ∧
    -Real.log (12500000000 / 31591166423) ≤ (185429779 / 200000000) := by
  have h := checkLog_sound (w := (6591166423 / 56591166423)) (n := 12)
    (lo := (234001713 / 1000000000)) (hi := (117000857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31591166423 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31591166423 / 25000000000) = 1/(12500000000 / 31591166423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (927148893 / 1000000000) (185429779 / 200000000) (Real.log (31591166423 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (31591166423 / 12500000000) = -Real.log (12500000000 / 31591166423) := by
    rw [show ((31591166423 / 12500000000) : ℝ) = ((12500000000 / 31591166423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (334065427 / 500000000) ≤ -Real.log (500000000000 / 975293989209) ∧
    -Real.log (500000000000 / 975293989209) ≤ (133626171 / 200000000) := by
  have h := checkLog_sound (w := (475293989209 / 1475293989209)) (n := 12)
    (lo := (334065427 / 500000000)) (hi := (133626171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((975293989209 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(975293989209 / 500000000000) = 1/(500000000000 / 975293989209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (334065427 / 500000000) (133626171 / 200000000) (Real.log (975293989209 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (975293989209 / 500000000000) = -Real.log (500000000000 / 975293989209) := by
    rw [show ((975293989209 / 500000000000) : ℝ) = ((500000000000 / 975293989209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1308117 / 1953125) ≤ -Real.log (100000000000 / 195376035847) ∧
    -Real.log (100000000000 / 195376035847) ≤ (133951181 / 200000000) := by
  have h := checkLog_sound (w := (95376035847 / 295376035847)) (n := 12)
    (lo := (1308117 / 1953125)) (hi := (133951181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195376035847 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195376035847 / 100000000000) = 1/(100000000000 / 195376035847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1308117 / 1953125) (133951181 / 200000000) (Real.log (195376035847 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (195376035847 / 100000000000) = -Real.log (100000000000 / 195376035847) := by
    rw [show ((195376035847 / 100000000000) : ℝ) = ((100000000000 / 195376035847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0206

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0207Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0207
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (262514493 / 1000000000) ≤ -Real.log (5120 / 6657) ∧
    -Real.log (5120 / 6657) ≤ (131257247 / 500000000) := by
  have h := checkLog_sound (w := (1537 / 11777)) (n := 12)
    (lo := (262514493 / 1000000000)) (hi := (131257247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6657 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6657 / 5120) = 1/(5120 / 6657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (262514493 / 1000000000) (131257247 / 500000000) (Real.log (6657 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6657 / 5120) = -Real.log (5120 / 6657) := by
    rw [show ((6657 / 5120) : ℝ) = ((5120 / 6657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (178477 / 500000) ≤ -Real.log (3583 / 5120) ∧
    -Real.log (3583 / 5120) ≤ (356954001 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 8703)) (n := 12)
    (lo := (178477 / 500000)) (hi := (356954001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3583) = 1/(3583 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-356954001 / 1000000000) (-178477 / 500000) (Real.log (3583 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (131031869 / 500000000) ≤ -Real.log (2560 / 3327) ∧
    -Real.log (2560 / 3327) ≤ (262063739 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 5887)) (n := 12)
    (lo := (131031869 / 500000000)) (hi := (262063739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3327 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3327 / 2560) = 1/(2560 / 3327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (131031869 / 500000000) (262063739 / 1000000000) (Real.log (3327 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3327 / 2560) = -Real.log (2560 / 3327) := by
    rw [show ((3327 / 2560) : ℝ) = ((2560 / 3327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (356117063 / 1000000000) ≤ -Real.log (1793 / 2560) ∧
    -Real.log (1793 / 2560) ≤ (44514633 / 125000000) := by
  have h := checkLog_sound (w := (767 / 4353)) (n := 12)
    (lo := (356117063 / 1000000000)) (hi := (44514633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1793) = 1/(1793 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-44514633 / 125000000) (-356117063 / 1000000000) (Real.log (1793 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23512387 / 50000000) ≤ -Real.log (2560 / 4097) ∧
    -Real.log (2560 / 4097) ≤ (470247741 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 6657)) (n := 12)
    (lo := (23512387 / 50000000)) (hi := (470247741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4097 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4097 / 2560) = 1/(2560 / 4097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23512387 / 50000000) (470247741 / 1000000000) (Real.log (4097 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4097 / 2560) = -Real.log (2560 / 4097) := by
    rw [show ((4097 / 2560) : ℝ) = ((2560 / 4097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (91726777 / 100000000) ≤ -Real.log (1023 / 2560) ∧
    -Real.log (1023 / 2560) ≤ (229316943 / 250000000) := by
  have h := checkLog_sound (w := (257 / 2303)) (n := 12)
    (lo := (22412059 / 100000000)) (hi := (224120591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1023) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1023) = 1/(1023 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-229316943 / 250000000) (-91726777 / 100000000) (Real.log (1023 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (117378807 / 250000000) ≤ -Real.log (1280 / 2047) ∧
    -Real.log (1280 / 2047) ≤ (469515229 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 3327)) (n := 12)
    (lo := (117378807 / 250000000)) (hi := (469515229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2047 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2047 / 1280) = 1/(1280 / 2047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (117378807 / 250000000) (469515229 / 1000000000) (Real.log (2047 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2047 / 1280) = -Real.log (1280 / 2047) := by
    rw [show ((2047 / 1280) : ℝ) = ((1280 / 2047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (914339511 / 1000000000) ≤ -Real.log (513 / 1280) ∧
    -Real.log (513 / 1280) ≤ (914339513 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 1153)) (n := 12)
    (lo := (221192331 / 1000000000)) (hi := (55298083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 513) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 513) = 1/(513 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-914339513 / 1000000000) (-914339511 / 1000000000) (Real.log (513 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (358537009 / 1000000000) ≤ -Real.log (500000 / 715617) ∧
    -Real.log (500000 / 715617) ≤ (35853701 / 100000000) := by
  have h := checkLog_sound (w := (215617 / 1215617)) (n := 12)
    (lo := (358537009 / 1000000000)) (hi := (35853701 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715617 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715617 / 500000) = 1/(500000 / 715617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (358537009 / 1000000000) (35853701 / 100000000) (Real.log (715617 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (715617 / 500000) = -Real.log (500000 / 715617) := by
    rw [show ((715617 / 500000) : ℝ) = ((500000 / 715617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (564286177 / 1000000000) ≤ -Real.log (284383 / 500000) ∧
    -Real.log (284383 / 500000) ≤ (282143089 / 500000000) := by
  have h := checkLog_sound (w := (215617 / 784383)) (n := 12)
    (lo := (564286177 / 1000000000)) (hi := (282143089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 284383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 284383) = 1/(284383 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-282143089 / 500000000) (-564286177 / 1000000000) (Real.log (284383 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (2805867 / 7812500) ≤ -Real.log (1000000 / 1432113) ∧
    -Real.log (1000000 / 1432113) ≤ (359150977 / 1000000000) := by
  have h := checkLog_sound (w := (432113 / 2432113)) (n := 12)
    (lo := (2805867 / 7812500)) (hi := (359150977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1432113 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1432113 / 1000000) = 1/(1000000 / 1432113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (2805867 / 7812500) (359150977 / 1000000000) (Real.log (1432113 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1432113 / 1000000) = -Real.log (1000000 / 1432113) := by
    rw [show ((1432113 / 1000000) : ℝ) = ((1000000 / 1432113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (565832823 / 1000000000) ≤ -Real.log (567887 / 1000000) ∧
    -Real.log (567887 / 1000000) ≤ (70729103 / 125000000) := by
  have h := checkLog_sound (w := (432113 / 1567887)) (n := 12)
    (lo := (565832823 / 1000000000)) (hi := (70729103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 567887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 567887) = 1/(567887 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-70729103 / 125000000) (-565832823 / 1000000000) (Real.log (567887 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (278724321 / 1000000000) ≤ -Real.log (1000000 / 1321443) ∧
    -Real.log (1000000 / 1321443) ≤ (139362161 / 500000000) := by
  have h := checkLog_sound (w := (321443 / 2321443)) (n := 12)
    (lo := (278724321 / 1000000000)) (hi := (139362161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321443 / 1000000) = 1/(1000000 / 1321443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (278724321 / 1000000000) (139362161 / 500000000) (Real.log (1321443 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1321443 / 1000000) = -Real.log (1000000 / 1321443) := by
    rw [show ((1321443 / 1000000) : ℝ) = ((1000000 / 1321443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (193893397 / 500000000) ≤ -Real.log (678557 / 1000000) ∧
    -Real.log (678557 / 1000000) ≤ (77557359 / 200000000) := by
  have h := checkLog_sound (w := (321443 / 1678557)) (n := 12)
    (lo := (193893397 / 500000000)) (hi := (77557359 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 678557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 678557) = 1/(678557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-77557359 / 200000000) (-193893397 / 500000000) (Real.log (678557 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (139637163 / 500000000) ≤ -Real.log (100000 / 132217) ∧
    -Real.log (100000 / 132217) ≤ (279274327 / 1000000000) := by
  have h := checkLog_sound (w := (32217 / 232217)) (n := 12)
    (lo := (139637163 / 500000000)) (hi := (279274327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132217 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132217 / 100000) = 1/(100000 / 132217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (139637163 / 500000000) (279274327 / 1000000000) (Real.log (132217 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (132217 / 100000) = -Real.log (100000 / 132217) := by
    rw [show ((132217 / 100000) : ℝ) = ((100000 / 132217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (388858759 / 1000000000) ≤ -Real.log (67783 / 100000) ∧
    -Real.log (67783 / 100000) ≤ (9721469 / 25000000) := by
  have h := checkLog_sound (w := (32217 / 167783)) (n := 12)
    (lo := (388858759 / 1000000000)) (hi := (9721469 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 67783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 67783) = 1/(67783 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-9721469 / 25000000) (-388858759 / 1000000000) (Real.log (67783 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (184564637 / 200000000) ≤ -Real.log (500000000000 / 1258192297007) ∧
    -Real.log (500000000000 / 1258192297007) ≤ (922823187 / 1000000000) := by
  have h := checkLog_sound (w := (258192297007 / 2258192297007)) (n := 12)
    (lo := (45935201 / 200000000)) (hi := (114838003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1258192297007 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1258192297007 / 1000000000000) = 1/(500000000000 / 1258192297007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (184564637 / 200000000) (922823187 / 1000000000) (Real.log (1258192297007 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1258192297007 / 500000000000) = -Real.log (500000000000 / 1258192297007) := by
    rw [show ((1258192297007 / 500000000000) : ℝ) = ((500000000000 / 1258192297007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (924983799 / 1000000000) ≤ -Real.log (500000000000 / 1260913702903) ∧
    -Real.log (500000000000 / 1260913702903) ≤ (924983801 / 1000000000) := by
  have h := checkLog_sound (w := (260913702903 / 2260913702903)) (n := 12)
    (lo := (231836619 / 1000000000)) (hi := (11591831 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260913702903 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1260913702903 / 1000000000000) = 1/(500000000000 / 1260913702903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (924983799 / 1000000000) (924983801 / 1000000000) (Real.log (1260913702903 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1260913702903 / 500000000000) = -Real.log (500000000000 / 1260913702903) := by
    rw [show ((1260913702903 / 500000000000) : ℝ) = ((500000000000 / 1260913702903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (133302223 / 200000000) ≤ -Real.log (125000000000 / 243428886593) ∧
    -Real.log (125000000000 / 243428886593) ≤ (166627779 / 250000000) := by
  have h := checkLog_sound (w := (118428886593 / 368428886593)) (n := 12)
    (lo := (133302223 / 200000000)) (hi := (166627779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243428886593 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243428886593 / 125000000000) = 1/(125000000000 / 243428886593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (133302223 / 200000000) (166627779 / 250000000) (Real.log (243428886593 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (243428886593 / 125000000000) = -Real.log (125000000000 / 243428886593) := by
    rw [show ((243428886593 / 125000000000) : ℝ) = ((125000000000 / 243428886593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (334066543 / 500000000) ≤ -Real.log (250000000000 / 487648082853) ∧
    -Real.log (250000000000 / 487648082853) ≤ (668133087 / 1000000000) := by
  have h := checkLog_sound (w := (237648082853 / 737648082853)) (n := 12)
    (lo := (334066543 / 500000000)) (hi := (668133087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487648082853 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487648082853 / 250000000000) = 1/(250000000000 / 487648082853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (334066543 / 500000000) (668133087 / 1000000000) (Real.log (487648082853 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (487648082853 / 250000000000) = -Real.log (250000000000 / 487648082853) := by
    rw [show ((487648082853 / 250000000000) : ℝ) = ((250000000000 / 487648082853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0207

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0208Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0208
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (131031869 / 500000000) ≤ -Real.log (2560 / 3327) ∧
    -Real.log (2560 / 3327) ≤ (262063739 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 5887)) (n := 12)
    (lo := (131031869 / 500000000)) (hi := (262063739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3327 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3327 / 2560) = 1/(2560 / 3327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (131031869 / 500000000) (262063739 / 1000000000) (Real.log (3327 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3327 / 2560) = -Real.log (2560 / 3327) := by
    rw [show ((3327 / 2560) : ℝ) = ((2560 / 3327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (356117063 / 1000000000) ≤ -Real.log (1793 / 2560) ∧
    -Real.log (1793 / 2560) ≤ (44514633 / 125000000) := by
  have h := checkLog_sound (w := (767 / 4353)) (n := 12)
    (lo := (356117063 / 1000000000)) (hi := (44514633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1793) = 1/(1793 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-44514633 / 125000000) (-356117063 / 1000000000) (Real.log (1793 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13080639 / 50000000) ≤ -Real.log (5120 / 6651) ∧
    -Real.log (5120 / 6651) ≤ (261612781 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 11771)) (n := 12)
    (lo := (13080639 / 50000000)) (hi := (261612781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6651 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6651 / 5120) = 1/(5120 / 6651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13080639 / 50000000) (261612781 / 1000000000) (Real.log (6651 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6651 / 5120) = -Real.log (5120 / 6651) := by
    rw [show ((6651 / 5120) : ℝ) = ((5120 / 6651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (177640413 / 500000000) ≤ -Real.log (3589 / 5120) ∧
    -Real.log (3589 / 5120) ≤ (355280827 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 8709)) (n := 12)
    (lo := (177640413 / 500000000)) (hi := (355280827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3589) = 1/(3589 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-355280827 / 1000000000) (-177640413 / 500000000) (Real.log (3589 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (117378807 / 250000000) ≤ -Real.log (1280 / 2047) ∧
    -Real.log (1280 / 2047) ≤ (469515229 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 3327)) (n := 12)
    (lo := (117378807 / 250000000)) (hi := (469515229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2047 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2047 / 1280) = 1/(1280 / 2047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (117378807 / 250000000) (469515229 / 1000000000) (Real.log (2047 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2047 / 1280) = -Real.log (1280 / 2047) := by
    rw [show ((2047 / 1280) : ℝ) = ((1280 / 2047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (914339511 / 1000000000) ≤ -Real.log (513 / 1280) ∧
    -Real.log (513 / 1280) ≤ (914339513 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 1153)) (n := 12)
    (lo := (221192331 / 1000000000)) (hi := (55298083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 513) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 513) = 1/(513 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-914339513 / 1000000000) (-914339511 / 1000000000) (Real.log (513 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23439109 / 50000000) ≤ -Real.log (2560 / 4091) ∧
    -Real.log (2560 / 4091) ≤ (468782181 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 6651)) (n := 12)
    (lo := (23439109 / 50000000)) (hi := (468782181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4091 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4091 / 2560) = 1/(2560 / 4091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23439109 / 50000000) (468782181 / 1000000000) (Real.log (4091 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4091 / 2560) = -Real.log (2560 / 4091) := by
    rw [show ((4091 / 2560) : ℝ) = ((2560 / 4091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (911419801 / 1000000000) ≤ -Real.log (1029 / 2560) ∧
    -Real.log (1029 / 2560) ≤ (911419803 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 2309)) (n := 12)
    (lo := (218272621 / 1000000000)) (hi := (109136311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1029) = 1/(1029 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-911419803 / 1000000000) (-911419801 / 1000000000) (Real.log (1029 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (71584533 / 200000000) ≤ -Real.log (200000 / 286071) ∧
    -Real.log (200000 / 286071) ≤ (178961333 / 500000000) := by
  have h := checkLog_sound (w := (86071 / 486071)) (n := 12)
    (lo := (71584533 / 200000000)) (hi := (178961333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286071 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286071 / 200000) = 1/(200000 / 286071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (71584533 / 200000000) (178961333 / 500000000) (Real.log (286071 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (286071 / 200000) = -Real.log (200000 / 286071) := by
    rw [show ((286071 / 200000) : ℝ) = ((200000 / 286071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (562741919 / 1000000000) ≤ -Real.log (113929 / 200000) ∧
    -Real.log (113929 / 200000) ≤ (3517137 / 6250000) := by
  have h := checkLog_sound (w := (86071 / 313929)) (n := 12)
    (lo := (562741919 / 1000000000)) (hi := (3517137 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 113929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 113929) = 1/(113929 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3517137 / 6250000) (-562741919 / 1000000000) (Real.log (113929 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (358537707 / 1000000000) ≤ -Real.log (200000 / 286247) ∧
    -Real.log (200000 / 286247) ≤ (89634427 / 250000000) := by
  have h := checkLog_sound (w := (86247 / 486247)) (n := 12)
    (lo := (358537707 / 1000000000)) (hi := (89634427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286247 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286247 / 200000) = 1/(200000 / 286247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (358537707 / 1000000000) (89634427 / 250000000) (Real.log (286247 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (286247 / 200000) = -Real.log (200000 / 286247) := by
    rw [show ((286247 / 200000) : ℝ) = ((200000 / 286247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (112857587 / 200000000) ≤ -Real.log (113753 / 200000) ∧
    -Real.log (113753 / 200000) ≤ (8816999 / 15625000) := by
  have h := checkLog_sound (w := (86247 / 313753)) (n := 12)
    (lo := (112857587 / 200000000)) (hi := (8816999 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 113753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 113753) = 1/(113753 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8816999 / 15625000) (-112857587 / 200000000) (Real.log (113753 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (34771941 / 125000000) ≤ -Real.log (500000 / 660359) ∧
    -Real.log (500000 / 660359) ≤ (278175529 / 1000000000) := by
  have h := checkLog_sound (w := (160359 / 1160359)) (n := 12)
    (lo := (34771941 / 125000000)) (hi := (278175529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660359 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660359 / 500000) = 1/(500000 / 660359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (34771941 / 125000000) (278175529 / 1000000000) (Real.log (660359 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (660359 / 500000) = -Real.log (500000 / 660359) := by
    rw [show ((660359 / 500000) : ℝ) = ((500000 / 660359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (386718921 / 1000000000) ≤ -Real.log (339641 / 500000) ∧
    -Real.log (339641 / 500000) ≤ (193359461 / 500000000) := by
  have h := checkLog_sound (w := (160359 / 839641)) (n := 12)
    (lo := (386718921 / 1000000000)) (hi := (193359461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 339641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 339641) = 1/(339641 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-193359461 / 500000000) (-386718921 / 1000000000) (Real.log (339641 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (139362539 / 500000000) ≤ -Real.log (250000 / 330361) ∧
    -Real.log (250000 / 330361) ≤ (278725079 / 1000000000) := by
  have h := checkLog_sound (w := (80361 / 580361)) (n := 12)
    (lo := (139362539 / 500000000)) (hi := (278725079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330361 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330361 / 250000) = 1/(250000 / 330361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (139362539 / 500000000) (278725079 / 1000000000) (Real.log (330361 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (330361 / 250000) = -Real.log (250000 / 330361) := by
    rw [show ((330361 / 250000) : ℝ) = ((250000 / 330361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (96947067 / 250000000) ≤ -Real.log (169639 / 250000) ∧
    -Real.log (169639 / 250000) ≤ (387788269 / 1000000000) := by
  have h := checkLog_sound (w := (80361 / 419639)) (n := 12)
    (lo := (96947067 / 250000000)) (hi := (387788269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 169639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 169639) = 1/(169639 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-387788269 / 1000000000) (-96947067 / 250000000) (Real.log (169639 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (920664583 / 1000000000) ≤ -Real.log (500000000000 / 1255479289733) ∧
    -Real.log (500000000000 / 1255479289733) ≤ (184132917 / 200000000) := by
  have h := checkLog_sound (w := (255479289733 / 2255479289733)) (n := 12)
    (lo := (227517403 / 1000000000)) (hi := (56879351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255479289733 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1255479289733 / 1000000000000) = 1/(500000000000 / 1255479289733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (920664583 / 1000000000) (184132917 / 200000000) (Real.log (1255479289733 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1255479289733 / 500000000000) = -Real.log (500000000000 / 1255479289733) := by
    rw [show ((1255479289733 / 500000000000) : ℝ) = ((500000000000 / 1255479289733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (461412821 / 500000000) ≤ -Real.log (250000000000 / 629097694127) ∧
    -Real.log (250000000000 / 629097694127) ≤ (230706411 / 250000000) := by
  have h := checkLog_sound (w := (129097694127 / 1129097694127)) (n := 12)
    (lo := (114839231 / 500000000)) (hi := (229678463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629097694127 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(629097694127 / 500000000000) = 1/(250000000000 / 629097694127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (461412821 / 500000000) (230706411 / 250000000) (Real.log (629097694127 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (629097694127 / 250000000000) = -Real.log (250000000000 / 629097694127) := by
    rw [show ((629097694127 / 250000000000) : ℝ) = ((250000000000 / 629097694127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (664894449 / 1000000000) ≤ -Real.log (500000000000 / 972142644733) ∧
    -Real.log (500000000000 / 972142644733) ≤ (13297889 / 20000000) := by
  have h := checkLog_sound (w := (472142644733 / 1472142644733)) (n := 12)
    (lo := (664894449 / 1000000000)) (hi := (13297889 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972142644733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972142644733 / 500000000000) = 1/(500000000000 / 972142644733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (664894449 / 1000000000) (13297889 / 20000000) (Real.log (972142644733 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (972142644733 / 500000000000) = -Real.log (500000000000 / 972142644733) := by
    rw [show ((972142644733 / 500000000000) : ℝ) = ((500000000000 / 972142644733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (333256673 / 500000000) ≤ -Real.log (250000000000 / 486858859107) ∧
    -Real.log (250000000000 / 486858859107) ≤ (666513347 / 1000000000) := by
  have h := checkLog_sound (w := (236858859107 / 736858859107)) (n := 12)
    (lo := (333256673 / 500000000)) (hi := (666513347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486858859107 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486858859107 / 250000000000) = 1/(250000000000 / 486858859107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (333256673 / 500000000) (666513347 / 1000000000) (Real.log (486858859107 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (486858859107 / 250000000000) = -Real.log (250000000000 / 486858859107) := by
    rw [show ((486858859107 / 250000000000) : ℝ) = ((250000000000 / 486858859107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0208

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0209Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0209
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (13080639 / 50000000) ≤ -Real.log (5120 / 6651) ∧
    -Real.log (5120 / 6651) ≤ (261612781 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 11771)) (n := 12)
    (lo := (13080639 / 50000000)) (hi := (261612781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6651 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6651 / 5120) = 1/(5120 / 6651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13080639 / 50000000) (261612781 / 1000000000) (Real.log (6651 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6651 / 5120) = -Real.log (5120 / 6651) := by
    rw [show ((6651 / 5120) : ℝ) = ((5120 / 6651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (177640413 / 500000000) ≤ -Real.log (3589 / 5120) ∧
    -Real.log (3589 / 5120) ≤ (355280827 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 8709)) (n := 12)
    (lo := (177640413 / 500000000)) (hi := (355280827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3589) = 1/(3589 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-355280827 / 1000000000) (-177640413 / 500000000) (Real.log (3589 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (130580809 / 500000000) ≤ -Real.log (640 / 831) ∧
    -Real.log (640 / 831) ≤ (261161619 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1471)) (n := 12)
    (lo := (130580809 / 500000000)) (hi := (261161619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831 / 640) = 1/(640 / 831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (130580809 / 500000000) (261161619 / 1000000000) (Real.log (831 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (831 / 640) = -Real.log (640 / 831) := by
    rw [show ((831 / 640) : ℝ) = ((640 / 831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (44305661 / 125000000) ≤ -Real.log (449 / 640) ∧
    -Real.log (449 / 640) ≤ (354445289 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1089)) (n := 12)
    (lo := (44305661 / 125000000)) (hi := (354445289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 449) = 1/(449 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-354445289 / 1000000000) (-44305661 / 125000000) (Real.log (449 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23439109 / 50000000) ≤ -Real.log (2560 / 4091) ∧
    -Real.log (2560 / 4091) ≤ (468782181 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 6651)) (n := 12)
    (lo := (23439109 / 50000000)) (hi := (468782181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4091 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4091 / 2560) = 1/(2560 / 4091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23439109 / 50000000) (468782181 / 1000000000) (Real.log (4091 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4091 / 2560) = -Real.log (2560 / 4091) := by
    rw [show ((4091 / 2560) : ℝ) = ((2560 / 4091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (911419801 / 1000000000) ≤ -Real.log (1029 / 2560) ∧
    -Real.log (1029 / 2560) ≤ (911419803 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 2309)) (n := 12)
    (lo := (218272621 / 1000000000)) (hi := (109136311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1029) = 1/(1029 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-911419803 / 1000000000) (-911419801 / 1000000000) (Real.log (1029 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (234024297 / 500000000) ≤ -Real.log (320 / 511) ∧
    -Real.log (320 / 511) ≤ (93609719 / 200000000) := by
  have h := checkLog_sound (w := (191 / 831)) (n := 12)
    (lo := (234024297 / 500000000)) (hi := (93609719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(511 / 320) = 1/(320 / 511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (234024297 / 500000000) (93609719 / 200000000) (Real.log (511 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (511 / 320) = -Real.log (320 / 511) := by
    rw [show ((511 / 320) : ℝ) = ((320 / 511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (90850859 / 100000000) ≤ -Real.log (129 / 320) ∧
    -Real.log (129 / 320) ≤ (56781787 / 62500000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 129) = 1/(129 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-56781787 / 62500000) (-90850859 / 100000000) (Real.log (129 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (357308643 / 1000000000) ≤ -Real.log (1000000 / 1429477) ∧
    -Real.log (1000000 / 1429477) ≤ (89327161 / 250000000) := by
  have h := checkLog_sound (w := (429477 / 2429477)) (n := 12)
    (lo := (357308643 / 1000000000)) (hi := (89327161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1429477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1429477 / 1000000) = 1/(1000000 / 1429477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (357308643 / 1000000000) (89327161 / 250000000) (Real.log (1429477 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1429477 / 1000000) = -Real.log (1000000 / 1429477) := by
    rw [show ((1429477 / 1000000) : ℝ) = ((1000000 / 1429477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (280600897 / 500000000) ≤ -Real.log (570523 / 1000000) ∧
    -Real.log (570523 / 1000000) ≤ (112240359 / 200000000) := by
  have h := checkLog_sound (w := (429477 / 1570523)) (n := 12)
    (lo := (280600897 / 500000000)) (hi := (112240359 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 570523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 570523) = 1/(570523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-112240359 / 200000000) (-280600897 / 500000000) (Real.log (570523 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (89480841 / 250000000) ≤ -Real.log (250000 / 357589) ∧
    -Real.log (250000 / 357589) ≤ (71584673 / 200000000) := by
  have h := checkLog_sound (w := (107589 / 607589)) (n := 12)
    (lo := (89480841 / 250000000)) (hi := (71584673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357589 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357589 / 250000) = 1/(250000 / 357589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (89480841 / 250000000) (71584673 / 200000000) (Real.log (357589 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (357589 / 250000) = -Real.log (250000 / 357589) := by
    rw [show ((357589 / 250000) : ℝ) = ((250000 / 357589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (281371837 / 500000000) ≤ -Real.log (142411 / 250000) ∧
    -Real.log (142411 / 250000) ≤ (22509747 / 40000000) := by
  have h := checkLog_sound (w := (107589 / 392411)) (n := 12)
    (lo := (281371837 / 500000000)) (hi := (22509747 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 142411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 142411) = 1/(142411 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22509747 / 40000000) (-281371837 / 500000000) (Real.log (142411 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (277626433 / 1000000000) ≤ -Real.log (1000000 / 1319993) ∧
    -Real.log (1000000 / 1319993) ≤ (138813217 / 500000000) := by
  have h := checkLog_sound (w := (319993 / 2319993)) (n := 12)
    (lo := (277626433 / 1000000000)) (hi := (138813217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319993 / 1000000) = 1/(1000000 / 1319993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (277626433 / 1000000000) (138813217 / 500000000) (Real.log (1319993 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1319993 / 1000000) = -Real.log (1000000 / 1319993) := by
    rw [show ((1319993 / 1000000) : ℝ) = ((1000000 / 1319993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (192826093 / 500000000) ≤ -Real.log (680007 / 1000000) ∧
    -Real.log (680007 / 1000000) ≤ (385652187 / 1000000000) := by
  have h := checkLog_sound (w := (319993 / 1680007)) (n := 12)
    (lo := (192826093 / 500000000)) (hi := (385652187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 680007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 680007) = 1/(680007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-385652187 / 1000000000) (-192826093 / 500000000) (Real.log (680007 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (55635257 / 200000000) ≤ -Real.log (1000000 / 1320719) ∧
    -Real.log (1000000 / 1320719) ≤ (139088143 / 500000000) := by
  have h := checkLog_sound (w := (320719 / 2320719)) (n := 12)
    (lo := (55635257 / 200000000)) (hi := (139088143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1320719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1320719 / 1000000) = 1/(1000000 / 1320719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (55635257 / 200000000) (139088143 / 500000000) (Real.log (1320719 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1320719 / 1000000) = -Real.log (1000000 / 1320719) := by
    rw [show ((1320719 / 1000000) : ℝ) = ((1000000 / 1320719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (386720393 / 1000000000) ≤ -Real.log (679281 / 1000000) ∧
    -Real.log (679281 / 1000000) ≤ (193360197 / 500000000) := by
  have h := checkLog_sound (w := (320719 / 1679281)) (n := 12)
    (lo := (386720393 / 1000000000)) (hi := (193360197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 679281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 679281) = 1/(679281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-193360197 / 500000000) (-386720393 / 1000000000) (Real.log (679281 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (918510437 / 1000000000) ≤ -Real.log (500000000000 / 1252777714483) ∧
    -Real.log (500000000000 / 1252777714483) ≤ (918510439 / 1000000000) := by
  have h := checkLog_sound (w := (252777714483 / 2252777714483)) (n := 12)
    (lo := (225363257 / 1000000000)) (hi := (112681629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252777714483 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1252777714483 / 1000000000000) = 1/(500000000000 / 1252777714483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (918510437 / 1000000000) (918510439 / 1000000000) (Real.log (1252777714483 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1252777714483 / 500000000000) = -Real.log (500000000000 / 1252777714483) := by
    rw [show ((1252777714483 / 500000000000) : ℝ) = ((500000000000 / 1252777714483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (460333519 / 500000000) ≤ -Real.log (500000000000 / 1255482371447) ∧
    -Real.log (500000000000 / 1255482371447) ≤ (5754169 / 6250000) := by
  have h := checkLog_sound (w := (255482371447 / 2255482371447)) (n := 12)
    (lo := (113759929 / 500000000)) (hi := (227519859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255482371447 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1255482371447 / 1000000000000) = 1/(500000000000 / 1255482371447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (460333519 / 500000000) (5754169 / 6250000) (Real.log (1255482371447 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1255482371447 / 500000000000) = -Real.log (500000000000 / 1255482371447) := by
    rw [show ((1255482371447 / 500000000000) : ℝ) = ((500000000000 / 1255482371447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33163931 / 50000000) ≤ -Real.log (500000000000 / 970573097041) ∧
    -Real.log (500000000000 / 970573097041) ≤ (663278621 / 1000000000) := by
  have h := checkLog_sound (w := (470573097041 / 1470573097041)) (n := 12)
    (lo := (33163931 / 50000000)) (hi := (663278621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970573097041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970573097041 / 500000000000) = 1/(500000000000 / 970573097041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (33163931 / 50000000) (663278621 / 1000000000) (Real.log (970573097041 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (970573097041 / 500000000000) = -Real.log (500000000000 / 970573097041) := by
    rw [show ((970573097041 / 500000000000) : ℝ) = ((500000000000 / 970573097041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (332448339 / 500000000) ≤ -Real.log (500000000000 / 972144811941) ∧
    -Real.log (500000000000 / 972144811941) ≤ (664896679 / 1000000000) := by
  have h := checkLog_sound (w := (472144811941 / 1472144811941)) (n := 12)
    (lo := (332448339 / 500000000)) (hi := (664896679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972144811941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972144811941 / 500000000000) = 1/(500000000000 / 972144811941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (332448339 / 500000000) (664896679 / 1000000000) (Real.log (972144811941 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (972144811941 / 500000000000) = -Real.log (500000000000 / 972144811941) := by
    rw [show ((972144811941 / 500000000000) : ℝ) = ((500000000000 / 972144811941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0209

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0210Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0210
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (130580809 / 500000000) ≤ -Real.log (640 / 831) ∧
    -Real.log (640 / 831) ≤ (261161619 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1471)) (n := 12)
    (lo := (130580809 / 500000000)) (hi := (261161619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831 / 640) = 1/(640 / 831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (130580809 / 500000000) (261161619 / 1000000000) (Real.log (831 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (831 / 640) = -Real.log (640 / 831) := by
    rw [show ((831 / 640) : ℝ) = ((640 / 831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (44305661 / 125000000) ≤ -Real.log (449 / 640) ∧
    -Real.log (449 / 640) ≤ (354445289 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1089)) (n := 12)
    (lo := (44305661 / 125000000)) (hi := (354445289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 449) = 1/(449 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-354445289 / 1000000000) (-44305661 / 125000000) (Real.log (449 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (260710253 / 1000000000) ≤ -Real.log (1024 / 1329) ∧
    -Real.log (1024 / 1329) ≤ (130355127 / 500000000) := by
  have h := checkLog_sound (w := (305 / 2353)) (n := 12)
    (lo := (260710253 / 1000000000)) (hi := (130355127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329 / 1024) = 1/(1024 / 1329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (260710253 / 1000000000) (130355127 / 500000000) (Real.log (1329 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1329 / 1024) = -Real.log (1024 / 1329) := by
    rw [show ((1329 / 1024) : ℝ) = ((1024 / 1329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (353610447 / 1000000000) ≤ -Real.log (719 / 1024) ∧
    -Real.log (719 / 1024) ≤ (22100653 / 62500000) := by
  have h := checkLog_sound (w := (305 / 1743)) (n := 12)
    (lo := (353610447 / 1000000000)) (hi := (22100653 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 719) = 1/(719 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22100653 / 62500000) (-353610447 / 1000000000) (Real.log (719 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (234024297 / 500000000) ≤ -Real.log (320 / 511) ∧
    -Real.log (320 / 511) ≤ (93609719 / 200000000) := by
  have h := checkLog_sound (w := (191 / 831)) (n := 12)
    (lo := (234024297 / 500000000)) (hi := (93609719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(511 / 320) = 1/(320 / 511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (234024297 / 500000000) (93609719 / 200000000) (Real.log (511 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (511 / 320) = -Real.log (320 / 511) := by
    rw [show ((511 / 320) : ℝ) = ((320 / 511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (90850859 / 100000000) ≤ -Real.log (129 / 320) ∧
    -Real.log (129 / 320) ≤ (56781787 / 62500000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 129) = 1/(129 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-56781787 / 62500000) (-90850859 / 100000000) (Real.log (129 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (467314469 / 1000000000) ≤ -Real.log (512 / 817) ∧
    -Real.log (512 / 817) ≤ (46731447 / 100000000) := by
  have h := checkLog_sound (w := (305 / 1329)) (n := 12)
    (lo := (467314469 / 1000000000)) (hi := (46731447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817 / 512) = 1/(512 / 817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (467314469 / 1000000000) (46731447 / 100000000) (Real.log (817 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (817 / 512) = -Real.log (512 / 817) := by
    rw [show ((817 / 512) : ℝ) = ((512 / 817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (905605831 / 1000000000) ≤ -Real.log (207 / 512) ∧
    -Real.log (207 / 512) ≤ (905605833 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 463)) (n := 12)
    (lo := (212458651 / 1000000000)) (hi := (53114663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 207) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 207) = 1/(207 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-905605833 / 1000000000) (-905605831 / 1000000000) (Real.log (207 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (356694243 / 1000000000) ≤ -Real.log (1000000 / 1428599) ∧
    -Real.log (1000000 / 1428599) ≤ (89173561 / 250000000) := by
  have h := checkLog_sound (w := (428599 / 2428599)) (n := 12)
    (lo := (356694243 / 1000000000)) (hi := (89173561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1428599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1428599 / 1000000) = 1/(1000000 / 1428599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (356694243 / 1000000000) (89173561 / 250000000) (Real.log (1428599 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1428599 / 1000000) = -Real.log (1000000 / 1428599) := by
    rw [show ((1428599 / 1000000) : ℝ) = ((1000000 / 1428599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (559664039 / 1000000000) ≤ -Real.log (571401 / 1000000) ∧
    -Real.log (571401 / 1000000) ≤ (13991601 / 25000000) := by
  have h := checkLog_sound (w := (428599 / 1571401)) (n := 12)
    (lo := (559664039 / 1000000000)) (hi := (13991601 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 571401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 571401) = 1/(571401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13991601 / 25000000) (-559664039 / 1000000000) (Real.log (571401 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (178654671 / 500000000) ≤ -Real.log (500000 / 714739) ∧
    -Real.log (500000 / 714739) ≤ (357309343 / 1000000000) := by
  have h := checkLog_sound (w := (214739 / 1214739)) (n := 12)
    (lo := (178654671 / 500000000)) (hi := (357309343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714739 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714739 / 500000) = 1/(500000 / 714739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (178654671 / 500000000) (357309343 / 1000000000) (Real.log (714739 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (714739 / 500000) = -Real.log (500000 / 714739) := by
    rw [show ((714739 / 500000) : ℝ) = ((500000 / 714739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (561203547 / 1000000000) ≤ -Real.log (285261 / 500000) ∧
    -Real.log (285261 / 500000) ≤ (140300887 / 250000000) := by
  have h := checkLog_sound (w := (214739 / 785261)) (n := 12)
    (lo := (561203547 / 1000000000)) (hi := (140300887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 285261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 285261) = 1/(285261 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-140300887 / 250000000) (-561203547 / 1000000000) (Real.log (285261 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (55415559 / 200000000) ≤ -Real.log (1000000 / 1319269) ∧
    -Real.log (1000000 / 1319269) ≤ (69269449 / 250000000) := by
  have h := checkLog_sound (w := (319269 / 2319269)) (n := 12)
    (lo := (55415559 / 200000000)) (hi := (69269449 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319269 / 1000000) = 1/(1000000 / 1319269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (55415559 / 200000000) (69269449 / 250000000) (Real.log (1319269 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1319269 / 1000000) = -Real.log (1000000 / 1319269) := by
    rw [show ((1319269 / 1000000) : ℝ) = ((1000000 / 1319269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (192294029 / 500000000) ≤ -Real.log (680731 / 1000000) ∧
    -Real.log (680731 / 1000000) ≤ (384588059 / 1000000000) := by
  have h := checkLog_sound (w := (319269 / 1680731)) (n := 12)
    (lo := (192294029 / 500000000)) (hi := (384588059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 680731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 680731) = 1/(680731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-384588059 / 1000000000) (-192294029 / 500000000) (Real.log (680731 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (277627191 / 1000000000) ≤ -Real.log (500000 / 659997) ∧
    -Real.log (500000 / 659997) ≤ (34703399 / 125000000) := by
  have h := checkLog_sound (w := (159997 / 1159997)) (n := 12)
    (lo := (277627191 / 1000000000)) (hi := (34703399 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659997 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659997 / 500000) = 1/(500000 / 659997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (277627191 / 1000000000) (34703399 / 125000000) (Real.log (659997 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (659997 / 500000) = -Real.log (500000 / 659997) := by
    rw [show ((659997 / 500000) : ℝ) = ((500000 / 659997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (385653657 / 1000000000) ≤ -Real.log (340003 / 500000) ∧
    -Real.log (340003 / 500000) ≤ (192826829 / 500000000) := by
  have h := checkLog_sound (w := (159997 / 840003)) (n := 12)
    (lo := (385653657 / 1000000000)) (hi := (192826829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 340003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 340003) = 1/(340003 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-192826829 / 500000000) (-385653657 / 1000000000) (Real.log (340003 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (458179141 / 500000000) ≤ -Real.log (250000000000 / 625042220787) ∧
    -Real.log (250000000000 / 625042220787) ≤ (229089571 / 250000000) := by
  have h := checkLog_sound (w := (125042220787 / 1125042220787)) (n := 12)
    (lo := (111605551 / 500000000)) (hi := (223211103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625042220787 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(625042220787 / 500000000000) = 1/(250000000000 / 625042220787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (458179141 / 500000000) (229089571 / 250000000) (Real.log (625042220787 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (625042220787 / 250000000000) = -Real.log (250000000000 / 625042220787) := by
    rw [show ((625042220787 / 250000000000) : ℝ) = ((250000000000 / 625042220787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (918512889 / 1000000000) ≤ -Real.log (500000000000 / 1252780786719) ∧
    -Real.log (500000000000 / 1252780786719) ≤ (918512891 / 1000000000) := by
  have h := checkLog_sound (w := (252780786719 / 2252780786719)) (n := 12)
    (lo := (225365709 / 1000000000)) (hi := (22536571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252780786719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1252780786719 / 1000000000000) = 1/(500000000000 / 1252780786719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (918512889 / 1000000000) (918512891 / 1000000000) (Real.log (1252780786719 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1252780786719 / 500000000000) = -Real.log (500000000000 / 1252780786719) := by
    rw [show ((1252780786719 / 500000000000) : ℝ) = ((500000000000 / 1252780786719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (661665853 / 1000000000) ≤ -Real.log (125000000000 / 242252262641) ∧
    -Real.log (125000000000 / 242252262641) ≤ (330832927 / 500000000) := by
  have h := checkLog_sound (w := (117252262641 / 367252262641)) (n := 12)
    (lo := (661665853 / 1000000000)) (hi := (330832927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242252262641 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242252262641 / 125000000000) = 1/(125000000000 / 242252262641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (661665853 / 1000000000) (330832927 / 500000000) (Real.log (242252262641 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (242252262641 / 125000000000) = -Real.log (125000000000 / 242252262641) := by
    rw [show ((242252262641 / 125000000000) : ℝ) = ((125000000000 / 242252262641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (41455053 / 62500000) ≤ -Real.log (500000000000 / 970575259631) ∧
    -Real.log (500000000000 / 970575259631) ≤ (663280849 / 1000000000) := by
  have h := checkLog_sound (w := (470575259631 / 1470575259631)) (n := 12)
    (lo := (41455053 / 62500000)) (hi := (663280849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970575259631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970575259631 / 500000000000) = 1/(500000000000 / 970575259631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (41455053 / 62500000) (663280849 / 1000000000) (Real.log (970575259631 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (970575259631 / 500000000000) = -Real.log (500000000000 / 970575259631) := by
    rw [show ((970575259631 / 500000000000) : ℝ) = ((500000000000 / 970575259631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0210

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0211Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0211
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (260710253 / 1000000000) ≤ -Real.log (1024 / 1329) ∧
    -Real.log (1024 / 1329) ≤ (130355127 / 500000000) := by
  have h := checkLog_sound (w := (305 / 2353)) (n := 12)
    (lo := (260710253 / 1000000000)) (hi := (130355127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329 / 1024) = 1/(1024 / 1329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (260710253 / 1000000000) (130355127 / 500000000) (Real.log (1329 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1329 / 1024) = -Real.log (1024 / 1329) := by
    rw [show ((1329 / 1024) : ℝ) = ((1024 / 1329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (353610447 / 1000000000) ≤ -Real.log (719 / 1024) ∧
    -Real.log (719 / 1024) ≤ (22100653 / 62500000) := by
  have h := checkLog_sound (w := (305 / 1743)) (n := 12)
    (lo := (353610447 / 1000000000)) (hi := (22100653 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 719) = 1/(719 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22100653 / 62500000) (-353610447 / 1000000000) (Real.log (719 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (260258683 / 1000000000) ≤ -Real.log (2560 / 3321) ∧
    -Real.log (2560 / 3321) ≤ (65064671 / 250000000) := by
  have h := checkLog_sound (w := (761 / 5881)) (n := 12)
    (lo := (260258683 / 1000000000)) (hi := (65064671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3321 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3321 / 2560) = 1/(2560 / 3321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (260258683 / 1000000000) (65064671 / 250000000) (Real.log (3321 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3321 / 2560) = -Real.log (2560 / 3321) := by
    rw [show ((3321 / 2560) : ℝ) = ((2560 / 3321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (352776303 / 1000000000) ≤ -Real.log (1799 / 2560) ∧
    -Real.log (1799 / 2560) ≤ (22048519 / 62500000) := by
  have h := checkLog_sound (w := (761 / 4359)) (n := 12)
    (lo := (352776303 / 1000000000)) (hi := (22048519 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1799) = 1/(1799 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22048519 / 62500000) (-352776303 / 1000000000) (Real.log (1799 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (467314469 / 1000000000) ≤ -Real.log (512 / 817) ∧
    -Real.log (512 / 817) ≤ (46731447 / 100000000) := by
  have h := checkLog_sound (w := (305 / 1329)) (n := 12)
    (lo := (467314469 / 1000000000)) (hi := (46731447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817 / 512) = 1/(512 / 817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (467314469 / 1000000000) (46731447 / 100000000) (Real.log (817 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (817 / 512) = -Real.log (512 / 817) := by
    rw [show ((817 / 512) : ℝ) = ((512 / 817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (905605831 / 1000000000) ≤ -Real.log (207 / 512) ∧
    -Real.log (207 / 512) ≤ (905605833 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 463)) (n := 12)
    (lo := (212458651 / 1000000000)) (hi := (53114663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 207) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 207) = 1/(207 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-905605833 / 1000000000) (-905605831 / 1000000000) (Real.log (207 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (93315961 / 200000000) ≤ -Real.log (1280 / 2041) ∧
    -Real.log (1280 / 2041) ≤ (233289903 / 500000000) := by
  have h := checkLog_sound (w := (761 / 3321)) (n := 12)
    (lo := (93315961 / 200000000)) (hi := (233289903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2041 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2041 / 1280) = 1/(1280 / 2041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (93315961 / 200000000) (233289903 / 500000000) (Real.log (2041 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2041 / 1280) = -Real.log (1280 / 2041) := by
    rw [show ((2041 / 1280) : ℝ) = ((1280 / 2041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (902711473 / 1000000000) ≤ -Real.log (519 / 1280) ∧
    -Real.log (519 / 1280) ≤ (36108459 / 40000000) := by
  have h := checkLog_sound (w := (121 / 1159)) (n := 12)
    (lo := (209564293 / 1000000000)) (hi := (104782147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 519) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 519) = 1/(519 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-36108459 / 40000000) (-902711473 / 1000000000) (Real.log (519 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (178039733 / 500000000) ≤ -Real.log (1000000 / 1427721) ∧
    -Real.log (1000000 / 1427721) ≤ (356079467 / 1000000000) := by
  have h := checkLog_sound (w := (427721 / 2427721)) (n := 12)
    (lo := (178039733 / 500000000)) (hi := (356079467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1427721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1427721 / 1000000) = 1/(1000000 / 1427721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (178039733 / 500000000) (356079467 / 1000000000) (Real.log (1427721 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1427721 / 1000000) = -Real.log (1000000 / 1427721) := by
    rw [show ((1427721 / 1000000) : ℝ) = ((1000000 / 1427721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (139532161 / 250000000) ≤ -Real.log (572279 / 1000000) ∧
    -Real.log (572279 / 1000000) ≤ (111625729 / 200000000) := by
  have h := checkLog_sound (w := (427721 / 1572279)) (n := 12)
    (lo := (139532161 / 250000000)) (hi := (111625729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 572279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 572279) = 1/(572279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-111625729 / 200000000) (-139532161 / 250000000) (Real.log (572279 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (356695643 / 1000000000) ≤ -Real.log (1000000 / 1428601) ∧
    -Real.log (1000000 / 1428601) ≤ (89173911 / 250000000) := by
  have h := checkLog_sound (w := (428601 / 2428601)) (n := 12)
    (lo := (356695643 / 1000000000)) (hi := (89173911 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1428601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1428601 / 1000000) = 1/(1000000 / 1428601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (356695643 / 1000000000) (89173911 / 250000000) (Real.log (1428601 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1428601 / 1000000) = -Real.log (1000000 / 1428601) := by
    rw [show ((1428601 / 1000000) : ℝ) = ((1000000 / 1428601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (559667539 / 1000000000) ≤ -Real.log (571399 / 1000000) ∧
    -Real.log (571399 / 1000000) ≤ (27983377 / 50000000) := by
  have h := checkLog_sound (w := (428601 / 1571399)) (n := 12)
    (lo := (559667539 / 1000000000)) (hi := (27983377 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 571399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 571399) = 1/(571399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-27983377 / 50000000) (-559667539 / 1000000000) (Real.log (571399 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (138264807 / 500000000) ≤ -Real.log (500000 / 659273) ∧
    -Real.log (500000 / 659273) ≤ (55305923 / 200000000) := by
  have h := checkLog_sound (w := (159273 / 1159273)) (n := 12)
    (lo := (138264807 / 500000000)) (hi := (55305923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659273 / 500000) = 1/(500000 / 659273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (138264807 / 500000000) (55305923 / 200000000) (Real.log (659273 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (659273 / 500000) = -Real.log (500000 / 659273) := by
    rw [show ((659273 / 500000) : ℝ) = ((500000 / 659273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2996301 / 7812500) ≤ -Real.log (340727 / 500000) ∧
    -Real.log (340727 / 500000) ≤ (383526529 / 1000000000) := by
  have h := checkLog_sound (w := (159273 / 840727)) (n := 12)
    (lo := (2996301 / 7812500)) (hi := (383526529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 340727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 340727) = 1/(340727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-383526529 / 1000000000) (-2996301 / 7812500) (Real.log (340727 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (277078553 / 1000000000) ≤ -Real.log (100000 / 131927) ∧
    -Real.log (100000 / 131927) ≤ (138539277 / 500000000) := by
  have h := checkLog_sound (w := (31927 / 231927)) (n := 12)
    (lo := (277078553 / 1000000000)) (hi := (138539277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131927 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131927 / 100000) = 1/(100000 / 131927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (277078553 / 1000000000) (138539277 / 500000000) (Real.log (131927 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (131927 / 100000) = -Real.log (100000 / 131927) := by
    rw [show ((131927 / 100000) : ℝ) = ((100000 / 131927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (384589527 / 1000000000) ≤ -Real.log (68073 / 100000) ∧
    -Real.log (68073 / 100000) ≤ (48073691 / 125000000) := by
  have h := checkLog_sound (w := (31927 / 168073)) (n := 12)
    (lo := (384589527 / 1000000000)) (hi := (48073691 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 68073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 68073) = 1/(68073 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-48073691 / 125000000) (-384589527 / 1000000000) (Real.log (68073 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (91420811 / 100000000) ≤ -Real.log (250000000000 / 623699716397) ∧
    -Real.log (250000000000 / 623699716397) ≤ (57138007 / 62500000) := by
  have h := checkLog_sound (w := (123699716397 / 1123699716397)) (n := 12)
    (lo := (22106093 / 100000000)) (hi := (221060931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623699716397 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(623699716397 / 500000000000) = 1/(250000000000 / 623699716397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (91420811 / 100000000) (57138007 / 62500000) (Real.log (623699716397 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (623699716397 / 250000000000) = -Real.log (250000000000 / 623699716397) := by
    rw [show ((623699716397 / 250000000000) : ℝ) = ((250000000000 / 623699716397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (458181591 / 500000000) ≤ -Real.log (500000000000 / 1250090567187) ∧
    -Real.log (500000000000 / 1250090567187) ≤ (57272699 / 62500000) := by
  have h := checkLog_sound (w := (250090567187 / 2250090567187)) (n := 12)
    (lo := (111608001 / 500000000)) (hi := (223216003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250090567187 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1250090567187 / 1000000000000) = 1/(500000000000 / 1250090567187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (458181591 / 500000000) (57272699 / 62500000) (Real.log (1250090567187 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1250090567187 / 500000000000) = -Real.log (500000000000 / 1250090567187) := by
    rw [show ((1250090567187 / 500000000000) : ℝ) = ((500000000000 / 1250090567187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (330028071 / 500000000) ≤ -Real.log (500000000000 / 967450480883) ∧
    -Real.log (500000000000 / 967450480883) ≤ (660056143 / 1000000000) := by
  have h := checkLog_sound (w := (467450480883 / 1467450480883)) (n := 12)
    (lo := (330028071 / 500000000)) (hi := (660056143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((967450480883 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(967450480883 / 500000000000) = 1/(500000000000 / 967450480883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (330028071 / 500000000) (660056143 / 1000000000) (Real.log (967450480883 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (967450480883 / 500000000000) = -Real.log (500000000000 / 967450480883) := by
    rw [show ((967450480883 / 500000000000) : ℝ) = ((500000000000 / 967450480883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (8270851 / 12500000) ≤ -Real.log (125000000000 / 242252802139) ∧
    -Real.log (125000000000 / 242252802139) ≤ (661668081 / 1000000000) := by
  have h := checkLog_sound (w := (117252802139 / 367252802139)) (n := 12)
    (lo := (8270851 / 12500000)) (hi := (661668081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242252802139 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242252802139 / 125000000000) = 1/(125000000000 / 242252802139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (8270851 / 12500000) (661668081 / 1000000000) (Real.log (242252802139 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (242252802139 / 125000000000) = -Real.log (125000000000 / 242252802139) := by
    rw [show ((242252802139 / 125000000000) : ℝ) = ((125000000000 / 242252802139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0211

end


