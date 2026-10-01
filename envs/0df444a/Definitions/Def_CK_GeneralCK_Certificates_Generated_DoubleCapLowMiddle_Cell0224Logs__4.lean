-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0224Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0224Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:50:33.19454+00:00
-- url     : https://prove2.me/theorems/c4241bb2-2b85-4e82-ac66-378ba3c2f199
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0224Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0225Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0224Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0225Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0226Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0227Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0224Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0225Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0226Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0227Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0224Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0225Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0226Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0227Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0224Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0225Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0226Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0227Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0224Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0224
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

theorem reflection_log_1_neg : (499258987 / 1000000000) ≤ -Real.log (400 / 659) ∧
    -Real.log (400 / 659) ≤ (124814747 / 250000000) := by
  have h := checkLog_sound (w := (259 / 1059)) (n := 12)
    (lo := (499258987 / 1000000000)) (hi := (124814747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659 / 400) = 1/(400 / 659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (499258987 / 1000000000) (124814747 / 250000000) (Real.log (659 / 400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (659 / 400) = -Real.log (400 / 659) := by
    rw [show ((659 / 400) : ℝ) = ((400 / 659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (65169041 / 62500000) ≤ -Real.log (141 / 400) ∧
    -Real.log (141 / 400) ≤ (521352329 / 500000000) := by
  have h := checkLog_sound (w := (59 / 341)) (n := 12)
    (lo := (87389369 / 250000000)) (hi := (349557477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 141) = 1/(141 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-521352329 / 500000000) (-65169041 / 62500000) (Real.log (141 / 400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (246012497 / 500000000) ≤ -Real.log (1600 / 2617) ∧
    -Real.log (1600 / 2617) ≤ (98404999 / 200000000) := by
  have h := checkLog_sound (w := (1017 / 4217)) (n := 12)
    (lo := (246012497 / 500000000)) (hi := (98404999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2617 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2617 / 1600) = 1/(1600 / 2617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (246012497 / 500000000) (98404999 / 200000000) (Real.log (2617 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2617 / 1600) = -Real.log (1600 / 2617) := by
    rw [show ((2617 / 1600) : ℝ) = ((1600 / 2617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1009571721 / 1000000000) ≤ -Real.log (583 / 1600) ∧
    -Real.log (583 / 1600) ≤ (1009571723 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1383)) (n := 12)
    (lo := (316424541 / 1000000000)) (hi := (158212271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 583) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 583) = 1/(583 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1009571723 / 1000000000) (-1009571721 / 1000000000) (Real.log (583 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (51702139 / 200000000) ≤ -Real.log (200 / 259) ∧
    -Real.log (200 / 259) ≤ (32313837 / 125000000) := by
  have h := checkLog_sound (w := (59 / 459)) (n := 12)
    (lo := (51702139 / 200000000)) (hi := (32313837 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259 / 200) = 1/(200 / 259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (51702139 / 200000000) (32313837 / 125000000) (Real.log (259 / 200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (259 / 200) = -Real.log (200 / 259) := by
    rw [show ((259 / 200) : ℝ) = ((200 / 259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (87389369 / 250000000) ≤ -Real.log (141 / 200) ∧
    -Real.log (141 / 200) ≤ (349557477 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 341)) (n := 12)
    (lo := (87389369 / 250000000)) (hi := (349557477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 141) = 1/(141 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-349557477 / 1000000000) (-87389369 / 250000000) (Real.log (141 / 200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (60000167 / 250000000) ≤ -Real.log (800 / 1017) ∧
    -Real.log (800 / 1017) ≤ (240000669 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1817)) (n := 12)
    (lo := (60000167 / 250000000)) (hi := (240000669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1017 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1017 / 800) = 1/(800 / 1017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (60000167 / 250000000) (240000669 / 1000000000) (Real.log (1017 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1017 / 800) = -Real.log (800 / 1017) := by
    rw [show ((1017 / 800) : ℝ) = ((800 / 1017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (316424541 / 1000000000) ≤ -Real.log (583 / 800) ∧
    -Real.log (583 / 800) ≤ (158212271 / 500000000) := by
  have h := checkLog_sound (w := (217 / 1383)) (n := 12)
    (lo := (316424541 / 1000000000)) (hi := (158212271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 583) = 1/(583 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-158212271 / 500000000) (-316424541 / 1000000000) (Real.log (583 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (293166137 / 500000000) ≤ -Real.log (125000 / 224673) ∧
    -Real.log (125000 / 224673) ≤ (23453291 / 40000000) := by
  have h := checkLog_sound (w := (99673 / 349673)) (n := 12)
    (lo := (293166137 / 500000000)) (hi := (23453291 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((224673 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(224673 / 125000) = 1/(125000 / 224673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (293166137 / 500000000) (23453291 / 40000000) (Real.log (224673 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (224673 / 125000) = -Real.log (125000 / 224673) := by
    rw [show ((224673 / 125000) : ℝ) = ((125000 / 224673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (319288543 / 200000000) ≤ -Real.log (25327 / 125000) ∧
    -Real.log (25327 / 125000) ≤ (798221359 / 500000000) := by
  have h := checkLog_sound (w := (5923 / 56577)) (n := 12)
    (lo := (42029671 / 200000000)) (hi := (52537089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25327) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 25327) = 1/(25327 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-798221359 / 500000000) (-319288543 / 200000000) (Real.log (25327 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (588086619 / 1000000000) ≤ -Real.log (50000 / 90027) ∧
    -Real.log (50000 / 90027) ≤ (29404331 / 50000000) := by
  have h := checkLog_sound (w := (40027 / 140027)) (n := 12)
    (lo := (588086619 / 1000000000)) (hi := (29404331 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90027 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90027 / 50000) = 1/(50000 / 90027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (588086619 / 1000000000) (29404331 / 50000000) (Real.log (90027 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (90027 / 50000) = -Real.log (50000 / 90027) := by
    rw [show ((90027 / 50000) : ℝ) = ((50000 / 90027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (806070781 / 500000000) ≤ -Real.log (9973 / 50000) ∧
    -Real.log (9973 / 50000) ≤ (322428313 / 200000000) := by
  have h := checkLog_sound (w := (2527 / 22473)) (n := 12)
    (lo := (112923601 / 500000000)) (hi := (225847203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9973) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(12500 / 9973) = 1/(9973 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-322428313 / 200000000) (-806070781 / 500000000) (Real.log (9973 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1085307 / 1953125) ≤ -Real.log (1000000 / 1743121) ∧
    -Real.log (1000000 / 1743121) ≤ (111135437 / 200000000) := by
  have h := checkLog_sound (w := (743121 / 2743121)) (n := 12)
    (lo := (1085307 / 1953125)) (hi := (111135437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1743121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1743121 / 1000000) = 1/(1000000 / 1743121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1085307 / 1953125) (111135437 / 200000000) (Real.log (1743121 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1743121 / 1000000) = -Real.log (1000000 / 1743121) := by
    rw [show ((1743121 / 1000000) : ℝ) = ((1000000 / 1743121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1359150121 / 1000000000) ≤ -Real.log (256879 / 1000000) ∧
    -Real.log (256879 / 1000000) ≤ (1359150123 / 1000000000) := by
  have h := checkLog_sound (w := (243121 / 756879)) (n := 12)
    (lo := (666002941 / 1000000000)) (hi := (333001471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 256879) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 256879) = 1/(256879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1359150123 / 1000000000) (-1359150121 / 1000000000) (Real.log (256879 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (559969439 / 1000000000) ≤ -Real.log (1000000 / 1750619) ∧
    -Real.log (1000000 / 1750619) ≤ (3499809 / 6250000) := by
  have h := checkLog_sound (w := (750619 / 2750619)) (n := 12)
    (lo := (559969439 / 1000000000)) (hi := (3499809 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1750619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1750619 / 1000000) = 1/(1000000 / 1750619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (559969439 / 1000000000) (3499809 / 6250000) (Real.log (1750619 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1750619 / 1000000) = -Real.log (1000000 / 1750619) := by
    rw [show ((1750619 / 1000000) : ℝ) = ((1000000 / 1750619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (138877343 / 100000000) ≤ -Real.log (249381 / 1000000) ∧
    -Real.log (249381 / 1000000) ≤ (1388773433 / 1000000000) := by
  have h := checkLog_sound (w := (619 / 499381)) (n := 12)
    (lo := (247907 / 100000000)) (hi := (2479071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249381) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 249381) = 1/(249381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1388773433 / 1000000000) (-138877343 / 100000000) (Real.log (249381 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2182774989 / 1000000000) ≤ -Real.log (125000000000 / 1108861096853) ∧
    -Real.log (125000000000 / 1108861096853) ≤ (2182774993 / 1000000000) := by
  have h := checkLog_sound (w := (108861096853 / 2108861096853)) (n := 12)
    (lo := (103333449 / 1000000000)) (hi := (2066669 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1108861096853 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1108861096853 / 1000000000000) = 1/(125000000000 / 1108861096853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2182774989 / 1000000000) (2182774993 / 1000000000) (Real.log (1108861096853 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1108861096853 / 125000000000) = -Real.log (125000000000 / 1108861096853) := by
    rw [show ((1108861096853 / 125000000000) : ℝ) = ((125000000000 / 1108861096853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1100114091 / 500000000) ≤ -Real.log (250000000000 / 2256768274341) ∧
    -Real.log (250000000000 / 2256768274341) ≤ (1100114093 / 500000000) := by
  have h := checkLog_sound (w := (256768274341 / 4256768274341)) (n := 12)
    (lo := (60393321 / 500000000)) (hi := (120786643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2256768274341 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2256768274341 / 2000000000000) = 1/(250000000000 / 2256768274341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1100114091 / 500000000) (1100114093 / 500000000) (Real.log (2256768274341 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2256768274341 / 250000000000) = -Real.log (250000000000 / 2256768274341) := by
    rw [show ((2256768274341 / 250000000000) : ℝ) = ((250000000000 / 2256768274341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (382965461 / 200000000) ≤ -Real.log (25000000000 / 169644170991) ∧
    -Real.log (25000000000 / 169644170991) ≤ (478706827 / 250000000) := by
  have h := checkLog_sound (w := (69644170991 / 269644170991)) (n := 12)
    (lo := (105706589 / 200000000)) (hi := (264266473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169644170991 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(169644170991 / 100000000000) = 1/(25000000000 / 169644170991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (382965461 / 200000000) (478706827 / 250000000) (Real.log (169644170991 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (169644170991 / 25000000000) = -Real.log (25000000000 / 169644170991) := by
    rw [show ((169644170991 / 25000000000) : ℝ) = ((25000000000 / 169644170991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (194874287 / 100000000) ≤ -Real.log (125000000000 / 877482145793) ∧
    -Real.log (125000000000 / 877482145793) ≤ (1948742873 / 1000000000) := by
  have h := checkLog_sound (w := (377482145793 / 1377482145793)) (n := 12)
    (lo := (56244851 / 100000000)) (hi := (562448511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((877482145793 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(877482145793 / 500000000000) = 1/(125000000000 / 877482145793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (194874287 / 100000000) (1948742873 / 1000000000) (Real.log (877482145793 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (877482145793 / 125000000000) = -Real.log (125000000000 / 877482145793) := by
    rw [show ((877482145793 / 125000000000) : ℝ) = ((125000000000 / 877482145793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0224

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0225Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0225
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

theorem reflection_log_1_neg : (246012497 / 500000000) ≤ -Real.log (1600 / 2617) ∧
    -Real.log (1600 / 2617) ≤ (98404999 / 200000000) := by
  have h := checkLog_sound (w := (1017 / 4217)) (n := 12)
    (lo := (246012497 / 500000000)) (hi := (98404999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2617 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2617 / 1600) = 1/(1600 / 2617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (246012497 / 500000000) (98404999 / 200000000) (Real.log (2617 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2617 / 1600) = -Real.log (1600 / 2617) := by
    rw [show ((2617 / 1600) : ℝ) = ((1600 / 2617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1009571721 / 1000000000) ≤ -Real.log (583 / 1600) ∧
    -Real.log (583 / 1600) ≤ (1009571723 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1383)) (n := 12)
    (lo := (316424541 / 1000000000)) (hi := (158212271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 583) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 583) = 1/(583 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1009571723 / 1000000000) (-1009571721 / 1000000000) (Real.log (583 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (484738289 / 1000000000) ≤ -Real.log (800 / 1299) ∧
    -Real.log (800 / 1299) ≤ (48473829 / 100000000) := by
  have h := checkLog_sound (w := (499 / 2099)) (n := 12)
    (lo := (484738289 / 1000000000)) (hi := (48473829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299 / 800) = 1/(800 / 1299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (484738289 / 1000000000) (48473829 / 100000000) (Real.log (1299 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1299 / 800) = -Real.log (800 / 1299) := by
    rw [show ((1299 / 800) : ℝ) = ((800 / 1299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (488750731 / 500000000) ≤ -Real.log (301 / 800) ∧
    -Real.log (301 / 800) ≤ (122187683 / 125000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 301) = 1/(301 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-122187683 / 125000000) (-488750731 / 500000000) (Real.log (301 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (60000167 / 250000000) ≤ -Real.log (800 / 1017) ∧
    -Real.log (800 / 1017) ≤ (240000669 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1817)) (n := 12)
    (lo := (60000167 / 250000000)) (hi := (240000669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1017 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1017 / 800) = 1/(800 / 1017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (60000167 / 250000000) (240000669 / 1000000000) (Real.log (1017 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1017 / 800) = -Real.log (800 / 1017) := by
    rw [show ((1017 / 800) : ℝ) = ((800 / 1017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (316424541 / 1000000000) ≤ -Real.log (583 / 800) ∧
    -Real.log (583 / 800) ≤ (158212271 / 500000000) := by
  have h := checkLog_sound (w := (217 / 1383)) (n := 12)
    (lo := (316424541 / 1000000000)) (hi := (158212271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 583) = 1/(583 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-158212271 / 500000000) (-316424541 / 1000000000) (Real.log (583 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (55285387 / 250000000) ≤ -Real.log (400 / 499) ∧
    -Real.log (400 / 499) ≤ (221141549 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 899)) (n := 12)
    (lo := (55285387 / 250000000)) (hi := (221141549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 400) = 1/(400 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (55285387 / 250000000) (221141549 / 1000000000) (Real.log (499 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (499 / 400) = -Real.log (400 / 499) := by
    rw [show ((499 / 400) : ℝ) = ((400 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (142177141 / 500000000) ≤ -Real.log (301 / 400) ∧
    -Real.log (301 / 400) ≤ (284354283 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 301) = 1/(301 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-284354283 / 1000000000) (-142177141 / 500000000) (Real.log (301 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (73089759 / 125000000) ≤ -Real.log (200000 / 358897) ∧
    -Real.log (200000 / 358897) ≤ (584718073 / 1000000000) := by
  have h := checkLog_sound (w := (158897 / 558897)) (n := 12)
    (lo := (73089759 / 125000000)) (hi := (584718073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358897 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358897 / 200000) = 1/(200000 / 358897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (73089759 / 125000000) (584718073 / 1000000000) (Real.log (358897 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (358897 / 200000) = -Real.log (200000 / 358897) := by
    rw [show ((358897 / 200000) : ℝ) = ((200000 / 358897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1582236253 / 1000000000) ≤ -Real.log (41103 / 200000) ∧
    -Real.log (41103 / 200000) ≤ (49444883 / 31250000) := by
  have h := checkLog_sound (w := (8897 / 91103)) (n := 12)
    (lo := (195941893 / 1000000000)) (hi := (97970947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41103) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 41103) = 1/(41103 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-49444883 / 31250000) (-1582236253 / 1000000000) (Real.log (41103 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (58633283 / 100000000) ≤ -Real.log (200000 / 359477) ∧
    -Real.log (200000 / 359477) ≤ (586332831 / 1000000000) := by
  have h := checkLog_sound (w := (159477 / 559477)) (n := 12)
    (lo := (58633283 / 100000000)) (hi := (586332831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359477 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359477 / 200000) = 1/(200000 / 359477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (58633283 / 100000000) (586332831 / 1000000000) (Real.log (359477 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (359477 / 200000) = -Real.log (200000 / 359477) := by
    rw [show ((359477 / 200000) : ℝ) = ((200000 / 359477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1596447651 / 1000000000) ≤ -Real.log (40523 / 200000) ∧
    -Real.log (40523 / 200000) ≤ (798223827 / 500000000) := by
  have h := checkLog_sound (w := (9477 / 90523)) (n := 12)
    (lo := (210153291 / 1000000000)) (hi := (52538323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40523) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 40523) = 1/(40523 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-798223827 / 500000000) (-1596447651 / 1000000000) (Real.log (40523 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (551382559 / 1000000000) ≤ -Real.log (1000000 / 1735651) ∧
    -Real.log (1000000 / 1735651) ≤ (3446141 / 6250000) := by
  have h := checkLog_sound (w := (735651 / 2735651)) (n := 12)
    (lo := (551382559 / 1000000000)) (hi := (3446141 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1735651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1735651 / 1000000) = 1/(1000000 / 1735651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (551382559 / 1000000000) (3446141 / 6250000) (Real.log (1735651 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1735651 / 1000000) = -Real.log (1000000 / 1735651) := by
    rw [show ((1735651 / 1000000) : ℝ) = ((1000000 / 1735651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (665242539 / 500000000) ≤ -Real.log (264349 / 1000000) ∧
    -Real.log (264349 / 1000000) ≤ (33262127 / 25000000) := by
  have h := checkLog_sound (w := (235651 / 764349)) (n := 12)
    (lo := (318668949 / 500000000)) (hi := (637337899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 264349) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 264349) = 1/(264349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-33262127 / 25000000) (-665242539 / 500000000) (Real.log (264349 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (277838879 / 500000000) ≤ -Real.log (500000 / 871561) ∧
    -Real.log (500000 / 871561) ≤ (555677759 / 1000000000) := by
  have h := checkLog_sound (w := (371561 / 1371561)) (n := 12)
    (lo := (277838879 / 500000000)) (hi := (555677759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871561 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871561 / 500000) = 1/(500000 / 871561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (277838879 / 500000000) (555677759 / 1000000000) (Real.log (871561 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (871561 / 500000) = -Real.log (500000 / 871561) := by
    rw [show ((871561 / 500000) : ℝ) = ((500000 / 871561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (679577007 / 500000000) ≤ -Real.log (128439 / 500000) ∧
    -Real.log (128439 / 500000) ≤ (42473563 / 31250000) := by
  have h := checkLog_sound (w := (121561 / 378439)) (n := 12)
    (lo := (333003417 / 500000000)) (hi := (133201367 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 128439) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 128439) = 1/(128439 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-42473563 / 31250000) (-679577007 / 500000000) (Real.log (128439 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1083477163 / 500000000) ≤ -Real.log (250000000000 / 2182912439481) ∧
    -Real.log (250000000000 / 2182912439481) ≤ (216695433 / 100000000) := by
  have h := checkLog_sound (w := (182912439481 / 4182912439481)) (n := 12)
    (lo := (43756393 / 500000000)) (hi := (87512787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2182912439481 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2182912439481 / 2000000000000) = 1/(250000000000 / 2182912439481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1083477163 / 500000000) (216695433 / 100000000) (Real.log (2182912439481 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2182912439481 / 250000000000) = -Real.log (250000000000 / 2182912439481) := by
    rw [show ((2182912439481 / 250000000000) : ℝ) = ((250000000000 / 2182912439481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2182780481 / 1000000000) ≤ -Real.log (100000000000 / 887093749229) ∧
    -Real.log (100000000000 / 887093749229) ≤ (436556097 / 200000000) := by
  have h := checkLog_sound (w := (87093749229 / 1687093749229)) (n := 12)
    (lo := (103338941 / 1000000000)) (hi := (51669471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887093749229 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(887093749229 / 800000000000) = 1/(100000000000 / 887093749229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2182780481 / 1000000000) (436556097 / 200000000) (Real.log (887093749229 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (887093749229 / 100000000000) = -Real.log (100000000000 / 887093749229) := by
    rw [show ((887093749229 / 100000000000) : ℝ) = ((100000000000 / 887093749229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1881867637 / 1000000000) ≤ -Real.log (500000000000 / 3282877937877) ∧
    -Real.log (500000000000 / 3282877937877) ≤ (47046691 / 25000000) := by
  have h := checkLog_sound (w := (1282877937877 / 5282877937877)) (n := 12)
    (lo := (495573277 / 1000000000)) (hi := (247786639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3282877937877 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3282877937877 / 2000000000000) = 1/(500000000000 / 3282877937877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1881867637 / 1000000000) (47046691 / 25000000) (Real.log (3282877937877 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3282877937877 / 500000000000) = -Real.log (500000000000 / 3282877937877) := by
    rw [show ((3282877937877 / 500000000000) : ℝ) = ((500000000000 / 3282877937877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (478707943 / 250000000) ≤ -Real.log (500000000000 / 3392898574421) ∧
    -Real.log (500000000000 / 3392898574421) ≤ (76593271 / 40000000) := by
  have h := checkLog_sound (w := (1392898574421 / 5392898574421)) (n := 12)
    (lo := (132134353 / 250000000)) (hi := (528537413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3392898574421 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3392898574421 / 2000000000000) = 1/(500000000000 / 3392898574421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (478707943 / 250000000) (76593271 / 40000000) (Real.log (3392898574421 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3392898574421 / 500000000000) = -Real.log (500000000000 / 3392898574421) := by
    rw [show ((3392898574421 / 500000000000) : ℝ) = ((500000000000 / 3392898574421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0225

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0226Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0226
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

theorem reflection_log_1_neg : (484738289 / 1000000000) ≤ -Real.log (800 / 1299) ∧
    -Real.log (800 / 1299) ≤ (48473829 / 100000000) := by
  have h := checkLog_sound (w := (499 / 2099)) (n := 12)
    (lo := (484738289 / 1000000000)) (hi := (48473829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299 / 800) = 1/(800 / 1299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (484738289 / 1000000000) (48473829 / 100000000) (Real.log (1299 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1299 / 800) = -Real.log (800 / 1299) := by
    rw [show ((1299 / 800) : ℝ) = ((800 / 1299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (488750731 / 500000000) ≤ -Real.log (301 / 800) ∧
    -Real.log (301 / 800) ≤ (122187683 / 125000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 301) = 1/(301 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122187683 / 125000000) (-488750731 / 500000000) (Real.log (301 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (477398097 / 1000000000) ≤ -Real.log (1600 / 2579) ∧
    -Real.log (1600 / 2579) ≤ (238699049 / 500000000) := by
  have h := checkLog_sound (w := (979 / 4179)) (n := 12)
    (lo := (477398097 / 1000000000)) (hi := (238699049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2579 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2579 / 1600) = 1/(1600 / 2579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (477398097 / 1000000000) (238699049 / 500000000) (Real.log (2579 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2579 / 1600) = -Real.log (1600 / 2579) := by
    rw [show ((2579 / 1600) : ℝ) = ((1600 / 2579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (37857113 / 40000000) ≤ -Real.log (621 / 1600) ∧
    -Real.log (621 / 1600) ≤ (946427827 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 1421)) (n := 12)
    (lo := (50656129 / 200000000)) (hi := (126640323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 621) = 1/(621 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-946427827 / 1000000000) (-37857113 / 40000000) (Real.log (621 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (55285387 / 250000000) ≤ -Real.log (400 / 499) ∧
    -Real.log (400 / 499) ≤ (221141549 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 899)) (n := 12)
    (lo := (55285387 / 250000000)) (hi := (221141549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 400) = 1/(400 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (55285387 / 250000000) (221141549 / 1000000000) (Real.log (499 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (499 / 400) = -Real.log (400 / 499) := by
    rw [show ((499 / 400) : ℝ) = ((400 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (142177141 / 500000000) ≤ -Real.log (301 / 400) ∧
    -Real.log (301 / 400) ≤ (284354283 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 301) = 1/(301 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-284354283 / 1000000000) (-142177141 / 500000000) (Real.log (301 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (100959957 / 500000000) ≤ -Real.log (800 / 979) ∧
    -Real.log (800 / 979) ≤ (40383983 / 200000000) := by
  have h := checkLog_sound (w := (179 / 1779)) (n := 12)
    (lo := (100959957 / 500000000)) (hi := (40383983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979 / 800) = 1/(800 / 979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (100959957 / 500000000) (40383983 / 200000000) (Real.log (979 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (979 / 800) = -Real.log (800 / 979) := by
    rw [show ((979 / 800) : ℝ) = ((800 / 979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50656129 / 200000000) ≤ -Real.log (621 / 800) ∧
    -Real.log (621 / 800) ≤ (126640323 / 500000000) := by
  have h := checkLog_sound (w := (179 / 1421)) (n := 12)
    (lo := (50656129 / 200000000)) (hi := (126640323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 621) = 1/(621 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-126640323 / 500000000) (-50656129 / 200000000) (Real.log (621 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (583245257 / 1000000000) ≤ -Real.log (250000 / 447961) ∧
    -Real.log (250000 / 447961) ≤ (291622629 / 500000000) := by
  have h := checkLog_sound (w := (197961 / 697961)) (n := 12)
    (lo := (583245257 / 1000000000)) (hi := (291622629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447961 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447961 / 250000) = 1/(250000 / 447961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (583245257 / 1000000000) (291622629 / 500000000) (Real.log (447961 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (447961 / 250000) = -Real.log (250000 / 447961) := by
    rw [show ((447961 / 250000) : ℝ) = ((250000 / 447961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1569467479 / 1000000000) ≤ -Real.log (52039 / 250000) ∧
    -Real.log (52039 / 250000) ≤ (784733741 / 500000000) := by
  have h := checkLog_sound (w := (10461 / 114539)) (n := 12)
    (lo := (183173119 / 1000000000)) (hi := (71552 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52039) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 52039) = 1/(52039 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-784733741 / 500000000) (-1569467479 / 1000000000) (Real.log (52039 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (584718629 / 1000000000) ≤ -Real.log (500000 / 897243) ∧
    -Real.log (500000 / 897243) ≤ (58471863 / 100000000) := by
  have h := checkLog_sound (w := (397243 / 1397243)) (n := 12)
    (lo := (584718629 / 1000000000)) (hi := (58471863 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897243 / 500000) = 1/(500000 / 897243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (584718629 / 1000000000) (58471863 / 100000000) (Real.log (897243 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (897243 / 500000) = -Real.log (500000 / 897243) := by
    rw [show ((897243 / 500000) : ℝ) = ((500000 / 897243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1582241119 / 1000000000) ≤ -Real.log (102757 / 500000) ∧
    -Real.log (102757 / 500000) ≤ (791120561 / 500000000) := by
  have h := checkLog_sound (w := (22243 / 227757)) (n := 12)
    (lo := (195946759 / 1000000000)) (hi := (4898669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102757) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 102757) = 1/(102757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-791120561 / 500000000) (-1582241119 / 1000000000) (Real.log (102757 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (273542227 / 500000000) ≤ -Real.log (1000000 / 1728207) ∧
    -Real.log (1000000 / 1728207) ≤ (109416891 / 200000000) := by
  have h := checkLog_sound (w := (728207 / 2728207)) (n := 12)
    (lo := (273542227 / 500000000)) (hi := (109416891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1728207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1728207 / 1000000) = 1/(1000000 / 1728207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (273542227 / 500000000) (109416891 / 200000000) (Real.log (1728207 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1728207 / 1000000) = -Real.log (1000000 / 1728207) := by
    rw [show ((1728207 / 1000000) : ℝ) = ((1000000 / 1728207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1302714531 / 1000000000) ≤ -Real.log (271793 / 1000000) ∧
    -Real.log (271793 / 1000000) ≤ (1302714533 / 1000000000) := by
  have h := checkLog_sound (w := (228207 / 771793)) (n := 12)
    (lo := (609567351 / 1000000000)) (hi := (76195919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 271793) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 271793) = 1/(271793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1302714533 / 1000000000) (-1302714531 / 1000000000) (Real.log (271793 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (110276627 / 200000000) ≤ -Real.log (250000 / 433913) ∧
    -Real.log (250000 / 433913) ≤ (17230723 / 31250000) := by
  have h := checkLog_sound (w := (183913 / 683913)) (n := 12)
    (lo := (110276627 / 200000000)) (hi := (17230723 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433913 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433913 / 250000) = 1/(250000 / 433913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (110276627 / 200000000) (17230723 / 31250000) (Real.log (433913 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (433913 / 250000) = -Real.log (250000 / 433913) := by
    rw [show ((433913 / 250000) : ℝ) = ((250000 / 433913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1330488861 / 1000000000) ≤ -Real.log (66087 / 250000) ∧
    -Real.log (66087 / 250000) ≤ (1330488863 / 1000000000) := by
  have h := checkLog_sound (w := (58913 / 191087)) (n := 12)
    (lo := (637341681 / 1000000000)) (hi := (318670841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 66087) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 66087) = 1/(66087 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1330488863 / 1000000000) (-1330488861 / 1000000000) (Real.log (66087 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (430542547 / 200000000) ≤ -Real.log (500000000000 / 4304089240761) ∧
    -Real.log (500000000000 / 4304089240761) ≤ (2152712739 / 1000000000) := by
  have h := checkLog_sound (w := (304089240761 / 8304089240761)) (n := 12)
    (lo := (14654239 / 200000000)) (hi := (18317799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4304089240761 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4304089240761 / 4000000000000) = 1/(500000000000 / 4304089240761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (430542547 / 200000000) (2152712739 / 1000000000) (Real.log (4304089240761 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4304089240761 / 500000000000) = -Real.log (500000000000 / 4304089240761) := by
    rw [show ((4304089240761 / 500000000000) : ℝ) = ((500000000000 / 4304089240761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2166959749 / 1000000000) ≤ -Real.log (50000000000 / 436584855533) ∧
    -Real.log (50000000000 / 436584855533) ≤ (2166959753 / 1000000000) := by
  have h := checkLog_sound (w := (36584855533 / 836584855533)) (n := 12)
    (lo := (87518209 / 1000000000)) (hi := (8751821 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((436584855533 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(436584855533 / 400000000000) = 1/(50000000000 / 436584855533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2166959749 / 1000000000) (2166959753 / 1000000000) (Real.log (436584855533 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (436584855533 / 50000000000) = -Real.log (50000000000 / 436584855533) := by
    rw [show ((436584855533 / 50000000000) : ℝ) = ((50000000000 / 436584855533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (369959797 / 200000000) ≤ -Real.log (31250000000 / 198704413837) ∧
    -Real.log (31250000000 / 198704413837) ≤ (462449747 / 250000000) := by
  have h := checkLog_sound (w := (73704413837 / 323704413837)) (n := 12)
    (lo := (3708037 / 8000000)) (hi := (231752313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198704413837 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(198704413837 / 125000000000) = 1/(31250000000 / 198704413837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (369959797 / 200000000) (462449747 / 250000000) (Real.log (198704413837 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (198704413837 / 31250000000) = -Real.log (31250000000 / 198704413837) := by
    rw [show ((198704413837 / 31250000000) : ℝ) = ((31250000000 / 198704413837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (470467999 / 250000000) ≤ -Real.log (250000000000 / 1641446124049) ∧
    -Real.log (250000000000 / 1641446124049) ≤ (1881871999 / 1000000000) := by
  have h := checkLog_sound (w := (641446124049 / 2641446124049)) (n := 12)
    (lo := (123894409 / 250000000)) (hi := (495577637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641446124049 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1641446124049 / 1000000000000) = 1/(250000000000 / 1641446124049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (470467999 / 250000000) (1881871999 / 1000000000) (Real.log (1641446124049 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1641446124049 / 250000000000) = -Real.log (250000000000 / 1641446124049) := by
    rw [show ((1641446124049 / 250000000000) : ℝ) = ((250000000000 / 1641446124049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0226

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0227Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0227
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

theorem reflection_log_1_neg : (477398097 / 1000000000) ≤ -Real.log (1600 / 2579) ∧
    -Real.log (1600 / 2579) ≤ (238699049 / 500000000) := by
  have h := checkLog_sound (w := (979 / 4179)) (n := 12)
    (lo := (477398097 / 1000000000)) (hi := (238699049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2579 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2579 / 1600) = 1/(1600 / 2579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (477398097 / 1000000000) (238699049 / 500000000) (Real.log (2579 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2579 / 1600) = -Real.log (1600 / 2579) := by
    rw [show ((2579 / 1600) : ℝ) = ((1600 / 2579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (37857113 / 40000000) ≤ -Real.log (621 / 1600) ∧
    -Real.log (621 / 1600) ≤ (946427827 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 1421)) (n := 12)
    (lo := (50656129 / 200000000)) (hi := (126640323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 621) = 1/(621 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-946427827 / 1000000000) (-37857113 / 40000000) (Real.log (621 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (470003629 / 1000000000) ≤ -Real.log (5 / 8) ∧
    -Real.log (5 / 8) ≤ (47000363 / 100000000) := by
  have h := checkLog_sound (w := (3 / 13)) (n := 12)
    (lo := (470003629 / 1000000000)) (hi := (47000363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8 / 5) = 1/(5 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (470003629 / 1000000000) (47000363 / 100000000) (Real.log (8 / 5)) := by
  have h := reflection_log_3_neg
  have he : Real.log (8 / 5) = -Real.log (5 / 8) := by
    rw [show ((8 / 5) : ℝ) = ((5 / 8) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (916290731 / 1000000000) ≤ -Real.log (2 / 5) ∧
    -Real.log (2 / 5) ≤ (916290733 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5 / 4) = 1/(2 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-916290733 / 1000000000) (-916290731 / 1000000000) (Real.log (2 / 5)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (100959957 / 500000000) ≤ -Real.log (800 / 979) ∧
    -Real.log (800 / 979) ≤ (40383983 / 200000000) := by
  have h := checkLog_sound (w := (179 / 1779)) (n := 12)
    (lo := (100959957 / 500000000)) (hi := (40383983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979 / 800) = 1/(800 / 979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (100959957 / 500000000) (40383983 / 200000000) (Real.log (979 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (979 / 800) = -Real.log (800 / 979) := by
    rw [show ((979 / 800) : ℝ) = ((800 / 979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (50656129 / 200000000) ≤ -Real.log (621 / 800) ∧
    -Real.log (621 / 800) ≤ (126640323 / 500000000) := by
  have h := checkLog_sound (w := (179 / 1421)) (n := 12)
    (lo := (50656129 / 200000000)) (hi := (126640323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 621) = 1/(621 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-126640323 / 500000000) (-50656129 / 200000000) (Real.log (621 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (45580389 / 250000000) ≤ -Real.log (5 / 6) ∧
    -Real.log (5 / 6) ≤ (182321557 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6 / 5) = 1/(5 / 6) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (45580389 / 250000000) (182321557 / 1000000000) (Real.log (6 / 5)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6 / 5) = -Real.log (5 / 6) := by
    rw [show ((6 / 5) : ℝ) = ((5 / 6) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
    -Real.log (4 / 5) ≤ (1743309 / 7812500) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 4) = 1/(4 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1743309 / 7812500) (-223143551 / 1000000000) (Real.log (4 / 5)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (581916133 / 1000000000) ≤ -Real.log (125000 / 223683) ∧
    -Real.log (125000 / 223683) ≤ (290958067 / 500000000) := by
  have h := checkLog_sound (w := (98683 / 348683)) (n := 12)
    (lo := (581916133 / 1000000000)) (hi := (290958067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223683 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223683 / 125000) = 1/(125000 / 223683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (581916133 / 1000000000) (290958067 / 500000000) (Real.log (223683 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (223683 / 125000) = -Real.log (125000 / 223683) := by
    rw [show ((223683 / 125000) : ℝ) = ((125000 / 223683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1558098617 / 1000000000) ≤ -Real.log (26317 / 125000) ∧
    -Real.log (26317 / 125000) ≤ (77904931 / 50000000) := by
  have h := checkLog_sound (w := (4933 / 57567)) (n := 12)
    (lo := (171804257 / 1000000000)) (hi := (85902129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26317) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 26317) = 1/(26317 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-77904931 / 50000000) (-1558098617 / 1000000000) (Real.log (26317 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (116649163 / 200000000) ≤ -Real.log (200000 / 358369) ∧
    -Real.log (200000 / 358369) ≤ (72905727 / 125000000) := by
  have h := checkLog_sound (w := (158369 / 558369)) (n := 12)
    (lo := (116649163 / 200000000)) (hi := (72905727 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358369 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358369 / 200000) = 1/(200000 / 358369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (116649163 / 200000000) (72905727 / 125000000) (Real.log (358369 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (358369 / 200000) = -Real.log (200000 / 358369) := by
    rw [show ((358369 / 200000) : ℝ) = ((200000 / 358369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1569472283 / 1000000000) ≤ -Real.log (41631 / 200000) ∧
    -Real.log (41631 / 200000) ≤ (784736143 / 500000000) := by
  have h := checkLog_sound (w := (8369 / 91631)) (n := 12)
    (lo := (183177923 / 1000000000)) (hi := (45794481 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41631) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 41631) = 1/(41631 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-784736143 / 500000000) (-1569472283 / 1000000000) (Real.log (41631 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (33923859 / 62500000) ≤ -Real.log (1000000 / 1720787) ∧
    -Real.log (1000000 / 1720787) ≤ (108556349 / 200000000) := by
  have h := checkLog_sound (w := (720787 / 2720787)) (n := 12)
    (lo := (33923859 / 62500000)) (hi := (108556349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1720787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1720787 / 1000000) = 1/(1000000 / 1720787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (33923859 / 62500000) (108556349 / 200000000) (Real.log (1720787 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1720787 / 1000000) = -Real.log (1000000 / 1720787) := by
    rw [show ((1720787 / 1000000) : ℝ) = ((1000000 / 1720787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1275780347 / 1000000000) ≤ -Real.log (279213 / 1000000) ∧
    -Real.log (279213 / 1000000) ≤ (1275780349 / 1000000000) := by
  have h := checkLog_sound (w := (220787 / 779213)) (n := 12)
    (lo := (582633167 / 1000000000)) (hi := (36414573 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 279213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 279213) = 1/(279213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1275780349 / 1000000000) (-1275780347 / 1000000000) (Real.log (279213 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (547085033 / 1000000000) ≤ -Real.log (62500 / 108013) ∧
    -Real.log (62500 / 108013) ≤ (273542517 / 500000000) := by
  have h := checkLog_sound (w := (45513 / 170513)) (n := 12)
    (lo := (547085033 / 1000000000)) (hi := (273542517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108013 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108013 / 62500) = 1/(62500 / 108013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (547085033 / 1000000000) (273542517 / 500000000) (Real.log (108013 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (108013 / 62500) = -Real.log (62500 / 108013) := by
    rw [show ((108013 / 62500) : ℝ) = ((62500 / 108013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (130271821 / 100000000) ≤ -Real.log (16987 / 62500) ∧
    -Real.log (16987 / 62500) ≤ (325679553 / 250000000) := by
  have h := checkLog_sound (w := (14263 / 48237)) (n := 12)
    (lo := (60957103 / 100000000)) (hi := (609571031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 16987) = 1/(16987 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-325679553 / 250000000) (-130271821 / 100000000) (Real.log (16987 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2140014751 / 1000000000) ≤ -Real.log (10000000000 / 84995630201) ∧
    -Real.log (10000000000 / 84995630201) ≤ (428002951 / 200000000) := by
  have h := checkLog_sound (w := (4995630201 / 164995630201)) (n := 12)
    (lo := (60573211 / 1000000000)) (hi := (15143303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84995630201 / 80000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(84995630201 / 80000000000) = 1/(10000000000 / 84995630201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2140014751 / 1000000000) (428002951 / 200000000) (Real.log (84995630201 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (84995630201 / 10000000000) = -Real.log (10000000000 / 84995630201) := by
    rw [show ((84995630201 / 10000000000) : ℝ) = ((10000000000 / 84995630201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1076359049 / 500000000) ≤ -Real.log (500000000000 / 4304112320147) ∧
    -Real.log (500000000000 / 4304112320147) ≤ (1076359051 / 500000000) := by
  have h := checkLog_sound (w := (304112320147 / 8304112320147)) (n := 12)
    (lo := (36638279 / 500000000)) (hi := (73276559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4304112320147 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4304112320147 / 4000000000000) = 1/(500000000000 / 4304112320147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1076359049 / 500000000) (1076359051 / 500000000) (Real.log (4304112320147 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4304112320147 / 500000000000) = -Real.log (500000000000 / 4304112320147) := by
    rw [show ((4304112320147 / 500000000000) : ℝ) = ((500000000000 / 4304112320147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (181856209 / 100000000) ≤ -Real.log (500000000000 / 3081495130957) ∧
    -Real.log (500000000000 / 3081495130957) ≤ (1818562093 / 1000000000) := by
  have h := checkLog_sound (w := (1081495130957 / 5081495130957)) (n := 12)
    (lo := (43226773 / 100000000)) (hi := (432267731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3081495130957 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3081495130957 / 2000000000000) = 1/(500000000000 / 3081495130957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (181856209 / 100000000) (1818562093 / 1000000000) (Real.log (3081495130957 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3081495130957 / 500000000000) = -Real.log (500000000000 / 3081495130957) := by
    rw [show ((3081495130957 / 500000000000) : ℝ) = ((500000000000 / 3081495130957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1849803243 / 1000000000) ≤ -Real.log (20000000000 / 127171366339) ∧
    -Real.log (20000000000 / 127171366339) ≤ (924901623 / 500000000) := by
  have h := checkLog_sound (w := (47171366339 / 207171366339)) (n := 12)
    (lo := (463508883 / 1000000000)) (hi := (115877221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127171366339 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(127171366339 / 80000000000) = 1/(20000000000 / 127171366339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1849803243 / 1000000000) (924901623 / 500000000) (Real.log (127171366339 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (127171366339 / 20000000000) = -Real.log (20000000000 / 127171366339) := by
    rw [show ((127171366339 / 20000000000) : ℝ) = ((20000000000 / 127171366339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0227

end


