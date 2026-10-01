-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0139Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0139Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:52:55.214374+00:00
-- url     : https://prove2.me/theorems/24f2c0c3-ea6b-422e-af9c-c27803285e0b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0139Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0140Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0139Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0140Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0141Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0142Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0143Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0144Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0139Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0140Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0141Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0142Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0143Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0144Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0139Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0140Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0141Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0142Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0143Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0144Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0139Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0140Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0141Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0142Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0143Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0144Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0139Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0139
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

theorem reflection_log_1_neg : (658814501 / 1000000000) ≤ -Real.log (400 / 773) ∧
    -Real.log (400 / 773) ≤ (329407251 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1173)) (n := 12)
    (lo := (658814501 / 1000000000)) (hi := (329407251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773 / 400) = 1/(400 / 773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (658814501 / 1000000000) (329407251 / 500000000) (Real.log (773 / 400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (773 / 400) = -Real.log (400 / 773) := by
    rw [show ((773 / 400) : ℝ) = ((400 / 773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2695627679 / 1000000000) ≤ -Real.log (27 / 400) ∧
    -Real.log (27 / 400) ≤ (2695627683 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 77)) (n := 12)
    (lo := (616186139 / 1000000000)) (hi := (30809307 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(50 / 27) = 1/(27 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2695627683 / 1000000000) (-2695627679 / 1000000000) (Real.log (27 / 400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (164607593 / 250000000) ≤ -Real.log (25600 / 49453) ∧
    -Real.log (25600 / 49453) ≤ (658430373 / 1000000000) := by
  have h := checkLog_sound (w := (23853 / 75053)) (n := 12)
    (lo := (164607593 / 250000000)) (hi := (658430373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49453 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49453 / 25600) = 1/(25600 / 49453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (164607593 / 250000000) (658430373 / 1000000000) (Real.log (49453 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49453 / 25600) = -Real.log (25600 / 49453) := by
    rw [show ((49453 / 25600) : ℝ) = ((25600 / 49453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1342346159 / 500000000) ≤ -Real.log (1747 / 25600) ∧
    -Real.log (1747 / 25600) ≤ (1342346161 / 500000000) := by
  have h := checkLog_sound (w := (1453 / 4947)) (n := 12)
    (lo := (302625389 / 500000000)) (hi := (605250779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1747) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1747) = 1/(1747 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1342346161 / 500000000) (-1342346159 / 500000000) (Real.log (1747 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (623261053 / 1000000000) ≤ -Real.log (200 / 373) ∧
    -Real.log (200 / 373) ≤ (311630527 / 500000000) := by
  have h := checkLog_sound (w := (173 / 573)) (n := 12)
    (lo := (623261053 / 1000000000)) (hi := (311630527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373 / 200) = 1/(200 / 373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (623261053 / 1000000000) (311630527 / 500000000) (Real.log (373 / 200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (373 / 200) = -Real.log (200 / 373) := by
    rw [show ((373 / 200) : ℝ) = ((200 / 373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2002480499 / 1000000000) ≤ -Real.log (27 / 200) ∧
    -Real.log (27 / 200) ≤ (1001240251 / 500000000) := by
  have h := checkLog_sound (w := (23 / 77)) (n := 12)
    (lo := (616186139 / 1000000000)) (hi := (30809307 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50 / 27) = 1/(27 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1001240251 / 500000000) (-2002480499 / 1000000000) (Real.log (27 / 200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (77808103 / 125000000) ≤ -Real.log (12800 / 23853) ∧
    -Real.log (12800 / 23853) ≤ (24898593 / 40000000) := by
  have h := checkLog_sound (w := (11053 / 36653)) (n := 12)
    (lo := (77808103 / 125000000)) (hi := (24898593 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23853 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23853 / 12800) = 1/(12800 / 23853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (77808103 / 125000000) (24898593 / 40000000) (Real.log (23853 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23853 / 12800) = -Real.log (12800 / 23853) := by
    rw [show ((23853 / 12800) : ℝ) = ((12800 / 23853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (995772569 / 500000000) ≤ -Real.log (1747 / 12800) ∧
    -Real.log (1747 / 12800) ≤ (1991545141 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 4947)) (n := 12)
    (lo := (302625389 / 500000000)) (hi := (605250779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1747) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1747) = 1/(1747 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1991545141 / 1000000000) (-995772569 / 500000000) (Real.log (1747 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (332833261 / 500000000) ≤ -Real.log (1000000 / 1945787) ∧
    -Real.log (1000000 / 1945787) ≤ (665666523 / 1000000000) := by
  have h := checkLog_sound (w := (945787 / 2945787)) (n := 12)
    (lo := (332833261 / 500000000)) (hi := (665666523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1945787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1945787 / 1000000) = 1/(1000000 / 1945787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (332833261 / 500000000) (665666523 / 1000000000) (Real.log (1945787 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1945787 / 1000000) = -Real.log (1000000 / 1945787) := by
    rw [show ((1945787 / 1000000) : ℝ) = ((1000000 / 1945787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182177159 / 62500000) ≤ -Real.log (54213 / 1000000) ∧
    -Real.log (54213 / 1000000) ≤ (2914834549 / 1000000000) := by
  have h := checkLog_sound (w := (8287 / 116713)) (n := 12)
    (lo := (2222591 / 15625000)) (hi := (5689833 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54213) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 54213) = 1/(54213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2914834549 / 1000000000) (-182177159 / 62500000) (Real.log (54213 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (665946061 / 1000000000) ≤ -Real.log (1000000 / 1946331) ∧
    -Real.log (1000000 / 1946331) ≤ (332973031 / 500000000) := by
  have h := checkLog_sound (w := (946331 / 2946331)) (n := 12)
    (lo := (665946061 / 1000000000)) (hi := (332973031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1946331 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1946331 / 1000000) = 1/(1000000 / 1946331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (665946061 / 1000000000) (332973031 / 500000000) (Real.log (1946331 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1946331 / 1000000) = -Real.log (1000000 / 1946331) := by
    rw [show ((1946331 / 1000000) : ℝ) = ((1000000 / 1946331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2924919723 / 1000000000) ≤ -Real.log (53669 / 1000000) ∧
    -Real.log (53669 / 1000000) ≤ (182807483 / 62500000) := by
  have h := checkLog_sound (w := (8831 / 116169)) (n := 12)
    (lo := (152331003 / 1000000000)) (hi := (38082751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53669) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 53669) = 1/(53669 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-182807483 / 62500000) (-2924919723 / 1000000000) (Real.log (53669 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (133032857 / 200000000) ≤ -Real.log (100000 / 194481) ∧
    -Real.log (100000 / 194481) ≤ (332582143 / 500000000) := by
  have h := checkLog_sound (w := (94481 / 294481)) (n := 12)
    (lo := (133032857 / 200000000)) (hi := (332582143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194481 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194481 / 100000) = 1/(100000 / 194481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (133032857 / 200000000) (332582143 / 500000000) (Real.log (194481 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (194481 / 100000) = -Real.log (100000 / 194481) := by
    rw [show ((194481 / 100000) : ℝ) = ((100000 / 194481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2896973499 / 1000000000) ≤ -Real.log (5519 / 100000) ∧
    -Real.log (5519 / 100000) ≤ (45265211 / 15625000) := by
  have h := checkLog_sound (w := (731 / 11769)) (n := 12)
    (lo := (124384779 / 1000000000)) (hi := (6219239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5519) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 5519) = 1/(5519 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-45265211 / 15625000) (-2896973499 / 1000000000) (Real.log (5519 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (332728151 / 500000000) ≤ -Real.log (500000 / 972689) ∧
    -Real.log (500000 / 972689) ≤ (665456303 / 1000000000) := by
  have h := checkLog_sound (w := (472689 / 1472689)) (n := 12)
    (lo := (332728151 / 500000000)) (hi := (665456303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972689 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972689 / 500000) = 1/(500000 / 972689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (332728151 / 500000000) (665456303 / 1000000000) (Real.log (972689 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (972689 / 500000) = -Real.log (500000 / 972689) := by
    rw [show ((972689 / 500000) : ℝ) = ((500000 / 972689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (181707409 / 62500000) ≤ -Real.log (27311 / 500000) ∧
    -Real.log (27311 / 500000) ≤ (2907318549 / 1000000000) := by
  have h := checkLog_sound (w := (3939 / 58561)) (n := 12)
    (lo := (4210307 / 31250000)) (hi := (5389193 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27311) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 27311) = 1/(27311 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2907318549 / 1000000000) (-181707409 / 62500000) (Real.log (27311 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1790250533 / 500000000) ≤ -Real.log (62500000000 / 2243220030251) ∧
    -Real.log (62500000000 / 2243220030251) ≤ (223781317 / 62500000) := by
  have h := checkLog_sound (w := (243220030251 / 4243220030251)) (n := 12)
    (lo := (57382583 / 500000000)) (hi := (114765167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2243220030251 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2243220030251 / 2000000000000) = 1/(62500000000 / 2243220030251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1790250533 / 500000000) (223781317 / 62500000) (Real.log (2243220030251 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2243220030251 / 62500000000) = -Real.log (62500000000 / 2243220030251) := by
    rw [show ((2243220030251 / 62500000000) : ℝ) = ((62500000000 / 2243220030251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (448858223 / 125000000) ≤ -Real.log (100000000000 / 3626546050793) ∧
    -Real.log (100000000000 / 3626546050793) ≤ (359086579 / 100000000) := by
  have h := checkLog_sound (w := (426546050793 / 6826546050793)) (n := 12)
    (lo := (31282471 / 250000000)) (hi := (25025977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3626546050793 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3626546050793 / 3200000000000) = 1/(100000000000 / 3626546050793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (448858223 / 125000000) (359086579 / 100000000) (Real.log (3626546050793 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3626546050793 / 100000000000) = -Real.log (100000000000 / 3626546050793) := by
    rw [show ((3626546050793 / 100000000000) : ℝ) = ((100000000000 / 3626546050793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (445267223 / 125000000) ≤ -Real.log (500000000000 / 17619224497191) ∧
    -Real.log (500000000000 / 17619224497191) ≤ (356213779 / 100000000) := by
  have h := checkLog_sound (w := (1619224497191 / 33619224497191)) (n := 12)
    (lo := (24100471 / 250000000)) (hi := (19280377 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17619224497191 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17619224497191 / 16000000000000) = 1/(500000000000 / 17619224497191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (445267223 / 125000000) (356213779 / 100000000) (Real.log (17619224497191 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (17619224497191 / 500000000000) = -Real.log (500000000000 / 17619224497191) := by
    rw [show ((17619224497191 / 500000000000) : ℝ) = ((500000000000 / 17619224497191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1786387423 / 500000000) ≤ -Real.log (62500000000 / 2225955201201) ∧
    -Real.log (62500000000 / 2225955201201) ≤ (893193713 / 250000000) := by
  have h := checkLog_sound (w := (225955201201 / 4225955201201)) (n := 12)
    (lo := (53519473 / 500000000)) (hi := (107038947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2225955201201 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2225955201201 / 2000000000000) = 1/(62500000000 / 2225955201201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1786387423 / 500000000) (893193713 / 250000000) (Real.log (2225955201201 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2225955201201 / 62500000000) = -Real.log (62500000000 / 2225955201201) := by
    rw [show ((2225955201201 / 62500000000) : ℝ) = ((62500000000 / 2225955201201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0139

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0140Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0140
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

theorem reflection_log_1_neg : (164607593 / 250000000) ≤ -Real.log (25600 / 49453) ∧
    -Real.log (25600 / 49453) ≤ (658430373 / 1000000000) := by
  have h := checkLog_sound (w := (23853 / 75053)) (n := 12)
    (lo := (164607593 / 250000000)) (hi := (658430373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49453 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49453 / 25600) = 1/(25600 / 49453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (164607593 / 250000000) (658430373 / 1000000000) (Real.log (49453 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49453 / 25600) = -Real.log (25600 / 49453) := by
    rw [show ((49453 / 25600) : ℝ) = ((25600 / 49453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1342346159 / 500000000) ≤ -Real.log (1747 / 25600) ∧
    -Real.log (1747 / 25600) ≤ (1342346161 / 500000000) := by
  have h := checkLog_sound (w := (1453 / 4947)) (n := 12)
    (lo := (302625389 / 500000000)) (hi := (605250779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1747) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1747) = 1/(1747 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1342346161 / 500000000) (-1342346159 / 500000000) (Real.log (1747 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (131609219 / 200000000) ≤ -Real.log (12800 / 24717) ∧
    -Real.log (12800 / 24717) ≤ (41127881 / 62500000) := by
  have h := checkLog_sound (w := (11917 / 37517)) (n := 12)
    (lo := (131609219 / 200000000)) (hi := (41127881 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24717 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24717 / 12800) = 1/(12800 / 24717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (131609219 / 200000000) (41127881 / 62500000) (Real.log (24717 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24717 / 12800) = -Real.log (12800 / 24717) := by
    rw [show ((24717 / 12800) : ℝ) = ((12800 / 24717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2673875247 / 1000000000) ≤ -Real.log (883 / 12800) ∧
    -Real.log (883 / 12800) ≤ (2673875251 / 1000000000) := by
  have h := checkLog_sound (w := (717 / 2483)) (n := 12)
    (lo := (594433707 / 1000000000)) (hi := (148608427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 883) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 883) = 1/(883 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2673875251 / 1000000000) (-2673875247 / 1000000000) (Real.log (883 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (77808103 / 125000000) ≤ -Real.log (12800 / 23853) ∧
    -Real.log (12800 / 23853) ≤ (24898593 / 40000000) := by
  have h := checkLog_sound (w := (11053 / 36653)) (n := 12)
    (lo := (77808103 / 125000000)) (hi := (24898593 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23853 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23853 / 12800) = 1/(12800 / 23853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (77808103 / 125000000) (24898593 / 40000000) (Real.log (23853 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23853 / 12800) = -Real.log (12800 / 23853) := by
    rw [show ((23853 / 12800) : ℝ) = ((12800 / 23853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (995772569 / 500000000) ≤ -Real.log (1747 / 12800) ∧
    -Real.log (1747 / 12800) ≤ (1991545141 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 4947)) (n := 12)
    (lo := (302625389 / 500000000)) (hi := (605250779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1747) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1747) = 1/(1747 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1991545141 / 1000000000) (-995772569 / 500000000) (Real.log (1747 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (621667961 / 1000000000) ≤ -Real.log (6400 / 11917) ∧
    -Real.log (6400 / 11917) ≤ (310833981 / 500000000) := by
  have h := checkLog_sound (w := (5517 / 18317)) (n := 12)
    (lo := (621667961 / 1000000000)) (hi := (310833981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11917 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11917 / 6400) = 1/(6400 / 11917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (621667961 / 1000000000) (310833981 / 500000000) (Real.log (11917 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11917 / 6400) = -Real.log (6400 / 11917) := by
    rw [show ((11917 / 6400) : ℝ) = ((6400 / 11917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1980728067 / 1000000000) ≤ -Real.log (883 / 6400) ∧
    -Real.log (883 / 6400) ≤ (198072807 / 100000000) := by
  have h := checkLog_sound (w := (717 / 2483)) (n := 12)
    (lo := (594433707 / 1000000000)) (hi := (148608427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 883) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 883) = 1/(883 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-198072807 / 100000000) (-1980728067 / 1000000000) (Real.log (883 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (665388447 / 1000000000) ≤ -Real.log (500000 / 972623) ∧
    -Real.log (500000 / 972623) ≤ (20793389 / 31250000) := by
  have h := checkLog_sound (w := (472623 / 1472623)) (n := 12)
    (lo := (665388447 / 1000000000)) (hi := (20793389 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972623 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972623 / 500000) = 1/(500000 / 972623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (665388447 / 1000000000) (20793389 / 31250000) (Real.log (972623 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (972623 / 500000) = -Real.log (500000 / 972623) := by
    rw [show ((972623 / 500000) : ℝ) = ((500000 / 972623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2904904851 / 1000000000) ≤ -Real.log (27377 / 500000) ∧
    -Real.log (27377 / 500000) ≤ (363113107 / 125000000) := by
  have h := checkLog_sound (w := (3873 / 58627)) (n := 12)
    (lo := (132316131 / 1000000000)) (hi := (33079033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27377) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 27377) = 1/(27377 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-363113107 / 125000000) (-2904904851 / 1000000000) (Real.log (27377 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (166416759 / 250000000) ≤ -Real.log (250000 / 486447) ∧
    -Real.log (250000 / 486447) ≤ (665667037 / 1000000000) := by
  have h := checkLog_sound (w := (236447 / 736447)) (n := 12)
    (lo := (166416759 / 250000000)) (hi := (665667037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486447 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486447 / 250000) = 1/(250000 / 486447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (166416759 / 250000000) (665667037 / 1000000000) (Real.log (486447 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (486447 / 250000) = -Real.log (250000 / 486447) := by
    rw [show ((486447 / 250000) : ℝ) = ((250000 / 486447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (291485299 / 100000000) ≤ -Real.log (13553 / 250000) ∧
    -Real.log (13553 / 250000) ≤ (582970599 / 200000000) := by
  have h := checkLog_sound (w := (1036 / 14589)) (n := 12)
    (lo := (14226427 / 100000000)) (hi := (142264271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13553) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 13553) = 1/(13553 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-582970599 / 200000000) (-291485299 / 100000000) (Real.log (13553 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (166218303 / 250000000) ≤ -Real.log (250000 / 486061) ∧
    -Real.log (250000 / 486061) ≤ (664873213 / 1000000000) := by
  have h := checkLog_sound (w := (236061 / 736061)) (n := 12)
    (lo := (166218303 / 250000000)) (hi := (664873213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486061 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486061 / 250000) = 1/(250000 / 486061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (166218303 / 250000000) (664873213 / 1000000000) (Real.log (486061 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (486061 / 250000) = -Real.log (250000 / 486061) := by
    rw [show ((486061 / 250000) : ℝ) = ((250000 / 486061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (360846281 / 125000000) ≤ -Real.log (13939 / 250000) ∧
    -Real.log (13939 / 250000) ≤ (2886770253 / 1000000000) := by
  have h := checkLog_sound (w := (843 / 14782)) (n := 12)
    (lo := (14272691 / 125000000)) (hi := (114181529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13939) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 13939) = 1/(13939 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2886770253 / 1000000000) (-360846281 / 125000000) (Real.log (13939 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (51966 / 78125) ≤ -Real.log (1000000 / 1944811) ∧
    -Real.log (1000000 / 1944811) ≤ (665164801 / 1000000000) := by
  have h := checkLog_sound (w := (944811 / 2944811)) (n := 12)
    (lo := (51966 / 78125)) (hi := (665164801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1944811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1944811 / 1000000) = 1/(1000000 / 1944811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (51966 / 78125) (665164801 / 1000000000) (Real.log (1944811 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1944811 / 1000000) = -Real.log (1000000 / 1944811) := by
    rw [show ((1944811 / 1000000) : ℝ) = ((1000000 / 1944811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1448495809 / 500000000) ≤ -Real.log (55189 / 1000000) ∧
    -Real.log (55189 / 1000000) ≤ (2896991623 / 1000000000) := by
  have h := checkLog_sound (w := (7311 / 117689)) (n := 12)
    (lo := (62201449 / 500000000)) (hi := (124402899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55189) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 55189) = 1/(55189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2896991623 / 1000000000) (-1448495809 / 500000000) (Real.log (55189 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1785146649 / 500000000) ≤ -Real.log (100000000000 / 3552701172517) ∧
    -Real.log (100000000000 / 3552701172517) ≤ (446286663 / 125000000) := by
  have h := checkLog_sound (w := (352701172517 / 6752701172517)) (n := 12)
    (lo := (52278699 / 500000000)) (hi := (104557399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3552701172517 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3552701172517 / 3200000000000) = 1/(100000000000 / 3552701172517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1785146649 / 500000000) (446286663 / 125000000) (Real.log (3552701172517 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3552701172517 / 100000000000) = -Real.log (100000000000 / 3552701172517) := by
    rw [show ((3552701172517 / 100000000000) : ℝ) = ((100000000000 / 3552701172517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1790260013 / 500000000) ≤ -Real.log (125000000000 / 4486525123589) ∧
    -Real.log (125000000000 / 4486525123589) ≤ (111891251 / 31250000) := by
  have h := checkLog_sound (w := (486525123589 / 8486525123589)) (n := 12)
    (lo := (57392063 / 500000000)) (hi := (114784127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4486525123589 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4486525123589 / 4000000000000) = 1/(125000000000 / 4486525123589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1790260013 / 500000000) (111891251 / 31250000) (Real.log (4486525123589 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4486525123589 / 125000000000) = -Real.log (125000000000 / 4486525123589) := by
    rw [show ((4486525123589 / 125000000000) : ℝ) = ((125000000000 / 4486525123589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (177582173 / 50000000) ≤ -Real.log (125000000000 / 4358822368893) ∧
    -Real.log (125000000000 / 4358822368893) ≤ (1775821733 / 500000000) := by
  have h := checkLog_sound (w := (358822368893 / 8358822368893)) (n := 12)
    (lo := (2147689 / 25000000)) (hi := (85907561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4358822368893 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4358822368893 / 4000000000000) = 1/(125000000000 / 4358822368893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (177582173 / 50000000) (1775821733 / 500000000) (Real.log (4358822368893 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4358822368893 / 125000000000) = -Real.log (125000000000 / 4358822368893) := by
    rw [show ((4358822368893 / 125000000000) : ℝ) = ((125000000000 / 4358822368893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1781078209 / 500000000) ≤ -Real.log (500000000000 / 17619552809437) ∧
    -Real.log (500000000000 / 17619552809437) ≤ (445269553 / 125000000) := by
  have h := checkLog_sound (w := (1619552809437 / 33619552809437)) (n := 12)
    (lo := (48210259 / 500000000)) (hi := (96420519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17619552809437 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17619552809437 / 16000000000000) = 1/(500000000000 / 17619552809437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1781078209 / 500000000) (445269553 / 125000000) (Real.log (17619552809437 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17619552809437 / 500000000000) = -Real.log (500000000000 / 17619552809437) := by
    rw [show ((17619552809437 / 500000000000) : ℝ) = ((500000000000 / 17619552809437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0140

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0141Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0141
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

theorem reflection_log_1_neg : (131609219 / 200000000) ≤ -Real.log (12800 / 24717) ∧
    -Real.log (12800 / 24717) ≤ (41127881 / 62500000) := by
  have h := checkLog_sound (w := (11917 / 37517)) (n := 12)
    (lo := (131609219 / 200000000)) (hi := (41127881 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24717 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24717 / 12800) = 1/(12800 / 24717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (131609219 / 200000000) (41127881 / 62500000) (Real.log (24717 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24717 / 12800) = -Real.log (12800 / 24717) := by
    rw [show ((24717 / 12800) : ℝ) = ((12800 / 24717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2673875247 / 1000000000) ≤ -Real.log (883 / 12800) ∧
    -Real.log (883 / 12800) ≤ (2673875251 / 1000000000) := by
  have h := checkLog_sound (w := (717 / 2483)) (n := 12)
    (lo := (594433707 / 1000000000)) (hi := (148608427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 883) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 883) = 1/(883 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2673875251 / 1000000000) (-2673875247 / 1000000000) (Real.log (883 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65766167 / 100000000) ≤ -Real.log (5120 / 9883) ∧
    -Real.log (5120 / 9883) ≤ (657661671 / 1000000000) := by
  have h := checkLog_sound (w := (4763 / 15003)) (n := 12)
    (lo := (65766167 / 100000000)) (hi := (657661671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9883 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9883 / 5120) = 1/(5120 / 9883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65766167 / 100000000) (657661671 / 1000000000) (Real.log (9883 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (9883 / 5120) = -Real.log (5120 / 9883) := by
    rw [show ((9883 / 5120) : ℝ) = ((5120 / 9883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1331586967 / 500000000) ≤ -Real.log (357 / 5120) ∧
    -Real.log (357 / 5120) ≤ (1331586969 / 500000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 357) = 1/(357 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1331586969 / 500000000) (-1331586967 / 500000000) (Real.log (357 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (621667961 / 1000000000) ≤ -Real.log (6400 / 11917) ∧
    -Real.log (6400 / 11917) ≤ (310833981 / 500000000) := by
  have h := checkLog_sound (w := (5517 / 18317)) (n := 12)
    (lo := (621667961 / 1000000000)) (hi := (310833981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11917 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11917 / 6400) = 1/(6400 / 11917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (621667961 / 1000000000) (310833981 / 500000000) (Real.log (11917 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11917 / 6400) = -Real.log (6400 / 11917) := by
    rw [show ((11917 / 6400) : ℝ) = ((6400 / 11917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1980728067 / 1000000000) ≤ -Real.log (883 / 6400) ∧
    -Real.log (883 / 6400) ≤ (198072807 / 100000000) := by
  have h := checkLog_sound (w := (717 / 2483)) (n := 12)
    (lo := (594433707 / 1000000000)) (hi := (148608427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 883) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 883) = 1/(883 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-198072807 / 100000000) (-1980728067 / 1000000000) (Real.log (883 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (620870463 / 1000000000) ≤ -Real.log (2560 / 4763) ∧
    -Real.log (2560 / 4763) ≤ (9701101 / 15625000) := by
  have h := checkLog_sound (w := (2203 / 7323)) (n := 12)
    (lo := (620870463 / 1000000000)) (hi := (9701101 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4763 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4763 / 2560) = 1/(2560 / 4763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (620870463 / 1000000000) (9701101 / 15625000) (Real.log (4763 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4763 / 2560) = -Real.log (2560 / 4763) := by
    rw [show ((4763 / 2560) : ℝ) = ((2560 / 4763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (985013377 / 500000000) ≤ -Real.log (357 / 2560) ∧
    -Real.log (357 / 2560) ≤ (1970026757 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(640 / 357) = 1/(357 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1970026757 / 1000000000) (-985013377 / 500000000) (Real.log (357 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (332555147 / 500000000) ≤ -Real.log (200000 / 388941) ∧
    -Real.log (200000 / 388941) ≤ (133022059 / 200000000) := by
  have h := checkLog_sound (w := (188941 / 588941)) (n := 12)
    (lo := (332555147 / 500000000)) (hi := (133022059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388941 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388941 / 200000) = 1/(200000 / 388941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (332555147 / 500000000) (133022059 / 200000000) (Real.log (388941 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (388941 / 200000) = -Real.log (200000 / 388941) := by
    rw [show ((388941 / 200000) : ℝ) = ((200000 / 388941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (723768197 / 250000000) ≤ -Real.log (11059 / 200000) ∧
    -Real.log (11059 / 200000) ≤ (2895072793 / 1000000000) := by
  have h := checkLog_sound (w := (1441 / 23559)) (n := 12)
    (lo := (30621017 / 250000000)) (hi := (122484069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11059) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 11059) = 1/(11059 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2895072793 / 1000000000) (-723768197 / 250000000) (Real.log (11059 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (665388961 / 1000000000) ≤ -Real.log (1000000 / 1945247) ∧
    -Real.log (1000000 / 1945247) ≤ (332694481 / 500000000) := by
  have h := checkLog_sound (w := (945247 / 2945247)) (n := 12)
    (lo := (665388961 / 1000000000)) (hi := (332694481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1945247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1945247 / 1000000) = 1/(1000000 / 1945247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (665388961 / 1000000000) (332694481 / 500000000) (Real.log (1945247 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1945247 / 1000000) = -Real.log (1000000 / 1945247) := by
    rw [show ((1945247 / 1000000) : ℝ) = ((1000000 / 1945247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (580984623 / 200000000) ≤ -Real.log (54753 / 1000000) ∧
    -Real.log (54753 / 1000000) ≤ (36311539 / 12500000) := by
  have h := checkLog_sound (w := (7747 / 117253)) (n := 12)
    (lo := (26466879 / 200000000)) (hi := (33083599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54753) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 54753) = 1/(54753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36311539 / 12500000) (-580984623 / 200000000) (Real.log (54753 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (83072821 / 125000000) ≤ -Real.log (1000000 / 1943679) ∧
    -Real.log (1000000 / 1943679) ≤ (664582569 / 1000000000) := by
  have h := checkLog_sound (w := (943679 / 2943679)) (n := 12)
    (lo := (83072821 / 125000000)) (hi := (664582569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1943679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1943679 / 1000000) = 1/(1000000 / 1943679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (83072821 / 125000000) (664582569 / 1000000000) (Real.log (1943679 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1943679 / 1000000) = -Real.log (1000000 / 1943679) := by
    rw [show ((1943679 / 1000000) : ℝ) = ((1000000 / 1943679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2876687809 / 1000000000) ≤ -Real.log (56321 / 1000000) ∧
    -Real.log (56321 / 1000000) ≤ (1438343907 / 500000000) := by
  have h := checkLog_sound (w := (6179 / 118821)) (n := 12)
    (lo := (104099089 / 1000000000)) (hi := (10409909 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56321) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 56321) = 1/(56321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1438343907 / 500000000) (-2876687809 / 1000000000) (Real.log (56321 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (332436863 / 500000000) ≤ -Real.log (200000 / 388849) ∧
    -Real.log (200000 / 388849) ≤ (664873727 / 1000000000) := by
  have h := checkLog_sound (w := (188849 / 588849)) (n := 12)
    (lo := (332436863 / 500000000)) (hi := (664873727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388849 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388849 / 200000) = 1/(200000 / 388849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (332436863 / 500000000) (664873727 / 1000000000) (Real.log (388849 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (388849 / 200000) = -Real.log (200000 / 388849) := by
    rw [show ((388849 / 200000) : ℝ) = ((200000 / 388849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (360848523 / 125000000) ≤ -Real.log (11151 / 200000) ∧
    -Real.log (11151 / 200000) ≤ (2886788189 / 1000000000) := by
  have h := checkLog_sound (w := (1349 / 23651)) (n := 12)
    (lo := (14274933 / 125000000)) (hi := (22839893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11151) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 11151) = 1/(11151 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2886788189 / 1000000000) (-360848523 / 125000000) (Real.log (11151 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1780091541 / 500000000) ≤ -Real.log (25000000000 / 879240889773) ∧
    -Real.log (25000000000 / 879240889773) ≤ (222511443 / 62500000) := by
  have h := checkLog_sound (w := (79240889773 / 1679240889773)) (n := 12)
    (lo := (47223591 / 500000000)) (hi := (94447183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879240889773 / 800000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(879240889773 / 800000000000) = 1/(25000000000 / 879240889773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1780091541 / 500000000) (222511443 / 62500000) (Real.log (879240889773 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (879240889773 / 25000000000) = -Real.log (25000000000 / 879240889773) := by
    rw [show ((879240889773 / 25000000000) : ℝ) = ((25000000000 / 879240889773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (142812483 / 40000000) ≤ -Real.log (125000000000 / 4440959856081) ∧
    -Real.log (125000000000 / 4440959856081) ≤ (3570312081 / 1000000000) := by
  have h := checkLog_sound (w := (440959856081 / 8440959856081)) (n := 12)
    (lo := (4183047 / 40000000)) (hi := (6536011 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4440959856081 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4440959856081 / 4000000000000) = 1/(125000000000 / 4440959856081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (142812483 / 40000000) (3570312081 / 1000000000) (Real.log (4440959856081 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4440959856081 / 125000000000) = -Real.log (125000000000 / 4440959856081) := by
    rw [show ((4440959856081 / 125000000000) : ℝ) = ((125000000000 / 4440959856081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3541270377 / 1000000000) ≤ -Real.log (250000000000 / 8627683279771) ∧
    -Real.log (250000000000 / 8627683279771) ≤ (3541270383 / 1000000000) := by
  have h := checkLog_sound (w := (627683279771 / 16627683279771)) (n := 12)
    (lo := (75534477 / 1000000000)) (hi := (37767239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8627683279771 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8627683279771 / 8000000000000) = 1/(250000000000 / 8627683279771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3541270377 / 1000000000) (3541270383 / 1000000000) (Real.log (8627683279771 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8627683279771 / 250000000000) = -Real.log (250000000000 / 8627683279771) := by
    rw [show ((8627683279771 / 250000000000) : ℝ) = ((250000000000 / 8627683279771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (355166191 / 100000000) ≤ -Real.log (500000000000 / 17435611155951) ∧
    -Real.log (500000000000 / 17435611155951) ≤ (887915479 / 250000000) := by
  have h := checkLog_sound (w := (1435611155951 / 33435611155951)) (n := 12)
    (lo := (8592601 / 100000000)) (hi := (85926011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17435611155951 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17435611155951 / 16000000000000) = 1/(500000000000 / 17435611155951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (355166191 / 100000000) (887915479 / 250000000) (Real.log (17435611155951 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17435611155951 / 500000000000) = -Real.log (500000000000 / 17435611155951) := by
    rw [show ((17435611155951 / 500000000000) : ℝ) = ((500000000000 / 17435611155951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0141

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0142Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0142
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

theorem reflection_log_1_neg : (65766167 / 100000000) ≤ -Real.log (5120 / 9883) ∧
    -Real.log (5120 / 9883) ≤ (657661671 / 1000000000) := by
  have h := checkLog_sound (w := (4763 / 15003)) (n := 12)
    (lo := (65766167 / 100000000)) (hi := (657661671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9883 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9883 / 5120) = 1/(5120 / 9883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65766167 / 100000000) (657661671 / 1000000000) (Real.log (9883 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (9883 / 5120) = -Real.log (5120 / 9883) := by
    rw [show ((9883 / 5120) : ℝ) = ((5120 / 9883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1331586967 / 500000000) ≤ -Real.log (357 / 5120) ∧
    -Real.log (357 / 5120) ≤ (1331586969 / 500000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 357) = 1/(357 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1331586969 / 500000000) (-1331586967 / 500000000) (Real.log (357 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (657277097 / 1000000000) ≤ -Real.log (6400 / 12349) ∧
    -Real.log (6400 / 12349) ≤ (328638549 / 500000000) := by
  have h := checkLog_sound (w := (5949 / 18749)) (n := 12)
    (lo := (657277097 / 1000000000)) (hi := (328638549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12349 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12349 / 6400) = 1/(6400 / 12349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (657277097 / 1000000000) (328638549 / 500000000) (Real.log (12349 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12349 / 6400) = -Real.log (6400 / 12349) := by
    rw [show ((12349 / 6400) : ℝ) = ((6400 / 12349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (331573241 / 125000000) ≤ -Real.log (451 / 6400) ∧
    -Real.log (451 / 6400) ≤ (663146483 / 250000000) := by
  have h := checkLog_sound (w := (349 / 1251)) (n := 12)
    (lo := (143286097 / 250000000)) (hi := (573144389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 451) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 451) = 1/(451 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-663146483 / 250000000) (-331573241 / 125000000) (Real.log (451 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (620870463 / 1000000000) ≤ -Real.log (2560 / 4763) ∧
    -Real.log (2560 / 4763) ≤ (9701101 / 15625000) := by
  have h := checkLog_sound (w := (2203 / 7323)) (n := 12)
    (lo := (620870463 / 1000000000)) (hi := (9701101 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4763 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4763 / 2560) = 1/(2560 / 4763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (620870463 / 1000000000) (9701101 / 15625000) (Real.log (4763 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4763 / 2560) = -Real.log (2560 / 4763) := by
    rw [show ((4763 / 2560) : ℝ) = ((2560 / 4763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (985013377 / 500000000) ≤ -Real.log (357 / 2560) ∧
    -Real.log (357 / 2560) ≤ (1970026757 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(640 / 357) = 1/(357 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1970026757 / 1000000000) (-985013377 / 500000000) (Real.log (357 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (77509041 / 125000000) ≤ -Real.log (3200 / 5949) ∧
    -Real.log (3200 / 5949) ≤ (620072329 / 1000000000) := by
  have h := checkLog_sound (w := (2749 / 9149)) (n := 12)
    (lo := (77509041 / 125000000)) (hi := (620072329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5949 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5949 / 3200) = 1/(3200 / 5949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (77509041 / 125000000) (620072329 / 1000000000) (Real.log (5949 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5949 / 3200) = -Real.log (3200 / 5949) := by
    rw [show ((5949 / 3200) : ℝ) = ((3200 / 5949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (489859687 / 250000000) ≤ -Real.log (451 / 3200) ∧
    -Real.log (451 / 3200) ≤ (1959438751 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1251)) (n := 12)
    (lo := (143286097 / 250000000)) (hi := (573144389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 451) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 451) = 1/(451 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1959438751 / 1000000000) (-489859687 / 250000000) (Real.log (451 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (664833093 / 1000000000) ≤ -Real.log (500000 / 972083) ∧
    -Real.log (500000 / 972083) ≤ (332416547 / 500000000) := by
  have h := checkLog_sound (w := (472083 / 1472083)) (n := 12)
    (lo := (664833093 / 1000000000)) (hi := (332416547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972083 / 500000) = 1/(500000 / 972083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (664833093 / 1000000000) (332416547 / 500000000) (Real.log (972083 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (972083 / 500000) = -Real.log (500000 / 972083) := by
    rw [show ((972083 / 500000) : ℝ) = ((500000 / 972083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2885372273 / 1000000000) ≤ -Real.log (27917 / 500000) ∧
    -Real.log (27917 / 500000) ≤ (1442686139 / 500000000) := by
  have h := checkLog_sound (w := (3333 / 59167)) (n := 12)
    (lo := (112783553 / 1000000000)) (hi := (56391777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27917) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 27917) = 1/(27917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1442686139 / 500000000) (-2885372273 / 1000000000) (Real.log (27917 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83138851 / 125000000) ≤ -Real.log (500000 / 972353) ∧
    -Real.log (500000 / 972353) ≤ (665110809 / 1000000000) := by
  have h := checkLog_sound (w := (472353 / 1472353)) (n := 12)
    (lo := (83138851 / 125000000)) (hi := (665110809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972353 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972353 / 500000) = 1/(500000 / 972353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83138851 / 125000000) (665110809 / 1000000000) (Real.log (972353 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (972353 / 500000) = -Real.log (500000 / 972353) := by
    rw [show ((972353 / 500000) : ℝ) = ((500000 / 972353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2895090873 / 1000000000) ≤ -Real.log (27647 / 500000) ∧
    -Real.log (27647 / 500000) ≤ (1447545439 / 500000000) := by
  have h := checkLog_sound (w := (3603 / 58897)) (n := 12)
    (lo := (122502153 / 1000000000)) (hi := (61251077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27647) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 27647) = 1/(27647 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1447545439 / 500000000) (-2895090873 / 1000000000) (Real.log (27647 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (259489 / 390625) ≤ -Real.log (500000 / 971557) ∧
    -Real.log (500000 / 971557) ≤ (664291841 / 1000000000) := by
  have h := checkLog_sound (w := (471557 / 1471557)) (n := 12)
    (lo := (259489 / 390625)) (hi := (664291841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971557 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971557 / 500000) = 1/(500000 / 971557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (259489 / 390625) (664291841 / 1000000000) (Real.log (971557 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (971557 / 500000) = -Real.log (500000 / 971557) := by
    rw [show ((971557 / 500000) : ℝ) = ((500000 / 971557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2866706011 / 1000000000) ≤ -Real.log (28443 / 500000) ∧
    -Real.log (28443 / 500000) ≤ (89584563 / 31250000) := by
  have h := checkLog_sound (w := (2807 / 59693)) (n := 12)
    (lo := (94117291 / 1000000000)) (hi := (23529323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28443) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 28443) = 1/(28443 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-89584563 / 31250000) (-2866706011 / 1000000000) (Real.log (28443 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (664583083 / 1000000000) ≤ -Real.log (3125 / 6074) ∧
    -Real.log (3125 / 6074) ≤ (166145771 / 250000000) := by
  have h := checkLog_sound (w := (2949 / 9199)) (n := 12)
    (lo := (664583083 / 1000000000)) (hi := (166145771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6074 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6074 / 3125) = 1/(3125 / 6074) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (664583083 / 1000000000) (166145771 / 250000000) (Real.log (6074 / 3125)) := by
  have h := reflection_log_15_neg
  have he : Real.log (6074 / 3125) = -Real.log (3125 / 6074) := by
    rw [show ((6074 / 3125) : ℝ) = ((3125 / 6074) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (719176391 / 250000000) ≤ -Real.log (176 / 3125) ∧
    -Real.log (176 / 3125) ≤ (2876705569 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 5941)) (n := 12)
    (lo := (26029211 / 250000000)) (hi := (20823369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2816) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2816) = 1/(176 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2876705569 / 1000000000) (-719176391 / 250000000) (Real.log (176 / 3125)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1775102683 / 500000000) ≤ -Real.log (250000000000 / 8705116953827) ∧
    -Real.log (250000000000 / 8705116953827) ≤ (887551343 / 250000000) := by
  have h := checkLog_sound (w := (705116953827 / 16705116953827)) (n := 12)
    (lo := (42234733 / 500000000)) (hi := (84469467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8705116953827 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8705116953827 / 8000000000000) = 1/(250000000000 / 8705116953827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1775102683 / 500000000) (887551343 / 250000000) (Real.log (8705116953827 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8705116953827 / 250000000000) = -Real.log (250000000000 / 8705116953827) := by
    rw [show ((8705116953827 / 250000000000) : ℝ) = ((250000000000 / 8705116953827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3560201681 / 1000000000) ≤ -Real.log (500000000000 / 17585144862011) ∧
    -Real.log (500000000000 / 17585144862011) ≤ (3560201687 / 1000000000) := by
  have h := checkLog_sound (w := (1585144862011 / 33585144862011)) (n := 12)
    (lo := (94465781 / 1000000000)) (hi := (47232891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17585144862011 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17585144862011 / 16000000000000) = 1/(500000000000 / 17585144862011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3560201681 / 1000000000) (3560201687 / 1000000000) (Real.log (17585144862011 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (17585144862011 / 500000000000) = -Real.log (500000000000 / 17585144862011) := by
    rw [show ((17585144862011 / 500000000000) : ℝ) = ((500000000000 / 17585144862011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3530997851 / 1000000000) ≤ -Real.log (500000000000 / 17079017684491) ∧
    -Real.log (500000000000 / 17079017684491) ≤ (3530997857 / 1000000000) := by
  have h := checkLog_sound (w := (1079017684491 / 33079017684491)) (n := 12)
    (lo := (65261951 / 1000000000)) (hi := (509859 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17079017684491 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17079017684491 / 16000000000000) = 1/(500000000000 / 17079017684491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3530997851 / 1000000000) (3530997857 / 1000000000) (Real.log (17079017684491 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (17079017684491 / 500000000000) = -Real.log (500000000000 / 17079017684491) := by
    rw [show ((17079017684491 / 500000000000) : ℝ) = ((500000000000 / 17079017684491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3541288647 / 1000000000) ≤ -Real.log (250000000000 / 8627840909091) ∧
    -Real.log (250000000000 / 8627840909091) ≤ (3541288653 / 1000000000) := by
  have h := checkLog_sound (w := (627840909091 / 16627840909091)) (n := 12)
    (lo := (75552747 / 1000000000)) (hi := (18888187 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8627840909091 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8627840909091 / 8000000000000) = 1/(250000000000 / 8627840909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3541288647 / 1000000000) (3541288653 / 1000000000) (Real.log (8627840909091 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8627840909091 / 250000000000) = -Real.log (250000000000 / 8627840909091) := by
    rw [show ((8627840909091 / 250000000000) : ℝ) = ((250000000000 / 8627840909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0142

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0143Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0143
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

theorem reflection_log_1_neg : (657277097 / 1000000000) ≤ -Real.log (6400 / 12349) ∧
    -Real.log (6400 / 12349) ≤ (328638549 / 500000000) := by
  have h := checkLog_sound (w := (5949 / 18749)) (n := 12)
    (lo := (657277097 / 1000000000)) (hi := (328638549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12349 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12349 / 6400) = 1/(6400 / 12349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (657277097 / 1000000000) (328638549 / 500000000) (Real.log (12349 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12349 / 6400) = -Real.log (6400 / 12349) := by
    rw [show ((12349 / 6400) : ℝ) = ((6400 / 12349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (331573241 / 125000000) ≤ -Real.log (451 / 6400) ∧
    -Real.log (451 / 6400) ≤ (663146483 / 250000000) := by
  have h := checkLog_sound (w := (349 / 1251)) (n := 12)
    (lo := (143286097 / 250000000)) (hi := (573144389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 451) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 451) = 1/(451 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-663146483 / 250000000) (-331573241 / 125000000) (Real.log (451 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (656892377 / 1000000000) ≤ -Real.log (25600 / 49377) ∧
    -Real.log (25600 / 49377) ≤ (328446189 / 500000000) := by
  have h := checkLog_sound (w := (23777 / 74977)) (n := 12)
    (lo := (656892377 / 1000000000)) (hi := (328446189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49377 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49377 / 25600) = 1/(25600 / 49377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (656892377 / 1000000000) (328446189 / 500000000) (Real.log (49377 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49377 / 25600) = -Real.log (25600 / 49377) := by
    rw [show ((49377 / 25600) : ℝ) = ((25600 / 49377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1321054427 / 500000000) ≤ -Real.log (1823 / 25600) ∧
    -Real.log (1823 / 25600) ≤ (1321054429 / 500000000) := by
  have h := checkLog_sound (w := (1377 / 5023)) (n := 12)
    (lo := (281333657 / 500000000)) (hi := (112533463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1823) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1823) = 1/(1823 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1321054429 / 500000000) (-1321054427 / 500000000) (Real.log (1823 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (77509041 / 125000000) ≤ -Real.log (3200 / 5949) ∧
    -Real.log (3200 / 5949) ≤ (620072329 / 1000000000) := by
  have h := checkLog_sound (w := (2749 / 9149)) (n := 12)
    (lo := (77509041 / 125000000)) (hi := (620072329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5949 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5949 / 3200) = 1/(3200 / 5949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (77509041 / 125000000) (620072329 / 1000000000) (Real.log (5949 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5949 / 3200) = -Real.log (3200 / 5949) := by
    rw [show ((5949 / 3200) : ℝ) = ((3200 / 5949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (489859687 / 250000000) ≤ -Real.log (451 / 3200) ∧
    -Real.log (451 / 3200) ≤ (1959438751 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1251)) (n := 12)
    (lo := (143286097 / 250000000)) (hi := (573144389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 451) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 451) = 1/(451 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1959438751 / 1000000000) (-489859687 / 250000000) (Real.log (451 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (123854711 / 200000000) ≤ -Real.log (12800 / 23777) ∧
    -Real.log (12800 / 23777) ≤ (154818389 / 250000000) := by
  have h := checkLog_sound (w := (10977 / 36577)) (n := 12)
    (lo := (123854711 / 200000000)) (hi := (154818389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23777 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23777 / 12800) = 1/(12800 / 23777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (123854711 / 200000000) (154818389 / 250000000) (Real.log (23777 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23777 / 12800) = -Real.log (12800 / 23777) := by
    rw [show ((23777 / 12800) : ℝ) = ((12800 / 23777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (974480837 / 500000000) ≤ -Real.log (1823 / 12800) ∧
    -Real.log (1823 / 12800) ≤ (1948961677 / 1000000000) := by
  have h := checkLog_sound (w := (1377 / 5023)) (n := 12)
    (lo := (281333657 / 500000000)) (hi := (112533463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1823) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1823) = 1/(1823 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1948961677 / 1000000000) (-974480837 / 500000000) (Real.log (1823 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (132911163 / 200000000) ≤ -Real.log (1000000 / 1943627) ∧
    -Real.log (1000000 / 1943627) ≤ (83069477 / 125000000) := by
  have h := checkLog_sound (w := (943627 / 2943627)) (n := 12)
    (lo := (132911163 / 200000000)) (hi := (83069477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1943627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1943627 / 1000000) = 1/(1000000 / 1943627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (132911163 / 200000000) (83069477 / 125000000) (Real.log (1943627 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1943627 / 1000000) = -Real.log (1000000 / 1943627) := by
    rw [show ((1943627 / 1000000) : ℝ) = ((1000000 / 1943627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (718941239 / 250000000) ≤ -Real.log (56373 / 1000000) ∧
    -Real.log (56373 / 1000000) ≤ (2875764961 / 1000000000) := by
  have h := checkLog_sound (w := (6127 / 118873)) (n := 12)
    (lo := (25794059 / 250000000)) (hi := (103176237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56373) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 56373) = 1/(56373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2875764961 / 1000000000) (-718941239 / 250000000) (Real.log (56373 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (664833607 / 1000000000) ≤ -Real.log (1000000 / 1944167) ∧
    -Real.log (1000000 / 1944167) ≤ (83104201 / 125000000) := by
  have h := checkLog_sound (w := (944167 / 2944167)) (n := 12)
    (lo := (664833607 / 1000000000)) (hi := (83104201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1944167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1944167 / 1000000) = 1/(1000000 / 1944167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (664833607 / 1000000000) (83104201 / 125000000) (Real.log (1944167 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1944167 / 1000000) = -Real.log (1000000 / 1944167) := by
    rw [show ((1944167 / 1000000) : ℝ) = ((1000000 / 1944167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (360673773 / 125000000) ≤ -Real.log (55833 / 1000000) ∧
    -Real.log (55833 / 1000000) ≤ (2885390189 / 1000000000) := by
  have h := checkLog_sound (w := (6667 / 118333)) (n := 12)
    (lo := (14100183 / 125000000)) (hi := (22560293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55833) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 55833) = 1/(55833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2885390189 / 1000000000) (-360673773 / 125000000) (Real.log (55833 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (166000257 / 250000000) ≤ -Real.log (1000000 / 1942549) ∧
    -Real.log (1000000 / 1942549) ≤ (664001029 / 1000000000) := by
  have h := checkLog_sound (w := (942549 / 2942549)) (n := 12)
    (lo := (166000257 / 250000000)) (hi := (664001029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1942549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1942549 / 1000000) = 1/(1000000 / 1942549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (166000257 / 250000000) (664001029 / 1000000000) (Real.log (1942549 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1942549 / 1000000) = -Real.log (1000000 / 1942549) := by
    rw [show ((1942549 / 1000000) : ℝ) = ((1000000 / 1942549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1428411433 / 500000000) ≤ -Real.log (57451 / 1000000) ∧
    -Real.log (57451 / 1000000) ≤ (2856822871 / 1000000000) := by
  have h := checkLog_sound (w := (5049 / 119951)) (n := 12)
    (lo := (42117073 / 500000000)) (hi := (84234147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57451) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 57451) = 1/(57451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2856822871 / 1000000000) (-1428411433 / 500000000) (Real.log (57451 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (132858471 / 200000000) ≤ -Real.log (200000 / 388623) ∧
    -Real.log (200000 / 388623) ≤ (166073089 / 250000000) := by
  have h := checkLog_sound (w := (188623 / 588623)) (n := 12)
    (lo := (132858471 / 200000000)) (hi := (166073089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388623 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388623 / 200000) = 1/(200000 / 388623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (132858471 / 200000000) (166073089 / 250000000) (Real.log (388623 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (388623 / 200000) = -Real.log (200000 / 388623) := by
    rw [show ((388623 / 200000) : ℝ) = ((200000 / 388623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (286672359 / 100000000) ≤ -Real.log (11377 / 200000) ∧
    -Real.log (11377 / 200000) ≤ (573344719 / 200000000) := by
  have h := checkLog_sound (w := (1123 / 23877)) (n := 12)
    (lo := (9413487 / 100000000)) (hi := (94134871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11377) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 11377) = 1/(11377 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-573344719 / 200000000) (-286672359 / 100000000) (Real.log (11377 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (354032077 / 100000000) ≤ -Real.log (250000000000 / 8619494261437) ∧
    -Real.log (250000000000 / 8619494261437) ≤ (442540097 / 125000000) := by
  have h := checkLog_sound (w := (619494261437 / 16619494261437)) (n := 12)
    (lo := (7458487 / 100000000)) (hi := (74584871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8619494261437 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8619494261437 / 8000000000000) = 1/(250000000000 / 8619494261437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (354032077 / 100000000) (442540097 / 125000000) (Real.log (8619494261437 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8619494261437 / 250000000000) = -Real.log (250000000000 / 8619494261437) := by
    rw [show ((8619494261437 / 250000000000) : ℝ) = ((250000000000 / 8619494261437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3550223791 / 1000000000) ≤ -Real.log (500000000000 / 17410554689879) ∧
    -Real.log (500000000000 / 17410554689879) ≤ (3550223797 / 1000000000) := by
  have h := checkLog_sound (w := (1410554689879 / 33410554689879)) (n := 12)
    (lo := (84487891 / 1000000000)) (hi := (21121973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17410554689879 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17410554689879 / 16000000000000) = 1/(500000000000 / 17410554689879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3550223791 / 1000000000) (3550223797 / 1000000000) (Real.log (17410554689879 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (17410554689879 / 500000000000) = -Real.log (500000000000 / 17410554689879) := by
    rw [show ((17410554689879 / 500000000000) : ℝ) = ((500000000000 / 17410554689879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3520823893 / 1000000000) ≤ -Real.log (31250000000 / 1056633587753) ∧
    -Real.log (31250000000 / 1056633587753) ≤ (3520823899 / 1000000000) := by
  have h := checkLog_sound (w := (56633587753 / 2056633587753)) (n := 12)
    (lo := (55087993 / 1000000000)) (hi := (27543997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056633587753 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1056633587753 / 1000000000000) = 1/(31250000000 / 1056633587753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3520823893 / 1000000000) (3520823899 / 1000000000) (Real.log (1056633587753 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1056633587753 / 31250000000) = -Real.log (31250000000 / 1056633587753) := by
    rw [show ((1056633587753 / 31250000000) : ℝ) = ((31250000000 / 1056633587753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (706203189 / 200000000) ≤ -Real.log (500000000000 / 17079326711787) ∧
    -Real.log (500000000000 / 17079326711787) ≤ (3531015951 / 1000000000) := by
  have h := checkLog_sound (w := (1079326711787 / 33079326711787)) (n := 12)
    (lo := (13056009 / 200000000)) (hi := (32640023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17079326711787 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17079326711787 / 16000000000000) = 1/(500000000000 / 17079326711787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (706203189 / 200000000) (3531015951 / 1000000000) (Real.log (17079326711787 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17079326711787 / 500000000000) = -Real.log (500000000000 / 17079326711787) := by
    rw [show ((17079326711787 / 500000000000) : ℝ) = ((500000000000 / 17079326711787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0143

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0144Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0144
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

theorem reflection_log_1_neg : (656892377 / 1000000000) ≤ -Real.log (25600 / 49377) ∧
    -Real.log (25600 / 49377) ≤ (328446189 / 500000000) := by
  have h := checkLog_sound (w := (23777 / 74977)) (n := 12)
    (lo := (656892377 / 1000000000)) (hi := (328446189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49377 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49377 / 25600) = 1/(25600 / 49377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (656892377 / 1000000000) (328446189 / 500000000) (Real.log (49377 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49377 / 25600) = -Real.log (25600 / 49377) := by
    rw [show ((49377 / 25600) : ℝ) = ((25600 / 49377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1321054427 / 500000000) ≤ -Real.log (1823 / 25600) ∧
    -Real.log (1823 / 25600) ≤ (1321054429 / 500000000) := by
  have h := checkLog_sound (w := (1377 / 5023)) (n := 12)
    (lo := (281333657 / 500000000)) (hi := (112533463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1823) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1823) = 1/(1823 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1321054429 / 500000000) (-1321054427 / 500000000) (Real.log (1823 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (164126877 / 250000000) ≤ -Real.log (12800 / 24679) ∧
    -Real.log (12800 / 24679) ≤ (656507509 / 1000000000) := by
  have h := checkLog_sound (w := (11879 / 37479)) (n := 12)
    (lo := (164126877 / 250000000)) (hi := (656507509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24679 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24679 / 12800) = 1/(12800 / 24679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (164126877 / 250000000) (656507509 / 1000000000) (Real.log (24679 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24679 / 12800) = -Real.log (12800 / 24679) := by
    rw [show ((24679 / 12800) : ℝ) = ((12800 / 24679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2631740411 / 1000000000) ≤ -Real.log (921 / 12800) ∧
    -Real.log (921 / 12800) ≤ (526348083 / 200000000) := by
  have h := checkLog_sound (w := (679 / 2521)) (n := 12)
    (lo := (552298871 / 1000000000)) (hi := (69037359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 921) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 921) = 1/(921 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-526348083 / 200000000) (-2631740411 / 1000000000) (Real.log (921 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (123854711 / 200000000) ≤ -Real.log (12800 / 23777) ∧
    -Real.log (12800 / 23777) ≤ (154818389 / 250000000) := by
  have h := checkLog_sound (w := (10977 / 36577)) (n := 12)
    (lo := (123854711 / 200000000)) (hi := (154818389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23777 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23777 / 12800) = 1/(12800 / 23777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (123854711 / 200000000) (154818389 / 250000000) (Real.log (23777 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23777 / 12800) = -Real.log (12800 / 23777) := by
    rw [show ((23777 / 12800) : ℝ) = ((12800 / 23777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (974480837 / 500000000) ≤ -Real.log (1823 / 12800) ∧
    -Real.log (1823 / 12800) ≤ (1948961677 / 1000000000) := by
  have h := checkLog_sound (w := (1377 / 5023)) (n := 12)
    (lo := (281333657 / 500000000)) (hi := (112533463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1823) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1823) = 1/(1823 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1948961677 / 1000000000) (-974480837 / 500000000) (Real.log (1823 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (19327317 / 31250000) ≤ -Real.log (6400 / 11879) ∧
    -Real.log (6400 / 11879) ≤ (123694829 / 200000000) := by
  have h := checkLog_sound (w := (5479 / 18279)) (n := 12)
    (lo := (19327317 / 31250000)) (hi := (123694829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11879 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11879 / 6400) = 1/(6400 / 11879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (19327317 / 31250000) (123694829 / 200000000) (Real.log (11879 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11879 / 6400) = -Real.log (6400 / 11879) := by
    rw [show ((11879 / 6400) : ℝ) = ((6400 / 11879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1938593231 / 1000000000) ≤ -Real.log (921 / 6400) ∧
    -Real.log (921 / 6400) ≤ (969296617 / 500000000) := by
  have h := checkLog_sound (w := (679 / 2521)) (n := 12)
    (lo := (552298871 / 1000000000)) (hi := (69037359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 921) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 921) = 1/(921 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-969296617 / 500000000) (-1938593231 / 1000000000) (Real.log (921 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (332139487 / 500000000) ≤ -Real.log (1000000 / 1943089) ∧
    -Real.log (1000000 / 1943089) ≤ (26571159 / 40000000) := by
  have h := checkLog_sound (w := (943089 / 2943089)) (n := 12)
    (lo := (332139487 / 500000000)) (hi := (26571159 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1943089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1943089 / 1000000) = 1/(1000000 / 1943089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (332139487 / 500000000) (26571159 / 40000000) (Real.log (1943089 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1943089 / 1000000) = -Real.log (1000000 / 1943089) := by
    rw [show ((1943089 / 1000000) : ℝ) = ((1000000 / 1943089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (358283329 / 125000000) ≤ -Real.log (56911 / 1000000) ∧
    -Real.log (56911 / 1000000) ≤ (2866266637 / 1000000000) := by
  have h := checkLog_sound (w := (5589 / 119411)) (n := 12)
    (lo := (11709739 / 125000000)) (hi := (93677913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56911) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 56911) = 1/(56911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2866266637 / 1000000000) (-358283329 / 125000000) (Real.log (56911 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (664556329 / 1000000000) ≤ -Real.log (250000 / 485907) ∧
    -Real.log (250000 / 485907) ≤ (66455633 / 100000000) := by
  have h := checkLog_sound (w := (235907 / 735907)) (n := 12)
    (lo := (664556329 / 1000000000)) (hi := (66455633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((485907 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(485907 / 250000) = 1/(250000 / 485907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (664556329 / 1000000000) (66455633 / 100000000) (Real.log (485907 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (485907 / 250000) = -Real.log (250000 / 485907) := by
    rw [show ((485907 / 250000) : ℝ) = ((250000 / 485907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (575156539 / 200000000) ≤ -Real.log (14093 / 250000) ∧
    -Real.log (14093 / 250000) ≤ (28757827 / 10000000) := by
  have h := checkLog_sound (w := (766 / 14859)) (n := 12)
    (lo := (4127759 / 40000000)) (hi := (12899247 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14093) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 14093) = 1/(14093 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-28757827 / 10000000) (-575156539 / 200000000) (Real.log (14093 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (132742129 / 200000000) ≤ -Real.log (200000 / 388397) ∧
    -Real.log (200000 / 388397) ≤ (331855323 / 500000000) := by
  have h := checkLog_sound (w := (188397 / 588397)) (n := 12)
    (lo := (132742129 / 200000000)) (hi := (331855323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388397 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388397 / 200000) = 1/(200000 / 388397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (132742129 / 200000000) (331855323 / 500000000) (Real.log (388397 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (388397 / 200000) = -Real.log (200000 / 388397) := by
    rw [show ((388397 / 200000) : ℝ) = ((200000 / 388397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1423526839 / 500000000) ≤ -Real.log (11603 / 200000) ∧
    -Real.log (11603 / 200000) ≤ (2847053683 / 1000000000) := by
  have h := checkLog_sound (w := (897 / 24103)) (n := 12)
    (lo := (37232479 / 500000000)) (hi := (74464959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11603) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 11603) = 1/(11603 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2847053683 / 1000000000) (-1423526839 / 500000000) (Real.log (11603 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (332000771 / 500000000) ≤ -Real.log (20000 / 38851) ∧
    -Real.log (20000 / 38851) ≤ (664001543 / 1000000000) := by
  have h := checkLog_sound (w := (18851 / 58851)) (n := 12)
    (lo := (332000771 / 500000000)) (hi := (664001543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38851 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38851 / 20000) = 1/(20000 / 38851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (332000771 / 500000000) (664001543 / 1000000000) (Real.log (38851 / 20000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (38851 / 20000) = -Real.log (20000 / 38851) := by
    rw [show ((38851 / 20000) : ℝ) = ((20000 / 38851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (178552517 / 62500000) ≤ -Real.log (1149 / 20000) ∧
    -Real.log (1149 / 20000) ≤ (2856840277 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 2399)) (n := 12)
    (lo := (2632861 / 31250000)) (hi := (84251553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1149) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1250 / 1149) = 1/(1149 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2856840277 / 1000000000) (-178552517 / 62500000) (Real.log (1149 / 20000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1765272803 / 500000000) ≤ -Real.log (500000000000 / 17071295531619) ∧
    -Real.log (500000000000 / 17071295531619) ≤ (882636403 / 250000000) := by
  have h := checkLog_sound (w := (1071295531619 / 33071295531619)) (n := 12)
    (lo := (32404853 / 500000000)) (hi := (64809707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17071295531619 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17071295531619 / 16000000000000) = 1/(500000000000 / 17071295531619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1765272803 / 500000000) (882636403 / 250000000) (Real.log (17071295531619 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (17071295531619 / 500000000000) = -Real.log (500000000000 / 17071295531619) := by
    rw [show ((17071295531619 / 500000000000) : ℝ) = ((500000000000 / 17071295531619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (221271189 / 62500000) ≤ -Real.log (500000000000 / 17239303200171) ∧
    -Real.log (500000000000 / 17239303200171) ≤ (354033903 / 100000000) := by
  have h := checkLog_sound (w := (1239303200171 / 33239303200171)) (n := 12)
    (lo := (18650781 / 250000000)) (hi := (23873 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17239303200171 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17239303200171 / 16000000000000) = 1/(500000000000 / 17239303200171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (221271189 / 62500000) (354033903 / 100000000) (Real.log (17239303200171 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (17239303200171 / 500000000000) = -Real.log (500000000000 / 17239303200171) := by
    rw [show ((17239303200171 / 500000000000) : ℝ) = ((500000000000 / 17239303200171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (877691081 / 250000000) ≤ -Real.log (250000000000 / 8368460742911) ∧
    -Real.log (250000000000 / 8368460742911) ≤ (351076433 / 100000000) := by
  have h := checkLog_sound (w := (368460742911 / 16368460742911)) (n := 12)
    (lo := (5628553 / 125000000)) (hi := (1801137 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8368460742911 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8368460742911 / 8000000000000) = 1/(250000000000 / 8368460742911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (877691081 / 250000000) (351076433 / 100000000) (Real.log (8368460742911 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8368460742911 / 250000000000) = -Real.log (250000000000 / 8368460742911) := by
    rw [show ((8368460742911 / 250000000000) : ℝ) = ((250000000000 / 8368460742911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1760420907 / 500000000) ≤ -Real.log (250000000000 / 8453220191471) ∧
    -Real.log (250000000000 / 8453220191471) ≤ (176042091 / 50000000) := by
  have h := checkLog_sound (w := (453220191471 / 16453220191471)) (n := 12)
    (lo := (27552957 / 500000000)) (hi := (11021183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8453220191471 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8453220191471 / 8000000000000) = 1/(250000000000 / 8453220191471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1760420907 / 500000000) (176042091 / 50000000) (Real.log (8453220191471 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8453220191471 / 250000000000) = -Real.log (250000000000 / 8453220191471) := by
    rw [show ((8453220191471 / 250000000000) : ℝ) = ((250000000000 / 8453220191471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0144

end


