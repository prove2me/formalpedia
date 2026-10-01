-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0099Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0099Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:07:23.160732+00:00
-- url     : https://prove2.me/theorems/631c233b-b803-46f6-8b2e-79b7fe95d4be
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0099Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0100Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0099Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0100Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0101Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0102Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0099Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0100Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0101Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0102Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0099Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0100Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0101Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0102Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0099Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0100Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0101Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0102Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0099Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0099
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

theorem reflection_log_1_neg : (335799151 / 500000000) ≤ -Real.log (51200 / 100217) ∧
    -Real.log (51200 / 100217) ≤ (671598303 / 1000000000) := by
  have h := checkLog_sound (w := (49017 / 151417)) (n := 12)
    (lo := (335799151 / 500000000)) (hi := (671598303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100217 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100217 / 51200) = 1/(51200 / 100217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (335799151 / 500000000) (671598303 / 1000000000) (Real.log (100217 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100217 / 51200) = -Real.log (51200 / 100217) := by
    rw [show ((100217 / 51200) : ℝ) = ((51200 / 100217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (788759863 / 250000000) ≤ -Real.log (2183 / 51200) ∧
    -Real.log (2183 / 51200) ≤ (3155039457 / 1000000000) := by
  have h := checkLog_sound (w := (1017 / 5383)) (n := 12)
    (lo := (95612683 / 250000000)) (hi := (382450733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2183) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2183) = 1/(2183 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3155039457 / 1000000000) (-788759863 / 250000000) (Real.log (2183 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (83926087 / 125000000) ≤ -Real.log (25600 / 50099) ∧
    -Real.log (25600 / 50099) ≤ (671408697 / 1000000000) := by
  have h := checkLog_sound (w := (24499 / 75699)) (n := 12)
    (lo := (83926087 / 125000000)) (hi := (671408697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50099 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50099 / 25600) = 1/(25600 / 50099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (83926087 / 125000000) (671408697 / 1000000000) (Real.log (50099 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50099 / 25600) = -Real.log (25600 / 50099) := by
    rw [show ((50099 / 25600) : ℝ) = ((25600 / 50099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3146373491 / 1000000000) ≤ -Real.log (1101 / 25600) ∧
    -Real.log (1101 / 25600) ≤ (393296687 / 125000000) := by
  have h := checkLog_sound (w := (499 / 2701)) (n := 12)
    (lo := (373784771 / 1000000000)) (hi := (93446193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1101) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1101) = 1/(1101 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-393296687 / 125000000) (-3146373491 / 1000000000) (Real.log (1101 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (25982993 / 40000000) ≤ -Real.log (25600 / 49017) ∧
    -Real.log (25600 / 49017) ≤ (324787413 / 500000000) := by
  have h := checkLog_sound (w := (23417 / 74617)) (n := 12)
    (lo := (25982993 / 40000000)) (hi := (324787413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49017 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49017 / 25600) = 1/(25600 / 49017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (25982993 / 40000000) (324787413 / 500000000) (Real.log (49017 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49017 / 25600) = -Real.log (25600 / 49017) := by
    rw [show ((49017 / 25600) : ℝ) = ((25600 / 49017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (153868267 / 62500000) ≤ -Real.log (2183 / 25600) ∧
    -Real.log (2183 / 25600) ≤ (615473069 / 250000000) := by
  have h := checkLog_sound (w := (1017 / 5383)) (n := 12)
    (lo := (95612683 / 250000000)) (hi := (382450733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2183) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2183) = 1/(2183 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-615473069 / 250000000) (-153868267 / 62500000) (Real.log (2183 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (649187129 / 1000000000) ≤ -Real.log (12800 / 24499) ∧
    -Real.log (12800 / 24499) ≤ (64918713 / 100000000) := by
  have h := checkLog_sound (w := (11699 / 37299)) (n := 12)
    (lo := (649187129 / 1000000000)) (hi := (64918713 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24499 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24499 / 12800) = 1/(12800 / 24499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (649187129 / 1000000000) (64918713 / 100000000) (Real.log (24499 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24499 / 12800) = -Real.log (12800 / 24499) := by
    rw [show ((24499 / 12800) : ℝ) = ((12800 / 24499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2453226311 / 1000000000) ≤ -Real.log (1101 / 12800) ∧
    -Real.log (1101 / 12800) ≤ (490645263 / 200000000) := by
  have h := checkLog_sound (w := (499 / 2701)) (n := 12)
    (lo := (373784771 / 1000000000)) (hi := (93446193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1101) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1101) = 1/(1101 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-490645263 / 200000000) (-2453226311 / 1000000000) (Real.log (1101 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135070559 / 200000000) ≤ -Real.log (500000 / 982363) ∧
    -Real.log (500000 / 982363) ≤ (168838199 / 250000000) := by
  have h := checkLog_sound (w := (482363 / 1482363)) (n := 12)
    (lo := (135070559 / 200000000)) (hi := (168838199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982363 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982363 / 500000) = 1/(500000 / 982363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135070559 / 200000000) (168838199 / 250000000) (Real.log (982363 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (982363 / 500000) = -Real.log (500000 / 982363) := by
    rw [show ((982363 / 500000) : ℝ) = ((500000 / 982363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (418076141 / 125000000) ≤ -Real.log (17637 / 500000) ∧
    -Real.log (17637 / 500000) ≤ (3344609133 / 1000000000) := by
  have h := checkLog_sound (w := (13613 / 48887)) (n := 12)
    (lo := (71502551 / 125000000)) (hi := (572020409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17637) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 17637) = 1/(17637 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3344609133 / 1000000000) (-418076141 / 125000000) (Real.log (17637 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (675498861 / 1000000000) ≤ -Real.log (1000000 / 1965013) ∧
    -Real.log (1000000 / 1965013) ≤ (337749431 / 500000000) := by
  have h := checkLog_sound (w := (965013 / 2965013)) (n := 12)
    (lo := (675498861 / 1000000000)) (hi := (337749431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965013 / 1000000) = 1/(1000000 / 1965013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (675498861 / 1000000000) (337749431 / 500000000) (Real.log (1965013 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1965013 / 1000000) = -Real.log (1000000 / 1965013) := by
    rw [show ((1965013 / 1000000) : ℝ) = ((1000000 / 1965013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (419097339 / 125000000) ≤ -Real.log (34987 / 1000000) ∧
    -Real.log (34987 / 1000000) ≤ (3352778717 / 1000000000) := by
  have h := checkLog_sound (w := (27513 / 97487)) (n := 12)
    (lo := (72523749 / 125000000)) (hi := (580189993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34987) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34987) = 1/(34987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3352778717 / 1000000000) (-419097339 / 125000000) (Real.log (34987 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67517871 / 100000000) ≤ -Real.log (31250 / 61387) ∧
    -Real.log (31250 / 61387) ≤ (675178711 / 1000000000) := by
  have h := checkLog_sound (w := (30137 / 92637)) (n := 12)
    (lo := (67517871 / 100000000)) (hi := (675178711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61387 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61387 / 31250) = 1/(31250 / 61387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67517871 / 100000000) (675178711 / 1000000000) (Real.log (61387 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61387 / 31250) = -Real.log (31250 / 61387) := by
    rw [show ((61387 / 31250) : ℝ) = ((31250 / 61387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3334960301 / 1000000000) ≤ -Real.log (1113 / 31250) ∧
    -Real.log (1113 / 31250) ≤ (1667480153 / 500000000) := by
  have h := checkLog_sound (w := (6721 / 24529)) (n := 12)
    (lo := (562371581 / 1000000000)) (hi := (281185791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8904) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8904) = 1/(1113 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1667480153 / 500000000) (-3334960301 / 1000000000) (Real.log (1113 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (675328873 / 1000000000) ≤ -Real.log (1000000 / 1964679) ∧
    -Real.log (1000000 / 1964679) ≤ (337664437 / 500000000) := by
  have h := checkLog_sound (w := (964679 / 2964679)) (n := 12)
    (lo := (675328873 / 1000000000)) (hi := (337664437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964679 / 1000000) = 1/(1000000 / 1964679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (675328873 / 1000000000) (337664437 / 500000000) (Real.log (1964679 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1964679 / 1000000) = -Real.log (1000000 / 1964679) := by
    rw [show ((1964679 / 1000000) : ℝ) = ((1000000 / 1964679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (835819397 / 250000000) ≤ -Real.log (35321 / 1000000) ∧
    -Real.log (35321 / 1000000) ≤ (3343277593 / 1000000000) := by
  have h := checkLog_sound (w := (27179 / 97821)) (n := 12)
    (lo := (142672217 / 250000000)) (hi := (570688869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35321) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35321) = 1/(35321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3343277593 / 1000000000) (-835819397 / 250000000) (Real.log (35321 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2009980961 / 500000000) ≤ -Real.log (500000000000 / 27849492544083) ∧
    -Real.log (500000000000 / 27849492544083) ≤ (502495241 / 125000000) := by
  have h := checkLog_sound (w := (11849492544083 / 43849492544083)) (n := 12)
    (lo := (277113011 / 500000000)) (hi := (554226023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27849492544083 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(27849492544083 / 16000000000000) = 1/(500000000000 / 27849492544083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2009980961 / 500000000) (502495241 / 125000000) (Real.log (27849492544083 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (27849492544083 / 500000000000) = -Real.log (500000000000 / 27849492544083) := by
    rw [show ((27849492544083 / 500000000000) : ℝ) = ((500000000000 / 27849492544083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4028277573 / 1000000000) ≤ -Real.log (500000000000 / 28082044759483) ∧
    -Real.log (500000000000 / 28082044759483) ≤ (4028277579 / 1000000000) := by
  have h := checkLog_sound (w := (12082044759483 / 44082044759483)) (n := 12)
    (lo := (562541673 / 1000000000)) (hi := (281270837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28082044759483 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28082044759483 / 16000000000000) = 1/(500000000000 / 28082044759483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4028277573 / 1000000000) (4028277579 / 1000000000) (Real.log (28082044759483 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28082044759483 / 500000000000) = -Real.log (500000000000 / 28082044759483) := by
    rw [show ((28082044759483 / 500000000000) : ℝ) = ((500000000000 / 28082044759483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4010139011 / 1000000000) ≤ -Real.log (250000000000 / 13788634321653) ∧
    -Real.log (250000000000 / 13788634321653) ≤ (4010139017 / 1000000000) := by
  have h := checkLog_sound (w := (5788634321653 / 21788634321653)) (n := 12)
    (lo := (544403111 / 1000000000)) (hi := (68050389 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13788634321653 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13788634321653 / 8000000000000) = 1/(250000000000 / 13788634321653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4010139011 / 1000000000) (4010139017 / 1000000000) (Real.log (13788634321653 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13788634321653 / 250000000000) = -Real.log (250000000000 / 13788634321653) := by
    rw [show ((13788634321653 / 250000000000) : ℝ) = ((250000000000 / 13788634321653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4018606461 / 1000000000) ≤ -Real.log (250000000000 / 13905884601229) ∧
    -Real.log (250000000000 / 13905884601229) ≤ (4018606467 / 1000000000) := by
  have h := checkLog_sound (w := (5905884601229 / 21905884601229)) (n := 12)
    (lo := (552870561 / 1000000000)) (hi := (276435281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13905884601229 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13905884601229 / 8000000000000) = 1/(250000000000 / 13905884601229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4018606461 / 1000000000) (4018606467 / 1000000000) (Real.log (13905884601229 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13905884601229 / 250000000000) = -Real.log (250000000000 / 13905884601229) := by
    rw [show ((13905884601229 / 250000000000) : ℝ) = ((250000000000 / 13905884601229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0099

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0100Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0100
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

theorem reflection_log_1_neg : (83926087 / 125000000) ≤ -Real.log (25600 / 50099) ∧
    -Real.log (25600 / 50099) ≤ (671408697 / 1000000000) := by
  have h := checkLog_sound (w := (24499 / 75699)) (n := 12)
    (lo := (83926087 / 125000000)) (hi := (671408697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50099 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50099 / 25600) = 1/(25600 / 50099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (83926087 / 125000000) (671408697 / 1000000000) (Real.log (50099 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50099 / 25600) = -Real.log (25600 / 50099) := by
    rw [show ((50099 / 25600) : ℝ) = ((25600 / 50099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3146373491 / 1000000000) ≤ -Real.log (1101 / 25600) ∧
    -Real.log (1101 / 25600) ≤ (393296687 / 125000000) := by
  have h := checkLog_sound (w := (499 / 2701)) (n := 12)
    (lo := (373784771 / 1000000000)) (hi := (93446193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1101) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1101) = 1/(1101 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-393296687 / 125000000) (-3146373491 / 1000000000) (Real.log (1101 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (671219053 / 1000000000) ≤ -Real.log (51200 / 100179) ∧
    -Real.log (51200 / 100179) ≤ (335609527 / 500000000) := by
  have h := checkLog_sound (w := (48979 / 151379)) (n := 12)
    (lo := (671219053 / 1000000000)) (hi := (335609527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100179 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100179 / 51200) = 1/(51200 / 100179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (671219053 / 1000000000) (335609527 / 500000000) (Real.log (100179 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100179 / 51200) = -Real.log (51200 / 100179) := by
    rw [show ((100179 / 51200) : ℝ) = ((51200 / 100179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (98055687 / 31250000) ≤ -Real.log (2221 / 51200) ∧
    -Real.log (2221 / 51200) ≤ (3137781989 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 5421)) (n := 12)
    (lo := (22824579 / 62500000)) (hi := (73038653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2221) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2221) = 1/(2221 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3137781989 / 1000000000) (-98055687 / 31250000) (Real.log (2221 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (649187129 / 1000000000) ≤ -Real.log (12800 / 24499) ∧
    -Real.log (12800 / 24499) ≤ (64918713 / 100000000) := by
  have h := checkLog_sound (w := (11699 / 37299)) (n := 12)
    (lo := (649187129 / 1000000000)) (hi := (64918713 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24499 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24499 / 12800) = 1/(12800 / 24499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (649187129 / 1000000000) (64918713 / 100000000) (Real.log (24499 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24499 / 12800) = -Real.log (12800 / 24499) := by
    rw [show ((24499 / 12800) : ℝ) = ((12800 / 24499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2453226311 / 1000000000) ≤ -Real.log (1101 / 12800) ∧
    -Real.log (1101 / 12800) ≤ (490645263 / 200000000) := by
  have h := checkLog_sound (w := (499 / 2701)) (n := 12)
    (lo := (373784771 / 1000000000)) (hi := (93446193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1101) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1101) = 1/(1101 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-490645263 / 200000000) (-2453226311 / 1000000000) (Real.log (1101 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (648799283 / 1000000000) ≤ -Real.log (25600 / 48979) ∧
    -Real.log (25600 / 48979) ≤ (162199821 / 250000000) := by
  have h := checkLog_sound (w := (23379 / 74579)) (n := 12)
    (lo := (648799283 / 1000000000)) (hi := (162199821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48979 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48979 / 25600) = 1/(25600 / 48979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (648799283 / 1000000000) (162199821 / 250000000) (Real.log (48979 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48979 / 25600) = -Real.log (25600 / 48979) := by
    rw [show ((48979 / 25600) : ℝ) = ((25600 / 48979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (611158701 / 250000000) ≤ -Real.log (2221 / 25600) ∧
    -Real.log (2221 / 25600) ≤ (305579351 / 125000000) := by
  have h := checkLog_sound (w := (979 / 5421)) (n := 12)
    (lo := (22824579 / 62500000)) (hi := (73038653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2221) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2221) = 1/(2221 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-305579351 / 125000000) (-611158701 / 250000000) (Real.log (2221 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (168801677 / 250000000) ≤ -Real.log (1000000 / 1964439) ∧
    -Real.log (1000000 / 1964439) ≤ (675206709 / 1000000000) := by
  have h := checkLog_sound (w := (964439 / 2964439)) (n := 12)
    (lo := (168801677 / 250000000)) (hi := (675206709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964439 / 1000000) = 1/(1000000 / 1964439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (168801677 / 250000000) (675206709 / 1000000000) (Real.log (1964439 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1964439 / 1000000) = -Real.log (1000000 / 1964439) := by
    rw [show ((1964439 / 1000000) : ℝ) = ((1000000 / 1964439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (667301149 / 200000000) ≤ -Real.log (35561 / 1000000) ∧
    -Real.log (35561 / 1000000) ≤ (13346023 / 4000000) := by
  have h := checkLog_sound (w := (26939 / 98061)) (n := 12)
    (lo := (22556681 / 40000000)) (hi := (281958513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35561) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35561) = 1/(35561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13346023 / 4000000) (-667301149 / 200000000) (Real.log (35561 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84419163 / 125000000) ≤ -Real.log (1000000 / 1964727) ∧
    -Real.log (1000000 / 1964727) ≤ (135070661 / 200000000) := by
  have h := checkLog_sound (w := (964727 / 2964727)) (n := 12)
    (lo := (84419163 / 125000000)) (hi := (135070661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964727 / 1000000) = 1/(1000000 / 1964727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84419163 / 125000000) (135070661 / 200000000) (Real.log (1964727 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1964727 / 1000000) = -Real.log (1000000 / 1964727) := by
    rw [show ((1964727 / 1000000) : ℝ) = ((1000000 / 1964727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3344637477 / 1000000000) ≤ -Real.log (35273 / 1000000) ∧
    -Real.log (35273 / 1000000) ≤ (1672318741 / 500000000) := by
  have h := checkLog_sound (w := (27227 / 97773)) (n := 12)
    (lo := (572048757 / 1000000000)) (hi := (286024379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35273) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35273) = 1/(35273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1672318741 / 500000000) (-3344637477 / 1000000000) (Real.log (35273 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (337514771 / 500000000) ≤ -Real.log (1000000 / 1964091) ∧
    -Real.log (1000000 / 1964091) ≤ (675029543 / 1000000000) := by
  have h := checkLog_sound (w := (964091 / 2964091)) (n := 12)
    (lo := (337514771 / 500000000)) (hi := (675029543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964091 / 1000000) = 1/(1000000 / 1964091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (337514771 / 500000000) (675029543 / 1000000000) (Real.log (1964091 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1964091 / 1000000) = -Real.log (1000000 / 1964091) := by
    rw [show ((1964091 / 1000000) : ℝ) = ((1000000 / 1964091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (831691829 / 250000000) ≤ -Real.log (35909 / 1000000) ∧
    -Real.log (35909 / 1000000) ≤ (3326767321 / 1000000000) := by
  have h := checkLog_sound (w := (26591 / 98409)) (n := 12)
    (lo := (138544649 / 250000000)) (hi := (554178597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35909) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35909) = 1/(35909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3326767321 / 1000000000) (-831691829 / 250000000) (Real.log (35909 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (675179219 / 1000000000) ≤ -Real.log (200000 / 392877) ∧
    -Real.log (200000 / 392877) ≤ (33758961 / 50000000) := by
  have h := checkLog_sound (w := (192877 / 592877)) (n := 12)
    (lo := (675179219 / 1000000000)) (hi := (33758961 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392877 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392877 / 200000) = 1/(200000 / 392877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (675179219 / 1000000000) (33758961 / 50000000) (Real.log (392877 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (392877 / 200000) = -Real.log (200000 / 392877) := by
    rw [show ((392877 / 200000) : ℝ) = ((200000 / 392877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3334988379 / 1000000000) ≤ -Real.log (7123 / 200000) ∧
    -Real.log (7123 / 200000) ≤ (104218387 / 31250000) := by
  have h := checkLog_sound (w := (5377 / 19623)) (n := 12)
    (lo := (562399659 / 1000000000)) (hi := (28119983 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7123) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 7123) = 1/(7123 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-104218387 / 31250000) (-3334988379 / 1000000000) (Real.log (7123 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1002928113 / 250000000) ≤ -Real.log (62500000000 / 3452586752341) ∧
    -Real.log (62500000000 / 3452586752341) ≤ (2005856229 / 500000000) := by
  have h := checkLog_sound (w := (1452586752341 / 5452586752341)) (n := 12)
    (lo := (68247069 / 125000000)) (hi := (545976553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3452586752341 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3452586752341 / 2000000000000) = 1/(62500000000 / 3452586752341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1002928113 / 250000000) (2005856229 / 500000000) (Real.log (3452586752341 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3452586752341 / 62500000000) = -Real.log (62500000000 / 3452586752341) := by
    rw [show ((3452586752341 / 62500000000) : ℝ) = ((62500000000 / 3452586752341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4019990781 / 1000000000) ≤ -Real.log (125000000000 / 6962574065149) ∧
    -Real.log (125000000000 / 6962574065149) ≤ (4019990787 / 1000000000) := by
  have h := checkLog_sound (w := (2962574065149 / 10962574065149)) (n := 12)
    (lo := (554254881 / 1000000000)) (hi := (277127441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6962574065149 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6962574065149 / 4000000000000) = 1/(125000000000 / 6962574065149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4019990781 / 1000000000) (4019990787 / 1000000000) (Real.log (6962574065149 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (6962574065149 / 125000000000) = -Real.log (125000000000 / 6962574065149) := by
    rw [show ((6962574065149 / 125000000000) : ℝ) = ((125000000000 / 6962574065149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2000898429 / 500000000) ≤ -Real.log (500000000000 / 27348171767523) ∧
    -Real.log (500000000000 / 27348171767523) ≤ (15632019 / 3906250) := by
  have h := checkLog_sound (w := (11348171767523 / 43348171767523)) (n := 12)
    (lo := (268030479 / 500000000)) (hi := (536060959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27348171767523 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(27348171767523 / 16000000000000) = 1/(500000000000 / 27348171767523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2000898429 / 500000000) (15632019 / 3906250) (Real.log (27348171767523 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (27348171767523 / 500000000000) = -Real.log (500000000000 / 27348171767523) := by
    rw [show ((27348171767523 / 500000000000) : ℝ) = ((500000000000 / 27348171767523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4010167597 / 1000000000) ≤ -Real.log (62500000000 / 3447257124807) ∧
    -Real.log (62500000000 / 3447257124807) ≤ (4010167603 / 1000000000) := by
  have h := checkLog_sound (w := (1447257124807 / 5447257124807)) (n := 12)
    (lo := (544431697 / 1000000000)) (hi := (272215849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3447257124807 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3447257124807 / 2000000000000) = 1/(62500000000 / 3447257124807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4010167597 / 1000000000) (4010167603 / 1000000000) (Real.log (3447257124807 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3447257124807 / 62500000000) = -Real.log (62500000000 / 3447257124807) := by
    rw [show ((3447257124807 / 62500000000) : ℝ) = ((62500000000 / 3447257124807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0100

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0101Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0101
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

theorem reflection_log_1_neg : (671219053 / 1000000000) ≤ -Real.log (51200 / 100179) ∧
    -Real.log (51200 / 100179) ≤ (335609527 / 500000000) := by
  have h := checkLog_sound (w := (48979 / 151379)) (n := 12)
    (lo := (671219053 / 1000000000)) (hi := (335609527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100179 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100179 / 51200) = 1/(51200 / 100179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (671219053 / 1000000000) (335609527 / 500000000) (Real.log (100179 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100179 / 51200) = -Real.log (51200 / 100179) := by
    rw [show ((100179 / 51200) : ℝ) = ((51200 / 100179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (98055687 / 31250000) ≤ -Real.log (2221 / 51200) ∧
    -Real.log (2221 / 51200) ≤ (3137781989 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 5421)) (n := 12)
    (lo := (22824579 / 62500000)) (hi := (73038653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2221) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2221) = 1/(2221 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3137781989 / 1000000000) (-98055687 / 31250000) (Real.log (2221 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (1073647 / 1600000) ≤ -Real.log (160 / 313) ∧
    -Real.log (160 / 313) ≤ (5242417 / 7812500) := by
  have h := checkLog_sound (w := (153 / 473)) (n := 12)
    (lo := (1073647 / 1600000)) (hi := (5242417 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313 / 160) = 1/(160 / 313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (1073647 / 1600000) (5242417 / 7812500) (Real.log (313 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (313 / 160) = -Real.log (160 / 313) := by
    rw [show ((313 / 160) : ℝ) = ((160 / 313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3129263663 / 1000000000) ≤ -Real.log (7 / 160) ∧
    -Real.log (7 / 160) ≤ (782315917 / 250000000) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10 / 7) = 1/(7 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-782315917 / 250000000) (-3129263663 / 1000000000) (Real.log (7 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (648799283 / 1000000000) ≤ -Real.log (25600 / 48979) ∧
    -Real.log (25600 / 48979) ≤ (162199821 / 250000000) := by
  have h := checkLog_sound (w := (23379 / 74579)) (n := 12)
    (lo := (648799283 / 1000000000)) (hi := (162199821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48979 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48979 / 25600) = 1/(25600 / 48979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (648799283 / 1000000000) (162199821 / 250000000) (Real.log (48979 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48979 / 25600) = -Real.log (25600 / 48979) := by
    rw [show ((48979 / 25600) : ℝ) = ((25600 / 48979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (611158701 / 250000000) ≤ -Real.log (2221 / 25600) ∧
    -Real.log (2221 / 25600) ≤ (305579351 / 125000000) := by
  have h := checkLog_sound (w := (979 / 5421)) (n := 12)
    (lo := (22824579 / 62500000)) (hi := (73038653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2221) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2221) = 1/(2221 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-305579351 / 125000000) (-611158701 / 250000000) (Real.log (2221 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (324205643 / 500000000) ≤ -Real.log (80 / 153) ∧
    -Real.log (80 / 153) ≤ (648411287 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 233)) (n := 12)
    (lo := (324205643 / 500000000)) (hi := (648411287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153 / 80) = 1/(80 / 153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (324205643 / 500000000) (648411287 / 1000000000) (Real.log (153 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (153 / 80) = -Real.log (80 / 153) := by
    rw [show ((153 / 80) : ℝ) = ((80 / 153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2436116483 / 1000000000) ≤ -Real.log (7 / 80) ∧
    -Real.log (7 / 80) ≤ (2436116487 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(10 / 7) = 1/(7 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2436116487 / 1000000000) (-2436116483 / 1000000000) (Real.log (7 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (675061109 / 1000000000) ≤ -Real.log (1000000 / 1964153) ∧
    -Real.log (1000000 / 1964153) ≤ (67506111 / 100000000) := by
  have h := checkLog_sound (w := (964153 / 2964153)) (n := 12)
    (lo := (675061109 / 1000000000)) (hi := (67506111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964153 / 1000000) = 1/(1000000 / 1964153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (675061109 / 1000000000) (67506111 / 100000000) (Real.log (1964153 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1964153 / 1000000) = -Real.log (1000000 / 1964153) := by
    rw [show ((1964153 / 1000000) : ℝ) = ((1000000 / 1964153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (665699079 / 200000000) ≤ -Real.log (35847 / 1000000) ∧
    -Real.log (35847 / 1000000) ≤ (16642477 / 5000000) := by
  have h := checkLog_sound (w := (26653 / 98347)) (n := 12)
    (lo := (22236267 / 40000000)) (hi := (138976669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35847) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35847) = 1/(35847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-16642477 / 5000000) (-665699079 / 200000000) (Real.log (35847 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (675207217 / 1000000000) ≤ -Real.log (25000 / 49111) ∧
    -Real.log (25000 / 49111) ≤ (337603609 / 500000000) := by
  have h := checkLog_sound (w := (24111 / 74111)) (n := 12)
    (lo := (675207217 / 1000000000)) (hi := (337603609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49111 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49111 / 25000) = 1/(25000 / 49111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (675207217 / 1000000000) (337603609 / 500000000) (Real.log (49111 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (49111 / 25000) = -Real.log (25000 / 49111) := by
    rw [show ((49111 / 25000) : ℝ) = ((25000 / 49111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1668266933 / 500000000) ≤ -Real.log (889 / 25000) ∧
    -Real.log (889 / 25000) ≤ (3336533871 / 1000000000) := by
  have h := checkLog_sound (w := (1347 / 4903)) (n := 12)
    (lo := (281972573 / 500000000)) (hi := (563945147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1778) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 1778) = 1/(889 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3336533871 / 1000000000) (-1668266933 / 500000000) (Real.log (889 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (337440431 / 500000000) ≤ -Real.log (1000000 / 1963799) ∧
    -Real.log (1000000 / 1963799) ≤ (674880863 / 1000000000) := by
  have h := checkLog_sound (w := (963799 / 2963799)) (n := 12)
    (lo := (337440431 / 500000000)) (hi := (674880863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963799 / 1000000) = 1/(1000000 / 1963799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (337440431 / 500000000) (674880863 / 1000000000) (Real.log (1963799 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1963799 / 1000000) = -Real.log (1000000 / 1963799) := by
    rw [show ((1963799 / 1000000) : ℝ) = ((1000000 / 1963799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3318668533 / 1000000000) ≤ -Real.log (36201 / 1000000) ∧
    -Real.log (36201 / 1000000) ≤ (1659334269 / 500000000) := by
  have h := checkLog_sound (w := (26299 / 98701)) (n := 12)
    (lo := (546079813 / 1000000000)) (hi := (273039907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36201) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36201) = 1/(36201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1659334269 / 500000000) (-3318668533 / 1000000000) (Real.log (36201 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (168757513 / 250000000) ≤ -Real.log (250000 / 491023) ∧
    -Real.log (250000 / 491023) ≤ (675030053 / 1000000000) := by
  have h := checkLog_sound (w := (241023 / 741023)) (n := 12)
    (lo := (168757513 / 250000000)) (hi := (675030053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491023 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491023 / 250000) = 1/(250000 / 491023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (168757513 / 250000000) (675030053 / 1000000000) (Real.log (491023 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (491023 / 250000) = -Real.log (250000 / 491023) := by
    rw [show ((491023 / 250000) : ℝ) = ((250000 / 491023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (831698791 / 250000000) ≤ -Real.log (8977 / 250000) ∧
    -Real.log (8977 / 250000) ≤ (3326795169 / 1000000000) := by
  have h := checkLog_sound (w := (3324 / 12301)) (n := 12)
    (lo := (138551611 / 250000000)) (hi := (110841289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8977) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8977) = 1/(8977 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3326795169 / 1000000000) (-831698791 / 250000000) (Real.log (8977 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4003556503 / 1000000000) ≤ -Real.log (125000000000 / 6849084302731) ∧
    -Real.log (125000000000 / 6849084302731) ≤ (4003556509 / 1000000000) := by
  have h := checkLog_sound (w := (2849084302731 / 10849084302731)) (n := 12)
    (lo := (537820603 / 1000000000)) (hi := (134455151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6849084302731 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6849084302731 / 4000000000000) = 1/(125000000000 / 6849084302731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4003556503 / 1000000000) (4003556509 / 1000000000) (Real.log (6849084302731 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6849084302731 / 125000000000) = -Real.log (125000000000 / 6849084302731) := by
    rw [show ((6849084302731 / 125000000000) : ℝ) = ((125000000000 / 6849084302731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2005870541 / 500000000) ≤ -Real.log (500000000000 / 27621484814399) ∧
    -Real.log (500000000000 / 27621484814399) ≤ (125366909 / 31250000) := by
  have h := checkLog_sound (w := (11621484814399 / 43621484814399)) (n := 12)
    (lo := (273002591 / 500000000)) (hi := (546005183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27621484814399 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(27621484814399 / 16000000000000) = 1/(500000000000 / 27621484814399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2005870541 / 500000000) (125366909 / 31250000) (Real.log (27621484814399 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (27621484814399 / 500000000000) = -Real.log (500000000000 / 27621484814399) := by
    rw [show ((27621484814399 / 500000000000) : ℝ) = ((500000000000 / 27621484814399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (798709879 / 200000000) ≤ -Real.log (4000000000 / 216988370487) ∧
    -Real.log (4000000000 / 216988370487) ≤ (3993549401 / 1000000000) := by
  have h := checkLog_sound (w := (88988370487 / 344988370487)) (n := 12)
    (lo := (105562699 / 200000000)) (hi := (65976687 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216988370487 / 128000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(216988370487 / 128000000000) = 1/(4000000000 / 216988370487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (798709879 / 200000000) (3993549401 / 1000000000) (Real.log (216988370487 / 4000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (216988370487 / 4000000000) = -Real.log (4000000000 / 216988370487) := by
    rw [show ((216988370487 / 4000000000) : ℝ) = ((4000000000 / 216988370487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (62528519 / 15625000) ≤ -Real.log (15625000000 / 854654603431) ∧
    -Real.log (15625000000 / 854654603431) ≤ (2000912611 / 500000000) := by
  have h := checkLog_sound (w := (354654603431 / 1354654603431)) (n := 12)
    (lo := (134022329 / 250000000)) (hi := (536089317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854654603431 / 500000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(854654603431 / 500000000000) = 1/(15625000000 / 854654603431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (62528519 / 15625000) (2000912611 / 500000000) (Real.log (854654603431 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (854654603431 / 15625000000) = -Real.log (15625000000 / 854654603431) := by
    rw [show ((854654603431 / 15625000000) : ℝ) = ((15625000000 / 854654603431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0101

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0102Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0102
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

theorem reflection_log_1_neg : (1073647 / 1600000) ≤ -Real.log (160 / 313) ∧
    -Real.log (160 / 313) ≤ (5242417 / 7812500) := by
  have h := checkLog_sound (w := (153 / 473)) (n := 12)
    (lo := (1073647 / 1600000)) (hi := (5242417 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313 / 160) = 1/(160 / 313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (1073647 / 1600000) (5242417 / 7812500) (Real.log (313 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (313 / 160) = -Real.log (160 / 313) := by
    rw [show ((313 / 160) : ℝ) = ((160 / 313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3129263663 / 1000000000) ≤ -Real.log (7 / 160) ∧
    -Real.log (7 / 160) ≤ (782315917 / 250000000) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10 / 7) = 1/(7 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-782315917 / 250000000) (-3129263663 / 1000000000) (Real.log (7 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33541983 / 50000000) ≤ -Real.log (51200 / 100141) ∧
    -Real.log (51200 / 100141) ≤ (670839661 / 1000000000) := by
  have h := checkLog_sound (w := (48941 / 151341)) (n := 12)
    (lo := (33541983 / 50000000)) (hi := (670839661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100141 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100141 / 51200) = 1/(51200 / 100141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33541983 / 50000000) (670839661 / 1000000000) (Real.log (100141 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100141 / 51200) = -Real.log (51200 / 100141) := by
    rw [show ((100141 / 51200) : ℝ) = ((51200 / 100141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (780204323 / 250000000) ≤ -Real.log (2259 / 51200) ∧
    -Real.log (2259 / 51200) ≤ (3120817297 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 5459)) (n := 12)
    (lo := (87057143 / 250000000)) (hi := (348228573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2259) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2259) = 1/(2259 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3120817297 / 1000000000) (-780204323 / 250000000) (Real.log (2259 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (324205643 / 500000000) ≤ -Real.log (80 / 153) ∧
    -Real.log (80 / 153) ≤ (648411287 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 233)) (n := 12)
    (lo := (324205643 / 500000000)) (hi := (648411287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153 / 80) = 1/(80 / 153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (324205643 / 500000000) (648411287 / 1000000000) (Real.log (153 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (153 / 80) = -Real.log (80 / 153) := by
    rw [show ((153 / 80) : ℝ) = ((80 / 153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2436116483 / 1000000000) ≤ -Real.log (7 / 80) ∧
    -Real.log (7 / 80) ≤ (2436116487 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(10 / 7) = 1/(7 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2436116487 / 1000000000) (-2436116483 / 1000000000) (Real.log (7 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (648023139 / 1000000000) ≤ -Real.log (25600 / 48941) ∧
    -Real.log (25600 / 48941) ≤ (32401157 / 50000000) := by
  have h := checkLog_sound (w := (23341 / 74541)) (n := 12)
    (lo := (648023139 / 1000000000)) (hi := (32401157 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48941 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48941 / 25600) = 1/(25600 / 48941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (648023139 / 1000000000) (32401157 / 50000000) (Real.log (48941 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48941 / 25600) = -Real.log (25600 / 48941) := by
    rw [show ((48941 / 25600) : ℝ) = ((25600 / 48941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (75864691 / 31250000) ≤ -Real.log (2259 / 25600) ∧
    -Real.log (2259 / 25600) ≤ (606917529 / 250000000) := by
  have h := checkLog_sound (w := (941 / 5459)) (n := 12)
    (lo := (87057143 / 250000000)) (hi := (348228573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2259) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2259) = 1/(2259 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-606917529 / 250000000) (-75864691 / 31250000) (Real.log (2259 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (674915997 / 1000000000) ≤ -Real.log (250000 / 490967) ∧
    -Real.log (250000 / 490967) ≤ (337457999 / 500000000) := by
  have h := checkLog_sound (w := (240967 / 740967)) (n := 12)
    (lo := (674915997 / 1000000000)) (hi := (337457999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490967 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490967 / 250000) = 1/(250000 / 490967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (674915997 / 1000000000) (337457999 / 500000000) (Real.log (490967 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (490967 / 250000) = -Real.log (250000 / 490967) := by
    rw [show ((490967 / 250000) : ℝ) = ((250000 / 490967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3320576377 / 1000000000) ≤ -Real.log (9033 / 250000) ∧
    -Real.log (9033 / 250000) ≤ (1660288191 / 500000000) := by
  have h := checkLog_sound (w := (3296 / 12329)) (n := 12)
    (lo := (547987657 / 1000000000)) (hi := (273993829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9033) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 9033) = 1/(9033 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1660288191 / 500000000) (-3320576377 / 1000000000) (Real.log (9033 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (337530809 / 500000000) ≤ -Real.log (500000 / 982077) ∧
    -Real.log (500000 / 982077) ≤ (675061619 / 1000000000) := by
  have h := checkLog_sound (w := (482077 / 1482077)) (n := 12)
    (lo := (337530809 / 500000000)) (hi := (675061619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982077 / 500000) = 1/(500000 / 982077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (337530809 / 500000000) (675061619 / 1000000000) (Real.log (982077 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (982077 / 500000) = -Real.log (500000 / 982077) := by
    rw [show ((982077 / 500000) : ℝ) = ((500000 / 982077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3328523291 / 1000000000) ≤ -Real.log (17923 / 500000) ∧
    -Real.log (17923 / 500000) ≤ (104016353 / 31250000) := by
  have h := checkLog_sound (w := (13327 / 49173)) (n := 12)
    (lo := (555934571 / 1000000000)) (hi := (138983643 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17923) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 17923) = 1/(17923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-104016353 / 31250000) (-3328523291 / 1000000000) (Real.log (17923 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13494633 / 20000000) ≤ -Real.log (500000 / 981753) ∧
    -Real.log (500000 / 981753) ≤ (674731651 / 1000000000) := by
  have h := checkLog_sound (w := (481753 / 1481753)) (n := 12)
    (lo := (13494633 / 20000000)) (hi := (674731651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981753 / 500000) = 1/(500000 / 981753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13494633 / 20000000) (674731651 / 1000000000) (Real.log (981753 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (981753 / 500000) = -Real.log (500000 / 981753) := by
    rw [show ((981753 / 500000) : ℝ) = ((500000 / 981753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3310607413 / 1000000000) ≤ -Real.log (18247 / 500000) ∧
    -Real.log (18247 / 500000) ≤ (1655303709 / 500000000) := by
  have h := checkLog_sound (w := (13003 / 49497)) (n := 12)
    (lo := (538018693 / 1000000000)) (hi := (269009347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18247) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18247) = 1/(18247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1655303709 / 500000000) (-3310607413 / 1000000000) (Real.log (18247 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (674881371 / 1000000000) ≤ -Real.log (5000 / 9819) ∧
    -Real.log (5000 / 9819) ≤ (168720343 / 250000000) := by
  have h := checkLog_sound (w := (4819 / 14819)) (n := 12)
    (lo := (674881371 / 1000000000)) (hi := (168720343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9819 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9819 / 5000) = 1/(5000 / 9819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (674881371 / 1000000000) (168720343 / 250000000) (Real.log (9819 / 5000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (9819 / 5000) = -Real.log (5000 / 9819) := by
    rw [show ((9819 / 5000) : ℝ) = ((5000 / 9819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3318696157 / 1000000000) ≤ -Real.log (181 / 5000) ∧
    -Real.log (181 / 5000) ≤ (1659348081 / 500000000) := by
  have h := checkLog_sound (w := (263 / 987)) (n := 12)
    (lo := (546107437 / 1000000000)) (hi := (273053719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 362) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625 / 362) = 1/(181 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1659348081 / 500000000) (-3318696157 / 1000000000) (Real.log (181 / 5000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1997746187 / 500000000) ≤ -Real.log (500000000000 / 27176298018377) ∧
    -Real.log (500000000000 / 27176298018377) ≤ (199774619 / 50000000) := by
  have h := checkLog_sound (w := (11176298018377 / 43176298018377)) (n := 12)
    (lo := (264878237 / 500000000)) (hi := (21190259 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27176298018377 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(27176298018377 / 16000000000000) = 1/(500000000000 / 27176298018377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1997746187 / 500000000) (199774619 / 50000000) (Real.log (27176298018377 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (27176298018377 / 500000000000) = -Real.log (500000000000 / 27176298018377) := by
    rw [show ((27176298018377 / 500000000000) : ℝ) = ((500000000000 / 27176298018377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4003584909 / 1000000000) ≤ -Real.log (62500000000 / 3424639429783) ∧
    -Real.log (62500000000 / 3424639429783) ≤ (800716983 / 200000000) := by
  have h := checkLog_sound (w := (1424639429783 / 5424639429783)) (n := 12)
    (lo := (537849009 / 1000000000)) (hi := (53784901 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3424639429783 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3424639429783 / 2000000000000) = 1/(62500000000 / 3424639429783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4003584909 / 1000000000) (800716983 / 200000000) (Real.log (3424639429783 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3424639429783 / 62500000000) = -Real.log (62500000000 / 3424639429783) := by
    rw [show ((3424639429783 / 62500000000) : ℝ) = ((62500000000 / 3424639429783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3985339063 / 1000000000) ≤ -Real.log (125000000000 / 6725441168411) ∧
    -Real.log (125000000000 / 6725441168411) ≤ (3985339069 / 1000000000) := by
  have h := checkLog_sound (w := (2725441168411 / 10725441168411)) (n := 12)
    (lo := (519603163 / 1000000000)) (hi := (129900791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6725441168411 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6725441168411 / 4000000000000) = 1/(125000000000 / 6725441168411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3985339063 / 1000000000) (3985339069 / 1000000000) (Real.log (6725441168411 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6725441168411 / 125000000000) = -Real.log (125000000000 / 6725441168411) := by
    rw [show ((6725441168411 / 125000000000) : ℝ) = ((125000000000 / 6725441168411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3993577529 / 1000000000) ≤ -Real.log (250000000000 / 13562154696133) ∧
    -Real.log (250000000000 / 13562154696133) ≤ (798715507 / 200000000) := by
  have h := checkLog_sound (w := (5562154696133 / 21562154696133)) (n := 12)
    (lo := (527841629 / 1000000000)) (hi := (52784163 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13562154696133 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13562154696133 / 8000000000000) = 1/(250000000000 / 13562154696133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3993577529 / 1000000000) (798715507 / 200000000) (Real.log (13562154696133 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13562154696133 / 250000000000) = -Real.log (250000000000 / 13562154696133) := by
    rw [show ((13562154696133 / 250000000000) : ℝ) = ((250000000000 / 13562154696133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0102

end


