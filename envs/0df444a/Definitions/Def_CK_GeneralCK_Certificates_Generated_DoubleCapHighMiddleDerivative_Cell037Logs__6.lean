-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell037Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell037Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:51:16.273816+00:00
-- url     : https://prove2.me/theorems/23d7d36e-ba68-4d12-b764-fd3cf3aa5cf0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell037Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell038…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell037Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell038Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell039Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell040Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell041Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell042Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell037Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell038Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell039Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell040Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell041Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell042Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell037Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell038Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell039Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell040Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell041Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell042Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell037Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell038Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell039Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell040Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell041Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell042Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell037Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell037
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

theorem reflection_log_1_neg : (240799267 / 1000000000) ≤ -Real.log (2560 / 3257) ∧
    -Real.log (2560 / 3257) ≤ (60199817 / 250000000) := by
  have h := checkLog_sound (w := (697 / 5817)) (n := 12)
    (lo := (240799267 / 1000000000)) (hi := (60199817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3257 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3257 / 2560) = 1/(2560 / 3257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (240799267 / 1000000000) (60199817 / 250000000) (Real.log (3257 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3257 / 2560) = -Real.log (2560 / 3257) := by
    rw [show ((3257 / 2560) : ℝ) = ((2560 / 3257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (158909583 / 500000000) ≤ -Real.log (1863 / 2560) ∧
    -Real.log (1863 / 2560) ≤ (317819167 / 1000000000) := by
  have h := checkLog_sound (w := (697 / 4423)) (n := 12)
    (lo := (158909583 / 500000000)) (hi := (317819167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1863) = 1/(1863 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-317819167 / 1000000000) (-158909583 / 500000000) (Real.log (1863 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (48067723 / 200000000) ≤ -Real.log (5120 / 6511) ∧
    -Real.log (5120 / 6511) ≤ (30042327 / 125000000) := by
  have h := checkLog_sound (w := (1391 / 11631)) (n := 12)
    (lo := (48067723 / 200000000)) (hi := (30042327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6511 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6511 / 5120) = 1/(5120 / 6511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (48067723 / 200000000) (30042327 / 125000000) (Real.log (6511 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6511 / 5120) = -Real.log (5120 / 6511) := by
    rw [show ((6511 / 5120) : ℝ) = ((5120 / 6511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (317014337 / 1000000000) ≤ -Real.log (3729 / 5120) ∧
    -Real.log (3729 / 5120) ≤ (158507169 / 500000000) := by
  have h := checkLog_sound (w := (1391 / 8849)) (n := 12)
    (lo := (317014337 / 1000000000)) (hi := (158507169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3729) = 1/(3729 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-158507169 / 500000000) (-317014337 / 1000000000) (Real.log (3729 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (176233059 / 1000000000) ≤ -Real.log (250000 / 298179) ∧
    -Real.log (250000 / 298179) ≤ (8811653 / 50000000) := by
  have h := checkLog_sound (w := (48179 / 548179)) (n := 12)
    (lo := (176233059 / 1000000000)) (hi := (8811653 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298179 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298179 / 250000) = 1/(250000 / 298179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (176233059 / 1000000000) (8811653 / 50000000) (Real.log (298179 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (298179 / 250000) = -Real.log (250000 / 298179) := by
    rw [show ((298179 / 250000) : ℝ) = ((250000 / 298179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (214079751 / 1000000000) ≤ -Real.log (201821 / 250000) ∧
    -Real.log (201821 / 250000) ≤ (26759969 / 125000000) := by
  have h := checkLog_sound (w := (48179 / 451821)) (n := 12)
    (lo := (214079751 / 1000000000)) (hi := (26759969 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201821) = 1/(201821 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26759969 / 125000000) (-214079751 / 1000000000) (Real.log (201821 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (22073037 / 125000000) ≤ -Real.log (200000 / 238627) ∧
    -Real.log (200000 / 238627) ≤ (176584297 / 1000000000) := by
  have h := checkLog_sound (w := (38627 / 438627)) (n := 12)
    (lo := (22073037 / 125000000)) (hi := (176584297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238627 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238627 / 200000) = 1/(200000 / 238627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (22073037 / 125000000) (176584297 / 1000000000) (Real.log (238627 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (238627 / 200000) = -Real.log (200000 / 238627) := by
    rw [show ((238627 / 200000) : ℝ) = ((200000 / 238627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (21459891 / 100000000) ≤ -Real.log (161373 / 200000) ∧
    -Real.log (161373 / 200000) ≤ (214598911 / 1000000000) := by
  have h := checkLog_sound (w := (38627 / 361373)) (n := 12)
    (lo := (21459891 / 100000000)) (hi := (214598911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 161373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 161373) = 1/(161373 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-214598911 / 1000000000) (-21459891 / 100000000) (Real.log (161373 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32249533 / 250000000) ≤ -Real.log (125000 / 142211) ∧
    -Real.log (125000 / 142211) ≤ (128998133 / 1000000000) := by
  have h := checkLog_sound (w := (17211 / 267211)) (n := 12)
    (lo := (32249533 / 250000000)) (hi := (128998133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142211 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142211 / 125000) = 1/(125000 / 142211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32249533 / 250000000) (128998133 / 1000000000) (Real.log (142211 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (142211 / 125000) = -Real.log (125000 / 142211) := by
    rw [show ((142211 / 125000) : ℝ) = ((125000 / 142211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (37034531 / 250000000) ≤ -Real.log (107789 / 125000) ∧
    -Real.log (107789 / 125000) ≤ (237021 / 1600000) := by
  have h := checkLog_sound (w := (17211 / 232789)) (n := 12)
    (lo := (37034531 / 250000000)) (hi := (237021 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107789) = 1/(107789 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-237021 / 1600000) (-37034531 / 250000000) (Real.log (107789 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (129267063 / 1000000000) ≤ -Real.log (500000 / 568997) ∧
    -Real.log (500000 / 568997) ≤ (16158383 / 125000000) := by
  have h := checkLog_sound (w := (68997 / 1068997)) (n := 12)
    (lo := (129267063 / 1000000000)) (hi := (16158383 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568997 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(568997 / 500000) = 1/(500000 / 568997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (129267063 / 1000000000) (16158383 / 125000000) (Real.log (568997 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (568997 / 500000) = -Real.log (500000 / 568997) := by
    rw [show ((568997 / 500000) : ℝ) = ((500000 / 568997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (148493047 / 1000000000) ≤ -Real.log (431003 / 500000) ∧
    -Real.log (431003 / 500000) ≤ (18561631 / 125000000) := by
  have h := checkLog_sound (w := (68997 / 931003)) (n := 12)
    (lo := (148493047 / 1000000000)) (hi := (18561631 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 431003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 431003) = 1/(431003 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-18561631 / 125000000) (-148493047 / 1000000000) (Real.log (431003 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (557352953 / 1000000000) ≤ -Real.log (250000000000 / 436511128989) ∧
    -Real.log (250000000000 / 436511128989) ≤ (278676477 / 500000000) := by
  have h := checkLog_sound (w := (186511128989 / 686511128989)) (n := 12)
    (lo := (557352953 / 1000000000)) (hi := (278676477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((436511128989 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(436511128989 / 250000000000) = 1/(250000000000 / 436511128989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (557352953 / 1000000000) (278676477 / 500000000) (Real.log (436511128989 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (436511128989 / 250000000000) = -Real.log (250000000000 / 436511128989) := by
    rw [show ((436511128989 / 250000000000) : ℝ) = ((250000000000 / 436511128989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (279309217 / 500000000) ≤ -Real.log (25000000000 / 43706387547) ∧
    -Real.log (25000000000 / 43706387547) ≤ (111723687 / 200000000) := by
  have h := checkLog_sound (w := (18706387547 / 68706387547)) (n := 12)
    (lo := (279309217 / 500000000)) (hi := (111723687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43706387547 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43706387547 / 25000000000) = 1/(25000000000 / 43706387547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (279309217 / 500000000) (111723687 / 200000000) (Real.log (43706387547 / 25000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (43706387547 / 25000000000) = -Real.log (25000000000 / 43706387547) := by
    rw [show ((43706387547 / 25000000000) : ℝ) = ((25000000000 / 43706387547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (390312811 / 1000000000) ≤ -Real.log (500000000000 / 738721441277) ∧
    -Real.log (500000000000 / 738721441277) ≤ (97578203 / 250000000) := by
  have h := checkLog_sound (w := (238721441277 / 1238721441277)) (n := 12)
    (lo := (390312811 / 1000000000)) (hi := (97578203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738721441277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738721441277 / 500000000000) = 1/(500000000000 / 738721441277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (390312811 / 1000000000) (97578203 / 250000000) (Real.log (738721441277 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (738721441277 / 500000000000) = -Real.log (500000000000 / 738721441277) := by
    rw [show ((738721441277 / 500000000000) : ℝ) = ((500000000000 / 738721441277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (391183207 / 1000000000) ≤ -Real.log (250000000000 / 369682350827) ∧
    -Real.log (250000000000 / 369682350827) ≤ (48897901 / 125000000) := by
  have h := checkLog_sound (w := (119682350827 / 619682350827)) (n := 12)
    (lo := (391183207 / 1000000000)) (hi := (48897901 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369682350827 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369682350827 / 250000000000) = 1/(250000000000 / 369682350827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (391183207 / 1000000000) (48897901 / 125000000) (Real.log (369682350827 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (369682350827 / 250000000000) = -Real.log (250000000000 / 369682350827) := by
    rw [show ((369682350827 / 250000000000) : ℝ) = ((250000000000 / 369682350827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (277136257 / 1000000000) ≤ -Real.log (500000000000 / 659673064969) ∧
    -Real.log (500000000000 / 659673064969) ≤ (138568129 / 500000000) := by
  have h := checkLog_sound (w := (159673064969 / 1159673064969)) (n := 12)
    (lo := (277136257 / 1000000000)) (hi := (138568129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659673064969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659673064969 / 500000000000) = 1/(500000000000 / 659673064969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (277136257 / 1000000000) (138568129 / 500000000) (Real.log (659673064969 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (659673064969 / 500000000000) = -Real.log (500000000000 / 659673064969) := by
    rw [show ((659673064969 / 500000000000) : ℝ) = ((500000000000 / 659673064969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (277760111 / 1000000000) ≤ -Real.log (500000000000 / 660084732589) ∧
    -Real.log (500000000000 / 660084732589) ≤ (17360007 / 62500000) := by
  have h := checkLog_sound (w := (160084732589 / 1160084732589)) (n := 12)
    (lo := (277760111 / 1000000000)) (hi := (17360007 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660084732589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660084732589 / 500000000000) = 1/(500000000000 / 660084732589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (277760111 / 1000000000) (17360007 / 62500000) (Real.log (660084732589 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (660084732589 / 500000000000) = -Real.log (500000000000 / 660084732589) := by
    rw [show ((660084732589 / 500000000000) : ℝ) = ((500000000000 / 660084732589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (150203 / 7812500) ≤ -Real.log (245239413991 / 250000000000) ∧
    -Real.log (245239413991 / 250000000000) ≤ (3845197 / 200000000) := by
  have h := checkLog_sound (w := (4760586009 / 495239413991)) (n := 12)
    (lo := (150203 / 7812500)) (hi := (3845197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245239413991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245239413991) = 1/(245239413991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3845197 / 200000000) (-150203 / 7812500) (Real.log (245239413991 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19139991 / 1000000000) ≤ -Real.log (15328781479 / 15625000000) ∧
    -Real.log (15328781479 / 15625000000) ≤ (2392499 / 125000000) := by
  have h := checkLog_sound (w := (296218521 / 30953781479)) (n := 12)
    (lo := (19139991 / 1000000000)) (hi := (2392499 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15328781479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15328781479) = 1/(15328781479 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2392499 / 125000000) (-19139991 / 1000000000) (Real.log (15328781479 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell037

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell038Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell038
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

theorem reflection_log_1_neg : (60314927 / 250000000) ≤ -Real.log (5120 / 6517) ∧
    -Real.log (5120 / 6517) ≤ (241259709 / 1000000000) := by
  have h := checkLog_sound (w := (1397 / 11637)) (n := 12)
    (lo := (60314927 / 250000000)) (hi := (241259709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6517 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6517 / 5120) = 1/(5120 / 6517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (60314927 / 250000000) (241259709 / 1000000000) (Real.log (6517 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6517 / 5120) = -Real.log (5120 / 6517) := by
    rw [show ((6517 / 5120) : ℝ) = ((5120 / 6517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (79656161 / 250000000) ≤ -Real.log (3723 / 5120) ∧
    -Real.log (3723 / 5120) ≤ (63724929 / 200000000) := by
  have h := checkLog_sound (w := (1397 / 8843)) (n := 12)
    (lo := (79656161 / 250000000)) (hi := (63724929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3723) = 1/(3723 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-63724929 / 200000000) (-79656161 / 250000000) (Real.log (3723 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (240799267 / 1000000000) ≤ -Real.log (2560 / 3257) ∧
    -Real.log (2560 / 3257) ≤ (60199817 / 250000000) := by
  have h := checkLog_sound (w := (697 / 5817)) (n := 12)
    (lo := (240799267 / 1000000000)) (hi := (60199817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3257 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3257 / 2560) = 1/(2560 / 3257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (240799267 / 1000000000) (60199817 / 250000000) (Real.log (3257 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3257 / 2560) = -Real.log (2560 / 3257) := by
    rw [show ((3257 / 2560) : ℝ) = ((2560 / 3257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (158909583 / 500000000) ≤ -Real.log (1863 / 2560) ∧
    -Real.log (1863 / 2560) ≤ (317819167 / 1000000000) := by
  have h := checkLog_sound (w := (697 / 4423)) (n := 12)
    (lo := (158909583 / 500000000)) (hi := (317819167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1863) = 1/(1863 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-317819167 / 1000000000) (-158909583 / 500000000) (Real.log (1863 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (88291729 / 500000000) ≤ -Real.log (500000 / 596567) ∧
    -Real.log (500000 / 596567) ≤ (176583459 / 1000000000) := by
  have h := checkLog_sound (w := (96567 / 1096567)) (n := 12)
    (lo := (88291729 / 500000000)) (hi := (176583459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596567 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596567 / 500000) = 1/(500000 / 596567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (88291729 / 500000000) (176583459 / 1000000000) (Real.log (596567 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (596567 / 500000) = -Real.log (500000 / 596567) := by
    rw [show ((596567 / 500000) : ℝ) = ((500000 / 596567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (214597671 / 1000000000) ≤ -Real.log (403433 / 500000) ∧
    -Real.log (403433 / 500000) ≤ (26824709 / 125000000) := by
  have h := checkLog_sound (w := (96567 / 903433)) (n := 12)
    (lo := (214597671 / 1000000000)) (hi := (26824709 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403433) = 1/(403433 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26824709 / 125000000) (-214597671 / 1000000000) (Real.log (403433 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (176934573 / 1000000000) ≤ -Real.log (1000000 / 1193553) ∧
    -Real.log (1000000 / 1193553) ≤ (88467287 / 500000000) := by
  have h := checkLog_sound (w := (193553 / 2193553)) (n := 12)
    (lo := (176934573 / 1000000000)) (hi := (88467287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193553 / 1000000) = 1/(1000000 / 1193553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (176934573 / 1000000000) (88467287 / 500000000) (Real.log (1193553 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1193553 / 1000000) = -Real.log (1000000 / 1193553) := by
    rw [show ((1193553 / 1000000) : ℝ) = ((1000000 / 1193553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (215117099 / 1000000000) ≤ -Real.log (806447 / 1000000) ∧
    -Real.log (806447 / 1000000) ≤ (2151171 / 10000000) := by
  have h := checkLog_sound (w := (193553 / 1806447)) (n := 12)
    (lo := (215117099 / 1000000000)) (hi := (2151171 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806447) = 1/(806447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2151171 / 10000000) (-215117099 / 1000000000) (Real.log (806447 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16158273 / 125000000) ≤ -Real.log (1000000 / 1137993) ∧
    -Real.log (1000000 / 1137993) ≤ (25853237 / 200000000) := by
  have h := checkLog_sound (w := (137993 / 2137993)) (n := 12)
    (lo := (16158273 / 125000000)) (hi := (25853237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137993 / 1000000) = 1/(1000000 / 1137993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16158273 / 125000000) (25853237 / 200000000) (Real.log (1137993 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1137993 / 1000000) = -Real.log (1000000 / 1137993) := by
    rw [show ((1137993 / 1000000) : ℝ) = ((1000000 / 1137993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (148491887 / 1000000000) ≤ -Real.log (862007 / 1000000) ∧
    -Real.log (862007 / 1000000) ≤ (9280743 / 62500000) := by
  have h := checkLog_sound (w := (137993 / 1862007)) (n := 12)
    (lo := (148491887 / 1000000000)) (hi := (9280743 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862007) = 1/(862007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9280743 / 62500000) (-148491887 / 1000000000) (Real.log (862007 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64767521 / 500000000) ≤ -Real.log (1000000 / 1138299) ∧
    -Real.log (1000000 / 1138299) ≤ (129535043 / 1000000000) := by
  have h := checkLog_sound (w := (138299 / 2138299)) (n := 12)
    (lo := (64767521 / 500000000)) (hi := (129535043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138299 / 1000000) = 1/(1000000 / 1138299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64767521 / 500000000) (129535043 / 1000000000) (Real.log (1138299 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1138299 / 1000000) = -Real.log (1000000 / 1138299) := by
    rw [show ((1138299 / 1000000) : ℝ) = ((1000000 / 1138299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18605867 / 125000000) ≤ -Real.log (861701 / 1000000) ∧
    -Real.log (861701 / 1000000) ≤ (148846937 / 1000000000) := by
  have h := checkLog_sound (w := (138299 / 1861701)) (n := 12)
    (lo := (18605867 / 125000000)) (hi := (148846937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861701) = 1/(861701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-148846937 / 1000000000) (-18605867 / 125000000) (Real.log (861701 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (279309217 / 500000000) ≤ -Real.log (500000000000 / 874127750939) ∧
    -Real.log (500000000000 / 874127750939) ≤ (111723687 / 200000000) := by
  have h := checkLog_sound (w := (374127750939 / 1374127750939)) (n := 12)
    (lo := (279309217 / 500000000)) (hi := (111723687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((874127750939 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(874127750939 / 500000000000) = 1/(500000000000 / 874127750939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (279309217 / 500000000) (111723687 / 200000000) (Real.log (874127750939 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (874127750939 / 500000000000) = -Real.log (500000000000 / 874127750939) := by
    rw [show ((874127750939 / 500000000000) : ℝ) = ((500000000000 / 874127750939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (8748193 / 15625000) ≤ -Real.log (250000000000 / 437617512759) ∧
    -Real.log (250000000000 / 437617512759) ≤ (559884353 / 1000000000) := by
  have h := checkLog_sound (w := (187617512759 / 687617512759)) (n := 12)
    (lo := (8748193 / 15625000)) (hi := (559884353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437617512759 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437617512759 / 250000000000) = 1/(250000000000 / 437617512759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (8748193 / 15625000) (559884353 / 1000000000) (Real.log (437617512759 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (437617512759 / 250000000000) = -Real.log (250000000000 / 437617512759) := by
    rw [show ((437617512759 / 250000000000) : ℝ) = ((250000000000 / 437617512759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (39118113 / 100000000) ≤ -Real.log (50000000000 / 73936316563) ∧
    -Real.log (50000000000 / 73936316563) ≤ (391181131 / 1000000000) := by
  have h := checkLog_sound (w := (23936316563 / 123936316563)) (n := 12)
    (lo := (39118113 / 100000000)) (hi := (391181131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73936316563 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73936316563 / 50000000000) = 1/(50000000000 / 73936316563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (39118113 / 100000000) (391181131 / 1000000000) (Real.log (73936316563 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (73936316563 / 50000000000) = -Real.log (50000000000 / 73936316563) := by
    rw [show ((73936316563 / 50000000000) : ℝ) = ((50000000000 / 73936316563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (49006459 / 125000000) ≤ -Real.log (500000000000 / 740007092841) ∧
    -Real.log (500000000000 / 740007092841) ≤ (392051673 / 1000000000) := by
  have h := checkLog_sound (w := (240007092841 / 1240007092841)) (n := 12)
    (lo := (49006459 / 125000000)) (hi := (392051673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740007092841 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740007092841 / 500000000000) = 1/(500000000000 / 740007092841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (49006459 / 125000000) (392051673 / 1000000000) (Real.log (740007092841 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (740007092841 / 500000000000) = -Real.log (500000000000 / 740007092841) := by
    rw [show ((740007092841 / 500000000000) : ℝ) = ((500000000000 / 740007092841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (34719759 / 125000000) ≤ -Real.log (500000000000 / 660083386793) ∧
    -Real.log (500000000000 / 660083386793) ≤ (277758073 / 1000000000) := by
  have h := checkLog_sound (w := (160083386793 / 1160083386793)) (n := 12)
    (lo := (34719759 / 125000000)) (hi := (277758073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660083386793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660083386793 / 500000000000) = 1/(500000000000 / 660083386793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (34719759 / 125000000) (277758073 / 1000000000) (Real.log (660083386793 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (660083386793 / 500000000000) = -Real.log (500000000000 / 660083386793) := by
    rw [show ((660083386793 / 500000000000) : ℝ) = ((500000000000 / 660083386793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (278381979 / 1000000000) ≤ -Real.log (250000000000 / 330247672917) ∧
    -Real.log (250000000000 / 330247672917) ≤ (13919099 / 50000000) := by
  have h := checkLog_sound (w := (80247672917 / 580247672917)) (n := 12)
    (lo := (278381979 / 1000000000)) (hi := (13919099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330247672917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330247672917 / 250000000000) = 1/(250000000000 / 330247672917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (278381979 / 1000000000) (13919099 / 50000000) (Real.log (330247672917 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (330247672917 / 250000000000) = -Real.log (250000000000 / 330247672917) := by
    rw [show ((330247672917 / 250000000000) : ℝ) = ((250000000000 / 330247672917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (19311893 / 1000000000) ≤ -Real.log (980873386599 / 1000000000000) ∧
    -Real.log (980873386599 / 1000000000000) ≤ (9655947 / 500000000) := by
  have h := checkLog_sound (w := (19126613401 / 1980873386599)) (n := 12)
    (lo := (19311893 / 1000000000)) (hi := (9655947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980873386599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980873386599) = 1/(980873386599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9655947 / 500000000) (-19311893 / 1000000000) (Real.log (980873386599 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19225703 / 1000000000) ≤ -Real.log (980957931951 / 1000000000000) ∧
    -Real.log (980957931951 / 1000000000000) ≤ (2403213 / 125000000) := by
  have h := checkLog_sound (w := (19042068049 / 1980957931951)) (n := 12)
    (lo := (19225703 / 1000000000)) (hi := (2403213 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980957931951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980957931951) = 1/(980957931951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2403213 / 125000000) (-19225703 / 1000000000) (Real.log (980957931951 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell038

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell039Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell039
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

theorem reflection_log_1_neg : (1888437 / 7812500) ≤ -Real.log (128 / 163) ∧
    -Real.log (128 / 163) ≤ (241719937 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 291)) (n := 12)
    (lo := (1888437 / 7812500)) (hi := (241719937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163 / 128) = 1/(128 / 163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (1888437 / 7812500) (241719937 / 1000000000) (Real.log (163 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (163 / 128) = -Real.log (128 / 163) := by
    rw [show ((163 / 128) : ℝ) = ((128 / 163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (31943077 / 100000000) ≤ -Real.log (93 / 128) ∧
    -Real.log (93 / 128) ≤ (319430771 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 221)) (n := 12)
    (lo := (31943077 / 100000000)) (hi := (319430771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 93) = 1/(93 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-319430771 / 1000000000) (-31943077 / 100000000) (Real.log (93 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (60314927 / 250000000) ≤ -Real.log (5120 / 6517) ∧
    -Real.log (5120 / 6517) ≤ (241259709 / 1000000000) := by
  have h := checkLog_sound (w := (1397 / 11637)) (n := 12)
    (lo := (60314927 / 250000000)) (hi := (241259709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6517 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6517 / 5120) = 1/(5120 / 6517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (60314927 / 250000000) (241259709 / 1000000000) (Real.log (6517 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6517 / 5120) = -Real.log (5120 / 6517) := by
    rw [show ((6517 / 5120) : ℝ) = ((5120 / 6517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (79656161 / 250000000) ≤ -Real.log (3723 / 5120) ∧
    -Real.log (3723 / 5120) ≤ (63724929 / 200000000) := by
  have h := checkLog_sound (w := (1397 / 8843)) (n := 12)
    (lo := (79656161 / 250000000)) (hi := (63724929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3723) = 1/(3723 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-63724929 / 200000000) (-79656161 / 250000000) (Real.log (3723 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (35386747 / 200000000) ≤ -Real.log (62500 / 74597) ∧
    -Real.log (62500 / 74597) ≤ (22116717 / 125000000) := by
  have h := checkLog_sound (w := (12097 / 137097)) (n := 12)
    (lo := (35386747 / 200000000)) (hi := (22116717 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74597 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74597 / 62500) = 1/(62500 / 74597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (35386747 / 200000000) (22116717 / 125000000) (Real.log (74597 / 62500)) := by
  have h := reflection_log_5_neg
  have he : Real.log (74597 / 62500) = -Real.log (62500 / 74597) := by
    rw [show ((74597 / 62500) : ℝ) = ((62500 / 74597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (215115859 / 1000000000) ≤ -Real.log (50403 / 62500) ∧
    -Real.log (50403 / 62500) ≤ (10755793 / 50000000) := by
  have h := checkLog_sound (w := (12097 / 112903)) (n := 12)
    (lo := (215115859 / 1000000000)) (hi := (10755793 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 50403) = 1/(50403 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-10755793 / 50000000) (-215115859 / 1000000000) (Real.log (50403 / 62500)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (44321391 / 250000000) ≤ -Real.log (250000 / 298493) ∧
    -Real.log (250000 / 298493) ≤ (35457113 / 200000000) := by
  have h := checkLog_sound (w := (48493 / 548493)) (n := 12)
    (lo := (44321391 / 250000000)) (hi := (35457113 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298493 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298493 / 250000) = 1/(250000 / 298493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (44321391 / 250000000) (35457113 / 200000000) (Real.log (298493 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (298493 / 250000) = -Real.log (250000 / 298493) := by
    rw [show ((298493 / 250000) : ℝ) = ((250000 / 298493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (215636797 / 1000000000) ≤ -Real.log (201507 / 250000) ∧
    -Real.log (201507 / 250000) ≤ (107818399 / 500000000) := by
  have h := checkLog_sound (w := (48493 / 451507)) (n := 12)
    (lo := (215636797 / 1000000000)) (hi := (107818399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201507) = 1/(201507 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-107818399 / 500000000) (-215636797 / 1000000000) (Real.log (201507 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32383541 / 250000000) ≤ -Real.log (500000 / 569149) ∧
    -Real.log (500000 / 569149) ≤ (25906833 / 200000000) := by
  have h := checkLog_sound (w := (69149 / 1069149)) (n := 12)
    (lo := (32383541 / 250000000)) (hi := (25906833 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569149 / 500000) = 1/(500000 / 569149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32383541 / 250000000) (25906833 / 200000000) (Real.log (569149 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (569149 / 500000) = -Real.log (500000 / 569149) := by
    rw [show ((569149 / 500000) : ℝ) = ((500000 / 569149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (5953831 / 40000000) ≤ -Real.log (430851 / 500000) ∧
    -Real.log (430851 / 500000) ≤ (9302861 / 62500000) := by
  have h := checkLog_sound (w := (69149 / 930851)) (n := 12)
    (lo := (5953831 / 40000000)) (hi := (9302861 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 430851) = 1/(430851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9302861 / 62500000) (-5953831 / 40000000) (Real.log (430851 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (2596059 / 20000000) ≤ -Real.log (250000 / 284651) ∧
    -Real.log (250000 / 284651) ≤ (129802951 / 1000000000) := by
  have h := checkLog_sound (w := (34651 / 534651)) (n := 12)
    (lo := (2596059 / 20000000)) (hi := (129802951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284651 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284651 / 250000) = 1/(250000 / 284651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (2596059 / 20000000) (129802951 / 1000000000) (Real.log (284651 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (284651 / 250000) = -Real.log (250000 / 284651) := by
    rw [show ((284651 / 250000) : ℝ) = ((250000 / 284651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (149200949 / 1000000000) ≤ -Real.log (215349 / 250000) ∧
    -Real.log (215349 / 250000) ≤ (2984019 / 20000000) := by
  have h := checkLog_sound (w := (34651 / 465349)) (n := 12)
    (lo := (149200949 / 1000000000)) (hi := (2984019 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 215349) = 1/(215349 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2984019 / 20000000) (-149200949 / 1000000000) (Real.log (215349 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (8748193 / 15625000) ≤ -Real.log (500000000000 / 875235025517) ∧
    -Real.log (500000000000 / 875235025517) ≤ (559884353 / 1000000000) := by
  have h := checkLog_sound (w := (375235025517 / 1375235025517)) (n := 12)
    (lo := (8748193 / 15625000)) (hi := (559884353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((875235025517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(875235025517 / 500000000000) = 1/(500000000000 / 875235025517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (8748193 / 15625000) (559884353 / 1000000000) (Real.log (875235025517 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (875235025517 / 500000000000) = -Real.log (500000000000 / 875235025517) := by
    rw [show ((875235025517 / 500000000000) : ℝ) = ((500000000000 / 875235025517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (561150707 / 1000000000) ≤ -Real.log (250000000000 / 438172043011) ∧
    -Real.log (250000000000 / 438172043011) ≤ (140287677 / 250000000) := by
  have h := checkLog_sound (w := (188172043011 / 688172043011)) (n := 12)
    (lo := (561150707 / 1000000000)) (hi := (140287677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438172043011 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438172043011 / 250000000000) = 1/(250000000000 / 438172043011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (561150707 / 1000000000) (140287677 / 250000000) (Real.log (438172043011 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (438172043011 / 250000000000) = -Real.log (250000000000 / 438172043011) := by
    rw [show ((438172043011 / 250000000000) : ℝ) = ((250000000000 / 438172043011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (196024797 / 500000000) ≤ -Real.log (62500000000 / 92500694403) ∧
    -Real.log (62500000000 / 92500694403) ≤ (78409919 / 200000000) := by
  have h := checkLog_sound (w := (30000694403 / 155000694403)) (n := 12)
    (lo := (196024797 / 500000000)) (hi := (78409919 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92500694403 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92500694403 / 62500000000) = 1/(62500000000 / 92500694403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (196024797 / 500000000) (78409919 / 200000000) (Real.log (92500694403 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (92500694403 / 62500000000) = -Real.log (62500000000 / 92500694403) := by
    rw [show ((92500694403 / 62500000000) : ℝ) = ((62500000000 / 92500694403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (392922361 / 1000000000) ≤ -Real.log (6250000000 / 9258146119) ∧
    -Real.log (6250000000 / 9258146119) ≤ (196461181 / 500000000) := by
  have h := checkLog_sound (w := (3008146119 / 15508146119)) (n := 12)
    (lo := (392922361 / 1000000000)) (hi := (196461181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9258146119 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9258146119 / 6250000000) = 1/(6250000000 / 9258146119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (392922361 / 1000000000) (196461181 / 500000000) (Real.log (9258146119 / 6250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (9258146119 / 6250000000) = -Real.log (6250000000 / 9258146119) := by
    rw [show ((9258146119 / 6250000000) : ℝ) = ((6250000000 / 9258146119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (13918997 / 50000000) ≤ -Real.log (100000000000 / 132098799817) ∧
    -Real.log (100000000000 / 132098799817) ≤ (278379941 / 1000000000) := by
  have h := checkLog_sound (w := (32098799817 / 232098799817)) (n := 12)
    (lo := (13918997 / 50000000)) (hi := (278379941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132098799817 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132098799817 / 100000000000) = 1/(100000000000 / 132098799817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (13918997 / 50000000) (278379941 / 1000000000) (Real.log (132098799817 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (132098799817 / 100000000000) = -Real.log (100000000000 / 132098799817) := by
    rw [show ((132098799817 / 100000000000) : ℝ) = ((100000000000 / 132098799817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2790039 / 10000000) ≤ -Real.log (100000000000 / 132181249971) ∧
    -Real.log (100000000000 / 132181249971) ≤ (279003901 / 1000000000) := by
  have h := checkLog_sound (w := (32181249971 / 232181249971)) (n := 12)
    (lo := (2790039 / 10000000)) (hi := (279003901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132181249971 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132181249971 / 100000000000) = 1/(100000000000 / 132181249971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2790039 / 10000000) (279003901 / 1000000000) (Real.log (132181249971 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (132181249971 / 100000000000) = -Real.log (100000000000 / 132181249971) := by
    rw [show ((132181249971 / 100000000000) : ℝ) = ((100000000000 / 132181249971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (19397999 / 1000000000) ≤ -Real.log (61299308199 / 62500000000) ∧
    -Real.log (61299308199 / 62500000000) ≤ (9699 / 500000) := by
  have h := checkLog_sound (w := (1200691801 / 123799308199)) (n := 12)
    (lo := (19397999 / 1000000000)) (hi := (9699 / 500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61299308199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61299308199) = 1/(61299308199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9699 / 500000) (-19397999 / 1000000000) (Real.log (61299308199 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19311611 / 1000000000) ≤ -Real.log (245218415799 / 250000000000) ∧
    -Real.log (245218415799 / 250000000000) ≤ (4827903 / 250000000) := by
  have h := checkLog_sound (w := (4781584201 / 495218415799)) (n := 12)
    (lo := (19311611 / 1000000000)) (hi := (4827903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245218415799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245218415799) = 1/(245218415799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4827903 / 250000000) (-19311611 / 1000000000) (Real.log (245218415799 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell039

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell040Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell040
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

theorem reflection_log_1_neg : (242179953 / 1000000000) ≤ -Real.log (5120 / 6523) ∧
    -Real.log (5120 / 6523) ≤ (121089977 / 500000000) := by
  have h := checkLog_sound (w := (1403 / 11643)) (n := 12)
    (lo := (242179953 / 1000000000)) (hi := (121089977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6523 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6523 / 5120) = 1/(5120 / 6523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (242179953 / 1000000000) (121089977 / 500000000) (Real.log (6523 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6523 / 5120) = -Real.log (5120 / 6523) := by
    rw [show ((6523 / 5120) : ℝ) = ((5120 / 6523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (320237547 / 1000000000) ≤ -Real.log (3717 / 5120) ∧
    -Real.log (3717 / 5120) ≤ (80059387 / 250000000) := by
  have h := checkLog_sound (w := (1403 / 8837)) (n := 12)
    (lo := (320237547 / 1000000000)) (hi := (80059387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3717) = 1/(3717 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-80059387 / 250000000) (-320237547 / 1000000000) (Real.log (3717 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (1888437 / 7812500) ≤ -Real.log (128 / 163) ∧
    -Real.log (128 / 163) ≤ (241719937 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 291)) (n := 12)
    (lo := (1888437 / 7812500)) (hi := (241719937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163 / 128) = 1/(128 / 163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (1888437 / 7812500) (241719937 / 1000000000) (Real.log (163 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (163 / 128) = -Real.log (128 / 163) := by
    rw [show ((163 / 128) : ℝ) = ((128 / 163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (31943077 / 100000000) ≤ -Real.log (93 / 128) ∧
    -Real.log (93 / 128) ≤ (319430771 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 221)) (n := 12)
    (lo := (31943077 / 100000000)) (hi := (319430771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 93) = 1/(93 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-319430771 / 1000000000) (-31943077 / 100000000) (Real.log (93 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (88642363 / 500000000) ≤ -Real.log (1000000 / 1193971) ∧
    -Real.log (1000000 / 1193971) ≤ (177284727 / 1000000000) := by
  have h := checkLog_sound (w := (193971 / 2193971)) (n := 12)
    (lo := (88642363 / 500000000)) (hi := (177284727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193971 / 1000000) = 1/(1000000 / 1193971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (88642363 / 500000000) (177284727 / 1000000000) (Real.log (1193971 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1193971 / 1000000) = -Real.log (1000000 / 1193971) := by
    rw [show ((1193971 / 1000000) : ℝ) = ((1000000 / 1193971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (53908889 / 250000000) ≤ -Real.log (806029 / 1000000) ∧
    -Real.log (806029 / 1000000) ≤ (215635557 / 1000000000) := by
  have h := checkLog_sound (w := (193971 / 1806029)) (n := 12)
    (lo := (53908889 / 250000000)) (hi := (215635557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806029) = 1/(806029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-215635557 / 1000000000) (-53908889 / 250000000) (Real.log (806029 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (88817797 / 500000000) ≤ -Real.log (100000 / 119439) ∧
    -Real.log (100000 / 119439) ≤ (35527119 / 200000000) := by
  have h := checkLog_sound (w := (19439 / 219439)) (n := 12)
    (lo := (88817797 / 500000000)) (hi := (35527119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119439 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119439 / 100000) = 1/(100000 / 119439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (88817797 / 500000000) (35527119 / 200000000) (Real.log (119439 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (119439 / 100000) = -Real.log (100000 / 119439) := by
    rw [show ((119439 / 100000) : ℝ) = ((100000 / 119439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (54038881 / 250000000) ≤ -Real.log (80561 / 100000) ∧
    -Real.log (80561 / 100000) ≤ (8646221 / 40000000) := by
  have h := checkLog_sound (w := (19439 / 180561)) (n := 12)
    (lo := (54038881 / 250000000)) (hi := (8646221 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80561) = 1/(80561 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-8646221 / 40000000) (-54038881 / 250000000) (Real.log (80561 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16225259 / 125000000) ≤ -Real.log (1000000 / 1138603) ∧
    -Real.log (1000000 / 1138603) ≤ (129802073 / 1000000000) := by
  have h := checkLog_sound (w := (138603 / 2138603)) (n := 12)
    (lo := (16225259 / 125000000)) (hi := (129802073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138603 / 1000000) = 1/(1000000 / 1138603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16225259 / 125000000) (129802073 / 1000000000) (Real.log (1138603 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1138603 / 1000000) = -Real.log (1000000 / 1138603) := by
    rw [show ((1138603 / 1000000) : ℝ) = ((1000000 / 1138603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (149199789 / 1000000000) ≤ -Real.log (861397 / 1000000) ∧
    -Real.log (861397 / 1000000) ≤ (14919979 / 100000000) := by
  have h := checkLog_sound (w := (138603 / 1861397)) (n := 12)
    (lo := (149199789 / 1000000000)) (hi := (14919979 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861397) = 1/(861397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-14919979 / 100000000) (-149199789 / 1000000000) (Real.log (861397 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (8129479 / 62500000) ≤ -Real.log (100000 / 113891) ∧
    -Real.log (100000 / 113891) ≤ (26014333 / 200000000) := by
  have h := checkLog_sound (w := (13891 / 213891)) (n := 12)
    (lo := (8129479 / 62500000)) (hi := (26014333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113891 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113891 / 100000) = 1/(100000 / 113891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (8129479 / 62500000) (26014333 / 200000000) (Real.log (113891 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (113891 / 100000) = -Real.log (100000 / 113891) := by
    rw [show ((113891 / 100000) : ℝ) = ((100000 / 113891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (23929 / 160000) ≤ -Real.log (86109 / 100000) ∧
    -Real.log (86109 / 100000) ≤ (149556251 / 1000000000) := by
  have h := checkLog_sound (w := (13891 / 186109)) (n := 12)
    (lo := (23929 / 160000)) (hi := (149556251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 86109) = 1/(86109 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-149556251 / 1000000000) (-23929 / 160000) (Real.log (86109 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (561150707 / 1000000000) ≤ -Real.log (500000000000 / 876344086021) ∧
    -Real.log (500000000000 / 876344086021) ≤ (140287677 / 250000000) := by
  have h := checkLog_sound (w := (376344086021 / 1376344086021)) (n := 12)
    (lo := (561150707 / 1000000000)) (hi := (140287677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((876344086021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(876344086021 / 500000000000) = 1/(500000000000 / 876344086021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (561150707 / 1000000000) (140287677 / 250000000) (Real.log (876344086021 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (876344086021 / 500000000000) = -Real.log (500000000000 / 876344086021) := by
    rw [show ((876344086021 / 500000000000) : ℝ) = ((500000000000 / 876344086021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (562417501 / 1000000000) ≤ -Real.log (500000000000 / 877454936777) ∧
    -Real.log (500000000000 / 877454936777) ≤ (281208751 / 500000000) := by
  have h := checkLog_sound (w := (377454936777 / 1377454936777)) (n := 12)
    (lo := (562417501 / 1000000000)) (hi := (281208751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((877454936777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(877454936777 / 500000000000) = 1/(500000000000 / 877454936777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (562417501 / 1000000000) (281208751 / 500000000) (Real.log (877454936777 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (877454936777 / 500000000000) = -Real.log (500000000000 / 877454936777) := by
    rw [show ((877454936777 / 500000000000) : ℝ) = ((500000000000 / 877454936777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (392920283 / 1000000000) ≤ -Real.log (15625000000 / 23145317197) ∧
    -Real.log (15625000000 / 23145317197) ≤ (98230071 / 250000000) := by
  have h := checkLog_sound (w := (7520317197 / 38770317197)) (n := 12)
    (lo := (392920283 / 1000000000)) (hi := (98230071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23145317197 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23145317197 / 15625000000) = 1/(15625000000 / 23145317197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (392920283 / 1000000000) (98230071 / 250000000) (Real.log (23145317197 / 15625000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (23145317197 / 15625000000) = -Real.log (15625000000 / 23145317197) := by
    rw [show ((23145317197 / 15625000000) : ℝ) = ((15625000000 / 23145317197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (393791119 / 1000000000) ≤ -Real.log (500000000000 / 741295415897) ∧
    -Real.log (500000000000 / 741295415897) ≤ (4922389 / 12500000) := by
  have h := checkLog_sound (w := (241295415897 / 1241295415897)) (n := 12)
    (lo := (393791119 / 1000000000)) (hi := (4922389 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741295415897 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741295415897 / 500000000000) = 1/(500000000000 / 741295415897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (393791119 / 1000000000) (4922389 / 12500000) (Real.log (741295415897 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (741295415897 / 500000000000) = -Real.log (500000000000 / 741295415897) := by
    rw [show ((741295415897 / 500000000000) : ℝ) = ((500000000000 / 741295415897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (279001861 / 1000000000) ≤ -Real.log (500000000000 / 660904902153) ∧
    -Real.log (500000000000 / 660904902153) ≤ (139500931 / 500000000) := by
  have h := checkLog_sound (w := (160904902153 / 1160904902153)) (n := 12)
    (lo := (279001861 / 1000000000)) (hi := (139500931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660904902153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660904902153 / 500000000000) = 1/(500000000000 / 660904902153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (279001861 / 1000000000) (139500931 / 500000000) (Real.log (660904902153 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (660904902153 / 500000000000) = -Real.log (500000000000 / 660904902153) := by
    rw [show ((660904902153 / 500000000000) : ℝ) = ((500000000000 / 660904902153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (55925583 / 200000000) ≤ -Real.log (500000000000 / 661318793623) ∧
    -Real.log (500000000000 / 661318793623) ≤ (69906979 / 250000000) := by
  have h := checkLog_sound (w := (161318793623 / 1161318793623)) (n := 12)
    (lo := (55925583 / 200000000)) (hi := (69906979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661318793623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661318793623 / 500000000000) = 1/(500000000000 / 661318793623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (55925583 / 200000000) (69906979 / 250000000) (Real.log (661318793623 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (661318793623 / 500000000000) = -Real.log (500000000000 / 661318793623) := by
    rw [show ((661318793623 / 500000000000) : ℝ) = ((500000000000 / 661318793623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3896917 / 200000000) ≤ -Real.log (9807040119 / 10000000000) ∧
    -Real.log (9807040119 / 10000000000) ≤ (9742293 / 500000000) := by
  have h := checkLog_sound (w := (192959881 / 19807040119)) (n := 12)
    (lo := (3896917 / 200000000)) (hi := (9742293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9807040119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9807040119) = 1/(9807040119 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9742293 / 500000000) (-3896917 / 200000000) (Real.log (9807040119 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4849429 / 250000000) ≤ -Real.log (980789208391 / 1000000000000) ∧
    -Real.log (980789208391 / 1000000000000) ≤ (19397717 / 1000000000) := by
  have h := checkLog_sound (w := (19210791609 / 1980789208391)) (n := 12)
    (lo := (4849429 / 250000000)) (hi := (19397717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980789208391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980789208391) = 1/(980789208391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19397717 / 1000000000) (-4849429 / 250000000) (Real.log (980789208391 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell040

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell041Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell041
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

theorem reflection_log_1_neg : (242639759 / 1000000000) ≤ -Real.log (2560 / 3263) ∧
    -Real.log (2560 / 3263) ≤ (3032997 / 12500000) := by
  have h := checkLog_sound (w := (703 / 5823)) (n := 12)
    (lo := (242639759 / 1000000000)) (hi := (3032997 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3263 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3263 / 2560) = 1/(2560 / 3263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (242639759 / 1000000000) (3032997 / 12500000) (Real.log (3263 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3263 / 2560) = -Real.log (2560 / 3263) := by
    rw [show ((3263 / 2560) : ℝ) = ((2560 / 3263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (20065311 / 62500000) ≤ -Real.log (1857 / 2560) ∧
    -Real.log (1857 / 2560) ≤ (321044977 / 1000000000) := by
  have h := checkLog_sound (w := (703 / 4417)) (n := 12)
    (lo := (20065311 / 62500000)) (hi := (321044977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1857) = 1/(1857 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-321044977 / 1000000000) (-20065311 / 62500000) (Real.log (1857 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (242179953 / 1000000000) ≤ -Real.log (5120 / 6523) ∧
    -Real.log (5120 / 6523) ≤ (121089977 / 500000000) := by
  have h := checkLog_sound (w := (1403 / 11643)) (n := 12)
    (lo := (242179953 / 1000000000)) (hi := (121089977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6523 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6523 / 5120) = 1/(5120 / 6523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (242179953 / 1000000000) (121089977 / 500000000) (Real.log (6523 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6523 / 5120) = -Real.log (5120 / 6523) := by
    rw [show ((6523 / 5120) : ℝ) = ((5120 / 6523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (320237547 / 1000000000) ≤ -Real.log (3717 / 5120) ∧
    -Real.log (3717 / 5120) ≤ (80059387 / 250000000) := by
  have h := checkLog_sound (w := (1403 / 8837)) (n := 12)
    (lo := (320237547 / 1000000000)) (hi := (80059387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3717) = 1/(3717 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-80059387 / 250000000) (-320237547 / 1000000000) (Real.log (3717 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (177634757 / 1000000000) ≤ -Real.log (1000000 / 1194389) ∧
    -Real.log (1000000 / 1194389) ≤ (88817379 / 500000000) := by
  have h := checkLog_sound (w := (194389 / 2194389)) (n := 12)
    (lo := (177634757 / 1000000000)) (hi := (88817379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194389 / 1000000) = 1/(1000000 / 1194389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (177634757 / 1000000000) (88817379 / 500000000) (Real.log (1194389 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1194389 / 1000000) = -Real.log (1000000 / 1194389) := by
    rw [show ((1194389 / 1000000) : ℝ) = ((1000000 / 1194389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (216154283 / 1000000000) ≤ -Real.log (805611 / 1000000) ∧
    -Real.log (805611 / 1000000) ≤ (54038571 / 250000000) := by
  have h := checkLog_sound (w := (194389 / 1805611)) (n := 12)
    (lo := (216154283 / 1000000000)) (hi := (54038571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805611) = 1/(805611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-54038571 / 250000000) (-216154283 / 1000000000) (Real.log (805611 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (177986339 / 1000000000) ≤ -Real.log (1000000 / 1194809) ∧
    -Real.log (1000000 / 1194809) ≤ (8899317 / 50000000) := by
  have h := checkLog_sound (w := (194809 / 2194809)) (n := 12)
    (lo := (177986339 / 1000000000)) (hi := (8899317 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194809 / 1000000) = 1/(1000000 / 1194809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (177986339 / 1000000000) (8899317 / 50000000) (Real.log (1194809 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1194809 / 1000000) = -Real.log (1000000 / 1194809) := by
    rw [show ((1194809 / 1000000) : ℝ) = ((1000000 / 1194809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (108337881 / 500000000) ≤ -Real.log (805191 / 1000000) ∧
    -Real.log (805191 / 1000000) ≤ (216675763 / 1000000000) := by
  have h := checkLog_sound (w := (194809 / 1805191)) (n := 12)
    (lo := (108337881 / 500000000)) (hi := (216675763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805191) = 1/(805191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-216675763 / 1000000000) (-108337881 / 500000000) (Real.log (805191 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (65035393 / 500000000) ≤ -Real.log (1000000 / 1138909) ∧
    -Real.log (1000000 / 1138909) ≤ (130070787 / 1000000000) := by
  have h := checkLog_sound (w := (138909 / 2138909)) (n := 12)
    (lo := (65035393 / 500000000)) (hi := (130070787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138909 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138909 / 1000000) = 1/(1000000 / 1138909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (65035393 / 500000000) (130070787 / 1000000000) (Real.log (1138909 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1138909 / 1000000) = -Real.log (1000000 / 1138909) := by
    rw [show ((1138909 / 1000000) : ℝ) = ((1000000 / 1138909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (149555089 / 1000000000) ≤ -Real.log (861091 / 1000000) ∧
    -Real.log (861091 / 1000000) ≤ (14955509 / 100000000) := by
  have h := checkLog_sound (w := (138909 / 1861091)) (n := 12)
    (lo := (149555089 / 1000000000)) (hi := (14955509 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861091) = 1/(861091 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-14955509 / 100000000) (-149555089 / 1000000000) (Real.log (861091 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (32584857 / 250000000) ≤ -Real.log (200000 / 227843) ∧
    -Real.log (200000 / 227843) ≤ (130339429 / 1000000000) := by
  have h := checkLog_sound (w := (27843 / 427843)) (n := 12)
    (lo := (32584857 / 250000000)) (hi := (130339429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227843 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227843 / 200000) = 1/(200000 / 227843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (32584857 / 250000000) (130339429 / 1000000000) (Real.log (227843 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (227843 / 200000) = -Real.log (200000 / 227843) := by
    rw [show ((227843 / 200000) : ℝ) = ((200000 / 227843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (29982103 / 200000000) ≤ -Real.log (172157 / 200000) ∧
    -Real.log (172157 / 200000) ≤ (37477629 / 250000000) := by
  have h := checkLog_sound (w := (27843 / 372157)) (n := 12)
    (lo := (29982103 / 200000000)) (hi := (37477629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 172157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 172157) = 1/(172157 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-37477629 / 250000000) (-29982103 / 200000000) (Real.log (172157 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (562417501 / 1000000000) ≤ -Real.log (62500000000 / 109681867097) ∧
    -Real.log (62500000000 / 109681867097) ≤ (281208751 / 500000000) := by
  have h := checkLog_sound (w := (47181867097 / 172181867097)) (n := 12)
    (lo := (562417501 / 1000000000)) (hi := (281208751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109681867097 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109681867097 / 62500000000) = 1/(62500000000 / 109681867097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (562417501 / 1000000000) (281208751 / 500000000) (Real.log (109681867097 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (109681867097 / 62500000000) = -Real.log (62500000000 / 109681867097) := by
    rw [show ((109681867097 / 62500000000) : ℝ) = ((62500000000 / 109681867097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (112736947 / 200000000) ≤ -Real.log (250000000000 / 439283791061) ∧
    -Real.log (250000000000 / 439283791061) ≤ (4403787 / 7812500) := by
  have h := checkLog_sound (w := (189283791061 / 689283791061)) (n := 12)
    (lo := (112736947 / 200000000)) (hi := (4403787 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((439283791061 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(439283791061 / 250000000000) = 1/(250000000000 / 439283791061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (112736947 / 200000000) (4403787 / 7812500) (Real.log (439283791061 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (439283791061 / 250000000000) = -Real.log (250000000000 / 439283791061) := by
    rw [show ((439283791061 / 250000000000) : ℝ) = ((250000000000 / 439283791061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (4922363 / 12500000) ≤ -Real.log (500000000000 / 741293875083) ∧
    -Real.log (500000000000 / 741293875083) ≤ (393789041 / 1000000000) := by
  have h := checkLog_sound (w := (241293875083 / 1241293875083)) (n := 12)
    (lo := (4922363 / 12500000)) (hi := (393789041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741293875083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741293875083 / 500000000000) = 1/(500000000000 / 741293875083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4922363 / 12500000) (393789041 / 1000000000) (Real.log (741293875083 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (741293875083 / 500000000000) = -Real.log (500000000000 / 741293875083) := by
    rw [show ((741293875083 / 500000000000) : ℝ) = ((500000000000 / 741293875083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (197331051 / 500000000) ≤ -Real.log (250000000000 / 370970676523) ∧
    -Real.log (250000000000 / 370970676523) ≤ (394662103 / 1000000000) := by
  have h := checkLog_sound (w := (120970676523 / 620970676523)) (n := 12)
    (lo := (197331051 / 500000000)) (hi := (394662103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370970676523 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370970676523 / 250000000000) = 1/(250000000000 / 370970676523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (197331051 / 500000000) (394662103 / 1000000000) (Real.log (370970676523 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (370970676523 / 250000000000) = -Real.log (250000000000 / 370970676523) := by
    rw [show ((370970676523 / 250000000000) : ℝ) = ((250000000000 / 370970676523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (2237007 / 8000000) ≤ -Real.log (250000000000 / 330658722481) ∧
    -Real.log (250000000000 / 330658722481) ≤ (69906469 / 250000000) := by
  have h := checkLog_sound (w := (80658722481 / 580658722481)) (n := 12)
    (lo := (2237007 / 8000000)) (hi := (69906469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330658722481 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330658722481 / 250000000000) = 1/(250000000000 / 330658722481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2237007 / 8000000) (69906469 / 250000000) (Real.log (330658722481 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (330658722481 / 250000000000) = -Real.log (250000000000 / 330658722481) := by
    rw [show ((330658722481 / 250000000000) : ℝ) = ((250000000000 / 330658722481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (35031243 / 125000000) ≤ -Real.log (500000000000 / 661730281081) ∧
    -Real.log (500000000000 / 661730281081) ≤ (56049989 / 200000000) := by
  have h := checkLog_sound (w := (161730281081 / 1161730281081)) (n := 12)
    (lo := (35031243 / 125000000)) (hi := (56049989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661730281081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661730281081 / 500000000000) = 1/(500000000000 / 661730281081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (35031243 / 125000000) (56049989 / 200000000) (Real.log (661730281081 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (661730281081 / 500000000000) = -Real.log (500000000000 / 661730281081) := by
    rw [show ((661730281081 / 500000000000) : ℝ) = ((500000000000 / 661730281081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9785543 / 500000000) ≤ -Real.log (39224767351 / 40000000000) ∧
    -Real.log (39224767351 / 40000000000) ≤ (19571087 / 1000000000) := by
  have h := checkLog_sound (w := (775232649 / 79224767351)) (n := 12)
    (lo := (9785543 / 500000000)) (hi := (19571087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39224767351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39224767351) = 1/(39224767351 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19571087 / 1000000000) (-9785543 / 500000000) (Real.log (39224767351 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (9742151 / 500000000) ≤ -Real.log (980704289719 / 1000000000000) ∧
    -Real.log (980704289719 / 1000000000000) ≤ (19484303 / 1000000000) := by
  have h := checkLog_sound (w := (19295710281 / 1980704289719)) (n := 12)
    (lo := (9742151 / 500000000)) (hi := (19484303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980704289719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980704289719) = 1/(980704289719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19484303 / 1000000000) (-9742151 / 500000000) (Real.log (980704289719 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell041

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell042Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell042
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

theorem reflection_log_1_neg : (243099353 / 1000000000) ≤ -Real.log (5120 / 6529) ∧
    -Real.log (5120 / 6529) ≤ (121549677 / 500000000) := by
  have h := checkLog_sound (w := (1409 / 11649)) (n := 12)
    (lo := (243099353 / 1000000000)) (hi := (121549677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6529 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6529 / 5120) = 1/(5120 / 6529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (243099353 / 1000000000) (121549677 / 500000000) (Real.log (6529 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6529 / 5120) = -Real.log (5120 / 6529) := by
    rw [show ((6529 / 5120) : ℝ) = ((5120 / 6529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2514477 / 7812500) ≤ -Real.log (3711 / 5120) ∧
    -Real.log (3711 / 5120) ≤ (321853057 / 1000000000) := by
  have h := checkLog_sound (w := (1409 / 8831)) (n := 12)
    (lo := (2514477 / 7812500)) (hi := (321853057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3711) = 1/(3711 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-321853057 / 1000000000) (-2514477 / 7812500) (Real.log (3711 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (242639759 / 1000000000) ≤ -Real.log (2560 / 3263) ∧
    -Real.log (2560 / 3263) ≤ (3032997 / 12500000) := by
  have h := checkLog_sound (w := (703 / 5823)) (n := 12)
    (lo := (242639759 / 1000000000)) (hi := (3032997 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3263 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3263 / 2560) = 1/(2560 / 3263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (242639759 / 1000000000) (3032997 / 12500000) (Real.log (3263 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3263 / 2560) = -Real.log (2560 / 3263) := by
    rw [show ((3263 / 2560) : ℝ) = ((2560 / 3263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (20065311 / 62500000) ≤ -Real.log (1857 / 2560) ∧
    -Real.log (1857 / 2560) ≤ (321044977 / 1000000000) := by
  have h := checkLog_sound (w := (703 / 4417)) (n := 12)
    (lo := (20065311 / 62500000)) (hi := (321044977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1857) = 1/(1857 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-321044977 / 1000000000) (-20065311 / 62500000) (Real.log (1857 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (177985503 / 1000000000) ≤ -Real.log (125000 / 149351) ∧
    -Real.log (125000 / 149351) ≤ (5562047 / 31250000) := by
  have h := checkLog_sound (w := (24351 / 274351)) (n := 12)
    (lo := (177985503 / 1000000000)) (hi := (5562047 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149351 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149351 / 125000) = 1/(125000 / 149351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (177985503 / 1000000000) (5562047 / 31250000) (Real.log (149351 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (149351 / 125000) = -Real.log (125000 / 149351) := by
    rw [show ((149351 / 125000) : ℝ) = ((125000 / 149351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (5416863 / 25000000) ≤ -Real.log (100649 / 125000) ∧
    -Real.log (100649 / 125000) ≤ (216674521 / 1000000000) := by
  have h := checkLog_sound (w := (24351 / 225649)) (n := 12)
    (lo := (5416863 / 25000000)) (hi := (216674521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 100649) = 1/(100649 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-216674521 / 1000000000) (-5416863 / 25000000) (Real.log (100649 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1426689 / 8000000) ≤ -Real.log (1000000 / 1195227) ∧
    -Real.log (1000000 / 1195227) ≤ (89168063 / 500000000) := by
  have h := checkLog_sound (w := (195227 / 2195227)) (n := 12)
    (lo := (1426689 / 8000000)) (hi := (89168063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1195227 / 1000000) = 1/(1000000 / 1195227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1426689 / 8000000) (89168063 / 500000000) (Real.log (1195227 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1195227 / 1000000) = -Real.log (1000000 / 1195227) := by
    rw [show ((1195227 / 1000000) : ℝ) = ((1000000 / 1195227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (54298757 / 250000000) ≤ -Real.log (804773 / 1000000) ∧
    -Real.log (804773 / 1000000) ≤ (217195029 / 1000000000) := by
  have h := checkLog_sound (w := (195227 / 1804773)) (n := 12)
    (lo := (54298757 / 250000000)) (hi := (217195029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 804773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 804773) = 1/(804773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-217195029 / 1000000000) (-54298757 / 250000000) (Real.log (804773 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2606771 / 20000000) ≤ -Real.log (500000 / 569607) ∧
    -Real.log (500000 / 569607) ≤ (130338551 / 1000000000) := by
  have h := checkLog_sound (w := (69607 / 1069607)) (n := 12)
    (lo := (2606771 / 20000000)) (hi := (130338551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569607 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569607 / 500000) = 1/(500000 / 569607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2606771 / 20000000) (130338551 / 1000000000) (Real.log (569607 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (569607 / 500000) = -Real.log (500000 / 569607) := by
    rw [show ((569607 / 500000) : ℝ) = ((500000 / 569607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (149909353 / 1000000000) ≤ -Real.log (430393 / 500000) ∧
    -Real.log (430393 / 500000) ≤ (74954677 / 500000000) := by
  have h := checkLog_sound (w := (69607 / 930393)) (n := 12)
    (lo := (149909353 / 1000000000)) (hi := (74954677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 430393) = 1/(430393 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-74954677 / 500000000) (-149909353 / 1000000000) (Real.log (430393 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (130607121 / 1000000000) ≤ -Real.log (3125 / 3561) ∧
    -Real.log (3125 / 3561) ≤ (65303561 / 500000000) := by
  have h := checkLog_sound (w := (218 / 3343)) (n := 12)
    (lo := (130607121 / 1000000000)) (hi := (65303561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3561 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3561 / 3125) = 1/(3125 / 3561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (130607121 / 1000000000) (65303561 / 500000000) (Real.log (3561 / 3125)) := by
  have h := reflection_log_11_neg
  have he : Real.log (3561 / 3125) = -Real.log (3125 / 3561) := by
    rw [show ((3561 / 3125) : ℝ) = ((3125 / 3561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (30052981 / 200000000) ≤ -Real.log (2689 / 3125) ∧
    -Real.log (2689 / 3125) ≤ (75132453 / 500000000) := by
  have h := checkLog_sound (w := (218 / 2907)) (n := 12)
    (lo := (30052981 / 200000000)) (hi := (75132453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2689) = 1/(2689 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-75132453 / 500000000) (-30052981 / 200000000) (Real.log (2689 / 3125)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (112736947 / 200000000) ≤ -Real.log (500000000000 / 878567582121) ∧
    -Real.log (500000000000 / 878567582121) ≤ (4403787 / 7812500) := by
  have h := checkLog_sound (w := (378567582121 / 1378567582121)) (n := 12)
    (lo := (112736947 / 200000000)) (hi := (4403787 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((878567582121 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(878567582121 / 500000000000) = 1/(500000000000 / 878567582121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (112736947 / 200000000) (4403787 / 7812500) (Real.log (878567582121 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (878567582121 / 500000000000) = -Real.log (500000000000 / 878567582121) := by
    rw [show ((878567582121 / 500000000000) : ℝ) = ((500000000000 / 878567582121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (56495241 / 100000000) ≤ -Real.log (62500000000 / 109960253301) ∧
    -Real.log (62500000000 / 109960253301) ≤ (564952411 / 1000000000) := by
  have h := checkLog_sound (w := (47460253301 / 172460253301)) (n := 12)
    (lo := (56495241 / 100000000)) (hi := (564952411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109960253301 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109960253301 / 62500000000) = 1/(62500000000 / 109960253301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (56495241 / 100000000) (564952411 / 1000000000) (Real.log (109960253301 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (109960253301 / 62500000000) = -Real.log (62500000000 / 109960253301) := by
    rw [show ((109960253301 / 62500000000) : ℝ) = ((62500000000 / 109960253301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (394660023 / 1000000000) ≤ -Real.log (500000000000 / 741939810629) ∧
    -Real.log (500000000000 / 741939810629) ≤ (49332503 / 125000000) := by
  have h := checkLog_sound (w := (241939810629 / 1241939810629)) (n := 12)
    (lo := (394660023 / 1000000000)) (hi := (49332503 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741939810629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741939810629 / 500000000000) = 1/(500000000000 / 741939810629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (394660023 / 1000000000) (49332503 / 125000000) (Real.log (741939810629 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (741939810629 / 500000000000) = -Real.log (500000000000 / 741939810629) := by
    rw [show ((741939810629 / 500000000000) : ℝ) = ((500000000000 / 741939810629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (197765577 / 500000000) ≤ -Real.log (500000000000 / 742586418779) ∧
    -Real.log (500000000000 / 742586418779) ≤ (79106231 / 200000000) := by
  have h := checkLog_sound (w := (242586418779 / 1242586418779)) (n := 12)
    (lo := (197765577 / 500000000)) (hi := (79106231 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742586418779 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742586418779 / 500000000000) = 1/(500000000000 / 742586418779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (197765577 / 500000000) (79106231 / 200000000) (Real.log (742586418779 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (742586418779 / 500000000000) = -Real.log (500000000000 / 742586418779) := by
    rw [show ((742586418779 / 500000000000) : ℝ) = ((500000000000 / 742586418779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (8757747 / 31250000) ≤ -Real.log (62500000000 / 82716116433) ∧
    -Real.log (62500000000 / 82716116433) ≤ (56049581 / 200000000) := by
  have h := checkLog_sound (w := (20216116433 / 145216116433)) (n := 12)
    (lo := (8757747 / 31250000)) (hi := (56049581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82716116433 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82716116433 / 62500000000) = 1/(62500000000 / 82716116433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (8757747 / 31250000) (56049581 / 200000000) (Real.log (82716116433 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (82716116433 / 62500000000) = -Real.log (62500000000 / 82716116433) := by
    rw [show ((82716116433 / 62500000000) : ℝ) = ((62500000000 / 82716116433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (280872027 / 1000000000) ≤ -Real.log (250000000000 / 331071030123) ∧
    -Real.log (250000000000 / 331071030123) ≤ (70218007 / 250000000) := by
  have h := checkLog_sound (w := (81071030123 / 581071030123)) (n := 12)
    (lo := (280872027 / 1000000000)) (hi := (70218007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331071030123 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331071030123 / 250000000000) = 1/(250000000000 / 331071030123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (280872027 / 1000000000) (70218007 / 250000000) (Real.log (331071030123 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (331071030123 / 250000000000) = -Real.log (250000000000 / 331071030123) := by
    rw [show ((331071030123 / 250000000000) : ℝ) = ((250000000000 / 331071030123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2457223 / 125000000) ≤ -Real.log (9575529 / 9765625) ∧
    -Real.log (9575529 / 9765625) ≤ (3931557 / 200000000) := by
  have h := checkLog_sound (w := (95048 / 9670577)) (n := 12)
    (lo := (2457223 / 125000000)) (hi := (3931557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9575529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9575529) = 1/(9575529 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3931557 / 200000000) (-2457223 / 125000000) (Real.log (9575529 / 9765625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (9785401 / 500000000) ≤ -Real.log (245154865551 / 250000000000) ∧
    -Real.log (245154865551 / 250000000000) ≤ (19570803 / 1000000000) := by
  have h := checkLog_sound (w := (4845134449 / 495154865551)) (n := 12)
    (lo := (9785401 / 500000000)) (hi := (19570803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245154865551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245154865551) = 1/(245154865551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19570803 / 1000000000) (-9785401 / 500000000) (Real.log (245154865551 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell042

end


