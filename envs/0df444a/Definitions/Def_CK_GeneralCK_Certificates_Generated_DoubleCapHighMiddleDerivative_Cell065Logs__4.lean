-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell065Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell065Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:39:49.649099+00:00
-- url     : https://prove2.me/theorems/828de3c1-c675-4e03-ad3e-b18055ca29f3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell065Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell066…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell065Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell066Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell067Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell068Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell065Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell066Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell067Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell068Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell065Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell066Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell067Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell068Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell065Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell066Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell067Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell068Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell065Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell065
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

theorem reflection_log_1_neg : (253612133 / 1000000000) ≤ -Real.log (2560 / 3299) ∧
    -Real.log (2560 / 3299) ≤ (126806067 / 500000000) := by
  have h := checkLog_sound (w := (739 / 5859)) (n := 12)
    (lo := (253612133 / 1000000000)) (hi := (126806067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3299 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3299 / 2560) = 1/(2560 / 3299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (253612133 / 1000000000) (126806067 / 500000000) (Real.log (3299 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3299 / 2560) = -Real.log (2560 / 3299) := by
    rw [show ((3299 / 2560) : ℝ) = ((2560 / 3299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (340621457 / 1000000000) ≤ -Real.log (1821 / 2560) ∧
    -Real.log (1821 / 2560) ≤ (170310729 / 500000000) := by
  have h := checkLog_sound (w := (739 / 4381)) (n := 12)
    (lo := (340621457 / 1000000000)) (hi := (170310729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1821) = 1/(1821 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-170310729 / 500000000) (-340621457 / 1000000000) (Real.log (1821 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (253157347 / 1000000000) ≤ -Real.log (1024 / 1319) ∧
    -Real.log (1024 / 1319) ≤ (63289337 / 250000000) := by
  have h := checkLog_sound (w := (295 / 2343)) (n := 12)
    (lo := (253157347 / 1000000000)) (hi := (63289337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319 / 1024) = 1/(1024 / 1319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (253157347 / 1000000000) (63289337 / 250000000) (Real.log (1319 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1319 / 1024) = -Real.log (1024 / 1319) := by
    rw [show ((1319 / 1024) : ℝ) = ((1024 / 1319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (339798073 / 1000000000) ≤ -Real.log (729 / 1024) ∧
    -Real.log (729 / 1024) ≤ (169899037 / 500000000) := by
  have h := checkLog_sound (w := (295 / 1753)) (n := 12)
    (lo := (339798073 / 1000000000)) (hi := (169899037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 729) = 1/(729 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-169899037 / 500000000) (-339798073 / 1000000000) (Real.log (729 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (186012237 / 1000000000) ≤ -Real.log (1000000 / 1204437) ∧
    -Real.log (1000000 / 1204437) ≤ (93006119 / 500000000) := by
  have h := checkLog_sound (w := (204437 / 2204437)) (n := 12)
    (lo := (186012237 / 1000000000)) (hi := (93006119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204437 / 1000000) = 1/(1000000 / 1204437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (186012237 / 1000000000) (93006119 / 500000000) (Real.log (1204437 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1204437 / 1000000) = -Real.log (1000000 / 1204437) := by
    rw [show ((1204437 / 1000000) : ℝ) = ((1000000 / 1204437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (114352619 / 500000000) ≤ -Real.log (795563 / 1000000) ∧
    -Real.log (795563 / 1000000) ≤ (228705239 / 1000000000) := by
  have h := checkLog_sound (w := (204437 / 1795563)) (n := 12)
    (lo := (114352619 / 500000000)) (hi := (228705239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795563) = 1/(795563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-228705239 / 1000000000) (-114352619 / 500000000) (Real.log (795563 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (186360887 / 1000000000) ≤ -Real.log (1000000 / 1204857) ∧
    -Real.log (1000000 / 1204857) ≤ (23295111 / 125000000) := by
  have h := checkLog_sound (w := (204857 / 2204857)) (n := 12)
    (lo := (186360887 / 1000000000)) (hi := (23295111 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204857 / 1000000) = 1/(1000000 / 1204857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (186360887 / 1000000000) (23295111 / 125000000) (Real.log (1204857 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1204857 / 1000000) = -Real.log (1000000 / 1204857) := by
    rw [show ((1204857 / 1000000) : ℝ) = ((1000000 / 1204857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (114616653 / 500000000) ≤ -Real.log (795143 / 1000000) ∧
    -Real.log (795143 / 1000000) ≤ (229233307 / 1000000000) := by
  have h := checkLog_sound (w := (204857 / 1795143)) (n := 12)
    (lo := (114616653 / 500000000)) (hi := (229233307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795143) = 1/(795143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-229233307 / 1000000000) (-114616653 / 500000000) (Real.log (795143 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (136497489 / 1000000000) ≤ -Real.log (250000 / 286563) ∧
    -Real.log (250000 / 286563) ≤ (13649749 / 100000000) := by
  have h := checkLog_sound (w := (36563 / 536563)) (n := 12)
    (lo := (136497489 / 1000000000)) (hi := (13649749 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286563 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286563 / 250000) = 1/(250000 / 286563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (136497489 / 1000000000) (13649749 / 100000000) (Real.log (286563 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (286563 / 250000) = -Real.log (250000 / 286563) := by
    rw [show ((286563 / 250000) : ℝ) = ((250000 / 286563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (15811921 / 100000000) ≤ -Real.log (213437 / 250000) ∧
    -Real.log (213437 / 250000) ≤ (158119211 / 1000000000) := by
  have h := checkLog_sound (w := (36563 / 463437)) (n := 12)
    (lo := (15811921 / 100000000)) (hi := (158119211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 213437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 213437) = 1/(213437 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-158119211 / 1000000000) (-15811921 / 100000000) (Real.log (213437 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (27353231 / 200000000) ≤ -Real.log (3125 / 3583) ∧
    -Real.log (3125 / 3583) ≤ (34191539 / 250000000) := by
  have h := checkLog_sound (w := (229 / 3354)) (n := 12)
    (lo := (27353231 / 200000000)) (hi := (34191539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3583 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3583 / 3125) = 1/(3125 / 3583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (27353231 / 200000000) (34191539 / 250000000) (Real.log (3583 / 3125)) := by
  have h := reflection_log_11_neg
  have he : Real.log (3583 / 3125) = -Real.log (3125 / 3583) := by
    rw [show ((3583 / 3125) : ℝ) = ((3125 / 3583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (158480037 / 1000000000) ≤ -Real.log (2667 / 3125) ∧
    -Real.log (2667 / 3125) ≤ (79240019 / 500000000) := by
  have h := checkLog_sound (w := (229 / 2896)) (n := 12)
    (lo := (158480037 / 1000000000)) (hi := (79240019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2667) = 1/(2667 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-79240019 / 500000000) (-158480037 / 1000000000) (Real.log (2667 / 3125)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (29647771 / 50000000) ≤ -Real.log (250000000000 / 452331961591) ∧
    -Real.log (250000000000 / 452331961591) ≤ (592955421 / 1000000000) := by
  have h := checkLog_sound (w := (202331961591 / 702331961591)) (n := 12)
    (lo := (29647771 / 50000000)) (hi := (592955421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((452331961591 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(452331961591 / 250000000000) = 1/(250000000000 / 452331961591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (29647771 / 50000000) (592955421 / 1000000000) (Real.log (452331961591 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (452331961591 / 250000000000) = -Real.log (250000000000 / 452331961591) := by
    rw [show ((452331961591 / 250000000000) : ℝ) = ((250000000000 / 452331961591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (594233591 / 1000000000) ≤ -Real.log (100000000000 / 181164195497) ∧
    -Real.log (100000000000 / 181164195497) ≤ (74279199 / 125000000) := by
  have h := checkLog_sound (w := (81164195497 / 281164195497)) (n := 12)
    (lo := (594233591 / 1000000000)) (hi := (74279199 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181164195497 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181164195497 / 100000000000) = 1/(100000000000 / 181164195497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (594233591 / 1000000000) (74279199 / 125000000) (Real.log (181164195497 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (181164195497 / 100000000000) = -Real.log (100000000000 / 181164195497) := by
    rw [show ((181164195497 / 100000000000) : ℝ) = ((100000000000 / 181164195497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (103679369 / 250000000) ≤ -Real.log (25000000000 / 37848573903) ∧
    -Real.log (25000000000 / 37848573903) ≤ (414717477 / 1000000000) := by
  have h := checkLog_sound (w := (12848573903 / 62848573903)) (n := 12)
    (lo := (103679369 / 250000000)) (hi := (414717477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37848573903 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37848573903 / 25000000000) = 1/(25000000000 / 37848573903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (103679369 / 250000000) (414717477 / 1000000000) (Real.log (37848573903 / 25000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (37848573903 / 25000000000) = -Real.log (25000000000 / 37848573903) := by
    rw [show ((37848573903 / 25000000000) : ℝ) = ((25000000000 / 37848573903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (415594193 / 1000000000) ≤ -Real.log (250000000000 / 378817709519) ∧
    -Real.log (250000000000 / 378817709519) ≤ (207797097 / 500000000) := by
  have h := checkLog_sound (w := (128817709519 / 628817709519)) (n := 12)
    (lo := (415594193 / 1000000000)) (hi := (207797097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((378817709519 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(378817709519 / 250000000000) = 1/(250000000000 / 378817709519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (415594193 / 1000000000) (207797097 / 500000000) (Real.log (378817709519 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (378817709519 / 250000000000) = -Real.log (250000000000 / 378817709519) := by
    rw [show ((378817709519 / 250000000000) : ℝ) = ((250000000000 / 378817709519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (2946167 / 10000000) ≤ -Real.log (250000000000 / 335652909289) ∧
    -Real.log (250000000000 / 335652909289) ≤ (294616701 / 1000000000) := by
  have h := checkLog_sound (w := (85652909289 / 585652909289)) (n := 12)
    (lo := (2946167 / 10000000)) (hi := (294616701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335652909289 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335652909289 / 250000000000) = 1/(250000000000 / 335652909289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2946167 / 10000000) (294616701 / 1000000000) (Real.log (335652909289 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (335652909289 / 250000000000) = -Real.log (250000000000 / 335652909289) := by
    rw [show ((335652909289 / 250000000000) : ℝ) = ((250000000000 / 335652909289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (295246193 / 1000000000) ≤ -Real.log (250000000000 / 335864266967) ∧
    -Real.log (250000000000 / 335864266967) ≤ (147623097 / 500000000) := by
  have h := checkLog_sound (w := (85864266967 / 585864266967)) (n := 12)
    (lo := (295246193 / 1000000000)) (hi := (147623097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335864266967 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335864266967 / 250000000000) = 1/(250000000000 / 335864266967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (295246193 / 1000000000) (147623097 / 500000000) (Real.log (335864266967 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (335864266967 / 250000000000) = -Real.log (250000000000 / 335864266967) := by
    rw [show ((335864266967 / 250000000000) : ℝ) = ((250000000000 / 335864266967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10856941 / 500000000) ≤ -Real.log (9555861 / 9765625) ∧
    -Real.log (9555861 / 9765625) ≤ (21713883 / 1000000000) := by
  have h := checkLog_sound (w := (104882 / 9660743)) (n := 12)
    (lo := (10856941 / 500000000)) (hi := (21713883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9555861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9555861) = 1/(9555861 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21713883 / 1000000000) (-10856941 / 500000000) (Real.log (9555861 / 9765625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21621721 / 1000000000) ≤ -Real.log (61163147031 / 62500000000) ∧
    -Real.log (61163147031 / 62500000000) ≤ (10810861 / 500000000) := by
  have h := checkLog_sound (w := (1336852969 / 123663147031)) (n := 12)
    (lo := (21621721 / 1000000000)) (hi := (10810861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61163147031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61163147031) = 1/(61163147031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10810861 / 500000000) (-21621721 / 1000000000) (Real.log (61163147031 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell065

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell066Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell066
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

theorem reflection_log_1_neg : (254066713 / 1000000000) ≤ -Real.log (5120 / 6601) ∧
    -Real.log (5120 / 6601) ≤ (127033357 / 500000000) := by
  have h := checkLog_sound (w := (1481 / 11721)) (n := 12)
    (lo := (254066713 / 1000000000)) (hi := (127033357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6601 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6601 / 5120) = 1/(5120 / 6601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (254066713 / 1000000000) (127033357 / 500000000) (Real.log (6601 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6601 / 5120) = -Real.log (5120 / 6601) := by
    rw [show ((6601 / 5120) : ℝ) = ((5120 / 6601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (4268069 / 12500000) ≤ -Real.log (3639 / 5120) ∧
    -Real.log (3639 / 5120) ≤ (341445521 / 1000000000) := by
  have h := checkLog_sound (w := (1481 / 8759)) (n := 12)
    (lo := (4268069 / 12500000)) (hi := (341445521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3639) = 1/(3639 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-341445521 / 1000000000) (-4268069 / 12500000) (Real.log (3639 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (253612133 / 1000000000) ≤ -Real.log (2560 / 3299) ∧
    -Real.log (2560 / 3299) ≤ (126806067 / 500000000) := by
  have h := checkLog_sound (w := (739 / 5859)) (n := 12)
    (lo := (253612133 / 1000000000)) (hi := (126806067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3299 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3299 / 2560) = 1/(2560 / 3299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (253612133 / 1000000000) (126806067 / 500000000) (Real.log (3299 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3299 / 2560) = -Real.log (2560 / 3299) := by
    rw [show ((3299 / 2560) : ℝ) = ((2560 / 3299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (340621457 / 1000000000) ≤ -Real.log (1821 / 2560) ∧
    -Real.log (1821 / 2560) ≤ (170310729 / 500000000) := by
  have h := checkLog_sound (w := (739 / 4381)) (n := 12)
    (lo := (340621457 / 1000000000)) (hi := (170310729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1821) = 1/(1821 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-170310729 / 500000000) (-340621457 / 1000000000) (Real.log (1821 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (186360057 / 1000000000) ≤ -Real.log (125000 / 150607) ∧
    -Real.log (125000 / 150607) ≤ (93180029 / 500000000) := by
  have h := checkLog_sound (w := (25607 / 275607)) (n := 12)
    (lo := (186360057 / 1000000000)) (hi := (93180029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150607 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150607 / 125000) = 1/(125000 / 150607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (186360057 / 1000000000) (93180029 / 500000000) (Real.log (150607 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (150607 / 125000) = -Real.log (125000 / 150607) := by
    rw [show ((150607 / 125000) : ℝ) = ((125000 / 150607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (14327003 / 62500000) ≤ -Real.log (99393 / 125000) ∧
    -Real.log (99393 / 125000) ≤ (229232049 / 1000000000) := by
  have h := checkLog_sound (w := (25607 / 224393)) (n := 12)
    (lo := (14327003 / 62500000)) (hi := (229232049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 99393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 99393) = 1/(99393 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-229232049 / 1000000000) (-14327003 / 62500000) (Real.log (99393 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (93354293 / 500000000) ≤ -Real.log (250000 / 301319) ∧
    -Real.log (250000 / 301319) ≤ (186708587 / 1000000000) := by
  have h := checkLog_sound (w := (51319 / 551319)) (n := 12)
    (lo := (93354293 / 500000000)) (hi := (186708587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301319 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301319 / 250000) = 1/(250000 / 301319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (93354293 / 500000000) (186708587 / 1000000000) (Real.log (301319 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (301319 / 250000) = -Real.log (250000 / 301319) := by
    rw [show ((301319 / 250000) : ℝ) = ((250000 / 301319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (114880197 / 500000000) ≤ -Real.log (198681 / 250000) ∧
    -Real.log (198681 / 250000) ≤ (45952079 / 200000000) := by
  have h := checkLog_sound (w := (51319 / 448681)) (n := 12)
    (lo := (114880197 / 500000000)) (hi := (45952079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 198681) = 1/(198681 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-45952079 / 200000000) (-114880197 / 500000000) (Real.log (198681 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68382641 / 500000000) ≤ -Real.log (1000000 / 1146559) ∧
    -Real.log (1000000 / 1146559) ≤ (136765283 / 1000000000) := by
  have h := checkLog_sound (w := (146559 / 2146559)) (n := 12)
    (lo := (68382641 / 500000000)) (hi := (136765283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1146559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1146559 / 1000000) = 1/(1000000 / 1146559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68382641 / 500000000) (136765283 / 1000000000) (Real.log (1146559 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1146559 / 1000000) = -Real.log (1000000 / 1146559) := by
    rw [show ((1146559 / 1000000) : ℝ) = ((1000000 / 1146559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (79239433 / 500000000) ≤ -Real.log (853441 / 1000000) ∧
    -Real.log (853441 / 1000000) ≤ (158478867 / 1000000000) := by
  have h := checkLog_sound (w := (146559 / 1853441)) (n := 12)
    (lo := (79239433 / 500000000)) (hi := (158478867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 853441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 853441) = 1/(853441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-158478867 / 1000000000) (-79239433 / 500000000) (Real.log (853441 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34258469 / 250000000) ≤ -Real.log (1000000 / 1146867) ∧
    -Real.log (1000000 / 1146867) ≤ (137033877 / 1000000000) := by
  have h := checkLog_sound (w := (146867 / 2146867)) (n := 12)
    (lo := (34258469 / 250000000)) (hi := (137033877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1146867 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1146867 / 1000000) = 1/(1000000 / 1146867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34258469 / 250000000) (137033877 / 1000000000) (Real.log (1146867 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1146867 / 1000000) = -Real.log (1000000 / 1146867) := by
    rw [show ((1146867 / 1000000) : ℝ) = ((1000000 / 1146867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (158839823 / 1000000000) ≤ -Real.log (853133 / 1000000) ∧
    -Real.log (853133 / 1000000) ≤ (9927489 / 62500000) := by
  have h := checkLog_sound (w := (146867 / 1853133)) (n := 12)
    (lo := (158839823 / 1000000000)) (hi := (9927489 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 853133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 853133) = 1/(853133 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-9927489 / 62500000) (-158839823 / 1000000000) (Real.log (853133 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (594233591 / 1000000000) ≤ -Real.log (125000000000 / 226455244371) ∧
    -Real.log (125000000000 / 226455244371) ≤ (74279199 / 125000000) := by
  have h := checkLog_sound (w := (101455244371 / 351455244371)) (n := 12)
    (lo := (594233591 / 1000000000)) (hi := (74279199 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226455244371 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226455244371 / 125000000000) = 1/(125000000000 / 226455244371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (594233591 / 1000000000) (74279199 / 125000000) (Real.log (226455244371 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (226455244371 / 125000000000) = -Real.log (125000000000 / 226455244371) := by
    rw [show ((226455244371 / 125000000000) : ℝ) = ((125000000000 / 226455244371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (297756117 / 500000000) ≤ -Real.log (62500000000 / 113372492443) ∧
    -Real.log (62500000000 / 113372492443) ≤ (119102447 / 200000000) := by
  have h := checkLog_sound (w := (50872492443 / 175872492443)) (n := 12)
    (lo := (297756117 / 500000000)) (hi := (119102447 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113372492443 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113372492443 / 62500000000) = 1/(62500000000 / 113372492443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (297756117 / 500000000) (119102447 / 200000000) (Real.log (113372492443 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (113372492443 / 62500000000) = -Real.log (62500000000 / 113372492443) := by
    rw [show ((113372492443 / 62500000000) : ℝ) = ((62500000000 / 113372492443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (207796053 / 500000000) ≤ -Real.log (31250000000 / 47352114837) ∧
    -Real.log (31250000000 / 47352114837) ≤ (415592107 / 1000000000) := by
  have h := checkLog_sound (w := (16102114837 / 78602114837)) (n := 12)
    (lo := (207796053 / 500000000)) (hi := (415592107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47352114837 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47352114837 / 31250000000) = 1/(31250000000 / 47352114837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (207796053 / 500000000) (415592107 / 1000000000) (Real.log (47352114837 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (47352114837 / 31250000000) = -Real.log (31250000000 / 47352114837) := by
    rw [show ((47352114837 / 31250000000) : ℝ) = ((31250000000 / 47352114837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (20823449 / 50000000) ≤ -Real.log (250000000000 / 379149239233) ∧
    -Real.log (250000000000 / 379149239233) ≤ (416468981 / 1000000000) := by
  have h := checkLog_sound (w := (129149239233 / 629149239233)) (n := 12)
    (lo := (20823449 / 50000000)) (hi := (416468981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379149239233 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379149239233 / 250000000000) = 1/(250000000000 / 379149239233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (20823449 / 50000000) (416468981 / 1000000000) (Real.log (379149239233 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (379149239233 / 250000000000) = -Real.log (250000000000 / 379149239233) := by
    rw [show ((379149239233 / 250000000000) : ℝ) = ((250000000000 / 379149239233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (295244149 / 1000000000) ≤ -Real.log (500000000000 / 671727160987) ∧
    -Real.log (500000000000 / 671727160987) ≤ (5904883 / 20000000) := by
  have h := checkLog_sound (w := (171727160987 / 1171727160987)) (n := 12)
    (lo := (295244149 / 1000000000)) (hi := (5904883 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671727160987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671727160987 / 500000000000) = 1/(500000000000 / 671727160987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (295244149 / 1000000000) (5904883 / 20000000) (Real.log (671727160987 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (671727160987 / 500000000000) = -Real.log (500000000000 / 671727160987) := by
    rw [show ((671727160987 / 500000000000) : ℝ) = ((500000000000 / 671727160987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2958737 / 10000000) ≤ -Real.log (50000000000 / 67215018057) ∧
    -Real.log (50000000000 / 67215018057) ≤ (295873701 / 1000000000) := by
  have h := checkLog_sound (w := (17215018057 / 117215018057)) (n := 12)
    (lo := (2958737 / 10000000)) (hi := (295873701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67215018057 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67215018057 / 50000000000) = 1/(50000000000 / 67215018057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2958737 / 10000000) (295873701 / 1000000000) (Real.log (67215018057 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (67215018057 / 50000000000) = -Real.log (50000000000 / 67215018057) := by
    rw [show ((67215018057 / 50000000000) : ℝ) = ((50000000000 / 67215018057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10902973 / 500000000) ≤ -Real.log (978430084311 / 1000000000000) ∧
    -Real.log (978430084311 / 1000000000000) ≤ (21805947 / 1000000000) := by
  have h := checkLog_sound (w := (21569915689 / 1978430084311)) (n := 12)
    (lo := (10902973 / 500000000)) (hi := (21805947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978430084311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978430084311) = 1/(978430084311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21805947 / 1000000000) (-10902973 / 500000000) (Real.log (978430084311 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21713583 / 1000000000) ≤ -Real.log (978520459519 / 1000000000000) ∧
    -Real.log (978520459519 / 1000000000000) ≤ (1357099 / 62500000) := by
  have h := checkLog_sound (w := (21479540481 / 1978520459519)) (n := 12)
    (lo := (21713583 / 1000000000)) (hi := (1357099 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978520459519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978520459519) = 1/(978520459519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1357099 / 62500000) (-21713583 / 1000000000) (Real.log (978520459519 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell066

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell067Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell067
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

theorem reflection_log_1_neg : (254521087 / 1000000000) ≤ -Real.log (1280 / 1651) ∧
    -Real.log (1280 / 1651) ≤ (994223 / 3906250) := by
  have h := checkLog_sound (w := (371 / 2931)) (n := 12)
    (lo := (254521087 / 1000000000)) (hi := (994223 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651 / 1280) = 1/(1280 / 1651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (254521087 / 1000000000) (994223 / 3906250) (Real.log (1651 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1651 / 1280) = -Real.log (1280 / 1651) := by
    rw [show ((1651 / 1280) : ℝ) = ((1280 / 1651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (171135131 / 500000000) ≤ -Real.log (909 / 1280) ∧
    -Real.log (909 / 1280) ≤ (342270263 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 2189)) (n := 12)
    (lo := (171135131 / 500000000)) (hi := (342270263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 909) = 1/(909 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-342270263 / 1000000000) (-171135131 / 500000000) (Real.log (909 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (254066713 / 1000000000) ≤ -Real.log (5120 / 6601) ∧
    -Real.log (5120 / 6601) ≤ (127033357 / 500000000) := by
  have h := checkLog_sound (w := (1481 / 11721)) (n := 12)
    (lo := (254066713 / 1000000000)) (hi := (127033357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6601 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6601 / 5120) = 1/(5120 / 6601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (254066713 / 1000000000) (127033357 / 500000000) (Real.log (6601 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6601 / 5120) = -Real.log (5120 / 6601) := by
    rw [show ((6601 / 5120) : ℝ) = ((5120 / 6601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (4268069 / 12500000) ≤ -Real.log (3639 / 5120) ∧
    -Real.log (3639 / 5120) ≤ (341445521 / 1000000000) := by
  have h := checkLog_sound (w := (1481 / 8759)) (n := 12)
    (lo := (4268069 / 12500000)) (hi := (341445521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3639) = 1/(3639 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-341445521 / 1000000000) (-4268069 / 12500000) (Real.log (3639 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (46676939 / 250000000) ≤ -Real.log (40000 / 48211) ∧
    -Real.log (40000 / 48211) ≤ (186707757 / 1000000000) := by
  have h := checkLog_sound (w := (8211 / 88211)) (n := 12)
    (lo := (46676939 / 250000000)) (hi := (186707757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48211 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48211 / 40000) = 1/(40000 / 48211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (46676939 / 250000000) (186707757 / 1000000000) (Real.log (48211 / 40000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48211 / 40000) = -Real.log (40000 / 48211) := by
    rw [show ((48211 / 40000) : ℝ) = ((40000 / 48211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (7179973 / 31250000) ≤ -Real.log (31789 / 40000) ∧
    -Real.log (31789 / 40000) ≤ (229759137 / 1000000000) := by
  have h := checkLog_sound (w := (8211 / 71789)) (n := 12)
    (lo := (7179973 / 31250000)) (hi := (229759137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31789) = 1/(31789 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-229759137 / 1000000000) (-7179973 / 31250000) (Real.log (31789 / 40000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (93527667 / 500000000) ≤ -Real.log (500000 / 602847) ∧
    -Real.log (500000 / 602847) ≤ (37411067 / 200000000) := by
  have h := checkLog_sound (w := (102847 / 1102847)) (n := 12)
    (lo := (93527667 / 500000000)) (hi := (37411067 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602847 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602847 / 500000) = 1/(500000 / 602847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (93527667 / 500000000) (37411067 / 200000000) (Real.log (602847 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (602847 / 500000) = -Real.log (500000 / 602847) := by
    rw [show ((602847 / 500000) : ℝ) = ((500000 / 602847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (230286501 / 1000000000) ≤ -Real.log (397153 / 500000) ∧
    -Real.log (397153 / 500000) ≤ (115143251 / 500000000) := by
  have h := checkLog_sound (w := (102847 / 897153)) (n := 12)
    (lo := (230286501 / 1000000000)) (hi := (115143251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 397153) = 1/(397153 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115143251 / 500000000) (-230286501 / 1000000000) (Real.log (397153 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (34258251 / 250000000) ≤ -Real.log (500000 / 573433) ∧
    -Real.log (500000 / 573433) ≤ (27406601 / 200000000) := by
  have h := checkLog_sound (w := (73433 / 1073433)) (n := 12)
    (lo := (34258251 / 250000000)) (hi := (27406601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573433 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(573433 / 500000) = 1/(500000 / 573433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (34258251 / 250000000) (27406601 / 200000000) (Real.log (573433 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (573433 / 500000) = -Real.log (500000 / 573433) := by
    rw [show ((573433 / 500000) : ℝ) = ((500000 / 573433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (158838651 / 1000000000) ≤ -Real.log (426567 / 500000) ∧
    -Real.log (426567 / 500000) ≤ (39709663 / 250000000) := by
  have h := checkLog_sound (w := (73433 / 926567)) (n := 12)
    (lo := (158838651 / 1000000000)) (hi := (39709663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 426567) = 1/(426567 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-39709663 / 250000000) (-158838651 / 1000000000) (Real.log (426567 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68650763 / 500000000) ≤ -Real.log (500000 / 573587) ∧
    -Real.log (500000 / 573587) ≤ (137301527 / 1000000000) := by
  have h := checkLog_sound (w := (73587 / 1073587)) (n := 12)
    (lo := (68650763 / 500000000)) (hi := (137301527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573587 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(573587 / 500000) = 1/(500000 / 573587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68650763 / 500000000) (137301527 / 1000000000) (Real.log (573587 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (573587 / 500000) = -Real.log (500000 / 573587) := by
    rw [show ((573587 / 500000) : ℝ) = ((500000 / 573587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (79599869 / 500000000) ≤ -Real.log (426413 / 500000) ∧
    -Real.log (426413 / 500000) ≤ (159199739 / 1000000000) := by
  have h := checkLog_sound (w := (73587 / 926413)) (n := 12)
    (lo := (79599869 / 500000000)) (hi := (159199739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 426413) = 1/(426413 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-159199739 / 1000000000) (-79599869 / 500000000) (Real.log (426413 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (297756117 / 500000000) ≤ -Real.log (500000000000 / 906979939543) ∧
    -Real.log (500000000000 / 906979939543) ≤ (119102447 / 200000000) := by
  have h := checkLog_sound (w := (406979939543 / 1406979939543)) (n := 12)
    (lo := (297756117 / 500000000)) (hi := (119102447 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((906979939543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(906979939543 / 500000000000) = 1/(500000000000 / 906979939543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (297756117 / 500000000) (119102447 / 200000000) (Real.log (906979939543 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (906979939543 / 500000000000) = -Real.log (500000000000 / 906979939543) := by
    rw [show ((906979939543 / 500000000000) : ℝ) = ((500000000000 / 906979939543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (596791349 / 1000000000) ≤ -Real.log (250000000000 / 454070407041) ∧
    -Real.log (250000000000 / 454070407041) ≤ (11935827 / 20000000) := by
  have h := checkLog_sound (w := (204070407041 / 704070407041)) (n := 12)
    (lo := (596791349 / 1000000000)) (hi := (11935827 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((454070407041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(454070407041 / 250000000000) = 1/(250000000000 / 454070407041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (596791349 / 1000000000) (11935827 / 20000000) (Real.log (454070407041 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (454070407041 / 250000000000) = -Real.log (250000000000 / 454070407041) := by
    rw [show ((454070407041 / 250000000000) : ℝ) = ((250000000000 / 454070407041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (104116723 / 250000000) ≤ -Real.log (31250000000 / 47393555947) ∧
    -Real.log (31250000000 / 47393555947) ≤ (416466893 / 1000000000) := by
  have h := checkLog_sound (w := (16143555947 / 78643555947)) (n := 12)
    (lo := (104116723 / 250000000)) (hi := (416466893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47393555947 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47393555947 / 31250000000) = 1/(31250000000 / 47393555947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (104116723 / 250000000) (416466893 / 1000000000) (Real.log (47393555947 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (47393555947 / 31250000000) = -Real.log (31250000000 / 47393555947) := by
    rw [show ((47393555947 / 31250000000) : ℝ) = ((31250000000 / 47393555947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (104335459 / 250000000) ≤ -Real.log (125000000000 / 189740163111) ∧
    -Real.log (125000000000 / 189740163111) ≤ (417341837 / 1000000000) := by
  have h := checkLog_sound (w := (64740163111 / 314740163111)) (n := 12)
    (lo := (104335459 / 250000000)) (hi := (417341837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189740163111 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189740163111 / 125000000000) = 1/(125000000000 / 189740163111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (104335459 / 250000000) (417341837 / 1000000000) (Real.log (189740163111 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (189740163111 / 125000000000) = -Real.log (125000000000 / 189740163111) := by
    rw [show ((189740163111 / 125000000000) : ℝ) = ((125000000000 / 189740163111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (36983957 / 125000000) ≤ -Real.log (100000000000 / 134429761327) ∧
    -Real.log (100000000000 / 134429761327) ≤ (295871657 / 1000000000) := by
  have h := checkLog_sound (w := (34429761327 / 234429761327)) (n := 12)
    (lo := (36983957 / 125000000)) (hi := (295871657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134429761327 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134429761327 / 100000000000) = 1/(100000000000 / 134429761327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (36983957 / 125000000) (295871657 / 1000000000) (Real.log (134429761327 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (134429761327 / 100000000000) = -Real.log (100000000000 / 134429761327) := by
    rw [show ((134429761327 / 100000000000) : ℝ) = ((100000000000 / 134429761327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (18531329 / 62500000) ≤ -Real.log (20000000000 / 26902885231) ∧
    -Real.log (20000000000 / 26902885231) ≤ (59300253 / 200000000) := by
  have h := checkLog_sound (w := (6902885231 / 46902885231)) (n := 12)
    (lo := (18531329 / 62500000)) (hi := (59300253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26902885231 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26902885231 / 20000000000) = 1/(20000000000 / 26902885231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (18531329 / 62500000) (59300253 / 200000000) (Real.log (26902885231 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (26902885231 / 20000000000) = -Real.log (20000000000 / 26902885231) := by
    rw [show ((26902885231 / 20000000000) : ℝ) = ((20000000000 / 26902885231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21898211 / 1000000000) ≤ -Real.log (244584953431 / 250000000000) ∧
    -Real.log (244584953431 / 250000000000) ≤ (5474553 / 250000000) := by
  have h := checkLog_sound (w := (5415046569 / 494584953431)) (n := 12)
    (lo := (21898211 / 1000000000)) (hi := (5474553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244584953431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244584953431) = 1/(244584953431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5474553 / 250000000) (-21898211 / 1000000000) (Real.log (244584953431 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (10902823 / 500000000) ≤ -Real.log (244607594511 / 250000000000) ∧
    -Real.log (244607594511 / 250000000000) ≤ (21805647 / 1000000000) := by
  have h := checkLog_sound (w := (5392405489 / 494607594511)) (n := 12)
    (lo := (10902823 / 500000000)) (hi := (21805647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244607594511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244607594511) = 1/(244607594511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21805647 / 1000000000) (-10902823 / 500000000) (Real.log (244607594511 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell067

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell068Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell068
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

theorem reflection_log_1_neg : (254975253 / 1000000000) ≤ -Real.log (5120 / 6607) ∧
    -Real.log (5120 / 6607) ≤ (127487627 / 500000000) := by
  have h := checkLog_sound (w := (1487 / 11727)) (n := 12)
    (lo := (254975253 / 1000000000)) (hi := (127487627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6607 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6607 / 5120) = 1/(5120 / 6607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (254975253 / 1000000000) (127487627 / 500000000) (Real.log (6607 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6607 / 5120) = -Real.log (5120 / 6607) := by
    rw [show ((6607 / 5120) : ℝ) = ((5120 / 6607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (68619137 / 200000000) ≤ -Real.log (3633 / 5120) ∧
    -Real.log (3633 / 5120) ≤ (171547843 / 500000000) := by
  have h := checkLog_sound (w := (1487 / 8753)) (n := 12)
    (lo := (68619137 / 200000000)) (hi := (171547843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3633) = 1/(3633 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-171547843 / 500000000) (-68619137 / 200000000) (Real.log (3633 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (254521087 / 1000000000) ≤ -Real.log (1280 / 1651) ∧
    -Real.log (1280 / 1651) ≤ (994223 / 3906250) := by
  have h := checkLog_sound (w := (371 / 2931)) (n := 12)
    (lo := (254521087 / 1000000000)) (hi := (994223 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651 / 1280) = 1/(1280 / 1651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (254521087 / 1000000000) (994223 / 3906250) (Real.log (1651 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1651 / 1280) = -Real.log (1280 / 1651) := by
    rw [show ((1651 / 1280) : ℝ) = ((1280 / 1651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (171135131 / 500000000) ≤ -Real.log (909 / 1280) ∧
    -Real.log (909 / 1280) ≤ (342270263 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 2189)) (n := 12)
    (lo := (171135131 / 500000000)) (hi := (342270263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 909) = 1/(909 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-342270263 / 1000000000) (-171135131 / 500000000) (Real.log (909 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (37410901 / 200000000) ≤ -Real.log (1000000 / 1205693) ∧
    -Real.log (1000000 / 1205693) ≤ (93527253 / 500000000) := by
  have h := checkLog_sound (w := (205693 / 2205693)) (n := 12)
    (lo := (37410901 / 200000000)) (hi := (93527253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205693 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1205693 / 1000000) = 1/(1000000 / 1205693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (37410901 / 200000000) (93527253 / 500000000) (Real.log (1205693 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1205693 / 1000000) = -Real.log (1000000 / 1205693) := by
    rw [show ((1205693 / 1000000) : ℝ) = ((1000000 / 1205693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (115142621 / 500000000) ≤ -Real.log (794307 / 1000000) ∧
    -Real.log (794307 / 1000000) ≤ (230285243 / 1000000000) := by
  have h := checkLog_sound (w := (205693 / 1794307)) (n := 12)
    (lo := (115142621 / 500000000)) (hi := (230285243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 794307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 794307) = 1/(794307 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-230285243 / 1000000000) (-115142621 / 500000000) (Real.log (794307 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23425349 / 125000000) ≤ -Real.log (1000000 / 1206113) ∧
    -Real.log (1000000 / 1206113) ≤ (187402793 / 1000000000) := by
  have h := checkLog_sound (w := (206113 / 2206113)) (n := 12)
    (lo := (23425349 / 125000000)) (hi := (187402793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206113 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206113 / 1000000) = 1/(1000000 / 1206113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23425349 / 125000000) (187402793 / 1000000000) (Real.log (1206113 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1206113 / 1000000) = -Real.log (1000000 / 1206113) := by
    rw [show ((1206113 / 1000000) : ℝ) = ((1000000 / 1206113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (46162829 / 200000000) ≤ -Real.log (793887 / 1000000) ∧
    -Real.log (793887 / 1000000) ≤ (115407073 / 500000000) := by
  have h := checkLog_sound (w := (206113 / 1793887)) (n := 12)
    (lo := (46162829 / 200000000)) (hi := (115407073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793887) = 1/(793887 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115407073 / 500000000) (-46162829 / 200000000) (Real.log (793887 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27460131 / 200000000) ≤ -Real.log (1000000 / 1147173) ∧
    -Real.log (1000000 / 1147173) ≤ (8581291 / 62500000) := by
  have h := checkLog_sound (w := (147173 / 2147173)) (n := 12)
    (lo := (27460131 / 200000000)) (hi := (8581291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1147173 / 1000000) = 1/(1000000 / 1147173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27460131 / 200000000) (8581291 / 62500000) (Real.log (1147173 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1147173 / 1000000) = -Real.log (1000000 / 1147173) := by
    rw [show ((1147173 / 1000000) : ℝ) = ((1000000 / 1147173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (31839713 / 200000000) ≤ -Real.log (852827 / 1000000) ∧
    -Real.log (852827 / 1000000) ≤ (79599283 / 500000000) := by
  have h := checkLog_sound (w := (147173 / 1852827)) (n := 12)
    (lo := (31839713 / 200000000)) (hi := (79599283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 852827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 852827) = 1/(852827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-79599283 / 500000000) (-31839713 / 200000000) (Real.log (852827 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (27513821 / 200000000) ≤ -Real.log (1000000 / 1147481) ∧
    -Real.log (1000000 / 1147481) ≤ (68784553 / 500000000) := by
  have h := checkLog_sound (w := (147481 / 2147481)) (n := 12)
    (lo := (27513821 / 200000000)) (hi := (68784553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147481 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1147481 / 1000000) = 1/(1000000 / 1147481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (27513821 / 200000000) (68784553 / 500000000) (Real.log (1147481 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1147481 / 1000000) = -Real.log (1000000 / 1147481) := by
    rw [show ((1147481 / 1000000) : ℝ) = ((1000000 / 1147481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (79779891 / 500000000) ≤ -Real.log (852519 / 1000000) ∧
    -Real.log (852519 / 1000000) ≤ (159559783 / 1000000000) := by
  have h := checkLog_sound (w := (147481 / 1852519)) (n := 12)
    (lo := (79779891 / 500000000)) (hi := (159559783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 852519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 852519) = 1/(852519 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-159559783 / 1000000000) (-79779891 / 500000000) (Real.log (852519 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (596791349 / 1000000000) ≤ -Real.log (500000000000 / 908140814081) ∧
    -Real.log (500000000000 / 908140814081) ≤ (11935827 / 20000000) := by
  have h := checkLog_sound (w := (408140814081 / 1408140814081)) (n := 12)
    (lo := (596791349 / 1000000000)) (hi := (11935827 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((908140814081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(908140814081 / 500000000000) = 1/(500000000000 / 908140814081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (596791349 / 1000000000) (11935827 / 20000000) (Real.log (908140814081 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (908140814081 / 500000000000) = -Real.log (500000000000 / 908140814081) := by
    rw [show ((908140814081 / 500000000000) : ℝ) = ((500000000000 / 908140814081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (598070939 / 1000000000) ≤ -Real.log (125000000000 / 227325901459) ∧
    -Real.log (125000000000 / 227325901459) ≤ (29903547 / 50000000) := by
  have h := checkLog_sound (w := (102325901459 / 352325901459)) (n := 12)
    (lo := (598070939 / 1000000000)) (hi := (29903547 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227325901459 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227325901459 / 125000000000) = 1/(125000000000 / 227325901459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (598070939 / 1000000000) (29903547 / 50000000) (Real.log (227325901459 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (227325901459 / 125000000000) = -Real.log (125000000000 / 227325901459) := by
    rw [show ((227325901459 / 125000000000) : ℝ) = ((125000000000 / 227325901459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (417339747 / 1000000000) ≤ -Real.log (500000000000 / 758959067463) ∧
    -Real.log (500000000000 / 758959067463) ≤ (104334937 / 250000000) := by
  have h := checkLog_sound (w := (258959067463 / 1258959067463)) (n := 12)
    (lo := (417339747 / 1000000000)) (hi := (104334937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758959067463 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(758959067463 / 500000000000) = 1/(500000000000 / 758959067463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (417339747 / 1000000000) (104334937 / 250000000) (Real.log (758959067463 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (758959067463 / 500000000000) = -Real.log (500000000000 / 758959067463) := by
    rw [show ((758959067463 / 500000000000) : ℝ) = ((500000000000 / 758959067463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (418216937 / 1000000000) ≤ -Real.log (4000000000 / 6077000883) ∧
    -Real.log (4000000000 / 6077000883) ≤ (209108469 / 500000000) := by
  have h := checkLog_sound (w := (2077000883 / 10077000883)) (n := 12)
    (lo := (418216937 / 1000000000)) (hi := (209108469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6077000883 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6077000883 / 4000000000) = 1/(4000000000 / 6077000883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (418216937 / 1000000000) (209108469 / 500000000) (Real.log (6077000883 / 4000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (6077000883 / 4000000000) = -Real.log (4000000000 / 6077000883) := by
    rw [show ((6077000883 / 4000000000) : ℝ) = ((4000000000 / 6077000883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14824961 / 50000000) ≤ -Real.log (10000000000 / 13451415117) ∧
    -Real.log (10000000000 / 13451415117) ≤ (296499221 / 1000000000) := by
  have h := checkLog_sound (w := (3451415117 / 23451415117)) (n := 12)
    (lo := (14824961 / 50000000)) (hi := (296499221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13451415117 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13451415117 / 10000000000) = 1/(10000000000 / 13451415117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14824961 / 50000000) (296499221 / 1000000000) (Real.log (13451415117 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (13451415117 / 10000000000) = -Real.log (10000000000 / 13451415117) := by
    rw [show ((13451415117 / 10000000000) : ℝ) = ((10000000000 / 13451415117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (297128887 / 1000000000) ≤ -Real.log (125000000000 / 168248596219) ∧
    -Real.log (125000000000 / 168248596219) ≤ (37141111 / 125000000) := by
  have h := checkLog_sound (w := (43248596219 / 293248596219)) (n := 12)
    (lo := (297128887 / 1000000000)) (hi := (37141111 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168248596219 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168248596219 / 125000000000) = 1/(125000000000 / 168248596219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (297128887 / 1000000000) (37141111 / 125000000) (Real.log (168248596219 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (168248596219 / 125000000000) = -Real.log (125000000000 / 168248596219) := by
    rw [show ((168248596219 / 125000000000) : ℝ) = ((125000000000 / 168248596219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21990677 / 1000000000) ≤ -Real.log (978249354639 / 1000000000000) ∧
    -Real.log (978249354639 / 1000000000000) ≤ (10995339 / 500000000) := by
  have h := checkLog_sound (w := (21750645361 / 1978249354639)) (n := 12)
    (lo := (21990677 / 1000000000)) (hi := (10995339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978249354639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978249354639) = 1/(978249354639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-10995339 / 500000000) (-21990677 / 1000000000) (Real.log (978249354639 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2189791 / 100000000) ≤ -Real.log (978340108071 / 1000000000000) ∧
    -Real.log (978340108071 / 1000000000000) ≤ (21897911 / 1000000000) := by
  have h := checkLog_sound (w := (21659891929 / 1978340108071)) (n := 12)
    (lo := (2189791 / 100000000)) (hi := (21897911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978340108071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978340108071) = 1/(978340108071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21897911 / 1000000000) (-2189791 / 100000000) (Real.log (978340108071 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell068

end


