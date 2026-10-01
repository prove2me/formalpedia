-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0163Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0163Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:23:07.658215+00:00
-- url     : https://prove2.me/theorems/3d5d43cc-8f86-47a1-8085-e50294616077
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0163Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0164Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0163Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0164Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0165Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0166Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0167Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0168Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0163Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0164Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0165Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0166Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0167Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0168Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0163Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0164Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0165Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0166Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0167Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0168Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0163Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0164Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0165Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0166Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0167Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0168Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0163Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0163
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

theorem reflection_log_1_neg : (8817163 / 31250000) ≤ -Real.log (5120 / 6789) ∧
    -Real.log (5120 / 6789) ≤ (282149217 / 1000000000) := by
  have h := checkLog_sound (w := (1669 / 11909)) (n := 12)
    (lo := (8817163 / 31250000)) (hi := (282149217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6789 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6789 / 5120) = 1/(5120 / 6789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8817163 / 31250000) (282149217 / 1000000000) (Real.log (6789 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6789 / 5120) = -Real.log (5120 / 6789) := by
    rw [show ((6789 / 5120) : ℝ) = ((5120 / 6789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (197245197 / 500000000) ≤ -Real.log (3451 / 5120) ∧
    -Real.log (3451 / 5120) ≤ (78898079 / 200000000) := by
  have h := checkLog_sound (w := (1669 / 8571)) (n := 12)
    (lo := (197245197 / 500000000)) (hi := (78898079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3451) = 1/(3451 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-78898079 / 200000000) (-197245197 / 500000000) (Real.log (3451 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (281707227 / 1000000000) ≤ -Real.log (2560 / 3393) ∧
    -Real.log (2560 / 3393) ≤ (70426807 / 250000000) := by
  have h := checkLog_sound (w := (833 / 5953)) (n := 12)
    (lo := (281707227 / 1000000000)) (hi := (70426807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3393 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3393 / 2560) = 1/(2560 / 3393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (281707227 / 1000000000) (70426807 / 250000000) (Real.log (3393 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3393 / 2560) = -Real.log (2560 / 3393) := by
    rw [show ((3393 / 2560) : ℝ) = ((2560 / 3393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (393621459 / 1000000000) ≤ -Real.log (1727 / 2560) ∧
    -Real.log (1727 / 2560) ≤ (19681073 / 50000000) := by
  have h := checkLog_sound (w := (833 / 4287)) (n := 12)
    (lo := (393621459 / 1000000000)) (hi := (19681073 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1727) = 1/(1727 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-19681073 / 50000000) (-393621459 / 1000000000) (Real.log (1727 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (501958299 / 1000000000) ≤ -Real.log (2560 / 4229) ∧
    -Real.log (2560 / 4229) ≤ (5019583 / 10000000) := by
  have h := checkLog_sound (w := (1669 / 6789)) (n := 12)
    (lo := (501958299 / 1000000000)) (hi := (5019583 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4229 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4229 / 2560) = 1/(2560 / 4229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (501958299 / 1000000000) (5019583 / 10000000) (Real.log (4229 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4229 / 2560) = -Real.log (2560 / 4229) := by
    rw [show ((4229 / 2560) : ℝ) = ((2560 / 4229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1055418109 / 1000000000) ≤ -Real.log (891 / 2560) ∧
    -Real.log (891 / 2560) ≤ (1055418111 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 2171)) (n := 12)
    (lo := (362270929 / 1000000000)) (hi := (36227093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 891) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 891) = 1/(891 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1055418111 / 1000000000) (-1055418109 / 1000000000) (Real.log (891 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25062433 / 50000000) ≤ -Real.log (1280 / 2113) ∧
    -Real.log (1280 / 2113) ≤ (501248661 / 1000000000) := by
  have h := checkLog_sound (w := (833 / 3393)) (n := 12)
    (lo := (25062433 / 50000000)) (hi := (501248661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2113 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2113 / 1280) = 1/(1280 / 2113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25062433 / 50000000) (501248661 / 1000000000) (Real.log (2113 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2113 / 1280) = -Real.log (1280 / 2113) := by
    rw [show ((2113 / 1280) : ℝ) = ((1280 / 2113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1052056761 / 1000000000) ≤ -Real.log (447 / 1280) ∧
    -Real.log (447 / 1280) ≤ (1052056763 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1087)) (n := 12)
    (lo := (358909581 / 1000000000)) (hi := (179454791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 447) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 447) = 1/(447 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1052056763 / 1000000000) (-1052056761 / 1000000000) (Real.log (447 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4817251 / 12500000) ≤ -Real.log (1000000 / 1470173) ∧
    -Real.log (1000000 / 1470173) ≤ (385380081 / 1000000000) := by
  have h := checkLog_sound (w := (470173 / 2470173)) (n := 12)
    (lo := (4817251 / 12500000)) (hi := (385380081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1470173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1470173 / 1000000) = 1/(1000000 / 1470173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4817251 / 12500000) (385380081 / 1000000000) (Real.log (1470173 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1470173 / 1000000) = -Real.log (1000000 / 1470173) := by
    rw [show ((1470173 / 1000000) : ℝ) = ((1000000 / 1470173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (31760237 / 50000000) ≤ -Real.log (529827 / 1000000) ∧
    -Real.log (529827 / 1000000) ≤ (635204741 / 1000000000) := by
  have h := checkLog_sound (w := (470173 / 1529827)) (n := 12)
    (lo := (31760237 / 50000000)) (hi := (635204741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 529827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 529827) = 1/(529827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-635204741 / 1000000000) (-31760237 / 50000000) (Real.log (529827 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (96496827 / 250000000) ≤ -Real.log (500000 / 735533) ∧
    -Real.log (500000 / 735533) ≤ (385987309 / 1000000000) := by
  have h := checkLog_sound (w := (235533 / 1235533)) (n := 12)
    (lo := (96496827 / 250000000)) (hi := (385987309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735533 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735533 / 500000) = 1/(500000 / 735533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (96496827 / 250000000) (385987309 / 1000000000) (Real.log (735533 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (735533 / 500000) = -Real.log (500000 / 735533) := by
    rw [show ((735533 / 500000) : ℝ) = ((500000 / 735533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (318445809 / 500000000) ≤ -Real.log (264467 / 500000) ∧
    -Real.log (264467 / 500000) ≤ (636891619 / 1000000000) := by
  have h := checkLog_sound (w := (235533 / 764467)) (n := 12)
    (lo := (318445809 / 500000000)) (hi := (636891619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 264467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 264467) = 1/(264467 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-636891619 / 1000000000) (-318445809 / 500000000) (Real.log (264467 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (18944541 / 62500000) ≤ -Real.log (1000000 / 1354067) ∧
    -Real.log (1000000 / 1354067) ≤ (303112657 / 1000000000) := by
  have h := checkLog_sound (w := (354067 / 2354067)) (n := 12)
    (lo := (18944541 / 62500000)) (hi := (303112657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1354067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1354067 / 1000000) = 1/(1000000 / 1354067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (18944541 / 62500000) (303112657 / 1000000000) (Real.log (1354067 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1354067 / 1000000) = -Real.log (1000000 / 1354067) := by
    rw [show ((1354067 / 1000000) : ℝ) = ((1000000 / 1354067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (87411899 / 200000000) ≤ -Real.log (645933 / 1000000) ∧
    -Real.log (645933 / 1000000) ≤ (54632437 / 125000000) := by
  have h := checkLog_sound (w := (354067 / 1645933)) (n := 12)
    (lo := (87411899 / 200000000)) (hi := (54632437 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 645933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 645933) = 1/(645933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-54632437 / 125000000) (-87411899 / 200000000) (Real.log (645933 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (30367377 / 100000000) ≤ -Real.log (1000000 / 1354827) ∧
    -Real.log (1000000 / 1354827) ≤ (303673771 / 1000000000) := by
  have h := checkLog_sound (w := (354827 / 2354827)) (n := 12)
    (lo := (30367377 / 100000000)) (hi := (303673771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1354827 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1354827 / 1000000) = 1/(1000000 / 1354827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (30367377 / 100000000) (303673771 / 1000000000) (Real.log (1354827 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1354827 / 1000000) = -Real.log (1000000 / 1354827) := by
    rw [show ((1354827 / 1000000) : ℝ) = ((1000000 / 1354827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (438236781 / 1000000000) ≤ -Real.log (645173 / 1000000) ∧
    -Real.log (645173 / 1000000) ≤ (219118391 / 500000000) := by
  have h := checkLog_sound (w := (354827 / 1645173)) (n := 12)
    (lo := (438236781 / 1000000000)) (hi := (219118391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 645173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 645173) = 1/(645173 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-219118391 / 500000000) (-438236781 / 1000000000) (Real.log (645173 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1020584821 / 1000000000) ≤ -Real.log (62500000000 / 173426066433) ∧
    -Real.log (62500000000 / 173426066433) ≤ (1020584823 / 1000000000) := by
  have h := checkLog_sound (w := (48426066433 / 298426066433)) (n := 12)
    (lo := (327437641 / 1000000000)) (hi := (163718821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173426066433 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(173426066433 / 125000000000) = 1/(62500000000 / 173426066433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1020584821 / 1000000000) (1020584823 / 1000000000) (Real.log (173426066433 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (173426066433 / 62500000000) = -Real.log (62500000000 / 173426066433) := by
    rw [show ((173426066433 / 62500000000) : ℝ) = ((62500000000 / 173426066433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (511439463 / 500000000) ≤ -Real.log (100000000000 / 278119009177) ∧
    -Real.log (100000000000 / 278119009177) ≤ (63929933 / 62500000) := by
  have h := checkLog_sound (w := (78119009177 / 478119009177)) (n := 12)
    (lo := (164865873 / 500000000)) (hi := (329731747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278119009177 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(278119009177 / 200000000000) = 1/(100000000000 / 278119009177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (511439463 / 500000000) (63929933 / 62500000) (Real.log (278119009177 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (278119009177 / 100000000000) = -Real.log (100000000000 / 278119009177) := by
    rw [show ((278119009177 / 100000000000) : ℝ) = ((100000000000 / 278119009177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (740172151 / 1000000000) ≤ -Real.log (500000000000 / 1048148182551) ∧
    -Real.log (500000000000 / 1048148182551) ≤ (740172153 / 1000000000) := by
  have h := checkLog_sound (w := (48148182551 / 2048148182551)) (n := 12)
    (lo := (47024971 / 1000000000)) (hi := (11756243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1048148182551 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1048148182551 / 1000000000000) = 1/(500000000000 / 1048148182551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (740172151 / 1000000000) (740172153 / 1000000000) (Real.log (1048148182551 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1048148182551 / 500000000000) = -Real.log (500000000000 / 1048148182551) := by
    rw [show ((1048148182551 / 500000000000) : ℝ) = ((500000000000 / 1048148182551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (741910551 / 1000000000) ≤ -Real.log (500000000000 / 1049971868011) ∧
    -Real.log (500000000000 / 1049971868011) ≤ (741910553 / 1000000000) := by
  have h := checkLog_sound (w := (49971868011 / 2049971868011)) (n := 12)
    (lo := (48763371 / 1000000000)) (hi := (12190843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1049971868011 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1049971868011 / 1000000000000) = 1/(500000000000 / 1049971868011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (741910551 / 1000000000) (741910553 / 1000000000) (Real.log (1049971868011 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1049971868011 / 500000000000) = -Real.log (500000000000 / 1049971868011) := by
    rw [show ((1049971868011 / 500000000000) : ℝ) = ((500000000000 / 1049971868011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0163

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0164Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0164
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

theorem reflection_log_1_neg : (281707227 / 1000000000) ≤ -Real.log (2560 / 3393) ∧
    -Real.log (2560 / 3393) ≤ (70426807 / 250000000) := by
  have h := checkLog_sound (w := (833 / 5953)) (n := 12)
    (lo := (281707227 / 1000000000)) (hi := (70426807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3393 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3393 / 2560) = 1/(2560 / 3393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (281707227 / 1000000000) (70426807 / 250000000) (Real.log (3393 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3393 / 2560) = -Real.log (2560 / 3393) := by
    rw [show ((3393 / 2560) : ℝ) = ((2560 / 3393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (393621459 / 1000000000) ≤ -Real.log (1727 / 2560) ∧
    -Real.log (1727 / 2560) ≤ (19681073 / 50000000) := by
  have h := checkLog_sound (w := (833 / 4287)) (n := 12)
    (lo := (393621459 / 1000000000)) (hi := (19681073 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1727) = 1/(1727 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-19681073 / 50000000) (-393621459 / 1000000000) (Real.log (1727 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (140632521 / 500000000) ≤ -Real.log (5120 / 6783) ∧
    -Real.log (5120 / 6783) ≤ (281265043 / 1000000000) := by
  have h := checkLog_sound (w := (1663 / 11903)) (n := 12)
    (lo := (140632521 / 500000000)) (hi := (281265043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6783 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6783 / 5120) = 1/(5120 / 6783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (140632521 / 500000000) (281265043 / 1000000000) (Real.log (6783 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6783 / 5120) = -Real.log (5120 / 6783) := by
    rw [show ((6783 / 5120) : ℝ) = ((5120 / 6783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (196376639 / 500000000) ≤ -Real.log (3457 / 5120) ∧
    -Real.log (3457 / 5120) ≤ (392753279 / 1000000000) := by
  have h := checkLog_sound (w := (1663 / 8577)) (n := 12)
    (lo := (196376639 / 500000000)) (hi := (392753279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3457) = 1/(3457 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-392753279 / 1000000000) (-196376639 / 500000000) (Real.log (3457 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (25062433 / 50000000) ≤ -Real.log (1280 / 2113) ∧
    -Real.log (1280 / 2113) ≤ (501248661 / 1000000000) := by
  have h := checkLog_sound (w := (833 / 3393)) (n := 12)
    (lo := (25062433 / 50000000)) (hi := (501248661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2113 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2113 / 1280) = 1/(1280 / 2113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (25062433 / 50000000) (501248661 / 1000000000) (Real.log (2113 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2113 / 1280) = -Real.log (1280 / 2113) := by
    rw [show ((2113 / 1280) : ℝ) = ((1280 / 2113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1052056761 / 1000000000) ≤ -Real.log (447 / 1280) ∧
    -Real.log (447 / 1280) ≤ (1052056763 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1087)) (n := 12)
    (lo := (358909581 / 1000000000)) (hi := (179454791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 447) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 447) = 1/(447 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1052056763 / 1000000000) (-1052056761 / 1000000000) (Real.log (447 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (500538517 / 1000000000) ≤ -Real.log (2560 / 4223) ∧
    -Real.log (2560 / 4223) ≤ (250269259 / 500000000) := by
  have h := checkLog_sound (w := (1663 / 6783)) (n := 12)
    (lo := (500538517 / 1000000000)) (hi := (250269259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4223 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4223 / 2560) = 1/(2560 / 4223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (500538517 / 1000000000) (250269259 / 500000000) (Real.log (4223 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4223 / 2560) = -Real.log (2560 / 4223) := by
    rw [show ((4223 / 2560) : ℝ) = ((2560 / 4223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (524353337 / 500000000) ≤ -Real.log (897 / 2560) ∧
    -Real.log (897 / 2560) ≤ (262176669 / 250000000) := by
  have h := checkLog_sound (w := (383 / 2177)) (n := 12)
    (lo := (177779747 / 500000000)) (hi := (71111899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 897) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 897) = 1/(897 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-262176669 / 250000000) (-524353337 / 500000000) (Real.log (897 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (76954633 / 200000000) ≤ -Real.log (1000000 / 1469281) ∧
    -Real.log (1000000 / 1469281) ≤ (192386583 / 500000000) := by
  have h := checkLog_sound (w := (469281 / 2469281)) (n := 12)
    (lo := (76954633 / 200000000)) (hi := (192386583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1469281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1469281 / 1000000) = 1/(1000000 / 1469281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (76954633 / 200000000) (192386583 / 500000000) (Real.log (1469281 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1469281 / 1000000) = -Real.log (1000000 / 1469281) := by
    rw [show ((1469281 / 1000000) : ℝ) = ((1000000 / 1469281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (158380647 / 250000000) ≤ -Real.log (530719 / 1000000) ∧
    -Real.log (530719 / 1000000) ≤ (633522589 / 1000000000) := by
  have h := checkLog_sound (w := (469281 / 1530719)) (n := 12)
    (lo := (158380647 / 250000000)) (hi := (633522589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 530719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 530719) = 1/(530719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-633522589 / 1000000000) (-158380647 / 250000000) (Real.log (530719 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (385380761 / 1000000000) ≤ -Real.log (500000 / 735087) ∧
    -Real.log (500000 / 735087) ≤ (192690381 / 500000000) := by
  have h := checkLog_sound (w := (235087 / 1235087)) (n := 12)
    (lo := (385380761 / 1000000000)) (hi := (192690381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735087 / 500000) = 1/(500000 / 735087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (385380761 / 1000000000) (192690381 / 500000000) (Real.log (735087 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (735087 / 500000) = -Real.log (500000 / 735087) := by
    rw [show ((735087 / 500000) : ℝ) = ((500000 / 735087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (158801657 / 250000000) ≤ -Real.log (264913 / 500000) ∧
    -Real.log (264913 / 500000) ≤ (635206629 / 1000000000) := by
  have h := checkLog_sound (w := (235087 / 764913)) (n := 12)
    (lo := (158801657 / 250000000)) (hi := (635206629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 264913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 264913) = 1/(264913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-635206629 / 1000000000) (-158801657 / 250000000) (Real.log (264913 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2363693 / 7812500) ≤ -Real.log (1000000 / 1353309) ∧
    -Real.log (1000000 / 1353309) ≤ (60510541 / 200000000) := by
  have h := checkLog_sound (w := (353309 / 2353309)) (n := 12)
    (lo := (2363693 / 7812500)) (hi := (60510541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353309 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353309 / 1000000) = 1/(1000000 / 1353309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2363693 / 7812500) (60510541 / 200000000) (Real.log (1353309 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1353309 / 1000000) = -Real.log (1000000 / 1353309) := by
    rw [show ((1353309 / 1000000) : ℝ) = ((1000000 / 1353309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (435886687 / 1000000000) ≤ -Real.log (646691 / 1000000) ∧
    -Real.log (646691 / 1000000) ≤ (13621459 / 31250000) := by
  have h := checkLog_sound (w := (353309 / 1646691)) (n := 12)
    (lo := (435886687 / 1000000000)) (hi := (13621459 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 646691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 646691) = 1/(646691 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-13621459 / 31250000) (-435886687 / 1000000000) (Real.log (646691 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (151556697 / 500000000) ≤ -Real.log (250000 / 338517) ∧
    -Real.log (250000 / 338517) ≤ (60622679 / 200000000) := by
  have h := checkLog_sound (w := (88517 / 588517)) (n := 12)
    (lo := (151556697 / 500000000)) (hi := (60622679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338517 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338517 / 250000) = 1/(250000 / 338517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (151556697 / 500000000) (60622679 / 200000000) (Real.log (338517 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (338517 / 250000) = -Real.log (250000 / 338517) := by
    rw [show ((338517 / 250000) : ℝ) = ((250000 / 338517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (437061043 / 1000000000) ≤ -Real.log (161483 / 250000) ∧
    -Real.log (161483 / 250000) ≤ (109265261 / 250000000) := by
  have h := checkLog_sound (w := (88517 / 411483)) (n := 12)
    (lo := (437061043 / 1000000000)) (hi := (109265261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 161483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 161483) = 1/(161483 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-109265261 / 250000000) (-437061043 / 1000000000) (Real.log (161483 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (127286969 / 125000000) ≤ -Real.log (500000000000 / 1384236290767) ∧
    -Real.log (500000000000 / 1384236290767) ≤ (509147877 / 500000000) := by
  have h := checkLog_sound (w := (384236290767 / 2384236290767)) (n := 12)
    (lo := (81287143 / 250000000)) (hi := (325148573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1384236290767 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1384236290767 / 1000000000000) = 1/(500000000000 / 1384236290767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (127286969 / 125000000) (509147877 / 500000000) (Real.log (1384236290767 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1384236290767 / 500000000000) = -Real.log (500000000000 / 1384236290767) := by
    rw [show ((1384236290767 / 500000000000) : ℝ) = ((500000000000 / 1384236290767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (255146847 / 250000000) ≤ -Real.log (250000000000 / 693706046891) ∧
    -Real.log (250000000000 / 693706046891) ≤ (102058739 / 100000000) := by
  have h := checkLog_sound (w := (193706046891 / 1193706046891)) (n := 12)
    (lo := (20465013 / 62500000)) (hi := (327440209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693706046891 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(693706046891 / 500000000000) = 1/(250000000000 / 693706046891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (255146847 / 250000000) (102058739 / 100000000) (Real.log (693706046891 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (693706046891 / 250000000000) = -Real.log (250000000000 / 693706046891) := by
    rw [show ((693706046891 / 250000000000) : ℝ) = ((250000000000 / 693706046891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (738439391 / 1000000000) ≤ -Real.log (250000000000 / 523166782899) ∧
    -Real.log (250000000000 / 523166782899) ≤ (738439393 / 1000000000) := by
  have h := checkLog_sound (w := (23166782899 / 1023166782899)) (n := 12)
    (lo := (45292211 / 1000000000)) (hi := (11323053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((523166782899 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(523166782899 / 500000000000) = 1/(250000000000 / 523166782899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (738439391 / 1000000000) (738439393 / 1000000000) (Real.log (523166782899 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (523166782899 / 250000000000) = -Real.log (250000000000 / 523166782899) := by
    rw [show ((523166782899 / 250000000000) : ℝ) = ((250000000000 / 523166782899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (370087219 / 500000000) ≤ -Real.log (250000000000 / 524075289659) ∧
    -Real.log (250000000000 / 524075289659) ≤ (18504361 / 25000000) := by
  have h := checkLog_sound (w := (24075289659 / 1024075289659)) (n := 12)
    (lo := (23513629 / 500000000)) (hi := (47027259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((524075289659 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(524075289659 / 500000000000) = 1/(250000000000 / 524075289659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (370087219 / 500000000) (18504361 / 25000000) (Real.log (524075289659 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (524075289659 / 250000000000) = -Real.log (250000000000 / 524075289659) := by
    rw [show ((524075289659 / 250000000000) : ℝ) = ((250000000000 / 524075289659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0164

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0165Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0165
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

theorem reflection_log_1_neg : (140632521 / 500000000) ≤ -Real.log (5120 / 6783) ∧
    -Real.log (5120 / 6783) ≤ (281265043 / 1000000000) := by
  have h := checkLog_sound (w := (1663 / 11903)) (n := 12)
    (lo := (140632521 / 500000000)) (hi := (281265043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6783 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6783 / 5120) = 1/(5120 / 6783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (140632521 / 500000000) (281265043 / 1000000000) (Real.log (6783 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6783 / 5120) = -Real.log (5120 / 6783) := by
    rw [show ((6783 / 5120) : ℝ) = ((5120 / 6783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (196376639 / 500000000) ≤ -Real.log (3457 / 5120) ∧
    -Real.log (3457 / 5120) ≤ (392753279 / 1000000000) := by
  have h := checkLog_sound (w := (1663 / 8577)) (n := 12)
    (lo := (196376639 / 500000000)) (hi := (392753279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3457) = 1/(3457 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-392753279 / 1000000000) (-196376639 / 500000000) (Real.log (3457 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (140411331 / 500000000) ≤ -Real.log (256 / 339) ∧
    -Real.log (256 / 339) ≤ (280822663 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 595)) (n := 12)
    (lo := (140411331 / 500000000)) (hi := (280822663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 256) = 1/(256 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (140411331 / 500000000) (280822663 / 1000000000) (Real.log (339 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (339 / 256) = -Real.log (256 / 339) := by
    rw [show ((339 / 256) : ℝ) = ((256 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (391885849 / 1000000000) ≤ -Real.log (173 / 256) ∧
    -Real.log (173 / 256) ≤ (7837717 / 20000000) := by
  have h := checkLog_sound (w := (83 / 429)) (n := 12)
    (lo := (391885849 / 1000000000)) (hi := (7837717 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 173) = 1/(173 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7837717 / 20000000) (-391885849 / 1000000000) (Real.log (173 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (500538517 / 1000000000) ≤ -Real.log (2560 / 4223) ∧
    -Real.log (2560 / 4223) ≤ (250269259 / 500000000) := by
  have h := checkLog_sound (w := (1663 / 6783)) (n := 12)
    (lo := (500538517 / 1000000000)) (hi := (250269259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4223 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4223 / 2560) = 1/(2560 / 4223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (500538517 / 1000000000) (250269259 / 500000000) (Real.log (4223 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4223 / 2560) = -Real.log (2560 / 4223) := by
    rw [show ((4223 / 2560) : ℝ) = ((2560 / 4223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (524353337 / 500000000) ≤ -Real.log (897 / 2560) ∧
    -Real.log (897 / 2560) ≤ (262176669 / 250000000) := by
  have h := checkLog_sound (w := (383 / 2177)) (n := 12)
    (lo := (177779747 / 500000000)) (hi := (71111899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 897) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 897) = 1/(897 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-262176669 / 250000000) (-524353337 / 500000000) (Real.log (897 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (499827869 / 1000000000) ≤ -Real.log (128 / 211) ∧
    -Real.log (128 / 211) ≤ (49982787 / 100000000) := by
  have h := checkLog_sound (w := (83 / 339)) (n := 12)
    (lo := (499827869 / 1000000000)) (hi := (49982787 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211 / 128) = 1/(128 / 211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (499827869 / 1000000000) (49982787 / 100000000) (Real.log (211 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (211 / 128) = -Real.log (128 / 211) := by
    rw [show ((211 / 128) : ℝ) = ((128 / 211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1045367773 / 1000000000) ≤ -Real.log (45 / 128) ∧
    -Real.log (45 / 128) ≤ (41814711 / 40000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 45) = 1/(45 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-41814711 / 40000000) (-1045367773 / 1000000000) (Real.log (45 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (192083281 / 500000000) ≤ -Real.log (100000 / 146839) ∧
    -Real.log (100000 / 146839) ≤ (384166563 / 1000000000) := by
  have h := checkLog_sound (w := (46839 / 246839)) (n := 12)
    (lo := (192083281 / 500000000)) (hi := (384166563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146839 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146839 / 100000) = 1/(100000 / 146839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (192083281 / 500000000) (384166563 / 1000000000) (Real.log (146839 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (146839 / 100000) = -Real.log (100000 / 146839) := by
    rw [show ((146839 / 100000) : ℝ) = ((100000 / 146839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (631845141 / 1000000000) ≤ -Real.log (53161 / 100000) ∧
    -Real.log (53161 / 100000) ≤ (315922571 / 500000000) := by
  have h := checkLog_sound (w := (46839 / 153161)) (n := 12)
    (lo := (631845141 / 1000000000)) (hi := (315922571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 53161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 53161) = 1/(53161 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-315922571 / 500000000) (-631845141 / 1000000000) (Real.log (53161 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (192386923 / 500000000) ≤ -Real.log (500000 / 734641) ∧
    -Real.log (500000 / 734641) ≤ (384773847 / 1000000000) := by
  have h := checkLog_sound (w := (234641 / 1234641)) (n := 12)
    (lo := (192386923 / 500000000)) (hi := (384773847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734641 / 500000) = 1/(500000 / 734641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (192386923 / 500000000) (384773847 / 1000000000) (Real.log (734641 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (734641 / 500000) = -Real.log (500000 / 734641) := by
    rw [show ((734641 / 500000) : ℝ) = ((500000 / 734641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (79190559 / 125000000) ≤ -Real.log (265359 / 500000) ∧
    -Real.log (265359 / 500000) ≤ (633524473 / 1000000000) := by
  have h := checkLog_sound (w := (234641 / 765359)) (n := 12)
    (lo := (79190559 / 125000000)) (hi := (633524473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 265359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 265359) = 1/(265359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-633524473 / 1000000000) (-79190559 / 125000000) (Real.log (265359 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (150996589 / 500000000) ≤ -Real.log (125000 / 169069) ∧
    -Real.log (125000 / 169069) ≤ (301993179 / 1000000000) := by
  have h := checkLog_sound (w := (44069 / 294069)) (n := 12)
    (lo := (150996589 / 500000000)) (hi := (301993179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169069 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169069 / 125000) = 1/(125000 / 169069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (150996589 / 500000000) (301993179 / 1000000000) (Real.log (169069 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (169069 / 125000) = -Real.log (125000 / 169069) := by
    rw [show ((169069 / 125000) : ℝ) = ((125000 / 169069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (434716797 / 1000000000) ≤ -Real.log (80931 / 125000) ∧
    -Real.log (80931 / 125000) ≤ (217358399 / 500000000) := by
  have h := checkLog_sound (w := (44069 / 205931)) (n := 12)
    (lo := (434716797 / 1000000000)) (hi := (217358399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 80931) = 1/(80931 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-217358399 / 500000000) (-434716797 / 1000000000) (Real.log (80931 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (302553443 / 1000000000) ≤ -Real.log (100000 / 135331) ∧
    -Real.log (100000 / 135331) ≤ (75638361 / 250000000) := by
  have h := checkLog_sound (w := (35331 / 235331)) (n := 12)
    (lo := (302553443 / 1000000000)) (hi := (75638361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135331 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135331 / 100000) = 1/(100000 / 135331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (302553443 / 1000000000) (75638361 / 250000000) (Real.log (135331 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (135331 / 100000) = -Real.log (100000 / 135331) := by
    rw [show ((135331 / 100000) : ℝ) = ((100000 / 135331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (435888233 / 1000000000) ≤ -Real.log (64669 / 100000) ∧
    -Real.log (64669 / 100000) ≤ (217944117 / 500000000) := by
  have h := checkLog_sound (w := (35331 / 164669)) (n := 12)
    (lo := (435888233 / 1000000000)) (hi := (217944117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 64669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 64669) = 1/(64669 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-217944117 / 500000000) (-435888233 / 1000000000) (Real.log (64669 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1016011703 / 1000000000) ≤ -Real.log (500000000000 / 1381078234043) ∧
    -Real.log (500000000000 / 1381078234043) ≤ (203202341 / 200000000) := by
  have h := checkLog_sound (w := (381078234043 / 2381078234043)) (n := 12)
    (lo := (322864523 / 1000000000)) (hi := (80716131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381078234043 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1381078234043 / 1000000000000) = 1/(500000000000 / 1381078234043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1016011703 / 1000000000) (203202341 / 200000000) (Real.log (1381078234043 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1381078234043 / 500000000000) = -Real.log (500000000000 / 1381078234043) := by
    rw [show ((1381078234043 / 500000000000) : ℝ) = ((500000000000 / 1381078234043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1018298317 / 1000000000) ≤ -Real.log (500000000000 / 1384239841121) ∧
    -Real.log (500000000000 / 1384239841121) ≤ (1018298319 / 1000000000) := by
  have h := checkLog_sound (w := (384239841121 / 2384239841121)) (n := 12)
    (lo := (325151137 / 1000000000)) (hi := (162575569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1384239841121 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1384239841121 / 1000000000000) = 1/(500000000000 / 1384239841121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1018298317 / 1000000000) (1018298319 / 1000000000) (Real.log (1384239841121 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1384239841121 / 500000000000) = -Real.log (500000000000 / 1384239841121) := by
    rw [show ((1384239841121 / 500000000000) : ℝ) = ((500000000000 / 1384239841121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (29468399 / 40000000) ≤ -Real.log (500000000000 / 1044525583521) ∧
    -Real.log (500000000000 / 1044525583521) ≤ (736709977 / 1000000000) := by
  have h := checkLog_sound (w := (44525583521 / 2044525583521)) (n := 12)
    (lo := (8712559 / 200000000)) (hi := (10890699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1044525583521 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1044525583521 / 1000000000000) = 1/(500000000000 / 1044525583521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (29468399 / 40000000) (736709977 / 1000000000) (Real.log (1044525583521 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1044525583521 / 500000000000) = -Real.log (500000000000 / 1044525583521) := by
    rw [show ((1044525583521 / 500000000000) : ℝ) = ((500000000000 / 1044525583521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (184610419 / 250000000) ≤ -Real.log (500000000000 / 1046335956951) ∧
    -Real.log (500000000000 / 1046335956951) ≤ (369220839 / 500000000) := by
  have h := checkLog_sound (w := (46335956951 / 2046335956951)) (n := 12)
    (lo := (1415453 / 31250000)) (hi := (45294497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1046335956951 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1046335956951 / 1000000000000) = 1/(500000000000 / 1046335956951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (184610419 / 250000000) (369220839 / 500000000) (Real.log (1046335956951 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1046335956951 / 500000000000) = -Real.log (500000000000 / 1046335956951) := by
    rw [show ((1046335956951 / 500000000000) : ℝ) = ((500000000000 / 1046335956951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0165

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0166Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0166
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

theorem reflection_log_1_neg : (140411331 / 500000000) ≤ -Real.log (256 / 339) ∧
    -Real.log (256 / 339) ≤ (280822663 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 595)) (n := 12)
    (lo := (140411331 / 500000000)) (hi := (280822663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 256) = 1/(256 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (140411331 / 500000000) (280822663 / 1000000000) (Real.log (339 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (339 / 256) = -Real.log (256 / 339) := by
    rw [show ((339 / 256) : ℝ) = ((256 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (391885849 / 1000000000) ≤ -Real.log (173 / 256) ∧
    -Real.log (173 / 256) ≤ (7837717 / 20000000) := by
  have h := checkLog_sound (w := (83 / 429)) (n := 12)
    (lo := (391885849 / 1000000000)) (hi := (7837717 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 173) = 1/(173 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7837717 / 20000000) (-391885849 / 1000000000) (Real.log (173 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (280380087 / 1000000000) ≤ -Real.log (5120 / 6777) ∧
    -Real.log (5120 / 6777) ≤ (35047511 / 125000000) := by
  have h := checkLog_sound (w := (1657 / 11897)) (n := 12)
    (lo := (280380087 / 1000000000)) (hi := (35047511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6777 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6777 / 5120) = 1/(5120 / 6777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (280380087 / 1000000000) (35047511 / 125000000) (Real.log (6777 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6777 / 5120) = -Real.log (5120 / 6777) := by
    rw [show ((6777 / 5120) : ℝ) = ((5120 / 6777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (391019173 / 1000000000) ≤ -Real.log (3463 / 5120) ∧
    -Real.log (3463 / 5120) ≤ (195509587 / 500000000) := by
  have h := checkLog_sound (w := (1657 / 8583)) (n := 12)
    (lo := (391019173 / 1000000000)) (hi := (195509587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3463) = 1/(3463 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-195509587 / 500000000) (-391019173 / 1000000000) (Real.log (3463 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (499827869 / 1000000000) ≤ -Real.log (128 / 211) ∧
    -Real.log (128 / 211) ≤ (49982787 / 100000000) := by
  have h := checkLog_sound (w := (83 / 339)) (n := 12)
    (lo := (499827869 / 1000000000)) (hi := (49982787 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211 / 128) = 1/(128 / 211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (499827869 / 1000000000) (49982787 / 100000000) (Real.log (211 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (211 / 128) = -Real.log (128 / 211) := by
    rw [show ((211 / 128) : ℝ) = ((128 / 211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1045367773 / 1000000000) ≤ -Real.log (45 / 128) ∧
    -Real.log (45 / 128) ≤ (41814711 / 40000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 45) = 1/(45 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-41814711 / 40000000) (-1045367773 / 1000000000) (Real.log (45 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (124779179 / 250000000) ≤ -Real.log (2560 / 4217) ∧
    -Real.log (2560 / 4217) ≤ (499116717 / 1000000000) := by
  have h := checkLog_sound (w := (1657 / 6777)) (n := 12)
    (lo := (124779179 / 250000000)) (hi := (499116717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4217 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4217 / 2560) = 1/(2560 / 4217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (124779179 / 250000000) (499116717 / 1000000000) (Real.log (4217 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4217 / 2560) = -Real.log (2560 / 4217) := by
    rw [show ((4217 / 2560) : ℝ) = ((2560 / 4217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1042039983 / 1000000000) ≤ -Real.log (903 / 2560) ∧
    -Real.log (903 / 2560) ≤ (208407997 / 200000000) := by
  have h := checkLog_sound (w := (377 / 2183)) (n := 12)
    (lo := (348892803 / 1000000000)) (hi := (87223201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 903) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 903) = 1/(903 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-208407997 / 200000000) (-1042039983 / 1000000000) (Real.log (903 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (383559591 / 1000000000) ≤ -Real.log (1000000 / 1467499) ∧
    -Real.log (1000000 / 1467499) ≤ (47944949 / 125000000) := by
  have h := checkLog_sound (w := (467499 / 2467499)) (n := 12)
    (lo := (383559591 / 1000000000)) (hi := (47944949 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1467499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1467499 / 1000000) = 1/(1000000 / 1467499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (383559591 / 1000000000) (47944949 / 125000000) (Real.log (1467499 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1467499 / 1000000) = -Real.log (1000000 / 1467499) := by
    rw [show ((1467499 / 1000000) : ℝ) = ((1000000 / 1467499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (630170503 / 1000000000) ≤ -Real.log (532501 / 1000000) ∧
    -Real.log (532501 / 1000000) ≤ (78771313 / 125000000) := by
  have h := checkLog_sound (w := (467499 / 1532501)) (n := 12)
    (lo := (630170503 / 1000000000)) (hi := (78771313 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 532501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 532501) = 1/(532501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-78771313 / 125000000) (-630170503 / 1000000000) (Real.log (532501 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (384167243 / 1000000000) ≤ -Real.log (1000000 / 1468391) ∧
    -Real.log (1000000 / 1468391) ≤ (96041811 / 250000000) := by
  have h := checkLog_sound (w := (468391 / 2468391)) (n := 12)
    (lo := (384167243 / 1000000000)) (hi := (96041811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1468391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1468391 / 1000000) = 1/(1000000 / 1468391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (384167243 / 1000000000) (96041811 / 250000000) (Real.log (1468391 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1468391 / 1000000) = -Real.log (1000000 / 1468391) := by
    rw [show ((1468391 / 1000000) : ℝ) = ((1000000 / 1468391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (315923511 / 500000000) ≤ -Real.log (531609 / 1000000) ∧
    -Real.log (531609 / 1000000) ≤ (631847023 / 1000000000) := by
  have h := checkLog_sound (w := (468391 / 1531609)) (n := 12)
    (lo := (315923511 / 500000000)) (hi := (631847023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 531609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 531609) = 1/(531609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-631847023 / 1000000000) (-315923511 / 500000000) (Real.log (531609 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (150717039 / 500000000) ≤ -Real.log (250000 / 337949) ∧
    -Real.log (250000 / 337949) ≤ (301434079 / 1000000000) := by
  have h := checkLog_sound (w := (87949 / 587949)) (n := 12)
    (lo := (150717039 / 500000000)) (hi := (301434079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337949 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337949 / 250000) = 1/(250000 / 337949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (150717039 / 500000000) (301434079 / 1000000000) (Real.log (337949 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (337949 / 250000) = -Real.log (250000 / 337949) := by
    rw [show ((337949 / 250000) : ℝ) = ((250000 / 337949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (433549817 / 1000000000) ≤ -Real.log (162051 / 250000) ∧
    -Real.log (162051 / 250000) ≤ (216774909 / 500000000) := by
  have h := checkLog_sound (w := (87949 / 412051)) (n := 12)
    (lo := (433549817 / 1000000000)) (hi := (216774909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 162051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 162051) = 1/(162051 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-216774909 / 500000000) (-433549817 / 1000000000) (Real.log (162051 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (301993917 / 1000000000) ≤ -Real.log (1000000 / 1352553) ∧
    -Real.log (1000000 / 1352553) ≤ (150996959 / 500000000) := by
  have h := checkLog_sound (w := (352553 / 2352553)) (n := 12)
    (lo := (301993917 / 1000000000)) (hi := (150996959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1352553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1352553 / 1000000) = 1/(1000000 / 1352553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (301993917 / 1000000000) (150996959 / 500000000) (Real.log (1352553 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1352553 / 1000000) = -Real.log (1000000 / 1352553) := by
    rw [show ((1352553 / 1000000) : ℝ) = ((1000000 / 1352553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (217359171 / 500000000) ≤ -Real.log (647447 / 1000000) ∧
    -Real.log (647447 / 1000000) ≤ (434718343 / 1000000000) := by
  have h := checkLog_sound (w := (352553 / 1647447)) (n := 12)
    (lo := (217359171 / 500000000)) (hi := (434718343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 647447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 647447) = 1/(647447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-434718343 / 1000000000) (-217359171 / 500000000) (Real.log (647447 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (506865047 / 500000000) ≤ -Real.log (500000000000 / 1377930745669) ∧
    -Real.log (500000000000 / 1377930745669) ≤ (63358131 / 62500000) := by
  have h := checkLog_sound (w := (377930745669 / 2377930745669)) (n := 12)
    (lo := (160291457 / 500000000)) (hi := (64116583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1377930745669 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1377930745669 / 1000000000000) = 1/(500000000000 / 1377930745669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (506865047 / 500000000) (63358131 / 62500000) (Real.log (1377930745669 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1377930745669 / 500000000000) = -Real.log (500000000000 / 1377930745669) := by
    rw [show ((1377930745669 / 500000000000) : ℝ) = ((500000000000 / 1377930745669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (203202853 / 200000000) ≤ -Real.log (250000000000 / 690540886253) ∧
    -Real.log (250000000000 / 690540886253) ≤ (1016014267 / 1000000000) := by
  have h := checkLog_sound (w := (190540886253 / 1190540886253)) (n := 12)
    (lo := (64573417 / 200000000)) (hi := (161433543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690540886253 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(690540886253 / 500000000000) = 1/(250000000000 / 690540886253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (203202853 / 200000000) (1016014267 / 1000000000) (Real.log (690540886253 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (690540886253 / 250000000000) = -Real.log (250000000000 / 690540886253) := by
    rw [show ((690540886253 / 250000000000) : ℝ) = ((250000000000 / 690540886253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (146996779 / 200000000) ≤ -Real.log (125000000000 / 260681051027) ∧
    -Real.log (125000000000 / 260681051027) ≤ (734983897 / 1000000000) := by
  have h := checkLog_sound (w := (10681051027 / 510681051027)) (n := 12)
    (lo := (8367343 / 200000000)) (hi := (10459179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((260681051027 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(260681051027 / 250000000000) = 1/(125000000000 / 260681051027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (146996779 / 200000000) (734983897 / 1000000000) (Real.log (260681051027 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (260681051027 / 125000000000) = -Real.log (125000000000 / 260681051027) := by
    rw [show ((260681051027 / 125000000000) : ℝ) = ((125000000000 / 260681051027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (736712259 / 1000000000) ≤ -Real.log (100000000000 / 208905593817) ∧
    -Real.log (100000000000 / 208905593817) ≤ (736712261 / 1000000000) := by
  have h := checkLog_sound (w := (8905593817 / 408905593817)) (n := 12)
    (lo := (43565079 / 1000000000)) (hi := (1089127 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208905593817 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(208905593817 / 200000000000) = 1/(100000000000 / 208905593817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (736712259 / 1000000000) (736712261 / 1000000000) (Real.log (208905593817 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (208905593817 / 100000000000) = -Real.log (100000000000 / 208905593817) := by
    rw [show ((208905593817 / 100000000000) : ℝ) = ((100000000000 / 208905593817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0166

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0167Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0167
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

theorem reflection_log_1_neg : (280380087 / 1000000000) ≤ -Real.log (5120 / 6777) ∧
    -Real.log (5120 / 6777) ≤ (35047511 / 125000000) := by
  have h := checkLog_sound (w := (1657 / 11897)) (n := 12)
    (lo := (280380087 / 1000000000)) (hi := (35047511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6777 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6777 / 5120) = 1/(5120 / 6777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (280380087 / 1000000000) (35047511 / 125000000) (Real.log (6777 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6777 / 5120) = -Real.log (5120 / 6777) := by
    rw [show ((6777 / 5120) : ℝ) = ((5120 / 6777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (391019173 / 1000000000) ≤ -Real.log (3463 / 5120) ∧
    -Real.log (3463 / 5120) ≤ (195509587 / 500000000) := by
  have h := checkLog_sound (w := (1657 / 8583)) (n := 12)
    (lo := (391019173 / 1000000000)) (hi := (195509587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3463) = 1/(3463 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-195509587 / 500000000) (-391019173 / 1000000000) (Real.log (3463 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (55987463 / 200000000) ≤ -Real.log (2560 / 3387) ∧
    -Real.log (2560 / 3387) ≤ (69984329 / 250000000) := by
  have h := checkLog_sound (w := (827 / 5947)) (n := 12)
    (lo := (55987463 / 200000000)) (hi := (69984329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3387 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3387 / 2560) = 1/(2560 / 3387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (55987463 / 200000000) (69984329 / 250000000) (Real.log (3387 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3387 / 2560) = -Real.log (2560 / 3387) := by
    rw [show ((3387 / 2560) : ℝ) = ((2560 / 3387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (390153247 / 1000000000) ≤ -Real.log (1733 / 2560) ∧
    -Real.log (1733 / 2560) ≤ (12192289 / 31250000) := by
  have h := checkLog_sound (w := (827 / 4293)) (n := 12)
    (lo := (390153247 / 1000000000)) (hi := (12192289 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1733) = 1/(1733 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12192289 / 31250000) (-390153247 / 1000000000) (Real.log (1733 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (124779179 / 250000000) ≤ -Real.log (2560 / 4217) ∧
    -Real.log (2560 / 4217) ≤ (499116717 / 1000000000) := by
  have h := checkLog_sound (w := (1657 / 6777)) (n := 12)
    (lo := (124779179 / 250000000)) (hi := (499116717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4217 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4217 / 2560) = 1/(2560 / 4217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (124779179 / 250000000) (499116717 / 1000000000) (Real.log (4217 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4217 / 2560) = -Real.log (2560 / 4217) := by
    rw [show ((4217 / 2560) : ℝ) = ((2560 / 4217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1042039983 / 1000000000) ≤ -Real.log (903 / 2560) ∧
    -Real.log (903 / 2560) ≤ (208407997 / 200000000) := by
  have h := checkLog_sound (w := (377 / 2183)) (n := 12)
    (lo := (348892803 / 1000000000)) (hi := (87223201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 903) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 903) = 1/(903 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-208407997 / 200000000) (-1042039983 / 1000000000) (Real.log (903 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (7787579 / 15625000) ≤ -Real.log (1280 / 2107) ∧
    -Real.log (1280 / 2107) ≤ (498405057 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 3387)) (n := 12)
    (lo := (7787579 / 15625000)) (hi := (498405057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2107 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2107 / 1280) = 1/(1280 / 2107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (7787579 / 15625000) (498405057 / 1000000000) (Real.log (2107 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2107 / 1280) = -Real.log (1280 / 2107) := by
    rw [show ((2107 / 1280) : ℝ) = ((1280 / 2107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (103872323 / 100000000) ≤ -Real.log (453 / 1280) ∧
    -Real.log (453 / 1280) ≤ (32460101 / 31250000) := by
  have h := checkLog_sound (w := (187 / 1093)) (n := 12)
    (lo := (6911521 / 20000000)) (hi := (345576051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 453) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 453) = 1/(453 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-32460101 / 31250000) (-103872323 / 100000000) (Real.log (453 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (382952251 / 1000000000) ≤ -Real.log (62500 / 91663) ∧
    -Real.log (62500 / 91663) ≤ (95738063 / 250000000) := by
  have h := checkLog_sound (w := (29163 / 154163)) (n := 12)
    (lo := (382952251 / 1000000000)) (hi := (95738063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91663 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91663 / 62500) = 1/(62500 / 91663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (382952251 / 1000000000) (95738063 / 250000000) (Real.log (91663 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (91663 / 62500) = -Real.log (62500 / 91663) := by
    rw [show ((91663 / 62500) : ℝ) = ((62500 / 91663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (125699733 / 200000000) ≤ -Real.log (33337 / 62500) ∧
    -Real.log (33337 / 62500) ≤ (314249333 / 500000000) := by
  have h := checkLog_sound (w := (29163 / 95837)) (n := 12)
    (lo := (125699733 / 200000000)) (hi := (314249333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 33337) = 1/(33337 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-314249333 / 500000000) (-125699733 / 200000000) (Real.log (33337 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (23972517 / 62500000) ≤ -Real.log (400 / 587) ∧
    -Real.log (400 / 587) ≤ (383560273 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 987)) (n := 12)
    (lo := (23972517 / 62500000)) (hi := (383560273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587 / 400) = 1/(400 / 587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (23972517 / 62500000) (383560273 / 1000000000) (Real.log (587 / 400)) := by
  have h := reflection_log_11_neg
  have he : Real.log (587 / 400) = -Real.log (400 / 587) := by
    rw [show ((587 / 400) : ℝ) = ((400 / 587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (630172381 / 1000000000) ≤ -Real.log (213 / 400) ∧
    -Real.log (213 / 400) ≤ (315086191 / 500000000) := by
  have h := checkLog_sound (w := (187 / 613)) (n := 12)
    (lo := (630172381 / 1000000000)) (hi := (315086191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 213) = 1/(213 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-315086191 / 500000000) (-630172381 / 1000000000) (Real.log (213 / 400)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (150437333 / 500000000) ≤ -Real.log (3125 / 4222) ∧
    -Real.log (3125 / 4222) ≤ (300874667 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 7347)) (n := 12)
    (lo := (150437333 / 500000000)) (hi := (300874667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4222 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4222 / 3125) = 1/(3125 / 4222) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (150437333 / 500000000) (300874667 / 1000000000) (Real.log (4222 / 3125)) := by
  have h := reflection_log_13_neg
  have he : Real.log (4222 / 3125) = -Real.log (3125 / 4222) := by
    rw [show ((4222 / 3125) : ℝ) = ((3125 / 4222) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (432384197 / 1000000000) ≤ -Real.log (2028 / 3125) ∧
    -Real.log (2028 / 3125) ≤ (216192099 / 500000000) := by
  have h := checkLog_sound (w := (1097 / 5153)) (n := 12)
    (lo := (432384197 / 1000000000)) (hi := (216192099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2028) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2028) = 1/(2028 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-216192099 / 500000000) (-432384197 / 1000000000) (Real.log (2028 / 3125)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (150717409 / 500000000) ≤ -Real.log (1000000 / 1351797) ∧
    -Real.log (1000000 / 1351797) ≤ (301434819 / 1000000000) := by
  have h := checkLog_sound (w := (351797 / 2351797)) (n := 12)
    (lo := (150717409 / 500000000)) (hi := (301434819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351797 / 1000000) = 1/(1000000 / 1351797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (150717409 / 500000000) (301434819 / 1000000000) (Real.log (1351797 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1351797 / 1000000) = -Real.log (1000000 / 1351797) := by
    rw [show ((1351797 / 1000000) : ℝ) = ((1000000 / 1351797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (169356 / 390625) ≤ -Real.log (648203 / 1000000) ∧
    -Real.log (648203 / 1000000) ≤ (433551361 / 1000000000) := by
  have h := checkLog_sound (w := (351797 / 1648203)) (n := 12)
    (lo := (169356 / 390625)) (hi := (433551361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 648203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 648203) = 1/(648203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-433551361 / 1000000000) (-169356 / 390625) (Real.log (648203 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (252862729 / 250000000) ≤ -Real.log (100000000000 / 274958754537) ∧
    -Real.log (100000000000 / 274958754537) ≤ (505725459 / 500000000) := by
  have h := checkLog_sound (w := (74958754537 / 474958754537)) (n := 12)
    (lo := (39787967 / 125000000)) (hi := (318303737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274958754537 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(274958754537 / 200000000000) = 1/(100000000000 / 274958754537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (252862729 / 250000000) (505725459 / 500000000) (Real.log (274958754537 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (274958754537 / 100000000000) = -Real.log (100000000000 / 274958754537) := by
    rw [show ((274958754537 / 100000000000) : ℝ) = ((100000000000 / 274958754537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1013732653 / 1000000000) ≤ -Real.log (500000000000 / 1377934272301) ∧
    -Real.log (500000000000 / 1377934272301) ≤ (202746531 / 200000000) := by
  have h := checkLog_sound (w := (377934272301 / 2377934272301)) (n := 12)
    (lo := (320585473 / 1000000000)) (hi := (160292737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1377934272301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1377934272301 / 1000000000000) = 1/(500000000000 / 1377934272301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1013732653 / 1000000000) (202746531 / 200000000) (Real.log (1377934272301 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1377934272301 / 500000000000) = -Real.log (500000000000 / 1377934272301) := by
    rw [show ((1377934272301 / 500000000000) : ℝ) = ((500000000000 / 1377934272301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (733258863 / 1000000000) ≤ -Real.log (3906250000 / 8132242357) ∧
    -Real.log (3906250000 / 8132242357) ≤ (146651773 / 200000000) := by
  have h := checkLog_sound (w := (319742357 / 15944742357)) (n := 12)
    (lo := (40111683 / 1000000000)) (hi := (10027921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8132242357 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8132242357 / 7812500000) = 1/(3906250000 / 8132242357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (733258863 / 1000000000) (146651773 / 200000000) (Real.log (8132242357 / 3906250000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8132242357 / 3906250000) = -Real.log (3906250000 / 8132242357) := by
    rw [show ((8132242357 / 3906250000) : ℝ) = ((3906250000 / 8132242357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (734986177 / 1000000000) ≤ -Real.log (500000000000 / 1042726584111) ∧
    -Real.log (500000000000 / 1042726584111) ≤ (734986179 / 1000000000) := by
  have h := checkLog_sound (w := (42726584111 / 2042726584111)) (n := 12)
    (lo := (41838997 / 1000000000)) (hi := (20919499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1042726584111 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1042726584111 / 1000000000000) = 1/(500000000000 / 1042726584111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (734986177 / 1000000000) (734986179 / 1000000000) (Real.log (1042726584111 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1042726584111 / 500000000000) = -Real.log (500000000000 / 1042726584111) := by
    rw [show ((1042726584111 / 500000000000) : ℝ) = ((500000000000 / 1042726584111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0167

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0168Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0168
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

theorem reflection_log_1_neg : (55987463 / 200000000) ≤ -Real.log (2560 / 3387) ∧
    -Real.log (2560 / 3387) ≤ (69984329 / 250000000) := by
  have h := checkLog_sound (w := (827 / 5947)) (n := 12)
    (lo := (55987463 / 200000000)) (hi := (69984329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3387 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3387 / 2560) = 1/(2560 / 3387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (55987463 / 200000000) (69984329 / 250000000) (Real.log (3387 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3387 / 2560) = -Real.log (2560 / 3387) := by
    rw [show ((3387 / 2560) : ℝ) = ((2560 / 3387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (390153247 / 1000000000) ≤ -Real.log (1733 / 2560) ∧
    -Real.log (1733 / 2560) ≤ (12192289 / 31250000) := by
  have h := checkLog_sound (w := (827 / 4293)) (n := 12)
    (lo := (390153247 / 1000000000)) (hi := (12192289 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1733) = 1/(1733 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12192289 / 31250000) (-390153247 / 1000000000) (Real.log (1733 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (279494347 / 1000000000) ≤ -Real.log (5120 / 6771) ∧
    -Real.log (5120 / 6771) ≤ (69873587 / 250000000) := by
  have h := checkLog_sound (w := (1651 / 11891)) (n := 12)
    (lo := (279494347 / 1000000000)) (hi := (69873587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6771 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6771 / 5120) = 1/(5120 / 6771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (279494347 / 1000000000) (69873587 / 250000000) (Real.log (6771 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6771 / 5120) = -Real.log (5120 / 6771) := by
    rw [show ((6771 / 5120) : ℝ) = ((5120 / 6771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (389288071 / 1000000000) ≤ -Real.log (3469 / 5120) ∧
    -Real.log (3469 / 5120) ≤ (48661009 / 125000000) := by
  have h := checkLog_sound (w := (1651 / 8589)) (n := 12)
    (lo := (389288071 / 1000000000)) (hi := (48661009 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3469) = 1/(3469 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-48661009 / 125000000) (-389288071 / 1000000000) (Real.log (3469 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7787579 / 15625000) ≤ -Real.log (1280 / 2107) ∧
    -Real.log (1280 / 2107) ≤ (498405057 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 3387)) (n := 12)
    (lo := (7787579 / 15625000)) (hi := (498405057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2107 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2107 / 1280) = 1/(1280 / 2107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7787579 / 15625000) (498405057 / 1000000000) (Real.log (2107 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2107 / 1280) = -Real.log (1280 / 2107) := by
    rw [show ((2107 / 1280) : ℝ) = ((1280 / 2107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (103872323 / 100000000) ≤ -Real.log (453 / 1280) ∧
    -Real.log (453 / 1280) ≤ (32460101 / 31250000) := by
  have h := checkLog_sound (w := (187 / 1093)) (n := 12)
    (lo := (6911521 / 20000000)) (hi := (345576051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 453) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 453) = 1/(453 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-32460101 / 31250000) (-103872323 / 100000000) (Real.log (453 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (49769289 / 100000000) ≤ -Real.log (2560 / 4211) ∧
    -Real.log (2560 / 4211) ≤ (497692891 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 6771)) (n := 12)
    (lo := (49769289 / 100000000)) (hi := (497692891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4211 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4211 / 2560) = 1/(2560 / 4211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (49769289 / 100000000) (497692891 / 1000000000) (Real.log (4211 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4211 / 2560) = -Real.log (2560 / 4211) := by
    rw [show ((4211 / 2560) : ℝ) = ((2560 / 4211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (517708721 / 500000000) ≤ -Real.log (909 / 2560) ∧
    -Real.log (909 / 2560) ≤ (258854361 / 250000000) := by
  have h := checkLog_sound (w := (371 / 2189)) (n := 12)
    (lo := (171135131 / 500000000)) (hi := (342270263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 909) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 909) = 1/(909 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-258854361 / 250000000) (-517708721 / 500000000) (Real.log (909 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (47793153 / 125000000) ≤ -Real.log (500000 / 732859) ∧
    -Real.log (500000 / 732859) ≤ (15293809 / 40000000) := by
  have h := checkLog_sound (w := (232859 / 1232859)) (n := 12)
    (lo := (47793153 / 125000000)) (hi := (15293809 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732859 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732859 / 500000) = 1/(500000 / 732859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (47793153 / 125000000) (15293809 / 40000000) (Real.log (732859 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (732859 / 500000) = -Real.log (500000 / 732859) := by
    rw [show ((732859 / 500000) : ℝ) = ((500000 / 732859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (626831489 / 1000000000) ≤ -Real.log (267141 / 500000) ∧
    -Real.log (267141 / 500000) ≤ (62683149 / 100000000) := by
  have h := checkLog_sound (w := (232859 / 767141)) (n := 12)
    (lo := (626831489 / 1000000000)) (hi := (62683149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 267141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 267141) = 1/(267141 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-62683149 / 100000000) (-626831489 / 1000000000) (Real.log (267141 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (382952933 / 1000000000) ≤ -Real.log (1000000 / 1466609) ∧
    -Real.log (1000000 / 1466609) ≤ (191476467 / 500000000) := by
  have h := checkLog_sound (w := (466609 / 2466609)) (n := 12)
    (lo := (382952933 / 1000000000)) (hi := (191476467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1466609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1466609 / 1000000) = 1/(1000000 / 1466609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (382952933 / 1000000000) (191476467 / 500000000) (Real.log (1466609 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1466609 / 1000000) = -Real.log (1000000 / 1466609) := by
    rw [show ((1466609 / 1000000) : ℝ) = ((1000000 / 1466609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (31425027 / 50000000) ≤ -Real.log (533391 / 1000000) ∧
    -Real.log (533391 / 1000000) ≤ (628500541 / 1000000000) := by
  have h := checkLog_sound (w := (466609 / 1533391)) (n := 12)
    (lo := (31425027 / 50000000)) (hi := (628500541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 533391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 533391) = 1/(533391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-628500541 / 1000000000) (-31425027 / 50000000) (Real.log (533391 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (300316421 / 1000000000) ≤ -Real.log (500000 / 675143) ∧
    -Real.log (500000 / 675143) ≤ (150158211 / 500000000) := by
  have h := checkLog_sound (w := (175143 / 1175143)) (n := 12)
    (lo := (300316421 / 1000000000)) (hi := (150158211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675143 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675143 / 500000) = 1/(500000 / 675143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (300316421 / 1000000000) (150158211 / 500000000) (Real.log (675143 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (675143 / 500000) = -Real.log (500000 / 675143) := by
    rw [show ((675143 / 500000) : ℝ) = ((500000 / 675143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (107805753 / 250000000) ≤ -Real.log (324857 / 500000) ∧
    -Real.log (324857 / 500000) ≤ (431223013 / 1000000000) := by
  have h := checkLog_sound (w := (175143 / 824857)) (n := 12)
    (lo := (107805753 / 250000000)) (hi := (431223013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 324857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 324857) = 1/(324857 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-431223013 / 1000000000) (-107805753 / 250000000) (Real.log (324857 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (150437703 / 500000000) ≤ -Real.log (1000000 / 1351041) ∧
    -Real.log (1000000 / 1351041) ≤ (300875407 / 1000000000) := by
  have h := checkLog_sound (w := (351041 / 2351041)) (n := 12)
    (lo := (150437703 / 500000000)) (hi := (300875407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351041 / 1000000) = 1/(1000000 / 1351041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (150437703 / 500000000) (300875407 / 1000000000) (Real.log (1351041 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1351041 / 1000000) = -Real.log (1000000 / 1351041) := by
    rw [show ((1351041 / 1000000) : ℝ) = ((1000000 / 1351041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (216192869 / 500000000) ≤ -Real.log (648959 / 1000000) ∧
    -Real.log (648959 / 1000000) ≤ (432385739 / 1000000000) := by
  have h := checkLog_sound (w := (351041 / 1648959)) (n := 12)
    (lo := (216192869 / 500000000)) (hi := (432385739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 648959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 648959) = 1/(648959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-432385739 / 1000000000) (-216192869 / 500000000) (Real.log (648959 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1009176713 / 1000000000) ≤ -Real.log (32000000 / 87786929) ∧
    -Real.log (32000000 / 87786929) ≤ (201835343 / 200000000) := by
  have h := checkLog_sound (w := (23786929 / 151786929)) (n := 12)
    (lo := (316029533 / 1000000000)) (hi := (158014767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87786929 / 64000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(87786929 / 64000000) = 1/(32000000 / 87786929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1009176713 / 1000000000) (201835343 / 200000000) (Real.log (87786929 / 32000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (87786929 / 32000000) = -Real.log (32000000 / 87786929) := by
    rw [show ((87786929 / 32000000) : ℝ) = ((32000000 / 87786929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1011453473 / 1000000000) ≤ -Real.log (62500000000 / 171849660943) ∧
    -Real.log (62500000000 / 171849660943) ≤ (40458139 / 40000000) := by
  have h := checkLog_sound (w := (46849660943 / 296849660943)) (n := 12)
    (lo := (318306293 / 1000000000)) (hi := (159153147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171849660943 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(171849660943 / 125000000000) = 1/(62500000000 / 171849660943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1011453473 / 1000000000) (40458139 / 40000000) (Real.log (171849660943 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (171849660943 / 62500000000) = -Real.log (62500000000 / 171849660943) := by
    rw [show ((171849660943 / 62500000000) : ℝ) = ((62500000000 / 171849660943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (365769717 / 500000000) ≤ -Real.log (100000000000 / 207827751903) ∧
    -Real.log (100000000000 / 207827751903) ≤ (182884859 / 250000000) := by
  have h := checkLog_sound (w := (7827751903 / 407827751903)) (n := 12)
    (lo := (19196127 / 500000000)) (hi := (7678451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207827751903 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(207827751903 / 200000000000) = 1/(100000000000 / 207827751903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (365769717 / 500000000) (182884859 / 250000000) (Real.log (207827751903 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (207827751903 / 100000000000) = -Real.log (100000000000 / 207827751903) := by
    rw [show ((207827751903 / 100000000000) : ℝ) = ((100000000000 / 207827751903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (91657643 / 125000000) ≤ -Real.log (125000000000 / 260232349039) ∧
    -Real.log (125000000000 / 260232349039) ≤ (366630573 / 500000000) := by
  have h := checkLog_sound (w := (10232349039 / 510232349039)) (n := 12)
    (lo := (10028491 / 250000000)) (hi := (8022793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((260232349039 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(260232349039 / 250000000000) = 1/(125000000000 / 260232349039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (91657643 / 125000000) (366630573 / 500000000) (Real.log (260232349039 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (260232349039 / 125000000000) = -Real.log (125000000000 / 260232349039) := by
    rw [show ((260232349039 / 125000000000) : ℝ) = ((125000000000 / 260232349039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0168

end


