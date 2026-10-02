-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell138Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell138Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:57:43.799987+00:00
-- url     : https://prove2.me/theorems/fb81dbba-beb7-4dcd-a470-259e250b4be3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell138Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell139…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell138Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell139Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell140Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell141Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell142Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell143Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell144Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell145Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell138Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell139Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell140Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell141Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell142Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell143Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell144Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell145Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell138Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell139Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell140Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell141Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell142Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell143Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell144Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell145Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell138Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell139Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell140Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell141Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell142Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell143Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell144Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell145Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell138Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell138
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

theorem reflection_log_1_neg : (286265053 / 1000000000) ≤ -Real.log (5120 / 6817) ∧
    -Real.log (5120 / 6817) ≤ (143132527 / 500000000) := by
  have h := checkLog_sound (w := (1697 / 11937)) (n := 12)
    (lo := (286265053 / 1000000000)) (hi := (143132527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6817 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6817 / 5120) = 1/(5120 / 6817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (286265053 / 1000000000) (143132527 / 500000000) (Real.log (6817 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6817 / 5120) = -Real.log (5120 / 6817) := by
    rw [show ((6817 / 5120) : ℝ) = ((5120 / 6817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (402637079 / 1000000000) ≤ -Real.log (3423 / 5120) ∧
    -Real.log (3423 / 5120) ≤ (10065927 / 25000000) := by
  have h := checkLog_sound (w := (1697 / 8543)) (n := 12)
    (lo := (402637079 / 1000000000)) (hi := (10065927 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3423) = 1/(3423 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10065927 / 25000000) (-402637079 / 1000000000) (Real.log (3423 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (3572811 / 12500000) ≤ -Real.log (2560 / 3407) ∧
    -Real.log (2560 / 3407) ≤ (285824881 / 1000000000) := by
  have h := checkLog_sound (w := (847 / 5967)) (n := 12)
    (lo := (3572811 / 12500000)) (hi := (285824881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3407 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3407 / 2560) = 1/(2560 / 3407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (3572811 / 12500000) (285824881 / 1000000000) (Real.log (3407 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3407 / 2560) = -Real.log (2560 / 3407) := by
    rw [show ((3407 / 2560) : ℝ) = ((2560 / 3407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (401761039 / 1000000000) ≤ -Real.log (1713 / 2560) ∧
    -Real.log (1713 / 2560) ≤ (5022013 / 12500000) := by
  have h := checkLog_sound (w := (847 / 4273)) (n := 12)
    (lo := (401761039 / 1000000000)) (hi := (5022013 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1713) = 1/(1713 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-5022013 / 12500000) (-401761039 / 1000000000) (Real.log (1713 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (105564229 / 500000000) ≤ -Real.log (1000000 / 1235071) ∧
    -Real.log (1000000 / 1235071) ≤ (211128459 / 1000000000) := by
  have h := checkLog_sound (w := (235071 / 2235071)) (n := 12)
    (lo := (105564229 / 500000000)) (hi := (211128459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235071 / 1000000) = 1/(1000000 / 1235071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (105564229 / 500000000) (211128459 / 1000000000) (Real.log (1235071 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1235071 / 1000000) = -Real.log (1000000 / 1235071) := by
    rw [show ((1235071 / 1000000) : ℝ) = ((1000000 / 1235071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (267972259 / 1000000000) ≤ -Real.log (764929 / 1000000) ∧
    -Real.log (764929 / 1000000) ≤ (13398613 / 50000000) := by
  have h := checkLog_sound (w := (235071 / 1764929)) (n := 12)
    (lo := (267972259 / 1000000000)) (hi := (13398613 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764929) = 1/(764929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-13398613 / 50000000) (-267972259 / 1000000000) (Real.log (764929 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (211469271 / 1000000000) ≤ -Real.log (250000 / 308873) ∧
    -Real.log (250000 / 308873) ≤ (26433659 / 125000000) := by
  have h := checkLog_sound (w := (58873 / 558873)) (n := 12)
    (lo := (211469271 / 1000000000)) (hi := (26433659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308873 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308873 / 250000) = 1/(250000 / 308873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (211469271 / 1000000000) (26433659 / 125000000) (Real.log (308873 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (308873 / 250000) = -Real.log (250000 / 308873) := by
    rw [show ((308873 / 250000) : ℝ) = ((250000 / 308873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (268522789 / 1000000000) ≤ -Real.log (191127 / 250000) ∧
    -Real.log (191127 / 250000) ≤ (26852279 / 100000000) := by
  have h := checkLog_sound (w := (58873 / 441127)) (n := 12)
    (lo := (268522789 / 1000000000)) (hi := (26852279 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191127) = 1/(191127 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26852279 / 100000000) (-268522789 / 1000000000) (Real.log (191127 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (155981859 / 1000000000) ≤ -Real.log (200000 / 233761) ∧
    -Real.log (200000 / 233761) ≤ (7799093 / 50000000) := by
  have h := checkLog_sound (w := (33761 / 433761)) (n := 12)
    (lo := (155981859 / 1000000000)) (hi := (7799093 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233761 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233761 / 200000) = 1/(200000 / 233761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (155981859 / 1000000000) (7799093 / 50000000) (Real.log (233761 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (233761 / 200000) = -Real.log (200000 / 233761) := by
    rw [show ((233761 / 200000) : ℝ) = ((200000 / 233761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (92445427 / 500000000) ≤ -Real.log (166239 / 200000) ∧
    -Real.log (166239 / 200000) ≤ (36978171 / 200000000) := by
  have h := checkLog_sound (w := (33761 / 366239)) (n := 12)
    (lo := (92445427 / 500000000)) (hi := (36978171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166239) = 1/(166239 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-36978171 / 200000000) (-92445427 / 500000000) (Real.log (166239 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (156248763 / 1000000000) ≤ -Real.log (1000000 / 1169117) ∧
    -Real.log (1000000 / 1169117) ≤ (39062191 / 250000000) := by
  have h := checkLog_sound (w := (169117 / 2169117)) (n := 12)
    (lo := (156248763 / 1000000000)) (hi := (39062191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169117 / 1000000) = 1/(1000000 / 1169117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (156248763 / 1000000000) (39062191 / 250000000) (Real.log (1169117 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1169117 / 1000000) = -Real.log (1000000 / 1169117) := by
    rw [show ((1169117 / 1000000) : ℝ) = ((1000000 / 1169117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (11579143 / 62500000) ≤ -Real.log (830883 / 1000000) ∧
    -Real.log (830883 / 1000000) ≤ (185266289 / 1000000000) := by
  have h := checkLog_sound (w := (169117 / 1830883)) (n := 12)
    (lo := (11579143 / 62500000)) (hi := (185266289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 830883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 830883) = 1/(830883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-185266289 / 1000000000) (-11579143 / 62500000) (Real.log (830883 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (687585919 / 1000000000) ≤ -Real.log (500000000000 / 994454173963) ∧
    -Real.log (500000000000 / 994454173963) ≤ (1074353 / 1562500) := by
  have h := checkLog_sound (w := (494454173963 / 1494454173963)) (n := 12)
    (lo := (687585919 / 1000000000)) (hi := (1074353 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((994454173963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(994454173963 / 500000000000) = 1/(500000000000 / 994454173963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (687585919 / 1000000000) (1074353 / 1562500) (Real.log (994454173963 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (994454173963 / 500000000000) = -Real.log (500000000000 / 994454173963) := by
    rw [show ((994454173963 / 500000000000) : ℝ) = ((500000000000 / 994454173963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (172225533 / 250000000) ≤ -Real.log (62500000000 / 124470493719) ∧
    -Real.log (62500000000 / 124470493719) ≤ (688902133 / 1000000000) := by
  have h := checkLog_sound (w := (61970493719 / 186970493719)) (n := 12)
    (lo := (172225533 / 250000000)) (hi := (688902133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124470493719 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124470493719 / 62500000000) = 1/(62500000000 / 124470493719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (172225533 / 250000000) (688902133 / 1000000000) (Real.log (124470493719 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (124470493719 / 62500000000) = -Real.log (62500000000 / 124470493719) := by
    rw [show ((124470493719 / 62500000000) : ℝ) = ((62500000000 / 124470493719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (239550359 / 500000000) ≤ -Real.log (125000000000 / 201827718651) ∧
    -Real.log (125000000000 / 201827718651) ≤ (479100719 / 1000000000) := by
  have h := checkLog_sound (w := (76827718651 / 326827718651)) (n := 12)
    (lo := (239550359 / 500000000)) (hi := (479100719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201827718651 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201827718651 / 125000000000) = 1/(125000000000 / 201827718651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (239550359 / 500000000) (479100719 / 1000000000) (Real.log (201827718651 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (201827718651 / 125000000000) = -Real.log (125000000000 / 201827718651) := by
    rw [show ((201827718651 / 125000000000) : ℝ) = ((125000000000 / 201827718651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23999603 / 50000000) ≤ -Real.log (500000000000 / 808030785813) ∧
    -Real.log (500000000000 / 808030785813) ≤ (479992061 / 1000000000) := by
  have h := checkLog_sound (w := (308030785813 / 1308030785813)) (n := 12)
    (lo := (23999603 / 50000000)) (hi := (479992061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808030785813 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808030785813 / 500000000000) = 1/(500000000000 / 808030785813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (23999603 / 50000000) (479992061 / 1000000000) (Real.log (808030785813 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (808030785813 / 500000000000) = -Real.log (500000000000 / 808030785813) := by
    rw [show ((808030785813 / 500000000000) : ℝ) = ((500000000000 / 808030785813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (340872713 / 1000000000) ≤ -Real.log (500000000000 / 703087121553) ∧
    -Real.log (500000000000 / 703087121553) ≤ (170436357 / 500000000) := by
  have h := checkLog_sound (w := (203087121553 / 1203087121553)) (n := 12)
    (lo := (340872713 / 1000000000)) (hi := (170436357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703087121553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703087121553 / 500000000000) = 1/(500000000000 / 703087121553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (340872713 / 1000000000) (170436357 / 500000000) (Real.log (703087121553 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (703087121553 / 500000000000) = -Real.log (500000000000 / 703087121553) := by
    rw [show ((703087121553 / 500000000000) : ℝ) = ((500000000000 / 703087121553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (341515051 / 1000000000) ≤ -Real.log (25000000000 / 35176944287) ∧
    -Real.log (25000000000 / 35176944287) ≤ (85378763 / 250000000) := by
  have h := checkLog_sound (w := (10176944287 / 60176944287)) (n := 12)
    (lo := (341515051 / 1000000000)) (hi := (85378763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35176944287 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35176944287 / 25000000000) = 1/(25000000000 / 35176944287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (341515051 / 1000000000) (85378763 / 250000000) (Real.log (35176944287 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (35176944287 / 25000000000) = -Real.log (25000000000 / 35176944287) := by
    rw [show ((35176944287 / 25000000000) : ℝ) = ((25000000000 / 35176944287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1160701 / 40000000) ≤ -Real.log (971399440311 / 1000000000000) ∧
    -Real.log (971399440311 / 1000000000000) ≤ (14508763 / 500000000) := by
  have h := checkLog_sound (w := (28600559689 / 1971399440311)) (n := 12)
    (lo := (1160701 / 40000000)) (hi := (14508763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971399440311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971399440311) = 1/(971399440311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-14508763 / 500000000) (-1160701 / 40000000) (Real.log (971399440311 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5781799 / 200000000) ≤ -Real.log (38860194879 / 40000000000) ∧
    -Real.log (38860194879 / 40000000000) ≤ (7227249 / 250000000) := by
  have h := checkLog_sound (w := (1139805121 / 78860194879)) (n := 12)
    (lo := (5781799 / 200000000)) (hi := (7227249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38860194879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38860194879) = 1/(38860194879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7227249 / 250000000) (-5781799 / 200000000) (Real.log (38860194879 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell138

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell139Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell139
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

theorem reflection_log_1_neg : (35838129 / 125000000) ≤ -Real.log (256 / 341) ∧
    -Real.log (256 / 341) ≤ (286705033 / 1000000000) := by
  have h := checkLog_sound (w := (85 / 597)) (n := 12)
    (lo := (35838129 / 125000000)) (hi := (286705033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341 / 256) = 1/(256 / 341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (35838129 / 125000000) (286705033 / 1000000000) (Real.log (341 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (341 / 256) = -Real.log (256 / 341) := by
    rw [show ((341 / 256) : ℝ) = ((256 / 341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (403513887 / 1000000000) ≤ -Real.log (171 / 256) ∧
    -Real.log (171 / 256) ≤ (12609809 / 31250000) := by
  have h := checkLog_sound (w := (85 / 427)) (n := 12)
    (lo := (403513887 / 1000000000)) (hi := (12609809 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 171) = 1/(171 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12609809 / 31250000) (-403513887 / 1000000000) (Real.log (171 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (286265053 / 1000000000) ≤ -Real.log (5120 / 6817) ∧
    -Real.log (5120 / 6817) ≤ (143132527 / 500000000) := by
  have h := checkLog_sound (w := (1697 / 11937)) (n := 12)
    (lo := (286265053 / 1000000000)) (hi := (143132527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6817 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6817 / 5120) = 1/(5120 / 6817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (286265053 / 1000000000) (143132527 / 500000000) (Real.log (6817 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6817 / 5120) = -Real.log (5120 / 6817) := by
    rw [show ((6817 / 5120) : ℝ) = ((5120 / 6817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (402637079 / 1000000000) ≤ -Real.log (3423 / 5120) ∧
    -Real.log (3423 / 5120) ≤ (10065927 / 25000000) := by
  have h := checkLog_sound (w := (1697 / 8543)) (n := 12)
    (lo := (402637079 / 1000000000)) (hi := (10065927 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3423) = 1/(3423 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10065927 / 25000000) (-402637079 / 1000000000) (Real.log (3423 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (211468461 / 1000000000) ≤ -Real.log (1000000 / 1235491) ∧
    -Real.log (1000000 / 1235491) ≤ (105734231 / 500000000) := by
  have h := checkLog_sound (w := (235491 / 2235491)) (n := 12)
    (lo := (211468461 / 1000000000)) (hi := (105734231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235491 / 1000000) = 1/(1000000 / 1235491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (211468461 / 1000000000) (105734231 / 500000000) (Real.log (1235491 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1235491 / 1000000) = -Real.log (1000000 / 1235491) := by
    rw [show ((1235491 / 1000000) : ℝ) = ((1000000 / 1235491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (268521481 / 1000000000) ≤ -Real.log (764509 / 1000000) ∧
    -Real.log (764509 / 1000000) ≤ (134260741 / 500000000) := by
  have h := checkLog_sound (w := (235491 / 1764509)) (n := 12)
    (lo := (268521481 / 1000000000)) (hi := (134260741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764509) = 1/(764509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-134260741 / 500000000) (-268521481 / 1000000000) (Real.log (764509 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13238123 / 62500000) ≤ -Real.log (1000000 / 1235913) ∧
    -Real.log (1000000 / 1235913) ≤ (211809969 / 1000000000) := by
  have h := checkLog_sound (w := (235913 / 2235913)) (n := 12)
    (lo := (13238123 / 62500000)) (hi := (211809969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235913 / 1000000) = 1/(1000000 / 1235913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13238123 / 62500000) (211809969 / 1000000000) (Real.log (1235913 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1235913 / 1000000) = -Real.log (1000000 / 1235913) := by
    rw [show ((1235913 / 1000000) : ℝ) = ((1000000 / 1235913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (269073621 / 1000000000) ≤ -Real.log (764087 / 1000000) ∧
    -Real.log (764087 / 1000000) ≤ (134536811 / 500000000) := by
  have h := checkLog_sound (w := (235913 / 1764087)) (n := 12)
    (lo := (269073621 / 1000000000)) (hi := (134536811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764087) = 1/(764087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-134536811 / 500000000) (-269073621 / 1000000000) (Real.log (764087 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (156247907 / 1000000000) ≤ -Real.log (250000 / 292279) ∧
    -Real.log (250000 / 292279) ≤ (39061977 / 250000000) := by
  have h := checkLog_sound (w := (42279 / 542279)) (n := 12)
    (lo := (156247907 / 1000000000)) (hi := (39061977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292279 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292279 / 250000) = 1/(250000 / 292279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (156247907 / 1000000000) (39061977 / 250000000) (Real.log (292279 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (292279 / 250000) = -Real.log (250000 / 292279) := by
    rw [show ((292279 / 250000) : ℝ) = ((250000 / 292279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (46316271 / 250000000) ≤ -Real.log (207721 / 250000) ∧
    -Real.log (207721 / 250000) ≤ (37053017 / 200000000) := by
  have h := checkLog_sound (w := (42279 / 457721)) (n := 12)
    (lo := (46316271 / 250000000)) (hi := (37053017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 207721) = 1/(207721 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-37053017 / 200000000) (-46316271 / 250000000) (Real.log (207721 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7825737 / 50000000) ≤ -Real.log (250000 / 292357) ∧
    -Real.log (250000 / 292357) ≤ (156514741 / 1000000000) := by
  have h := checkLog_sound (w := (42357 / 542357)) (n := 12)
    (lo := (7825737 / 50000000)) (hi := (156514741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292357 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292357 / 250000) = 1/(250000 / 292357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7825737 / 50000000) (156514741 / 1000000000) (Real.log (292357 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (292357 / 250000) = -Real.log (250000 / 292357) := by
    rw [show ((292357 / 250000) : ℝ) = ((250000 / 292357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (92820329 / 500000000) ≤ -Real.log (207643 / 250000) ∧
    -Real.log (207643 / 250000) ≤ (185640659 / 1000000000) := by
  have h := checkLog_sound (w := (42357 / 457643)) (n := 12)
    (lo := (92820329 / 500000000)) (hi := (185640659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 207643) = 1/(207643 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-185640659 / 1000000000) (-92820329 / 500000000) (Real.log (207643 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (172225533 / 250000000) ≤ -Real.log (500000000000 / 995763949751) ∧
    -Real.log (500000000000 / 995763949751) ≤ (688902133 / 1000000000) := by
  have h := checkLog_sound (w := (495763949751 / 1495763949751)) (n := 12)
    (lo := (172225533 / 250000000)) (hi := (688902133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((995763949751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(995763949751 / 500000000000) = 1/(500000000000 / 995763949751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (172225533 / 250000000) (688902133 / 1000000000) (Real.log (995763949751 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (995763949751 / 500000000000) = -Real.log (500000000000 / 995763949751) := by
    rw [show ((995763949751 / 500000000000) : ℝ) = ((500000000000 / 995763949751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (17255473 / 25000000) ≤ -Real.log (15625000000 / 31158625731) ∧
    -Real.log (15625000000 / 31158625731) ≤ (690218921 / 1000000000) := by
  have h := checkLog_sound (w := (15533625731 / 46783625731)) (n := 12)
    (lo := (17255473 / 25000000)) (hi := (690218921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31158625731 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31158625731 / 15625000000) = 1/(15625000000 / 31158625731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (17255473 / 25000000) (690218921 / 1000000000) (Real.log (31158625731 / 15625000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (31158625731 / 15625000000) = -Real.log (15625000000 / 31158625731) := by
    rw [show ((31158625731 / 15625000000) : ℝ) = ((15625000000 / 31158625731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (479989943 / 1000000000) ≤ -Real.log (50000000000 / 80802907487) ∧
    -Real.log (50000000000 / 80802907487) ≤ (59998743 / 125000000) := by
  have h := checkLog_sound (w := (30802907487 / 130802907487)) (n := 12)
    (lo := (479989943 / 1000000000)) (hi := (59998743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80802907487 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80802907487 / 50000000000) = 1/(50000000000 / 80802907487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (479989943 / 1000000000) (59998743 / 125000000) (Real.log (80802907487 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (80802907487 / 50000000000) = -Real.log (50000000000 / 80802907487) := by
    rw [show ((80802907487 / 50000000000) : ℝ) = ((50000000000 / 80802907487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48088359 / 100000000) ≤ -Real.log (500000000000 / 808751490341) ∧
    -Real.log (500000000000 / 808751490341) ≤ (480883591 / 1000000000) := by
  have h := checkLog_sound (w := (308751490341 / 1308751490341)) (n := 12)
    (lo := (48088359 / 100000000)) (hi := (480883591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808751490341 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808751490341 / 500000000000) = 1/(500000000000 / 808751490341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (48088359 / 100000000) (480883591 / 1000000000) (Real.log (808751490341 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (808751490341 / 500000000000) = -Real.log (500000000000 / 808751490341) := by
    rw [show ((808751490341 / 500000000000) : ℝ) = ((500000000000 / 808751490341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (10672281 / 31250000) ≤ -Real.log (100000000000 / 140707487447) ∧
    -Real.log (100000000000 / 140707487447) ≤ (341512993 / 1000000000) := by
  have h := checkLog_sound (w := (40707487447 / 240707487447)) (n := 12)
    (lo := (10672281 / 31250000)) (hi := (341512993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140707487447 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140707487447 / 100000000000) = 1/(100000000000 / 140707487447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (10672281 / 31250000) (341512993 / 1000000000) (Real.log (140707487447 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (140707487447 / 100000000000) = -Real.log (100000000000 / 140707487447) := by
    rw [show ((140707487447 / 100000000000) : ℝ) = ((100000000000 / 140707487447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (342155399 / 1000000000) ≤ -Real.log (500000000000 / 703989539739) ∧
    -Real.log (500000000000 / 703989539739) ≤ (1710777 / 5000000) := by
  have h := checkLog_sound (w := (203989539739 / 1203989539739)) (n := 12)
    (lo := (342155399 / 1000000000)) (hi := (1710777 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703989539739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703989539739 / 500000000000) = 1/(500000000000 / 703989539739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (342155399 / 1000000000) (1710777 / 5000000) (Real.log (703989539739 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (703989539739 / 500000000000) = -Real.log (500000000000 / 703989539739) := by
    rw [show ((703989539739 / 500000000000) : ℝ) = ((500000000000 / 703989539739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (14562959 / 500000000) ≤ -Real.log (60705884551 / 62500000000) ∧
    -Real.log (60705884551 / 62500000000) ≤ (29125919 / 1000000000) := by
  have h := checkLog_sound (w := (1794115449 / 123205884551)) (n := 12)
    (lo := (14562959 / 500000000)) (hi := (29125919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60705884551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60705884551) = 1/(60705884551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29125919 / 1000000000) (-14562959 / 500000000) (Real.log (60705884551 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (29017177 / 1000000000) ≤ -Real.log (60712486159 / 62500000000) ∧
    -Real.log (60712486159 / 62500000000) ≤ (14508589 / 500000000) := by
  have h := checkLog_sound (w := (1787513841 / 123212486159)) (n := 12)
    (lo := (29017177 / 1000000000)) (hi := (14508589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60712486159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60712486159) = 1/(60712486159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-14508589 / 500000000) (-29017177 / 1000000000) (Real.log (60712486159 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell139

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell140Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell140
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

theorem reflection_log_1_neg : (143572409 / 500000000) ≤ -Real.log (5120 / 6823) ∧
    -Real.log (5120 / 6823) ≤ (287144819 / 1000000000) := by
  have h := checkLog_sound (w := (1703 / 11943)) (n := 12)
    (lo := (143572409 / 500000000)) (hi := (287144819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6823 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6823 / 5120) = 1/(5120 / 6823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (143572409 / 500000000) (287144819 / 1000000000) (Real.log (6823 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6823 / 5120) = -Real.log (5120 / 6823) := by
    rw [show ((6823 / 5120) : ℝ) = ((5120 / 6823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (80878293 / 200000000) ≤ -Real.log (3417 / 5120) ∧
    -Real.log (3417 / 5120) ≤ (202195733 / 500000000) := by
  have h := checkLog_sound (w := (1703 / 8537)) (n := 12)
    (lo := (80878293 / 200000000)) (hi := (202195733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3417) = 1/(3417 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-202195733 / 500000000) (-80878293 / 200000000) (Real.log (3417 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (35838129 / 125000000) ≤ -Real.log (256 / 341) ∧
    -Real.log (256 / 341) ≤ (286705033 / 1000000000) := by
  have h := checkLog_sound (w := (85 / 597)) (n := 12)
    (lo := (35838129 / 125000000)) (hi := (286705033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341 / 256) = 1/(256 / 341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (35838129 / 125000000) (286705033 / 1000000000) (Real.log (341 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (341 / 256) = -Real.log (256 / 341) := by
    rw [show ((341 / 256) : ℝ) = ((256 / 341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (403513887 / 1000000000) ≤ -Real.log (171 / 256) ∧
    -Real.log (171 / 256) ≤ (12609809 / 31250000) := by
  have h := checkLog_sound (w := (85 / 427)) (n := 12)
    (lo := (403513887 / 1000000000)) (hi := (12609809 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 171) = 1/(171 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12609809 / 31250000) (-403513887 / 1000000000) (Real.log (171 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (211809159 / 1000000000) ≤ -Real.log (125000 / 154489) ∧
    -Real.log (125000 / 154489) ≤ (5295229 / 25000000) := by
  have h := checkLog_sound (w := (29489 / 279489)) (n := 12)
    (lo := (211809159 / 1000000000)) (hi := (5295229 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154489 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154489 / 125000) = 1/(125000 / 154489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (211809159 / 1000000000) (5295229 / 25000000) (Real.log (154489 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (154489 / 125000) = -Real.log (125000 / 154489) := by
    rw [show ((154489 / 125000) : ℝ) = ((125000 / 154489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (269072313 / 1000000000) ≤ -Real.log (95511 / 125000) ∧
    -Real.log (95511 / 125000) ≤ (134536157 / 500000000) := by
  have h := checkLog_sound (w := (29489 / 220511)) (n := 12)
    (lo := (269072313 / 1000000000)) (hi := (134536157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 95511) = 1/(95511 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-134536157 / 500000000) (-269072313 / 1000000000) (Real.log (95511 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10607487 / 50000000) ≤ -Real.log (1000000 / 1236333) ∧
    -Real.log (1000000 / 1236333) ≤ (212149741 / 1000000000) := by
  have h := checkLog_sound (w := (236333 / 2236333)) (n := 12)
    (lo := (10607487 / 50000000)) (hi := (212149741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236333 / 1000000) = 1/(1000000 / 1236333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10607487 / 50000000) (212149741 / 1000000000) (Real.log (1236333 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1236333 / 1000000) = -Real.log (1000000 / 1236333) := by
    rw [show ((1236333 / 1000000) : ℝ) = ((1000000 / 1236333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (33702931 / 125000000) ≤ -Real.log (763667 / 1000000) ∧
    -Real.log (763667 / 1000000) ≤ (269623449 / 1000000000) := by
  have h := checkLog_sound (w := (236333 / 1763667)) (n := 12)
    (lo := (33702931 / 125000000)) (hi := (269623449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763667) = 1/(763667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-269623449 / 1000000000) (-33702931 / 125000000) (Real.log (763667 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (31302777 / 200000000) ≤ -Real.log (1000000 / 1169427) ∧
    -Real.log (1000000 / 1169427) ≤ (78256943 / 500000000) := by
  have h := checkLog_sound (w := (169427 / 2169427)) (n := 12)
    (lo := (31302777 / 200000000)) (hi := (78256943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169427 / 1000000) = 1/(1000000 / 1169427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (31302777 / 200000000) (78256943 / 500000000) (Real.log (1169427 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1169427 / 1000000) = -Real.log (1000000 / 1169427) := by
    rw [show ((1169427 / 1000000) : ℝ) = ((1000000 / 1169427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (92819727 / 500000000) ≤ -Real.log (830573 / 1000000) ∧
    -Real.log (830573 / 1000000) ≤ (37127891 / 200000000) := by
  have h := checkLog_sound (w := (169427 / 1830573)) (n := 12)
    (lo := (92819727 / 500000000)) (hi := (37127891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 830573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 830573) = 1/(830573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-37127891 / 200000000) (-92819727 / 500000000) (Real.log (830573 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (156781501 / 1000000000) ≤ -Real.log (50000 / 58487) ∧
    -Real.log (50000 / 58487) ≤ (78390751 / 500000000) := by
  have h := checkLog_sound (w := (8487 / 108487)) (n := 12)
    (lo := (156781501 / 1000000000)) (hi := (78390751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58487 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58487 / 50000) = 1/(50000 / 58487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (156781501 / 1000000000) (78390751 / 500000000) (Real.log (58487 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (58487 / 50000) = -Real.log (50000 / 58487) := by
    rw [show ((58487 / 50000) : ℝ) = ((50000 / 58487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93008187 / 500000000) ≤ -Real.log (41513 / 50000) ∧
    -Real.log (41513 / 50000) ≤ (1488131 / 8000000) := by
  have h := checkLog_sound (w := (8487 / 91513)) (n := 12)
    (lo := (93008187 / 500000000)) (hi := (1488131 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 41513) = 1/(41513 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1488131 / 8000000) (-93008187 / 500000000) (Real.log (41513 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (17255473 / 25000000) ≤ -Real.log (500000000000 / 997076023391) ∧
    -Real.log (500000000000 / 997076023391) ≤ (690218921 / 1000000000) := by
  have h := checkLog_sound (w := (497076023391 / 1497076023391)) (n := 12)
    (lo := (17255473 / 25000000)) (hi := (690218921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997076023391 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997076023391 / 500000000000) = 1/(500000000000 / 997076023391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (17255473 / 25000000) (690218921 / 1000000000) (Real.log (997076023391 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (997076023391 / 500000000000) = -Real.log (500000000000 / 997076023391) := by
    rw [show ((997076023391 / 500000000000) : ℝ) = ((500000000000 / 997076023391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (172884071 / 250000000) ≤ -Real.log (500000000000 / 998390400937) ∧
    -Real.log (500000000000 / 998390400937) ≤ (138307257 / 200000000) := by
  have h := checkLog_sound (w := (498390400937 / 1498390400937)) (n := 12)
    (lo := (172884071 / 250000000)) (hi := (138307257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((998390400937 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(998390400937 / 500000000000) = 1/(500000000000 / 998390400937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (172884071 / 250000000) (138307257 / 200000000) (Real.log (998390400937 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (998390400937 / 500000000000) = -Real.log (500000000000 / 998390400937) := by
    rw [show ((998390400937 / 500000000000) : ℝ) = ((500000000000 / 998390400937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (7513773 / 15625000) ≤ -Real.log (62500000000 / 101093722189) ∧
    -Real.log (62500000000 / 101093722189) ≤ (480881473 / 1000000000) := by
  have h := checkLog_sound (w := (38593722189 / 163593722189)) (n := 12)
    (lo := (7513773 / 15625000)) (hi := (480881473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101093722189 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101093722189 / 62500000000) = 1/(62500000000 / 101093722189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (7513773 / 15625000) (480881473 / 1000000000) (Real.log (101093722189 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (101093722189 / 62500000000) = -Real.log (62500000000 / 101093722189) := by
    rw [show ((101093722189 / 62500000000) : ℝ) = ((62500000000 / 101093722189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (120443297 / 250000000) ≤ -Real.log (15625000000 / 25295977337) ∧
    -Real.log (15625000000 / 25295977337) ≤ (481773189 / 1000000000) := by
  have h := checkLog_sound (w := (9670977337 / 40920977337)) (n := 12)
    (lo := (120443297 / 250000000)) (hi := (481773189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25295977337 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25295977337 / 15625000000) = 1/(15625000000 / 25295977337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (120443297 / 250000000) (481773189 / 1000000000) (Real.log (25295977337 / 15625000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (25295977337 / 15625000000) = -Real.log (15625000000 / 25295977337) := by
    rw [show ((25295977337 / 15625000000) : ℝ) = ((15625000000 / 25295977337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (17107667 / 50000000) ≤ -Real.log (500000000000 / 703988090149) ∧
    -Real.log (500000000000 / 703988090149) ≤ (342153341 / 1000000000) := by
  have h := checkLog_sound (w := (203988090149 / 1203988090149)) (n := 12)
    (lo := (17107667 / 50000000)) (hi := (342153341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703988090149 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703988090149 / 500000000000) = 1/(500000000000 / 703988090149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (17107667 / 50000000) (342153341 / 1000000000) (Real.log (703988090149 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (703988090149 / 500000000000) = -Real.log (500000000000 / 703988090149) := by
    rw [show ((703988090149 / 500000000000) : ℝ) = ((500000000000 / 703988090149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (85699469 / 250000000) ≤ -Real.log (50000000000 / 70444198203) ∧
    -Real.log (50000000000 / 70444198203) ≤ (342797877 / 1000000000) := by
  have h := checkLog_sound (w := (20444198203 / 120444198203)) (n := 12)
    (lo := (85699469 / 250000000)) (hi := (342797877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70444198203 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70444198203 / 50000000000) = 1/(50000000000 / 70444198203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (85699469 / 250000000) (342797877 / 1000000000) (Real.log (70444198203 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (70444198203 / 50000000000) = -Real.log (50000000000 / 70444198203) := by
    rw [show ((70444198203 / 50000000000) : ℝ) = ((50000000000 / 70444198203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3654359 / 125000000) ≤ -Real.log (2427970831 / 2500000000) ∧
    -Real.log (2427970831 / 2500000000) ≤ (29234873 / 1000000000) := by
  have h := checkLog_sound (w := (72029169 / 4927970831)) (n := 12)
    (lo := (3654359 / 125000000)) (hi := (29234873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2427970831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2427970831) = 1/(2427970831 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29234873 / 1000000000) (-3654359 / 125000000) (Real.log (2427970831 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (29125569 / 1000000000) ≤ -Real.log (971294491671 / 1000000000000) ∧
    -Real.log (971294491671 / 1000000000000) ≤ (2912557 / 100000000) := by
  have h := checkLog_sound (w := (28705508329 / 1971294491671)) (n := 12)
    (lo := (29125569 / 1000000000)) (hi := (2912557 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971294491671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971294491671) = 1/(971294491671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2912557 / 100000000) (-29125569 / 1000000000) (Real.log (971294491671 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell140

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell141Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell141
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

theorem reflection_log_1_neg : (287584411 / 1000000000) ≤ -Real.log (2560 / 3413) ∧
    -Real.log (2560 / 3413) ≤ (71896103 / 250000000) := by
  have h := checkLog_sound (w := (853 / 5973)) (n := 12)
    (lo := (287584411 / 1000000000)) (hi := (71896103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3413 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3413 / 2560) = 1/(2560 / 3413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (287584411 / 1000000000) (71896103 / 250000000) (Real.log (3413 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3413 / 2560) = -Real.log (2560 / 3413) := by
    rw [show ((3413 / 2560) : ℝ) = ((2560 / 3413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (202634907 / 500000000) ≤ -Real.log (1707 / 2560) ∧
    -Real.log (1707 / 2560) ≤ (81053963 / 200000000) := by
  have h := checkLog_sound (w := (853 / 4267)) (n := 12)
    (lo := (202634907 / 500000000)) (hi := (81053963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1707) = 1/(1707 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-81053963 / 200000000) (-202634907 / 500000000) (Real.log (1707 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (143572409 / 500000000) ≤ -Real.log (5120 / 6823) ∧
    -Real.log (5120 / 6823) ≤ (287144819 / 1000000000) := by
  have h := checkLog_sound (w := (1703 / 11943)) (n := 12)
    (lo := (143572409 / 500000000)) (hi := (287144819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6823 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6823 / 5120) = 1/(5120 / 6823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (143572409 / 500000000) (287144819 / 1000000000) (Real.log (6823 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6823 / 5120) = -Real.log (5120 / 6823) := by
    rw [show ((6823 / 5120) : ℝ) = ((5120 / 6823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (80878293 / 200000000) ≤ -Real.log (3417 / 5120) ∧
    -Real.log (3417 / 5120) ≤ (202195733 / 500000000) := by
  have h := checkLog_sound (w := (1703 / 8537)) (n := 12)
    (lo := (80878293 / 200000000)) (hi := (202195733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3417) = 1/(3417 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-202195733 / 500000000) (-80878293 / 200000000) (Real.log (3417 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (212148931 / 1000000000) ≤ -Real.log (250000 / 309083) ∧
    -Real.log (250000 / 309083) ≤ (53037233 / 250000000) := by
  have h := checkLog_sound (w := (59083 / 559083)) (n := 12)
    (lo := (212148931 / 1000000000)) (hi := (53037233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309083 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309083 / 250000) = 1/(250000 / 309083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (212148931 / 1000000000) (53037233 / 250000000) (Real.log (309083 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (309083 / 250000) = -Real.log (250000 / 309083) := by
    rw [show ((309083 / 250000) : ℝ) = ((250000 / 309083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (269622139 / 1000000000) ≤ -Real.log (190917 / 250000) ∧
    -Real.log (190917 / 250000) ≤ (13481107 / 50000000) := by
  have h := checkLog_sound (w := (59083 / 440917)) (n := 12)
    (lo := (269622139 / 1000000000)) (hi := (13481107 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 190917) = 1/(190917 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-13481107 / 50000000) (-269622139 / 1000000000) (Real.log (190917 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42498041 / 200000000) ≤ -Real.log (500000 / 618377) ∧
    -Real.log (500000 / 618377) ≤ (106245103 / 500000000) := by
  have h := checkLog_sound (w := (118377 / 1118377)) (n := 12)
    (lo := (42498041 / 200000000)) (hi := (106245103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618377 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618377 / 500000) = 1/(500000 / 618377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42498041 / 200000000) (106245103 / 500000000) (Real.log (618377 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (618377 / 500000) = -Real.log (500000 / 618377) := by
    rw [show ((618377 / 500000) : ℝ) = ((500000 / 618377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (33771861 / 125000000) ≤ -Real.log (381623 / 500000) ∧
    -Real.log (381623 / 500000) ≤ (270174889 / 1000000000) := by
  have h := checkLog_sound (w := (118377 / 881623)) (n := 12)
    (lo := (33771861 / 125000000)) (hi := (270174889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381623) = 1/(381623 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-270174889 / 1000000000) (-33771861 / 125000000) (Real.log (381623 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (156780647 / 1000000000) ≤ -Real.log (1000000 / 1169739) ∧
    -Real.log (1000000 / 1169739) ≤ (19597581 / 125000000) := by
  have h := checkLog_sound (w := (169739 / 2169739)) (n := 12)
    (lo := (156780647 / 1000000000)) (hi := (19597581 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169739 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169739 / 1000000) = 1/(1000000 / 1169739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (156780647 / 1000000000) (19597581 / 125000000) (Real.log (1169739 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1169739 / 1000000) = -Real.log (1000000 / 1169739) := by
    rw [show ((1169739 / 1000000) : ℝ) = ((1000000 / 1169739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (186015169 / 1000000000) ≤ -Real.log (830261 / 1000000) ∧
    -Real.log (830261 / 1000000) ≤ (18601517 / 100000000) := by
  have h := checkLog_sound (w := (169739 / 1830261)) (n := 12)
    (lo := (186015169 / 1000000000)) (hi := (18601517 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 830261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 830261) = 1/(830261 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18601517 / 100000000) (-186015169 / 1000000000) (Real.log (830261 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (157047337 / 1000000000) ≤ -Real.log (1000000 / 1170051) ∧
    -Real.log (1000000 / 1170051) ≤ (78523669 / 500000000) := by
  have h := checkLog_sound (w := (170051 / 2170051)) (n := 12)
    (lo := (157047337 / 1000000000)) (hi := (78523669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170051 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1170051 / 1000000) = 1/(1000000 / 1170051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (157047337 / 1000000000) (78523669 / 500000000) (Real.log (1170051 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1170051 / 1000000) = -Real.log (1000000 / 1170051) := by
    rw [show ((1170051 / 1000000) : ℝ) = ((1000000 / 1170051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7455641 / 40000000) ≤ -Real.log (829949 / 1000000) ∧
    -Real.log (829949 / 1000000) ≤ (93195513 / 500000000) := by
  have h := checkLog_sound (w := (170051 / 1829949)) (n := 12)
    (lo := (7455641 / 40000000)) (hi := (93195513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 829949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 829949) = 1/(829949 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-93195513 / 500000000) (-7455641 / 40000000) (Real.log (829949 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (172884071 / 250000000) ≤ -Real.log (62500000000 / 124798800117) ∧
    -Real.log (62500000000 / 124798800117) ≤ (138307257 / 200000000) := by
  have h := checkLog_sound (w := (62298800117 / 187298800117)) (n := 12)
    (lo := (172884071 / 250000000)) (hi := (138307257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124798800117 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124798800117 / 62500000000) = 1/(62500000000 / 124798800117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (172884071 / 250000000) (138307257 / 200000000) (Real.log (124798800117 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (124798800117 / 62500000000) = -Real.log (62500000000 / 124798800117) := by
    rw [show ((124798800117 / 62500000000) : ℝ) = ((62500000000 / 124798800117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (346427113 / 500000000) ≤ -Real.log (25000000000 / 49985354423) ∧
    -Real.log (25000000000 / 49985354423) ≤ (692854227 / 1000000000) := by
  have h := checkLog_sound (w := (24985354423 / 74985354423)) (n := 12)
    (lo := (346427113 / 500000000)) (hi := (692854227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49985354423 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49985354423 / 25000000000) = 1/(25000000000 / 49985354423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (346427113 / 500000000) (692854227 / 1000000000) (Real.log (49985354423 / 25000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (49985354423 / 25000000000) = -Real.log (25000000000 / 49985354423) := by
    rw [show ((49985354423 / 25000000000) : ℝ) = ((25000000000 / 49985354423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (48177107 / 100000000) ≤ -Real.log (50000000000 / 80946956007) ∧
    -Real.log (50000000000 / 80946956007) ≤ (481771071 / 1000000000) := by
  have h := checkLog_sound (w := (30946956007 / 130946956007)) (n := 12)
    (lo := (48177107 / 100000000)) (hi := (481771071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80946956007 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80946956007 / 50000000000) = 1/(50000000000 / 80946956007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (48177107 / 100000000) (481771071 / 1000000000) (Real.log (80946956007 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (80946956007 / 50000000000) = -Real.log (50000000000 / 80946956007) := by
    rw [show ((80946956007 / 50000000000) : ℝ) = ((50000000000 / 80946956007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (482665093 / 1000000000) ≤ -Real.log (250000000000 / 405096783999) ∧
    -Real.log (250000000000 / 405096783999) ≤ (241332547 / 500000000) := by
  have h := checkLog_sound (w := (155096783999 / 655096783999)) (n := 12)
    (lo := (482665093 / 1000000000)) (hi := (241332547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405096783999 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(405096783999 / 250000000000) = 1/(250000000000 / 405096783999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (482665093 / 1000000000) (241332547 / 500000000) (Real.log (405096783999 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (405096783999 / 250000000000) = -Real.log (250000000000 / 405096783999) := by
    rw [show ((405096783999 / 250000000000) : ℝ) = ((250000000000 / 405096783999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (42849477 / 125000000) ≤ -Real.log (10000000000 / 14088810627) ∧
    -Real.log (10000000000 / 14088810627) ≤ (342795817 / 1000000000) := by
  have h := checkLog_sound (w := (4088810627 / 24088810627)) (n := 12)
    (lo := (42849477 / 125000000)) (hi := (342795817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14088810627 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14088810627 / 10000000000) = 1/(10000000000 / 14088810627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (42849477 / 125000000) (342795817 / 1000000000) (Real.log (14088810627 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (14088810627 / 10000000000) = -Real.log (10000000000 / 14088810627) := by
    rw [show ((14088810627 / 10000000000) : ℝ) = ((10000000000 / 14088810627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (343438363 / 1000000000) ≤ -Real.log (250000000000 / 352446656361) ∧
    -Real.log (250000000000 / 352446656361) ≤ (85859591 / 250000000) := by
  have h := checkLog_sound (w := (102446656361 / 602446656361)) (n := 12)
    (lo := (343438363 / 1000000000)) (hi := (85859591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352446656361 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352446656361 / 250000000000) = 1/(250000000000 / 352446656361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (343438363 / 1000000000) (85859591 / 250000000) (Real.log (352446656361 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (352446656361 / 250000000000) = -Real.log (250000000000 / 352446656361) := by
    rw [show ((352446656361 / 250000000000) : ℝ) = ((250000000000 / 352446656361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3667961 / 125000000) ≤ -Real.log (971082657399 / 1000000000000) ∧
    -Real.log (971082657399 / 1000000000000) ≤ (29343689 / 1000000000) := by
  have h := checkLog_sound (w := (28917342601 / 1971082657399)) (n := 12)
    (lo := (3667961 / 125000000)) (hi := (29343689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971082657399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971082657399) = 1/(971082657399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29343689 / 1000000000) (-3667961 / 125000000) (Real.log (971082657399 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14617261 / 500000000) ≤ -Real.log (971188671879 / 1000000000000) ∧
    -Real.log (971188671879 / 1000000000000) ≤ (29234523 / 1000000000) := by
  have h := checkLog_sound (w := (28811328121 / 1971188671879)) (n := 12)
    (lo := (14617261 / 500000000)) (hi := (29234523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971188671879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971188671879) = 1/(971188671879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-29234523 / 1000000000) (-14617261 / 500000000) (Real.log (971188671879 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell141

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell142Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell142
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

theorem reflection_log_1_neg : (28802381 / 100000000) ≤ -Real.log (5120 / 6829) ∧
    -Real.log (5120 / 6829) ≤ (288023811 / 1000000000) := by
  have h := checkLog_sound (w := (1709 / 11949)) (n := 12)
    (lo := (28802381 / 100000000)) (hi := (288023811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6829 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6829 / 5120) = 1/(5120 / 6829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (28802381 / 100000000) (288023811 / 1000000000) (Real.log (6829 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6829 / 5120) = -Real.log (5120 / 6829) := by
    rw [show ((6829 / 5120) : ℝ) = ((5120 / 6829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (81229787 / 200000000) ≤ -Real.log (3411 / 5120) ∧
    -Real.log (3411 / 5120) ≤ (50768617 / 125000000) := by
  have h := checkLog_sound (w := (1709 / 8531)) (n := 12)
    (lo := (81229787 / 200000000)) (hi := (50768617 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3411) = 1/(3411 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-50768617 / 125000000) (-81229787 / 200000000) (Real.log (3411 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (287584411 / 1000000000) ≤ -Real.log (2560 / 3413) ∧
    -Real.log (2560 / 3413) ≤ (71896103 / 250000000) := by
  have h := checkLog_sound (w := (853 / 5973)) (n := 12)
    (lo := (287584411 / 1000000000)) (hi := (71896103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3413 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3413 / 2560) = 1/(2560 / 3413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (287584411 / 1000000000) (71896103 / 250000000) (Real.log (3413 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3413 / 2560) = -Real.log (2560 / 3413) := by
    rw [show ((3413 / 2560) : ℝ) = ((2560 / 3413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (202634907 / 500000000) ≤ -Real.log (1707 / 2560) ∧
    -Real.log (1707 / 2560) ≤ (81053963 / 200000000) := by
  have h := checkLog_sound (w := (853 / 4267)) (n := 12)
    (lo := (202634907 / 500000000)) (hi := (81053963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1707) = 1/(1707 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-81053963 / 200000000) (-202634907 / 500000000) (Real.log (1707 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (53122349 / 250000000) ≤ -Real.log (1000000 / 1236753) ∧
    -Real.log (1000000 / 1236753) ≤ (212489397 / 1000000000) := by
  have h := checkLog_sound (w := (236753 / 2236753)) (n := 12)
    (lo := (53122349 / 250000000)) (hi := (212489397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236753 / 1000000) = 1/(1000000 / 1236753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (53122349 / 250000000) (212489397 / 1000000000) (Real.log (1236753 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1236753 / 1000000) = -Real.log (1000000 / 1236753) := by
    rw [show ((1236753 / 1000000) : ℝ) = ((1000000 / 1236753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (270173577 / 1000000000) ≤ -Real.log (763247 / 1000000) ∧
    -Real.log (763247 / 1000000) ≤ (135086789 / 500000000) := by
  have h := checkLog_sound (w := (236753 / 1763247)) (n := 12)
    (lo := (270173577 / 1000000000)) (hi := (135086789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763247) = 1/(763247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-135086789 / 500000000) (-270173577 / 1000000000) (Real.log (763247 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (106415277 / 500000000) ≤ -Real.log (40000 / 49487) ∧
    -Real.log (40000 / 49487) ≤ (42566111 / 200000000) := by
  have h := checkLog_sound (w := (9487 / 89487)) (n := 12)
    (lo := (106415277 / 500000000)) (hi := (42566111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49487 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49487 / 40000) = 1/(40000 / 49487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (106415277 / 500000000) (42566111 / 200000000) (Real.log (49487 / 40000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49487 / 40000) = -Real.log (40000 / 49487) := by
    rw [show ((49487 / 40000) : ℝ) = ((40000 / 49487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (270726631 / 1000000000) ≤ -Real.log (30513 / 40000) ∧
    -Real.log (30513 / 40000) ≤ (33840829 / 125000000) := by
  have h := checkLog_sound (w := (9487 / 70513)) (n := 12)
    (lo := (270726631 / 1000000000)) (hi := (33840829 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 30513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 30513) = 1/(30513 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-33840829 / 125000000) (-270726631 / 1000000000) (Real.log (30513 / 40000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (78523241 / 500000000) ≤ -Real.log (20000 / 23401) ∧
    -Real.log (20000 / 23401) ≤ (157046483 / 1000000000) := by
  have h := checkLog_sound (w := (3401 / 43401)) (n := 12)
    (lo := (78523241 / 500000000)) (hi := (157046483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23401 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23401 / 20000) = 1/(20000 / 23401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (78523241 / 500000000) (157046483 / 1000000000) (Real.log (23401 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (23401 / 20000) = -Real.log (20000 / 23401) := by
    rw [show ((23401 / 20000) : ℝ) = ((20000 / 23401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9319491 / 50000000) ≤ -Real.log (16599 / 20000) ∧
    -Real.log (16599 / 20000) ≤ (186389821 / 1000000000) := by
  have h := checkLog_sound (w := (3401 / 36599)) (n := 12)
    (lo := (9319491 / 50000000)) (hi := (186389821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 16599) = 1/(16599 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-186389821 / 1000000000) (-9319491 / 50000000) (Real.log (16599 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (157313957 / 1000000000) ≤ -Real.log (1000000 / 1170363) ∧
    -Real.log (1000000 / 1170363) ≤ (78656979 / 500000000) := by
  have h := checkLog_sound (w := (170363 / 2170363)) (n := 12)
    (lo := (157313957 / 1000000000)) (hi := (78656979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1170363 / 1000000) = 1/(1000000 / 1170363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (157313957 / 1000000000) (78656979 / 500000000) (Real.log (1170363 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1170363 / 1000000) = -Real.log (1000000 / 1170363) := by
    rw [show ((1170363 / 1000000) : ℝ) = ((1000000 / 1170363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (186767023 / 1000000000) ≤ -Real.log (829637 / 1000000) ∧
    -Real.log (829637 / 1000000) ≤ (11672939 / 62500000) := by
  have h := checkLog_sound (w := (170363 / 1829637)) (n := 12)
    (lo := (186767023 / 1000000000)) (hi := (11672939 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 829637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 829637) = 1/(829637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11672939 / 62500000) (-186767023 / 1000000000) (Real.log (829637 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (346427113 / 500000000) ≤ -Real.log (500000000000 / 999707088459) ∧
    -Real.log (500000000000 / 999707088459) ≤ (692854227 / 1000000000) := by
  have h := checkLog_sound (w := (499707088459 / 1499707088459)) (n := 12)
    (lo := (346427113 / 500000000)) (hi := (692854227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((999707088459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(999707088459 / 500000000000) = 1/(500000000000 / 999707088459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (346427113 / 500000000) (692854227 / 1000000000) (Real.log (999707088459 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (999707088459 / 500000000000) = -Real.log (500000000000 / 999707088459) := by
    rw [show ((999707088459 / 500000000000) : ℝ) = ((500000000000 / 999707088459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (138834549 / 200000000) ≤ -Real.log (62500000000 / 125128261507) ∧
    -Real.log (62500000000 / 125128261507) ≤ (694172747 / 1000000000) := by
  have h := checkLog_sound (w := (128261507 / 250128261507)) (n := 12)
    (lo := (205113 / 200000000)) (hi := (512783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125128261507 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125128261507 / 125000000000) = 1/(62500000000 / 125128261507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (138834549 / 200000000) (694172747 / 1000000000) (Real.log (125128261507 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (125128261507 / 62500000000) = -Real.log (62500000000 / 125128261507) := by
    rw [show ((125128261507 / 62500000000) : ℝ) = ((62500000000 / 125128261507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (241331487 / 500000000) ≤ -Real.log (3906250000 / 6329623839) ∧
    -Real.log (3906250000 / 6329623839) ≤ (19306519 / 40000000) := by
  have h := checkLog_sound (w := (2423373839 / 10235873839)) (n := 12)
    (lo := (241331487 / 500000000)) (hi := (19306519 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6329623839 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6329623839 / 3906250000) = 1/(3906250000 / 6329623839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (241331487 / 500000000) (19306519 / 40000000) (Real.log (6329623839 / 3906250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (6329623839 / 3906250000) = -Real.log (3906250000 / 6329623839) := by
    rw [show ((6329623839 / 3906250000) : ℝ) = ((3906250000 / 6329623839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (241778593 / 500000000) ≤ -Real.log (250000000000 / 405458329237) ∧
    -Real.log (250000000000 / 405458329237) ≤ (483557187 / 1000000000) := by
  have h := checkLog_sound (w := (155458329237 / 655458329237)) (n := 12)
    (lo := (241778593 / 500000000)) (hi := (483557187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405458329237 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(405458329237 / 250000000000) = 1/(250000000000 / 405458329237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (241778593 / 500000000) (483557187 / 1000000000) (Real.log (405458329237 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (405458329237 / 250000000000) = -Real.log (250000000000 / 405458329237) := by
    rw [show ((405458329237 / 250000000000) : ℝ) = ((250000000000 / 405458329237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (343436303 / 1000000000) ≤ -Real.log (100000000000 / 140978372191) ∧
    -Real.log (100000000000 / 140978372191) ≤ (21464769 / 62500000) := by
  have h := checkLog_sound (w := (40978372191 / 240978372191)) (n := 12)
    (lo := (343436303 / 1000000000)) (hi := (21464769 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140978372191 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140978372191 / 100000000000) = 1/(100000000000 / 140978372191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (343436303 / 1000000000) (21464769 / 62500000) (Real.log (140978372191 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (140978372191 / 100000000000) = -Real.log (100000000000 / 140978372191) := by
    rw [show ((140978372191 / 100000000000) : ℝ) = ((100000000000 / 140978372191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (17204049 / 50000000) ≤ -Real.log (250000000000 / 352673217323) ∧
    -Real.log (250000000000 / 352673217323) ≤ (344080981 / 1000000000) := by
  have h := checkLog_sound (w := (102673217323 / 602673217323)) (n := 12)
    (lo := (17204049 / 50000000)) (hi := (344080981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352673217323 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352673217323 / 250000000000) = 1/(250000000000 / 352673217323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (17204049 / 50000000) (344080981 / 1000000000) (Real.log (352673217323 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (352673217323 / 250000000000) = -Real.log (250000000000 / 352673217323) := by
    rw [show ((352673217323 / 250000000000) : ℝ) = ((250000000000 / 352673217323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (14726533 / 500000000) ≤ -Real.log (970976448231 / 1000000000000) ∧
    -Real.log (970976448231 / 1000000000000) ≤ (29453067 / 1000000000) := by
  have h := checkLog_sound (w := (29023551769 / 1970976448231)) (n := 12)
    (lo := (14726533 / 500000000)) (hi := (29453067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970976448231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970976448231) = 1/(970976448231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29453067 / 1000000000) (-14726533 / 500000000) (Real.log (970976448231 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14671669 / 500000000) ≤ -Real.log (388433199 / 400000000) ∧
    -Real.log (388433199 / 400000000) ≤ (29343339 / 1000000000) := by
  have h := checkLog_sound (w := (11566801 / 788433199)) (n := 12)
    (lo := (14671669 / 500000000)) (hi := (29343339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 388433199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 388433199) = 1/(388433199 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-29343339 / 1000000000) (-14671669 / 500000000) (Real.log (388433199 / 400000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell142

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell143Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell143
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

theorem reflection_log_1_neg : (288463017 / 1000000000) ≤ -Real.log (320 / 427) ∧
    -Real.log (320 / 427) ≤ (144231509 / 500000000) := by
  have h := checkLog_sound (w := (107 / 747)) (n := 12)
    (lo := (288463017 / 1000000000)) (hi := (144231509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427 / 320) = 1/(320 / 427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (288463017 / 1000000000) (144231509 / 500000000) (Real.log (427 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (427 / 320) = -Real.log (320 / 427) := by
    rw [show ((427 / 320) : ℝ) = ((320 / 427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (40702883 / 100000000) ≤ -Real.log (213 / 320) ∧
    -Real.log (213 / 320) ≤ (407028831 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 213) = 1/(213 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-407028831 / 1000000000) (-40702883 / 100000000) (Real.log (213 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (28802381 / 100000000) ≤ -Real.log (5120 / 6829) ∧
    -Real.log (5120 / 6829) ≤ (288023811 / 1000000000) := by
  have h := checkLog_sound (w := (1709 / 11949)) (n := 12)
    (lo := (28802381 / 100000000)) (hi := (288023811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6829 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6829 / 5120) = 1/(5120 / 6829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (28802381 / 100000000) (288023811 / 1000000000) (Real.log (6829 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6829 / 5120) = -Real.log (5120 / 6829) := by
    rw [show ((6829 / 5120) : ℝ) = ((5120 / 6829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (81229787 / 200000000) ≤ -Real.log (3411 / 5120) ∧
    -Real.log (3411 / 5120) ≤ (50768617 / 125000000) := by
  have h := checkLog_sound (w := (1709 / 8531)) (n := 12)
    (lo := (81229787 / 200000000)) (hi := (50768617 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3411) = 1/(3411 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-50768617 / 125000000) (-81229787 / 200000000) (Real.log (3411 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (106414469 / 500000000) ≤ -Real.log (1000000 / 1237173) ∧
    -Real.log (1000000 / 1237173) ≤ (212828939 / 1000000000) := by
  have h := checkLog_sound (w := (237173 / 2237173)) (n := 12)
    (lo := (106414469 / 500000000)) (hi := (212828939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1237173 / 1000000) = 1/(1000000 / 1237173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (106414469 / 500000000) (212828939 / 1000000000) (Real.log (1237173 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1237173 / 1000000) = -Real.log (1000000 / 1237173) := by
    rw [show ((1237173 / 1000000) : ℝ) = ((1000000 / 1237173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (270724009 / 1000000000) ≤ -Real.log (762827 / 1000000) ∧
    -Real.log (762827 / 1000000) ≤ (27072401 / 100000000) := by
  have h := checkLog_sound (w := (237173 / 1762827)) (n := 12)
    (lo := (270724009 / 1000000000)) (hi := (27072401 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 762827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 762827) = 1/(762827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-27072401 / 100000000) (-270724009 / 1000000000) (Real.log (762827 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10658499 / 50000000) ≤ -Real.log (200000 / 247519) ∧
    -Real.log (200000 / 247519) ≤ (213169981 / 1000000000) := by
  have h := checkLog_sound (w := (47519 / 447519)) (n := 12)
    (lo := (10658499 / 50000000)) (hi := (213169981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247519 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247519 / 200000) = 1/(200000 / 247519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10658499 / 50000000) (213169981 / 1000000000) (Real.log (247519 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (247519 / 200000) = -Real.log (200000 / 247519) := by
    rw [show ((247519 / 200000) : ℝ) = ((200000 / 247519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (33909671 / 125000000) ≤ -Real.log (152481 / 200000) ∧
    -Real.log (152481 / 200000) ≤ (271277369 / 1000000000) := by
  have h := checkLog_sound (w := (47519 / 352481)) (n := 12)
    (lo := (33909671 / 125000000)) (hi := (271277369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152481) = 1/(152481 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-271277369 / 1000000000) (-33909671 / 125000000) (Real.log (152481 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (78656551 / 500000000) ≤ -Real.log (500000 / 585181) ∧
    -Real.log (500000 / 585181) ≤ (157313103 / 1000000000) := by
  have h := checkLog_sound (w := (85181 / 1085181)) (n := 12)
    (lo := (78656551 / 500000000)) (hi := (157313103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585181 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585181 / 500000) = 1/(500000 / 585181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (78656551 / 500000000) (157313103 / 1000000000) (Real.log (585181 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (585181 / 500000) = -Real.log (500000 / 585181) := by
    rw [show ((585181 / 500000) : ℝ) = ((500000 / 585181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (186765817 / 1000000000) ≤ -Real.log (414819 / 500000) ∧
    -Real.log (414819 / 500000) ≤ (93382909 / 500000000) := by
  have h := checkLog_sound (w := (85181 / 914819)) (n := 12)
    (lo := (186765817 / 1000000000)) (hi := (93382909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414819) = 1/(414819 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-93382909 / 500000000) (-186765817 / 1000000000) (Real.log (414819 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31516101 / 200000000) ≤ -Real.log (40000 / 46827) ∧
    -Real.log (40000 / 46827) ≤ (78790253 / 500000000) := by
  have h := checkLog_sound (w := (6827 / 86827)) (n := 12)
    (lo := (31516101 / 200000000)) (hi := (78790253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46827 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46827 / 40000) = 1/(40000 / 46827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31516101 / 200000000) (78790253 / 500000000) (Real.log (46827 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (46827 / 40000) = -Real.log (40000 / 46827) := by
    rw [show ((46827 / 40000) : ℝ) = ((40000 / 46827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93571581 / 500000000) ≤ -Real.log (33173 / 40000) ∧
    -Real.log (33173 / 40000) ≤ (187143163 / 1000000000) := by
  have h := checkLog_sound (w := (6827 / 73173)) (n := 12)
    (lo := (93571581 / 500000000)) (hi := (187143163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33173) = 1/(33173 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-187143163 / 1000000000) (-93571581 / 500000000) (Real.log (33173 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (138834549 / 200000000) ≤ -Real.log (100000000000 / 200205218411) ∧
    -Real.log (100000000000 / 200205218411) ≤ (694172747 / 1000000000) := by
  have h := checkLog_sound (w := (205218411 / 400205218411)) (n := 12)
    (lo := (205113 / 200000000)) (hi := (512783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200205218411 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200205218411 / 200000000000) = 1/(100000000000 / 200205218411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (138834549 / 200000000) (694172747 / 1000000000) (Real.log (200205218411 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (200205218411 / 100000000000) = -Real.log (100000000000 / 200205218411) := by
    rw [show ((200205218411 / 100000000000) : ℝ) = ((100000000000 / 200205218411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (347745923 / 500000000) ≤ -Real.log (500000000000 / 1002347417841) ∧
    -Real.log (500000000000 / 1002347417841) ≤ (86936481 / 125000000) := by
  have h := checkLog_sound (w := (2347417841 / 2002347417841)) (n := 12)
    (lo := (1172333 / 500000000)) (hi := (2344667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1002347417841 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1002347417841 / 1000000000000) = 1/(500000000000 / 1002347417841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (347745923 / 500000000) (86936481 / 125000000) (Real.log (1002347417841 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1002347417841 / 500000000000) = -Real.log (500000000000 / 1002347417841) := by
    rw [show ((1002347417841 / 500000000000) : ℝ) = ((500000000000 / 1002347417841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (120888237 / 250000000) ≤ -Real.log (500000000000 / 810913221477) ∧
    -Real.log (500000000000 / 810913221477) ≤ (483552949 / 1000000000) := by
  have h := checkLog_sound (w := (310913221477 / 1310913221477)) (n := 12)
    (lo := (120888237 / 250000000)) (hi := (483552949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((810913221477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(810913221477 / 500000000000) = 1/(500000000000 / 810913221477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (120888237 / 250000000) (483552949 / 1000000000) (Real.log (810913221477 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (810913221477 / 500000000000) = -Real.log (500000000000 / 810913221477) := by
    rw [show ((810913221477 / 500000000000) : ℝ) = ((500000000000 / 810913221477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (121111837 / 250000000) ≤ -Real.log (500000000000 / 811638827133) ∧
    -Real.log (500000000000 / 811638827133) ≤ (484447349 / 1000000000) := by
  have h := checkLog_sound (w := (311638827133 / 1311638827133)) (n := 12)
    (lo := (121111837 / 250000000)) (hi := (484447349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811638827133 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811638827133 / 500000000000) = 1/(500000000000 / 811638827133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (121111837 / 250000000) (484447349 / 1000000000) (Real.log (811638827133 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (811638827133 / 500000000000) = -Real.log (500000000000 / 811638827133) := by
    rw [show ((811638827133 / 500000000000) : ℝ) = ((500000000000 / 811638827133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (8601973 / 25000000) ≤ -Real.log (500000000000 / 705344981787) ∧
    -Real.log (500000000000 / 705344981787) ≤ (344078921 / 1000000000) := by
  have h := checkLog_sound (w := (205344981787 / 1205344981787)) (n := 12)
    (lo := (8601973 / 25000000)) (hi := (344078921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705344981787 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705344981787 / 500000000000) = 1/(500000000000 / 705344981787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (8601973 / 25000000) (344078921 / 1000000000) (Real.log (705344981787 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (705344981787 / 500000000000) = -Real.log (500000000000 / 705344981787) := by
    rw [show ((705344981787 / 500000000000) : ℝ) = ((500000000000 / 705344981787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (344723667 / 1000000000) ≤ -Real.log (125000000000 / 176449974377) ∧
    -Real.log (125000000000 / 176449974377) ≤ (86180917 / 250000000) := by
  have h := checkLog_sound (w := (51449974377 / 301449974377)) (n := 12)
    (lo := (344723667 / 1000000000)) (hi := (86180917 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176449974377 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176449974377 / 125000000000) = 1/(125000000000 / 176449974377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (344723667 / 1000000000) (86180917 / 250000000) (Real.log (176449974377 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (176449974377 / 125000000000) = -Real.log (125000000000 / 176449974377) := by
    rw [show ((176449974377 / 125000000000) : ℝ) = ((125000000000 / 176449974377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (923833 / 31250000) ≤ -Real.log (1553392071 / 1600000000) ∧
    -Real.log (1553392071 / 1600000000) ≤ (29562657 / 1000000000) := by
  have h := checkLog_sound (w := (46607929 / 3153392071)) (n := 12)
    (lo := (923833 / 31250000)) (hi := (29562657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1553392071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1553392071) = 1/(1553392071 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29562657 / 1000000000) (-923833 / 31250000) (Real.log (1553392071 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5890543 / 200000000) ≤ -Real.log (242744197239 / 250000000000) ∧
    -Real.log (242744197239 / 250000000000) ≤ (7363179 / 250000000) := by
  have h := checkLog_sound (w := (7255802761 / 492744197239)) (n := 12)
    (lo := (5890543 / 200000000)) (hi := (7363179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242744197239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242744197239) = 1/(242744197239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7363179 / 250000000) (-5890543 / 200000000) (Real.log (242744197239 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell143

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell144Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell144
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

theorem reflection_log_1_neg : (288902031 / 1000000000) ≤ -Real.log (1024 / 1367) ∧
    -Real.log (1024 / 1367) ≤ (18056377 / 62500000) := by
  have h := checkLog_sound (w := (343 / 2391)) (n := 12)
    (lo := (288902031 / 1000000000)) (hi := (18056377 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1367 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1367 / 1024) = 1/(1024 / 1367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (288902031 / 1000000000) (18056377 / 62500000) (Real.log (1367 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1367 / 1024) = -Real.log (1024 / 1367) := by
    rw [show ((1367 / 1024) : ℝ) = ((1024 / 1367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (407909499 / 1000000000) ≤ -Real.log (681 / 1024) ∧
    -Real.log (681 / 1024) ≤ (815819 / 2000000) := by
  have h := checkLog_sound (w := (343 / 1705)) (n := 12)
    (lo := (407909499 / 1000000000)) (hi := (815819 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 681) = 1/(681 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-815819 / 2000000) (-407909499 / 1000000000) (Real.log (681 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (288463017 / 1000000000) ≤ -Real.log (320 / 427) ∧
    -Real.log (320 / 427) ≤ (144231509 / 500000000) := by
  have h := checkLog_sound (w := (107 / 747)) (n := 12)
    (lo := (288463017 / 1000000000)) (hi := (144231509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427 / 320) = 1/(320 / 427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (288463017 / 1000000000) (144231509 / 500000000) (Real.log (427 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (427 / 320) = -Real.log (320 / 427) := by
    rw [show ((427 / 320) : ℝ) = ((320 / 427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (40702883 / 100000000) ≤ -Real.log (213 / 320) ∧
    -Real.log (213 / 320) ≤ (407028831 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 213) = 1/(213 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-407028831 / 1000000000) (-40702883 / 100000000) (Real.log (213 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (53292293 / 250000000) ≤ -Real.log (500000 / 618797) ∧
    -Real.log (500000 / 618797) ≤ (213169173 / 1000000000) := by
  have h := checkLog_sound (w := (118797 / 1118797)) (n := 12)
    (lo := (53292293 / 250000000)) (hi := (213169173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618797 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618797 / 500000) = 1/(500000 / 618797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (53292293 / 250000000) (213169173 / 1000000000) (Real.log (618797 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (618797 / 500000) = -Real.log (500000 / 618797) := by
    rw [show ((618797 / 500000) : ℝ) = ((500000 / 618797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (33909507 / 125000000) ≤ -Real.log (381203 / 500000) ∧
    -Real.log (381203 / 500000) ≤ (271276057 / 1000000000) := by
  have h := checkLog_sound (w := (118797 / 881203)) (n := 12)
    (lo := (33909507 / 125000000)) (hi := (271276057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381203) = 1/(381203 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-271276057 / 1000000000) (-33909507 / 125000000) (Real.log (381203 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (106755049 / 500000000) ≤ -Real.log (15625 / 19344) ∧
    -Real.log (15625 / 19344) ≤ (213510099 / 1000000000) := by
  have h := checkLog_sound (w := (3719 / 34969)) (n := 12)
    (lo := (106755049 / 500000000)) (hi := (213510099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19344 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19344 / 15625) = 1/(15625 / 19344) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (106755049 / 500000000) (213510099 / 1000000000) (Real.log (19344 / 15625)) := by
  have h := reflection_log_7_neg
  have he : Real.log (19344 / 15625) = -Real.log (15625 / 19344) := by
    rw [show ((19344 / 15625) : ℝ) = ((15625 / 19344) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6795743 / 25000000) ≤ -Real.log (11906 / 15625) ∧
    -Real.log (11906 / 15625) ≤ (271829721 / 1000000000) := by
  have h := checkLog_sound (w := (3719 / 27531)) (n := 12)
    (lo := (6795743 / 25000000)) (hi := (271829721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11906) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11906) = 1/(11906 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-271829721 / 1000000000) (-6795743 / 25000000) (Real.log (11906 / 15625)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (157579651 / 1000000000) ≤ -Real.log (500000 / 585337) ∧
    -Real.log (500000 / 585337) ≤ (39394913 / 250000000) := by
  have h := checkLog_sound (w := (85337 / 1085337)) (n := 12)
    (lo := (157579651 / 1000000000)) (hi := (39394913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585337 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585337 / 500000) = 1/(500000 / 585337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (157579651 / 1000000000) (39394913 / 250000000) (Real.log (585337 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (585337 / 500000) = -Real.log (500000 / 585337) := by
    rw [show ((585337 / 500000) : ℝ) = ((500000 / 585337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (46785489 / 250000000) ≤ -Real.log (414663 / 500000) ∧
    -Real.log (414663 / 500000) ≤ (187141957 / 1000000000) := by
  have h := checkLog_sound (w := (85337 / 914663)) (n := 12)
    (lo := (46785489 / 250000000)) (hi := (187141957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414663) = 1/(414663 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-187141957 / 1000000000) (-46785489 / 250000000) (Real.log (414663 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9865383 / 62500000) ≤ -Real.log (500000 / 585493) ∧
    -Real.log (500000 / 585493) ≤ (157846129 / 1000000000) := by
  have h := checkLog_sound (w := (85493 / 1085493)) (n := 12)
    (lo := (9865383 / 62500000)) (hi := (157846129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585493 / 500000) = 1/(500000 / 585493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9865383 / 62500000) (157846129 / 1000000000) (Real.log (585493 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (585493 / 500000) = -Real.log (500000 / 585493) := by
    rw [show ((585493 / 500000) : ℝ) = ((500000 / 585493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (46879559 / 250000000) ≤ -Real.log (414507 / 500000) ∧
    -Real.log (414507 / 500000) ≤ (187518237 / 1000000000) := by
  have h := checkLog_sound (w := (85493 / 914507)) (n := 12)
    (lo := (46879559 / 250000000)) (hi := (187518237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414507) = 1/(414507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-187518237 / 1000000000) (-46879559 / 250000000) (Real.log (414507 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (347745923 / 500000000) ≤ -Real.log (6250000000 / 12529342723) ∧
    -Real.log (6250000000 / 12529342723) ≤ (86936481 / 125000000) := by
  have h := checkLog_sound (w := (29342723 / 25029342723)) (n := 12)
    (lo := (1172333 / 500000000)) (hi := (2344667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12529342723 / 12500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12529342723 / 12500000000) = 1/(6250000000 / 12529342723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (347745923 / 500000000) (86936481 / 125000000) (Real.log (12529342723 / 6250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (12529342723 / 6250000000) = -Real.log (6250000000 / 12529342723) := by
    rw [show ((12529342723 / 6250000000) : ℝ) = ((6250000000 / 12529342723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69681153 / 100000000) ≤ -Real.log (250000000000 / 501835535977) ∧
    -Real.log (250000000000 / 501835535977) ≤ (174202883 / 250000000) := by
  have h := checkLog_sound (w := (1835535977 / 1001835535977)) (n := 12)
    (lo := (73287 / 20000000)) (hi := (3664351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((501835535977 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(501835535977 / 500000000000) = 1/(250000000000 / 501835535977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (69681153 / 100000000) (174202883 / 250000000) (Real.log (501835535977 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (501835535977 / 250000000000) = -Real.log (250000000000 / 501835535977) := by
    rw [show ((501835535977 / 250000000000) : ℝ) = ((250000000000 / 501835535977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (121111307 / 250000000) ≤ -Real.log (250000000000 / 405818553369) ∧
    -Real.log (250000000000 / 405818553369) ≤ (484445229 / 1000000000) := by
  have h := checkLog_sound (w := (155818553369 / 655818553369)) (n := 12)
    (lo := (121111307 / 250000000)) (hi := (484445229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405818553369 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(405818553369 / 250000000000) = 1/(250000000000 / 405818553369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (121111307 / 250000000) (484445229 / 1000000000) (Real.log (405818553369 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (405818553369 / 250000000000) = -Real.log (250000000000 / 405818553369) := by
    rw [show ((405818553369 / 250000000000) : ℝ) = ((250000000000 / 405818553369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (485339819 / 1000000000) ≤ -Real.log (100000000000 / 162472702839) ∧
    -Real.log (100000000000 / 162472702839) ≤ (24266991 / 50000000) := by
  have h := checkLog_sound (w := (62472702839 / 262472702839)) (n := 12)
    (lo := (485339819 / 1000000000)) (hi := (24266991 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162472702839 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162472702839 / 100000000000) = 1/(100000000000 / 162472702839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (485339819 / 1000000000) (24266991 / 50000000) (Real.log (162472702839 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (162472702839 / 100000000000) = -Real.log (100000000000 / 162472702839) := by
    rw [show ((162472702839 / 100000000000) : ℝ) = ((100000000000 / 162472702839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (344721607 / 1000000000) ≤ -Real.log (100000000000 / 141159688711) ∧
    -Real.log (100000000000 / 141159688711) ≤ (43090201 / 125000000) := by
  have h := checkLog_sound (w := (41159688711 / 241159688711)) (n := 12)
    (lo := (344721607 / 1000000000)) (hi := (43090201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141159688711 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141159688711 / 100000000000) = 1/(100000000000 / 141159688711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (344721607 / 1000000000) (43090201 / 125000000) (Real.log (141159688711 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (141159688711 / 100000000000) = -Real.log (100000000000 / 141159688711) := by
    rw [show ((141159688711 / 100000000000) : ℝ) = ((100000000000 / 141159688711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (69072873 / 200000000) ≤ -Real.log (100000000000 / 141250449329) ∧
    -Real.log (100000000000 / 141250449329) ≤ (172682183 / 500000000) := by
  have h := checkLog_sound (w := (41250449329 / 241250449329)) (n := 12)
    (lo := (69072873 / 200000000)) (hi := (172682183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141250449329 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141250449329 / 100000000000) = 1/(100000000000 / 141250449329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (69072873 / 200000000) (172682183 / 500000000) (Real.log (141250449329 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (141250449329 / 100000000000) = -Real.log (100000000000 / 141250449329) := by
    rw [show ((141250449329 / 100000000000) : ℝ) = ((100000000000 / 141250449329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (29672107 / 1000000000) ≤ -Real.log (242690946951 / 250000000000) ∧
    -Real.log (242690946951 / 250000000000) ≤ (7418027 / 250000000) := by
  have h := checkLog_sound (w := (7309053049 / 492690946951)) (n := 12)
    (lo := (29672107 / 1000000000)) (hi := (7418027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242690946951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242690946951) = 1/(242690946951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-7418027 / 250000000) (-29672107 / 1000000000) (Real.log (242690946951 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (461911 / 15625000) ≤ -Real.log (242717596431 / 250000000000) ∧
    -Real.log (242717596431 / 250000000000) ≤ (5912461 / 200000000) := by
  have h := checkLog_sound (w := (7282403569 / 492717596431)) (n := 12)
    (lo := (461911 / 15625000)) (hi := (5912461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242717596431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242717596431) = 1/(242717596431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5912461 / 200000000) (-461911 / 15625000) (Real.log (242717596431 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell144

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell145Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell145
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

theorem reflection_log_1_neg : (72335213 / 250000000) ≤ -Real.log (2560 / 3419) ∧
    -Real.log (2560 / 3419) ≤ (289340853 / 1000000000) := by
  have h := checkLog_sound (w := (859 / 5979)) (n := 12)
    (lo := (72335213 / 250000000)) (hi := (289340853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3419 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3419 / 2560) = 1/(2560 / 3419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (72335213 / 250000000) (289340853 / 1000000000) (Real.log (3419 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3419 / 2560) = -Real.log (2560 / 3419) := by
    rw [show ((3419 / 2560) : ℝ) = ((2560 / 3419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (81758189 / 200000000) ≤ -Real.log (1701 / 2560) ∧
    -Real.log (1701 / 2560) ≤ (204395473 / 500000000) := by
  have h := checkLog_sound (w := (859 / 4261)) (n := 12)
    (lo := (81758189 / 200000000)) (hi := (204395473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1701) = 1/(1701 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-204395473 / 500000000) (-81758189 / 200000000) (Real.log (1701 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (288902031 / 1000000000) ≤ -Real.log (1024 / 1367) ∧
    -Real.log (1024 / 1367) ≤ (18056377 / 62500000) := by
  have h := checkLog_sound (w := (343 / 2391)) (n := 12)
    (lo := (288902031 / 1000000000)) (hi := (18056377 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1367 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1367 / 1024) = 1/(1024 / 1367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (288902031 / 1000000000) (18056377 / 62500000) (Real.log (1367 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1367 / 1024) = -Real.log (1024 / 1367) := by
    rw [show ((1367 / 1024) : ℝ) = ((1024 / 1367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (407909499 / 1000000000) ≤ -Real.log (681 / 1024) ∧
    -Real.log (681 / 1024) ≤ (815819 / 2000000) := by
  have h := checkLog_sound (w := (343 / 1705)) (n := 12)
    (lo := (407909499 / 1000000000)) (hi := (815819 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 681) = 1/(681 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-815819 / 2000000) (-407909499 / 1000000000) (Real.log (681 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21350929 / 100000000) ≤ -Real.log (200000 / 247603) ∧
    -Real.log (200000 / 247603) ≤ (213509291 / 1000000000) := by
  have h := checkLog_sound (w := (47603 / 447603)) (n := 12)
    (lo := (21350929 / 100000000)) (hi := (213509291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247603 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247603 / 200000) = 1/(200000 / 247603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21350929 / 100000000) (213509291 / 1000000000) (Real.log (247603 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (247603 / 200000) = -Real.log (200000 / 247603) := by
    rw [show ((247603 / 200000) : ℝ) = ((200000 / 247603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (33978551 / 125000000) ≤ -Real.log (152397 / 200000) ∧
    -Real.log (152397 / 200000) ≤ (271828409 / 1000000000) := by
  have h := checkLog_sound (w := (47603 / 352397)) (n := 12)
    (lo := (33978551 / 125000000)) (hi := (271828409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152397) = 1/(152397 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-271828409 / 1000000000) (-33978551 / 125000000) (Real.log (152397 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (53462727 / 250000000) ≤ -Real.log (500000 / 619219) ∧
    -Real.log (500000 / 619219) ≤ (213850909 / 1000000000) := by
  have h := checkLog_sound (w := (119219 / 1119219)) (n := 12)
    (lo := (53462727 / 250000000)) (hi := (213850909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619219 / 500000) = 1/(500000 / 619219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (53462727 / 250000000) (213850909 / 1000000000) (Real.log (619219 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (619219 / 500000) = -Real.log (500000 / 619219) := by
    rw [show ((619219 / 500000) : ℝ) = ((500000 / 619219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (272383691 / 1000000000) ≤ -Real.log (380781 / 500000) ∧
    -Real.log (380781 / 500000) ≤ (68095923 / 250000000) := by
  have h := checkLog_sound (w := (119219 / 880781)) (n := 12)
    (lo := (272383691 / 1000000000)) (hi := (68095923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380781) = 1/(380781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-68095923 / 250000000) (-272383691 / 1000000000) (Real.log (380781 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (78922637 / 500000000) ≤ -Real.log (200000 / 234197) ∧
    -Real.log (200000 / 234197) ≤ (6313811 / 40000000) := by
  have h := checkLog_sound (w := (34197 / 434197)) (n := 12)
    (lo := (78922637 / 500000000)) (hi := (6313811 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234197 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234197 / 200000) = 1/(200000 / 234197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (78922637 / 500000000) (6313811 / 40000000) (Real.log (234197 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (234197 / 200000) = -Real.log (200000 / 234197) := by
    rw [show ((234197 / 200000) : ℝ) = ((200000 / 234197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (187517029 / 1000000000) ≤ -Real.log (165803 / 200000) ∧
    -Real.log (165803 / 200000) ≤ (18751703 / 100000000) := by
  have h := checkLog_sound (w := (34197 / 365803)) (n := 12)
    (lo := (187517029 / 1000000000)) (hi := (18751703 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 165803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 165803) = 1/(165803 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18751703 / 100000000) (-187517029 / 1000000000) (Real.log (165803 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31622507 / 200000000) ≤ -Real.log (500000 / 585649) ∧
    -Real.log (500000 / 585649) ≤ (19764067 / 125000000) := by
  have h := checkLog_sound (w := (85649 / 1085649)) (n := 12)
    (lo := (31622507 / 200000000)) (hi := (19764067 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585649 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585649 / 500000) = 1/(500000 / 585649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31622507 / 200000000) (19764067 / 125000000) (Real.log (585649 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (585649 / 500000) = -Real.log (500000 / 585649) := by
    rw [show ((585649 / 500000) : ℝ) = ((500000 / 585649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (187894657 / 1000000000) ≤ -Real.log (414351 / 500000) ∧
    -Real.log (414351 / 500000) ≤ (93947329 / 500000000) := by
  have h := checkLog_sound (w := (85649 / 914351)) (n := 12)
    (lo := (187894657 / 1000000000)) (hi := (93947329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414351) = 1/(414351 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-93947329 / 500000000) (-187894657 / 1000000000) (Real.log (414351 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (69681153 / 100000000) ≤ -Real.log (500000000000 / 1003671071953) ∧
    -Real.log (500000000000 / 1003671071953) ≤ (174202883 / 250000000) := by
  have h := checkLog_sound (w := (3671071953 / 2003671071953)) (n := 12)
    (lo := (73287 / 20000000)) (hi := (3664351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1003671071953 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1003671071953 / 1000000000000) = 1/(500000000000 / 1003671071953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (69681153 / 100000000) (174202883 / 250000000) (Real.log (1003671071953 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1003671071953 / 500000000000) = -Real.log (500000000000 / 1003671071953) := by
    rw [show ((1003671071953 / 500000000000) : ℝ) = ((500000000000 / 1003671071953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (174532949 / 250000000) ≤ -Real.log (500000000000 / 1004997060553) ∧
    -Real.log (500000000000 / 1004997060553) ≤ (349065899 / 500000000) := by
  have h := checkLog_sound (w := (4997060553 / 2004997060553)) (n := 12)
    (lo := (623077 / 125000000)) (hi := (4984617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1004997060553 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1004997060553 / 1000000000000) = 1/(500000000000 / 1004997060553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (174532949 / 250000000) (349065899 / 500000000) (Real.log (1004997060553 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1004997060553 / 500000000000) = -Real.log (500000000000 / 1004997060553) := by
    rw [show ((1004997060553 / 500000000000) : ℝ) = ((500000000000 / 1004997060553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (485337699 / 1000000000) ≤ -Real.log (250000000000 / 406180895949) ∧
    -Real.log (250000000000 / 406180895949) ≤ (4853377 / 10000000) := by
  have h := checkLog_sound (w := (156180895949 / 656180895949)) (n := 12)
    (lo := (485337699 / 1000000000)) (hi := (4853377 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406180895949 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406180895949 / 250000000000) = 1/(250000000000 / 406180895949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (485337699 / 1000000000) (4853377 / 10000000) (Real.log (406180895949 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (406180895949 / 250000000000) = -Real.log (250000000000 / 406180895949) := by
    rw [show ((406180895949 / 250000000000) : ℝ) = ((250000000000 / 406180895949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (486234599 / 1000000000) ≤ -Real.log (500000000000 / 813090726691) ∧
    -Real.log (500000000000 / 813090726691) ≤ (2431173 / 5000000) := by
  have h := checkLog_sound (w := (313090726691 / 1313090726691)) (n := 12)
    (lo := (486234599 / 1000000000)) (hi := (2431173 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813090726691 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813090726691 / 500000000000) = 1/(500000000000 / 813090726691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (486234599 / 1000000000) (2431173 / 5000000) (Real.log (813090726691 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (813090726691 / 500000000000) = -Real.log (500000000000 / 813090726691) := by
    rw [show ((813090726691 / 500000000000) : ℝ) = ((500000000000 / 813090726691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (2698143 / 7812500) ≤ -Real.log (250000000000 / 353125395801) ∧
    -Real.log (250000000000 / 353125395801) ≤ (69072461 / 200000000) := by
  have h := checkLog_sound (w := (103125395801 / 603125395801)) (n := 12)
    (lo := (2698143 / 7812500)) (hi := (69072461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353125395801 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353125395801 / 250000000000) = 1/(250000000000 / 353125395801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2698143 / 7812500) (69072461 / 200000000) (Real.log (353125395801 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (353125395801 / 250000000000) = -Real.log (250000000000 / 353125395801) := by
    rw [show ((353125395801 / 250000000000) : ℝ) = ((250000000000 / 353125395801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (346007193 / 1000000000) ≤ -Real.log (250000000000 / 353353195721) ∧
    -Real.log (250000000000 / 353353195721) ≤ (173003597 / 500000000) := by
  have h := checkLog_sound (w := (103353195721 / 603353195721)) (n := 12)
    (lo := (346007193 / 1000000000)) (hi := (173003597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353353195721 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353353195721 / 250000000000) = 1/(250000000000 / 353353195721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (346007193 / 1000000000) (173003597 / 500000000) (Real.log (353353195721 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (353353195721 / 250000000000) = -Real.log (250000000000 / 353353195721) := by
    rw [show ((353353195721 / 250000000000) : ℝ) = ((250000000000 / 353353195721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (14891061 / 500000000) ≤ -Real.log (242664248799 / 250000000000) ∧
    -Real.log (242664248799 / 250000000000) ≤ (29782123 / 1000000000) := by
  have h := checkLog_sound (w := (7335751201 / 492664248799)) (n := 12)
    (lo := (14891061 / 500000000)) (hi := (29782123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242664248799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242664248799) = 1/(242664248799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29782123 / 1000000000) (-14891061 / 500000000) (Real.log (242664248799 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14835877 / 500000000) ≤ -Real.log (38830565191 / 40000000000) ∧
    -Real.log (38830565191 / 40000000000) ≤ (5934351 / 200000000) := by
  have h := checkLog_sound (w := (1169434809 / 78830565191)) (n := 12)
    (lo := (14835877 / 500000000)) (hi := (5934351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38830565191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38830565191) = 1/(38830565191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5934351 / 200000000) (-14835877 / 500000000) (Real.log (38830565191 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell145

end


