-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell017Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell017Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:36:45.025532+00:00
-- url     : https://prove2.me/theorems/a43c834e-6599-4e4e-83b1-6ab63699e17a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell017Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell018…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell017Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell018Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell019Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell020Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell021Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell022Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell017Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell018Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell019Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell020Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell021Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell022Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell017Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell018Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell019Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell020Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell021Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell022Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell017Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell018Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell019Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell020Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell021Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell022Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell017Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell017
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

theorem reflection_log_1_neg : (115772827 / 500000000) ≤ -Real.log (2560 / 3227) ∧
    -Real.log (2560 / 3227) ≤ (46309131 / 200000000) := by
  have h := checkLog_sound (w := (667 / 5787)) (n := 12)
    (lo := (115772827 / 500000000)) (hi := (46309131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3227 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3227 / 2560) = 1/(2560 / 3227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (115772827 / 500000000) (46309131 / 200000000) (Real.log (3227 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3227 / 2560) = -Real.log (2560 / 3227) := by
    rw [show ((3227 / 2560) : ℝ) = ((2560 / 3227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (150922193 / 500000000) ≤ -Real.log (1893 / 2560) ∧
    -Real.log (1893 / 2560) ≤ (301844387 / 1000000000) := by
  have h := checkLog_sound (w := (667 / 4453)) (n := 12)
    (lo := (150922193 / 500000000)) (hi := (301844387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1893) = 1/(1893 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-301844387 / 1000000000) (-150922193 / 500000000) (Real.log (1893 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (115540359 / 500000000) ≤ -Real.log (5120 / 6451) ∧
    -Real.log (5120 / 6451) ≤ (231080719 / 1000000000) := by
  have h := checkLog_sound (w := (1331 / 11571)) (n := 12)
    (lo := (115540359 / 500000000)) (hi := (231080719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6451 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6451 / 5120) = 1/(5120 / 6451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (115540359 / 500000000) (231080719 / 1000000000) (Real.log (6451 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6451 / 5120) = -Real.log (5120 / 6451) := by
    rw [show ((6451 / 5120) : ℝ) = ((5120 / 6451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (301052307 / 1000000000) ≤ -Real.log (3789 / 5120) ∧
    -Real.log (3789 / 5120) ≤ (75263077 / 250000000) := by
  have h := checkLog_sound (w := (1331 / 8909)) (n := 12)
    (lo := (301052307 / 1000000000)) (hi := (75263077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3789) = 1/(3789 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-75263077 / 250000000) (-301052307 / 1000000000) (Real.log (3789 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (169195789 / 1000000000) ≤ -Real.log (31250 / 37011) ∧
    -Real.log (31250 / 37011) ≤ (16919579 / 100000000) := by
  have h := checkLog_sound (w := (5761 / 68261)) (n := 12)
    (lo := (169195789 / 1000000000)) (hi := (16919579 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37011 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37011 / 31250) = 1/(31250 / 37011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (169195789 / 1000000000) (16919579 / 100000000) (Real.log (37011 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (37011 / 31250) = -Real.log (31250 / 37011) := by
    rw [show ((37011 / 31250) : ℝ) = ((31250 / 37011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (203772389 / 1000000000) ≤ -Real.log (25489 / 31250) ∧
    -Real.log (25489 / 31250) ≤ (20377239 / 100000000) := by
  have h := checkLog_sound (w := (5761 / 56739)) (n := 12)
    (lo := (203772389 / 1000000000)) (hi := (20377239 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25489) = 1/(25489 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-20377239 / 100000000) (-203772389 / 1000000000) (Real.log (25489 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (84774753 / 500000000) ≤ -Real.log (1000000 / 1184771) ∧
    -Real.log (1000000 / 1184771) ≤ (169549507 / 1000000000) := by
  have h := checkLog_sound (w := (184771 / 2184771)) (n := 12)
    (lo := (84774753 / 500000000)) (hi := (169549507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1184771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1184771 / 1000000) = 1/(1000000 / 1184771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (84774753 / 500000000) (169549507 / 1000000000) (Real.log (1184771 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1184771 / 1000000) = -Real.log (1000000 / 1184771) := by
    rw [show ((1184771 / 1000000) : ℝ) = ((1000000 / 1184771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (204286223 / 1000000000) ≤ -Real.log (815229 / 1000000) ∧
    -Real.log (815229 / 1000000) ≤ (12767889 / 62500000) := by
  have h := checkLog_sound (w := (184771 / 1815229)) (n := 12)
    (lo := (204286223 / 1000000000)) (hi := (12767889 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 815229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 815229) = 1/(815229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12767889 / 62500000) (-204286223 / 1000000000) (Real.log (815229 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4945161 / 40000000) ≤ -Real.log (250000 / 282899) ∧
    -Real.log (250000 / 282899) ≤ (61814513 / 500000000) := by
  have h := checkLog_sound (w := (32899 / 532899)) (n := 12)
    (lo := (4945161 / 40000000)) (hi := (61814513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282899 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282899 / 250000) = 1/(250000 / 282899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4945161 / 40000000) (61814513 / 500000000) (Real.log (282899 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (282899 / 250000) = -Real.log (250000 / 282899) := by
    rw [show ((282899 / 250000) : ℝ) = ((250000 / 282899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (70549117 / 500000000) ≤ -Real.log (217101 / 250000) ∧
    -Real.log (217101 / 250000) ≤ (28219647 / 200000000) := by
  have h := checkLog_sound (w := (32899 / 467101)) (n := 12)
    (lo := (70549117 / 500000000)) (hi := (28219647 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217101) = 1/(217101 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28219647 / 200000000) (-70549117 / 500000000) (Real.log (217101 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3097463 / 25000000) ≤ -Real.log (1000000 / 1131901) ∧
    -Real.log (1000000 / 1131901) ≤ (123898521 / 1000000000) := by
  have h := checkLog_sound (w := (131901 / 2131901)) (n := 12)
    (lo := (3097463 / 25000000)) (hi := (123898521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131901 / 1000000) = 1/(1000000 / 1131901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3097463 / 25000000) (123898521 / 1000000000) (Real.log (1131901 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1131901 / 1000000) = -Real.log (1000000 / 1131901) := by
    rw [show ((1131901 / 1000000) : ℝ) = ((1000000 / 1131901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28289903 / 200000000) ≤ -Real.log (868099 / 1000000) ∧
    -Real.log (868099 / 1000000) ≤ (35362379 / 250000000) := by
  have h := checkLog_sound (w := (131901 / 1868099)) (n := 12)
    (lo := (28289903 / 200000000)) (hi := (35362379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868099) = 1/(868099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-35362379 / 250000000) (-28289903 / 200000000) (Real.log (868099 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21285321 / 40000000) ≤ -Real.log (500000000000 / 851280021113) ∧
    -Real.log (500000000000 / 851280021113) ≤ (266066513 / 500000000) := by
  have h := checkLog_sound (w := (351280021113 / 1351280021113)) (n := 12)
    (lo := (21285321 / 40000000)) (hi := (266066513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851280021113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851280021113 / 500000000000) = 1/(500000000000 / 851280021113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21285321 / 40000000) (266066513 / 500000000) (Real.log (851280021113 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (851280021113 / 500000000000) = -Real.log (500000000000 / 851280021113) := by
    rw [show ((851280021113 / 500000000000) : ℝ) = ((500000000000 / 851280021113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (13334751 / 25000000) ≤ -Real.log (25000000000 / 42617538299) ∧
    -Real.log (25000000000 / 42617538299) ≤ (533390041 / 1000000000) := by
  have h := checkLog_sound (w := (17617538299 / 67617538299)) (n := 12)
    (lo := (13334751 / 25000000)) (hi := (533390041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42617538299 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42617538299 / 25000000000) = 1/(25000000000 / 42617538299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (13334751 / 25000000) (533390041 / 1000000000) (Real.log (42617538299 / 25000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (42617538299 / 25000000000) = -Real.log (25000000000 / 42617538299) := by
    rw [show ((42617538299 / 25000000000) : ℝ) = ((25000000000 / 42617538299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (372968179 / 1000000000) ≤ -Real.log (62500000000 / 90752383381) ∧
    -Real.log (62500000000 / 90752383381) ≤ (18648409 / 50000000) := by
  have h := checkLog_sound (w := (28252383381 / 153252383381)) (n := 12)
    (lo := (372968179 / 1000000000)) (hi := (18648409 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90752383381 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90752383381 / 62500000000) = 1/(62500000000 / 90752383381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (372968179 / 1000000000) (18648409 / 50000000) (Real.log (90752383381 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (90752383381 / 62500000000) = -Real.log (62500000000 / 90752383381) := by
    rw [show ((90752383381 / 62500000000) : ℝ) = ((62500000000 / 90752383381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (37383573 / 100000000) ≤ -Real.log (500000000000 / 726649199183) ∧
    -Real.log (500000000000 / 726649199183) ≤ (373835731 / 1000000000) := by
  have h := checkLog_sound (w := (226649199183 / 1226649199183)) (n := 12)
    (lo := (37383573 / 100000000)) (hi := (373835731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726649199183 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726649199183 / 500000000000) = 1/(500000000000 / 726649199183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (37383573 / 100000000) (373835731 / 1000000000) (Real.log (726649199183 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (726649199183 / 500000000000) = -Real.log (500000000000 / 726649199183) := by
    rw [show ((726649199183 / 500000000000) : ℝ) = ((500000000000 / 726649199183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (13236363 / 50000000) ≤ -Real.log (500000000000 / 651537763529) ∧
    -Real.log (500000000000 / 651537763529) ≤ (264727261 / 1000000000) := by
  have h := checkLog_sound (w := (151537763529 / 1151537763529)) (n := 12)
    (lo := (13236363 / 50000000)) (hi := (264727261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651537763529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651537763529 / 500000000000) = 1/(500000000000 / 651537763529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (13236363 / 50000000) (264727261 / 1000000000) (Real.log (651537763529 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (651537763529 / 500000000000) = -Real.log (500000000000 / 651537763529) := by
    rw [show ((651537763529 / 500000000000) : ℝ) = ((500000000000 / 651537763529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (53069607 / 200000000) ≤ -Real.log (50000000000 / 65194234759) ∧
    -Real.log (50000000000 / 65194234759) ≤ (66337009 / 250000000) := by
  have h := checkLog_sound (w := (15194234759 / 115194234759)) (n := 12)
    (lo := (53069607 / 200000000)) (hi := (66337009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65194234759 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65194234759 / 50000000000) = 1/(50000000000 / 65194234759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (53069607 / 200000000) (66337009 / 250000000) (Real.log (65194234759 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (65194234759 / 50000000000) = -Real.log (50000000000 / 65194234759) := by
    rw [show ((65194234759 / 50000000000) : ℝ) = ((50000000000 / 65194234759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3510199 / 200000000) ≤ -Real.log (982602126199 / 1000000000000) ∧
    -Real.log (982602126199 / 1000000000000) ≤ (4387749 / 250000000) := by
  have h := checkLog_sound (w := (17397873801 / 1982602126199)) (n := 12)
    (lo := (3510199 / 200000000)) (hi := (4387749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982602126199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982602126199) = 1/(982602126199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4387749 / 250000000) (-3510199 / 200000000) (Real.log (982602126199 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17469209 / 1000000000) ≤ -Real.log (61417655799 / 62500000000) ∧
    -Real.log (61417655799 / 62500000000) ≤ (1746921 / 100000000) := by
  have h := checkLog_sound (w := (1082344201 / 123917655799)) (n := 12)
    (lo := (17469209 / 1000000000)) (hi := (1746921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61417655799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61417655799) = 1/(61417655799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1746921 / 100000000) (-17469209 / 1000000000) (Real.log (61417655799 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell017

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell018Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell018
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

theorem reflection_log_1_neg : (116005187 / 500000000) ≤ -Real.log (5120 / 6457) ∧
    -Real.log (5120 / 6457) ≤ (1856083 / 8000000) := by
  have h := checkLog_sound (w := (1337 / 11577)) (n := 12)
    (lo := (116005187 / 500000000)) (hi := (1856083 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6457 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6457 / 5120) = 1/(5120 / 6457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (116005187 / 500000000) (1856083 / 8000000) (Real.log (6457 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6457 / 5120) = -Real.log (5120 / 6457) := by
    rw [show ((6457 / 5120) : ℝ) = ((5120 / 6457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (302637093 / 1000000000) ≤ -Real.log (3783 / 5120) ∧
    -Real.log (3783 / 5120) ≤ (151318547 / 500000000) := by
  have h := checkLog_sound (w := (1337 / 8903)) (n := 12)
    (lo := (302637093 / 1000000000)) (hi := (151318547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3783) = 1/(3783 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-151318547 / 500000000) (-302637093 / 1000000000) (Real.log (3783 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (115772827 / 500000000) ≤ -Real.log (2560 / 3227) ∧
    -Real.log (2560 / 3227) ≤ (46309131 / 200000000) := by
  have h := checkLog_sound (w := (667 / 5787)) (n := 12)
    (lo := (115772827 / 500000000)) (hi := (46309131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3227 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3227 / 2560) = 1/(2560 / 3227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (115772827 / 500000000) (46309131 / 200000000) (Real.log (3227 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3227 / 2560) = -Real.log (2560 / 3227) := by
    rw [show ((3227 / 2560) : ℝ) = ((2560 / 3227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (150922193 / 500000000) ≤ -Real.log (1893 / 2560) ∧
    -Real.log (1893 / 2560) ≤ (301844387 / 1000000000) := by
  have h := checkLog_sound (w := (667 / 4453)) (n := 12)
    (lo := (150922193 / 500000000)) (hi := (301844387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1893) = 1/(1893 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-301844387 / 1000000000) (-150922193 / 500000000) (Real.log (1893 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (84774331 / 500000000) ≤ -Real.log (100000 / 118477) ∧
    -Real.log (100000 / 118477) ≤ (169548663 / 1000000000) := by
  have h := checkLog_sound (w := (18477 / 218477)) (n := 12)
    (lo := (84774331 / 500000000)) (hi := (169548663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118477 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118477 / 100000) = 1/(100000 / 118477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (84774331 / 500000000) (169548663 / 1000000000) (Real.log (118477 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (118477 / 100000) = -Real.log (100000 / 118477) := by
    rw [show ((118477 / 100000) : ℝ) = ((100000 / 118477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (51071249 / 250000000) ≤ -Real.log (81523 / 100000) ∧
    -Real.log (81523 / 100000) ≤ (204284997 / 1000000000) := by
  have h := checkLog_sound (w := (18477 / 181523)) (n := 12)
    (lo := (51071249 / 250000000)) (hi := (204284997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81523) = 1/(81523 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-204284997 / 1000000000) (-51071249 / 250000000) (Real.log (81523 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (33980451 / 200000000) ≤ -Real.log (1000000 / 1185189) ∧
    -Real.log (1000000 / 1185189) ≤ (10618891 / 62500000) := by
  have h := checkLog_sound (w := (185189 / 2185189)) (n := 12)
    (lo := (33980451 / 200000000)) (hi := (10618891 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1185189 / 1000000) = 1/(1000000 / 1185189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (33980451 / 200000000) (10618891 / 62500000) (Real.log (1185189 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1185189 / 1000000) = -Real.log (1000000 / 1185189) := by
    rw [show ((1185189 / 1000000) : ℝ) = ((1000000 / 1185189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (102399547 / 500000000) ≤ -Real.log (814811 / 1000000) ∧
    -Real.log (814811 / 1000000) ≤ (40959819 / 200000000) := by
  have h := checkLog_sound (w := (185189 / 1814811)) (n := 12)
    (lo := (102399547 / 500000000)) (hi := (40959819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 814811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 814811) = 1/(814811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-40959819 / 200000000) (-102399547 / 500000000) (Real.log (814811 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (30974409 / 250000000) ≤ -Real.log (10000 / 11319) ∧
    -Real.log (10000 / 11319) ≤ (123897637 / 1000000000) := by
  have h := checkLog_sound (w := (1319 / 21319)) (n := 12)
    (lo := (30974409 / 250000000)) (hi := (123897637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11319 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11319 / 10000) = 1/(10000 / 11319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (30974409 / 250000000) (123897637 / 1000000000) (Real.log (11319 / 10000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (11319 / 10000) = -Real.log (10000 / 11319) := by
    rw [show ((11319 / 10000) : ℝ) = ((10000 / 11319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (141448363 / 1000000000) ≤ -Real.log (8681 / 10000) ∧
    -Real.log (8681 / 10000) ≤ (35362091 / 250000000) := by
  have h := checkLog_sound (w := (1319 / 18681)) (n := 12)
    (lo := (141448363 / 1000000000)) (hi := (35362091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8681) = 1/(8681 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-35362091 / 250000000) (-141448363 / 1000000000) (Real.log (8681 / 10000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (62083529 / 500000000) ≤ -Real.log (200000 / 226441) ∧
    -Real.log (200000 / 226441) ≤ (124167059 / 1000000000) := by
  have h := checkLog_sound (w := (26441 / 426441)) (n := 12)
    (lo := (62083529 / 500000000)) (hi := (124167059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226441 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226441 / 200000) = 1/(200000 / 226441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (62083529 / 500000000) (124167059 / 1000000000) (Real.log (226441 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (226441 / 200000) = -Real.log (200000 / 226441) := by
    rw [show ((226441 / 200000) : ℝ) = ((200000 / 226441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (141799767 / 1000000000) ≤ -Real.log (173559 / 200000) ∧
    -Real.log (173559 / 200000) ≤ (17724971 / 125000000) := by
  have h := checkLog_sound (w := (26441 / 373559)) (n := 12)
    (lo := (141799767 / 1000000000)) (hi := (17724971 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173559) = 1/(173559 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-17724971 / 125000000) (-141799767 / 1000000000) (Real.log (173559 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13334751 / 25000000) ≤ -Real.log (500000000000 / 852350765979) ∧
    -Real.log (500000000000 / 852350765979) ≤ (533390041 / 1000000000) := by
  have h := checkLog_sound (w := (352350765979 / 1352350765979)) (n := 12)
    (lo := (13334751 / 25000000)) (hi := (533390041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((852350765979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(852350765979 / 500000000000) = 1/(500000000000 / 852350765979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13334751 / 25000000) (533390041 / 1000000000) (Real.log (852350765979 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (852350765979 / 500000000000) = -Real.log (500000000000 / 852350765979) := by
    rw [show ((852350765979 / 500000000000) : ℝ) = ((500000000000 / 852350765979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (534647467 / 1000000000) ≤ -Real.log (250000000000 / 426711604547) ∧
    -Real.log (250000000000 / 426711604547) ≤ (133661867 / 250000000) := by
  have h := checkLog_sound (w := (176711604547 / 676711604547)) (n := 12)
    (lo := (534647467 / 1000000000)) (hi := (133661867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((426711604547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(426711604547 / 250000000000) = 1/(250000000000 / 426711604547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (534647467 / 1000000000) (133661867 / 250000000) (Real.log (426711604547 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (426711604547 / 250000000000) = -Real.log (250000000000 / 426711604547) := by
    rw [show ((426711604547 / 250000000000) : ℝ) = ((250000000000 / 426711604547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (373833659 / 1000000000) ≤ -Real.log (100000000000 / 145329538903) ∧
    -Real.log (100000000000 / 145329538903) ≤ (18691683 / 50000000) := by
  have h := checkLog_sound (w := (45329538903 / 245329538903)) (n := 12)
    (lo := (373833659 / 1000000000)) (hi := (18691683 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145329538903 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145329538903 / 100000000000) = 1/(100000000000 / 145329538903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (373833659 / 1000000000) (18691683 / 50000000) (Real.log (145329538903 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (145329538903 / 100000000000) = -Real.log (100000000000 / 145329538903) := by
    rw [show ((145329538903 / 100000000000) : ℝ) = ((100000000000 / 145329538903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (7494027 / 20000000) ≤ -Real.log (31250000000 / 45454904573) ∧
    -Real.log (31250000000 / 45454904573) ≤ (374701351 / 1000000000) := by
  have h := checkLog_sound (w := (14204904573 / 76704904573)) (n := 12)
    (lo := (7494027 / 20000000)) (hi := (374701351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45454904573 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45454904573 / 31250000000) = 1/(31250000000 / 45454904573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (7494027 / 20000000) (374701351 / 1000000000) (Real.log (45454904573 / 31250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (45454904573 / 31250000000) = -Real.log (31250000000 / 45454904573) := by
    rw [show ((45454904573 / 31250000000) : ℝ) = ((31250000000 / 45454904573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (132673 / 500000) ≤ -Real.log (500000000000 / 651941020619) ∧
    -Real.log (500000000000 / 651941020619) ≤ (265346001 / 1000000000) := by
  have h := checkLog_sound (w := (151941020619 / 1151941020619)) (n := 12)
    (lo := (132673 / 500000)) (hi := (265346001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651941020619 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651941020619 / 500000000000) = 1/(500000000000 / 651941020619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (132673 / 500000) (265346001 / 1000000000) (Real.log (651941020619 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (651941020619 / 500000000000) = -Real.log (500000000000 / 651941020619) := by
    rw [show ((651941020619 / 500000000000) : ℝ) = ((500000000000 / 651941020619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (132983413 / 500000000) ≤ -Real.log (250000000000 / 326172944071) ∧
    -Real.log (250000000000 / 326172944071) ≤ (265966827 / 1000000000) := by
  have h := checkLog_sound (w := (76172944071 / 576172944071)) (n := 12)
    (lo := (132983413 / 500000000)) (hi := (265966827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326172944071 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326172944071 / 250000000000) = 1/(250000000000 / 326172944071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (132983413 / 500000000) (265966827 / 1000000000) (Real.log (326172944071 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (326172944071 / 250000000000) = -Real.log (250000000000 / 326172944071) := by
    rw [show ((326172944071 / 250000000000) : ℝ) = ((250000000000 / 326172944071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4408177 / 250000000) ≤ -Real.log (39300873519 / 40000000000) ∧
    -Real.log (39300873519 / 40000000000) ≤ (17632709 / 1000000000) := by
  have h := checkLog_sound (w := (699126481 / 79300873519)) (n := 12)
    (lo := (4408177 / 250000000)) (hi := (17632709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39300873519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39300873519) = 1/(39300873519 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17632709 / 1000000000) (-4408177 / 250000000) (Real.log (39300873519 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8775363 / 500000000) ≤ -Real.log (98260239 / 100000000) ∧
    -Real.log (98260239 / 100000000) ≤ (17550727 / 1000000000) := by
  have h := checkLog_sound (w := (1739761 / 198260239)) (n := 12)
    (lo := (8775363 / 500000000)) (hi := (17550727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 98260239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 98260239) = 1/(98260239 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-17550727 / 1000000000) (-8775363 / 500000000) (Real.log (98260239 / 100000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell018

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell019Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell019
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

theorem reflection_log_1_neg : (116237439 / 500000000) ≤ -Real.log (256 / 323) ∧
    -Real.log (256 / 323) ≤ (232474879 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 579)) (n := 12)
    (lo := (116237439 / 500000000)) (hi := (232474879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323 / 256) = 1/(256 / 323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (116237439 / 500000000) (232474879 / 1000000000) (Real.log (323 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (323 / 256) = -Real.log (256 / 323) := by
    rw [show ((323 / 256) : ℝ) = ((256 / 323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (303430429 / 1000000000) ≤ -Real.log (189 / 256) ∧
    -Real.log (189 / 256) ≤ (30343043 / 100000000) := by
  have h := checkLog_sound (w := (67 / 445)) (n := 12)
    (lo := (303430429 / 1000000000)) (hi := (30343043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 189) = 1/(189 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-30343043 / 100000000) (-303430429 / 1000000000) (Real.log (189 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (116005187 / 500000000) ≤ -Real.log (5120 / 6457) ∧
    -Real.log (5120 / 6457) ≤ (1856083 / 8000000) := by
  have h := checkLog_sound (w := (1337 / 11577)) (n := 12)
    (lo := (116005187 / 500000000)) (hi := (1856083 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6457 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6457 / 5120) = 1/(5120 / 6457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (116005187 / 500000000) (1856083 / 8000000) (Real.log (6457 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6457 / 5120) = -Real.log (5120 / 6457) := by
    rw [show ((6457 / 5120) : ℝ) = ((5120 / 6457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (302637093 / 1000000000) ≤ -Real.log (3783 / 5120) ∧
    -Real.log (3783 / 5120) ≤ (151318547 / 500000000) := by
  have h := checkLog_sound (w := (1337 / 8903)) (n := 12)
    (lo := (302637093 / 1000000000)) (hi := (151318547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3783) = 1/(3783 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-151318547 / 500000000) (-302637093 / 1000000000) (Real.log (3783 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (169901411 / 1000000000) ≤ -Real.log (250000 / 296297) ∧
    -Real.log (250000 / 296297) ≤ (42475353 / 250000000) := by
  have h := checkLog_sound (w := (46297 / 546297)) (n := 12)
    (lo := (169901411 / 1000000000)) (hi := (42475353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296297 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296297 / 250000) = 1/(250000 / 296297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (169901411 / 1000000000) (42475353 / 250000000) (Real.log (296297 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (296297 / 250000) = -Real.log (250000 / 296297) := by
    rw [show ((296297 / 250000) : ℝ) = ((250000 / 296297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (204797867 / 1000000000) ≤ -Real.log (203703 / 250000) ∧
    -Real.log (203703 / 250000) ≤ (51199467 / 250000000) := by
  have h := checkLog_sound (w := (46297 / 453703)) (n := 12)
    (lo := (204797867 / 1000000000)) (hi := (51199467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203703) = 1/(203703 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-51199467 / 250000000) (-204797867 / 1000000000) (Real.log (203703 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (170254879 / 1000000000) ≤ -Real.log (1000000 / 1185607) ∧
    -Real.log (1000000 / 1185607) ≤ (1064093 / 6250000) := by
  have h := checkLog_sound (w := (185607 / 2185607)) (n := 12)
    (lo := (170254879 / 1000000000)) (hi := (1064093 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1185607 / 1000000) = 1/(1000000 / 1185607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (170254879 / 1000000000) (1064093 / 6250000) (Real.log (1185607 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1185607 / 1000000) = -Real.log (1000000 / 1185607) := by
    rw [show ((1185607 / 1000000) : ℝ) = ((1000000 / 1185607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (51328057 / 250000000) ≤ -Real.log (814393 / 1000000) ∧
    -Real.log (814393 / 1000000) ≤ (205312229 / 1000000000) := by
  have h := checkLog_sound (w := (185607 / 1814393)) (n := 12)
    (lo := (51328057 / 250000000)) (hi := (205312229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 814393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 814393) = 1/(814393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-205312229 / 1000000000) (-51328057 / 250000000) (Real.log (814393 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4966647 / 40000000) ≤ -Real.log (250000 / 283051) ∧
    -Real.log (250000 / 283051) ≤ (3880193 / 31250000) := by
  have h := checkLog_sound (w := (33051 / 533051)) (n := 12)
    (lo := (4966647 / 40000000)) (hi := (3880193 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283051 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(283051 / 250000) = 1/(250000 / 283051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4966647 / 40000000) (3880193 / 31250000) (Real.log (283051 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (283051 / 250000) = -Real.log (250000 / 283051) := by
    rw [show ((283051 / 250000) : ℝ) = ((250000 / 283051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (70899307 / 500000000) ≤ -Real.log (216949 / 250000) ∧
    -Real.log (216949 / 250000) ≤ (28359723 / 200000000) := by
  have h := checkLog_sound (w := (33051 / 466949)) (n := 12)
    (lo := (70899307 / 500000000)) (hi := (28359723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 216949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 216949) = 1/(216949 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28359723 / 200000000) (-70899307 / 500000000) (Real.log (216949 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15554551 / 125000000) ≤ -Real.log (100000 / 113251) ∧
    -Real.log (100000 / 113251) ≤ (124436409 / 1000000000) := by
  have h := checkLog_sound (w := (13251 / 213251)) (n := 12)
    (lo := (15554551 / 125000000)) (hi := (124436409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113251 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113251 / 100000) = 1/(100000 / 113251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15554551 / 125000000) (124436409 / 1000000000) (Real.log (113251 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (113251 / 100000) = -Real.log (100000 / 113251) := by
    rw [show ((113251 / 100000) : ℝ) = ((100000 / 113251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (71075647 / 500000000) ≤ -Real.log (86749 / 100000) ∧
    -Real.log (86749 / 100000) ≤ (28430259 / 200000000) := by
  have h := checkLog_sound (w := (13251 / 186749)) (n := 12)
    (lo := (71075647 / 500000000)) (hi := (28430259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 86749) = 1/(86749 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-28430259 / 200000000) (-71075647 / 500000000) (Real.log (86749 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (534647467 / 1000000000) ≤ -Real.log (500000000000 / 853423209093) ∧
    -Real.log (500000000000 / 853423209093) ≤ (133661867 / 250000000) := by
  have h := checkLog_sound (w := (353423209093 / 1353423209093)) (n := 12)
    (lo := (534647467 / 1000000000)) (hi := (133661867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853423209093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853423209093 / 500000000000) = 1/(500000000000 / 853423209093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (534647467 / 1000000000) (133661867 / 250000000) (Real.log (853423209093 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (853423209093 / 500000000000) = -Real.log (500000000000 / 853423209093) := by
    rw [show ((853423209093 / 500000000000) : ℝ) = ((500000000000 / 853423209093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (133976327 / 250000000) ≤ -Real.log (250000000000 / 427248677249) ∧
    -Real.log (250000000000 / 427248677249) ≤ (535905309 / 1000000000) := by
  have h := checkLog_sound (w := (177248677249 / 677248677249)) (n := 12)
    (lo := (133976327 / 250000000)) (hi := (535905309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427248677249 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427248677249 / 250000000000) = 1/(250000000000 / 427248677249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (133976327 / 250000000) (535905309 / 1000000000) (Real.log (427248677249 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (427248677249 / 250000000000) = -Real.log (250000000000 / 427248677249) := by
    rw [show ((427248677249 / 250000000000) : ℝ) = ((250000000000 / 427248677249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (187349639 / 500000000) ≤ -Real.log (125000000000 / 181819241739) ∧
    -Real.log (125000000000 / 181819241739) ≤ (374699279 / 1000000000) := by
  have h := checkLog_sound (w := (56819241739 / 306819241739)) (n := 12)
    (lo := (187349639 / 500000000)) (hi := (374699279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181819241739 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181819241739 / 125000000000) = 1/(125000000000 / 181819241739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (187349639 / 500000000) (374699279 / 1000000000) (Real.log (181819241739 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (181819241739 / 125000000000) = -Real.log (125000000000 / 181819241739) := by
    rw [show ((181819241739 / 125000000000) : ℝ) = ((125000000000 / 181819241739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (93891777 / 250000000) ≤ -Real.log (500000000000 / 727908393123) ∧
    -Real.log (500000000000 / 727908393123) ≤ (375567109 / 1000000000) := by
  have h := checkLog_sound (w := (227908393123 / 1227908393123)) (n := 12)
    (lo := (93891777 / 250000000)) (hi := (375567109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727908393123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727908393123 / 500000000000) = 1/(500000000000 / 727908393123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (93891777 / 250000000) (375567109 / 1000000000) (Real.log (727908393123 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (727908393123 / 500000000000) = -Real.log (500000000000 / 727908393123) := by
    rw [show ((727908393123 / 500000000000) : ℝ) = ((500000000000 / 727908393123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (26596479 / 100000000) ≤ -Real.log (250000000000 / 326172280121) ∧
    -Real.log (250000000000 / 326172280121) ≤ (265964791 / 1000000000) := by
  have h := checkLog_sound (w := (76172280121 / 576172280121)) (n := 12)
    (lo := (26596479 / 100000000)) (hi := (265964791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326172280121 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326172280121 / 250000000000) = 1/(250000000000 / 326172280121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (26596479 / 100000000) (265964791 / 1000000000) (Real.log (326172280121 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (326172280121 / 250000000000) = -Real.log (250000000000 / 326172280121) := by
    rw [show ((326172280121 / 250000000000) : ℝ) = ((250000000000 / 326172280121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (133293851 / 500000000) ≤ -Real.log (250000000000 / 326375520179) ∧
    -Real.log (250000000000 / 326375520179) ≤ (266587703 / 1000000000) := by
  have h := checkLog_sound (w := (76375520179 / 576375520179)) (n := 12)
    (lo := (133293851 / 500000000)) (hi := (266587703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326375520179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326375520179 / 250000000000) = 1/(250000000000 / 326375520179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (133293851 / 500000000) (266587703 / 1000000000) (Real.log (326375520179 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (326375520179 / 250000000000) = -Real.log (250000000000 / 326375520179) := by
    rw [show ((326375520179 / 250000000000) : ℝ) = ((250000000000 / 326375520179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8857443 / 500000000) ≤ -Real.log (9824410999 / 10000000000) ∧
    -Real.log (9824410999 / 10000000000) ≤ (17714887 / 1000000000) := by
  have h := checkLog_sound (w := (175589001 / 19824410999)) (n := 12)
    (lo := (8857443 / 500000000)) (hi := (17714887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9824410999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9824410999) = 1/(9824410999 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17714887 / 1000000000) (-8857443 / 500000000) (Real.log (9824410999 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17632439 / 1000000000) ≤ -Real.log (61407631399 / 62500000000) ∧
    -Real.log (61407631399 / 62500000000) ≤ (440811 / 25000000) := by
  have h := checkLog_sound (w := (1092368601 / 123907631399)) (n := 12)
    (lo := (17632439 / 1000000000)) (hi := (440811 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61407631399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61407631399) = 1/(61407631399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-440811 / 25000000) (-17632439 / 1000000000) (Real.log (61407631399 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell019

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell020Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell020
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

theorem reflection_log_1_neg : (232939167 / 1000000000) ≤ -Real.log (5120 / 6463) ∧
    -Real.log (5120 / 6463) ≤ (7279349 / 31250000) := by
  have h := checkLog_sound (w := (1343 / 11583)) (n := 12)
    (lo := (232939167 / 1000000000)) (hi := (7279349 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6463 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6463 / 5120) = 1/(5120 / 6463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (232939167 / 1000000000) (7279349 / 31250000) (Real.log (6463 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6463 / 5120) = -Real.log (5120 / 6463) := by
    rw [show ((6463 / 5120) : ℝ) = ((5120 / 6463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (60844879 / 200000000) ≤ -Real.log (3777 / 5120) ∧
    -Real.log (3777 / 5120) ≤ (76056099 / 250000000) := by
  have h := checkLog_sound (w := (1343 / 8897)) (n := 12)
    (lo := (60844879 / 200000000)) (hi := (76056099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3777) = 1/(3777 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-76056099 / 250000000) (-60844879 / 200000000) (Real.log (3777 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (116237439 / 500000000) ≤ -Real.log (256 / 323) ∧
    -Real.log (256 / 323) ≤ (232474879 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 579)) (n := 12)
    (lo := (116237439 / 500000000)) (hi := (232474879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323 / 256) = 1/(256 / 323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (116237439 / 500000000) (232474879 / 1000000000) (Real.log (323 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (323 / 256) = -Real.log (256 / 323) := by
    rw [show ((323 / 256) : ℝ) = ((256 / 323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (303430429 / 1000000000) ≤ -Real.log (189 / 256) ∧
    -Real.log (189 / 256) ≤ (30343043 / 100000000) := by
  have h := checkLog_sound (w := (67 / 445)) (n := 12)
    (lo := (303430429 / 1000000000)) (hi := (30343043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 189) = 1/(189 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-30343043 / 100000000) (-303430429 / 1000000000) (Real.log (189 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42563509 / 250000000) ≤ -Real.log (500000 / 592803) ∧
    -Real.log (500000 / 592803) ≤ (170254037 / 1000000000) := by
  have h := checkLog_sound (w := (92803 / 1092803)) (n := 12)
    (lo := (42563509 / 250000000)) (hi := (170254037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592803 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592803 / 500000) = 1/(500000 / 592803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42563509 / 250000000) (170254037 / 1000000000) (Real.log (592803 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (592803 / 500000) = -Real.log (500000 / 592803) := by
    rw [show ((592803 / 500000) : ℝ) = ((500000 / 592803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (205311 / 1000000) ≤ -Real.log (407197 / 500000) ∧
    -Real.log (407197 / 500000) ≤ (205311001 / 1000000000) := by
  have h := checkLog_sound (w := (92803 / 907197)) (n := 12)
    (lo := (205311 / 1000000)) (hi := (205311001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 407197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 407197) = 1/(407197 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-205311001 / 1000000000) (-205311 / 1000000) (Real.log (407197 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (170607379 / 1000000000) ≤ -Real.log (40000 / 47441) ∧
    -Real.log (40000 / 47441) ≤ (8530369 / 50000000) := by
  have h := checkLog_sound (w := (7441 / 87441)) (n := 12)
    (lo := (170607379 / 1000000000)) (hi := (8530369 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47441 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47441 / 40000) = 1/(40000 / 47441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (170607379 / 1000000000) (8530369 / 50000000) (Real.log (47441 / 40000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (47441 / 40000) = -Real.log (40000 / 47441) := by
    rw [show ((47441 / 40000) : ℝ) = ((40000 / 47441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (329321 / 1600000) ≤ -Real.log (32559 / 40000) ∧
    -Real.log (32559 / 40000) ≤ (102912813 / 500000000) := by
  have h := checkLog_sound (w := (7441 / 72559)) (n := 12)
    (lo := (329321 / 1600000)) (hi := (102912813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32559) = 1/(32559 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-102912813 / 500000000) (-329321 / 1600000) (Real.log (32559 / 40000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4977421 / 40000000) ≤ -Real.log (1000000 / 1132509) ∧
    -Real.log (1000000 / 1132509) ≤ (62217763 / 500000000) := by
  have h := checkLog_sound (w := (132509 / 2132509)) (n := 12)
    (lo := (4977421 / 40000000)) (hi := (62217763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1132509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1132509 / 1000000) = 1/(1000000 / 1132509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4977421 / 40000000) (62217763 / 500000000) (Real.log (1132509 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1132509 / 1000000) = -Real.log (1000000 / 1132509) := by
    rw [show ((1132509 / 1000000) : ℝ) = ((1000000 / 1132509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (142150141 / 1000000000) ≤ -Real.log (867491 / 1000000) ∧
    -Real.log (867491 / 1000000) ≤ (71075071 / 500000000) := by
  have h := checkLog_sound (w := (132509 / 1867491)) (n := 12)
    (lo := (142150141 / 1000000000)) (hi := (71075071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 867491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 867491) = 1/(867491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-71075071 / 500000000) (-142150141 / 1000000000) (Real.log (867491 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (62352401 / 500000000) ≤ -Real.log (500000 / 566407) ∧
    -Real.log (500000 / 566407) ≤ (124704803 / 1000000000) := by
  have h := checkLog_sound (w := (66407 / 1066407)) (n := 12)
    (lo := (62352401 / 500000000)) (hi := (124704803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566407 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566407 / 500000) = 1/(500000 / 566407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (62352401 / 500000000) (124704803 / 1000000000) (Real.log (566407 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (566407 / 500000) = -Real.log (500000 / 566407) := by
    rw [show ((566407 / 500000) : ℝ) = ((500000 / 566407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4453181 / 31250000) ≤ -Real.log (433593 / 500000) ∧
    -Real.log (433593 / 500000) ≤ (142501793 / 1000000000) := by
  have h := checkLog_sound (w := (66407 / 933593)) (n := 12)
    (lo := (4453181 / 31250000)) (hi := (142501793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433593) = 1/(433593 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-142501793 / 1000000000) (-4453181 / 31250000) (Real.log (433593 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (133976327 / 250000000) ≤ -Real.log (500000000000 / 854497354497) ∧
    -Real.log (500000000000 / 854497354497) ≤ (535905309 / 1000000000) := by
  have h := checkLog_sound (w := (354497354497 / 1354497354497)) (n := 12)
    (lo := (133976327 / 250000000)) (hi := (535905309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854497354497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(854497354497 / 500000000000) = 1/(500000000000 / 854497354497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (133976327 / 250000000) (535905309 / 1000000000) (Real.log (854497354497 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (854497354497 / 500000000000) = -Real.log (500000000000 / 854497354497) := by
    rw [show ((854497354497 / 500000000000) : ℝ) = ((500000000000 / 854497354497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (268581781 / 500000000) ≤ -Real.log (500000000000 / 855573206249) ∧
    -Real.log (500000000000 / 855573206249) ≤ (537163563 / 1000000000) := by
  have h := checkLog_sound (w := (355573206249 / 1355573206249)) (n := 12)
    (lo := (268581781 / 500000000)) (hi := (537163563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855573206249 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855573206249 / 500000000000) = 1/(500000000000 / 855573206249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (268581781 / 500000000) (537163563 / 1000000000) (Real.log (855573206249 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (855573206249 / 500000000000) = -Real.log (500000000000 / 855573206249) := by
    rw [show ((855573206249 / 500000000000) : ℝ) = ((500000000000 / 855573206249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (93891259 / 250000000) ≤ -Real.log (100000000000 / 145581377073) ∧
    -Real.log (100000000000 / 145581377073) ≤ (375565037 / 1000000000) := by
  have h := checkLog_sound (w := (45581377073 / 245581377073)) (n := 12)
    (lo := (93891259 / 250000000)) (hi := (375565037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145581377073 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145581377073 / 100000000000) = 1/(100000000000 / 145581377073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (93891259 / 250000000) (375565037 / 1000000000) (Real.log (145581377073 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (145581377073 / 100000000000) = -Real.log (100000000000 / 145581377073) := by
    rw [show ((145581377073 / 100000000000) : ℝ) = ((100000000000 / 145581377073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (75286601 / 200000000) ≤ -Real.log (250000000000 / 364269480021) ∧
    -Real.log (250000000000 / 364269480021) ≤ (188216503 / 500000000) := by
  have h := checkLog_sound (w := (114269480021 / 614269480021)) (n := 12)
    (lo := (75286601 / 200000000)) (hi := (188216503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364269480021 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364269480021 / 250000000000) = 1/(250000000000 / 364269480021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (75286601 / 200000000) (188216503 / 500000000) (Real.log (364269480021 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (364269480021 / 250000000000) = -Real.log (250000000000 / 364269480021) := by
    rw [show ((364269480021 / 250000000000) : ℝ) = ((250000000000 / 364269480021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (266585667 / 1000000000) ≤ -Real.log (125000000000 / 163187427881) ∧
    -Real.log (125000000000 / 163187427881) ≤ (66646417 / 250000000) := by
  have h := checkLog_sound (w := (38187427881 / 288187427881)) (n := 12)
    (lo := (266585667 / 1000000000)) (hi := (66646417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163187427881 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163187427881 / 125000000000) = 1/(125000000000 / 163187427881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (266585667 / 1000000000) (66646417 / 250000000) (Real.log (163187427881 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (163187427881 / 125000000000) = -Real.log (125000000000 / 163187427881) := by
    rw [show ((163187427881 / 125000000000) : ℝ) = ((125000000000 / 163187427881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (133603297 / 500000000) ≤ -Real.log (2500000000 / 3265775739) ∧
    -Real.log (2500000000 / 3265775739) ≤ (53441319 / 200000000) := by
  have h := checkLog_sound (w := (765775739 / 5765775739)) (n := 12)
    (lo := (133603297 / 500000000)) (hi := (53441319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3265775739 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3265775739 / 2500000000) = 1/(2500000000 / 3265775739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (133603297 / 500000000) (53441319 / 200000000) (Real.log (3265775739 / 2500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3265775739 / 2500000000) = -Real.log (2500000000 / 3265775739) := by
    rw [show ((3265775739 / 2500000000) : ℝ) = ((2500000000 / 3265775739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17796989 / 1000000000) ≤ -Real.log (245590110351 / 250000000000) ∧
    -Real.log (245590110351 / 250000000000) ≤ (1779699 / 100000000) := by
  have h := checkLog_sound (w := (4409889649 / 495590110351)) (n := 12)
    (lo := (17796989 / 1000000000)) (hi := (1779699 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245590110351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245590110351) = 1/(245590110351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1779699 / 100000000) (-17796989 / 1000000000) (Real.log (245590110351 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2214327 / 125000000) ≤ -Real.log (982441364919 / 1000000000000) ∧
    -Real.log (982441364919 / 1000000000000) ≤ (17714617 / 1000000000) := by
  have h := checkLog_sound (w := (17558635081 / 1982441364919)) (n := 12)
    (lo := (2214327 / 125000000)) (hi := (17714617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982441364919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982441364919) = 1/(982441364919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-17714617 / 1000000000) (-2214327 / 125000000) (Real.log (982441364919 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell020

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell021Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell021
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

theorem reflection_log_1_neg : (5835081 / 25000000) ≤ -Real.log (2560 / 3233) ∧
    -Real.log (2560 / 3233) ≤ (233403241 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 5793)) (n := 12)
    (lo := (5835081 / 25000000)) (hi := (233403241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3233 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3233 / 2560) = 1/(2560 / 3233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5835081 / 25000000) (233403241 / 1000000000) (Real.log (3233 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3233 / 2560) = -Real.log (2560 / 3233) := by
    rw [show ((3233 / 2560) : ℝ) = ((2560 / 3233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19063687 / 62500000) ≤ -Real.log (1887 / 2560) ∧
    -Real.log (1887 / 2560) ≤ (305018993 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 4447)) (n := 12)
    (lo := (19063687 / 62500000)) (hi := (305018993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1887) = 1/(1887 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-305018993 / 1000000000) (-19063687 / 62500000) (Real.log (1887 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (232939167 / 1000000000) ≤ -Real.log (5120 / 6463) ∧
    -Real.log (5120 / 6463) ≤ (7279349 / 31250000) := by
  have h := checkLog_sound (w := (1343 / 11583)) (n := 12)
    (lo := (232939167 / 1000000000)) (hi := (7279349 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6463 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6463 / 5120) = 1/(5120 / 6463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (232939167 / 1000000000) (7279349 / 31250000) (Real.log (6463 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6463 / 5120) = -Real.log (5120 / 6463) := by
    rw [show ((6463 / 5120) : ℝ) = ((5120 / 6463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (60844879 / 200000000) ≤ -Real.log (3777 / 5120) ∧
    -Real.log (3777 / 5120) ≤ (76056099 / 250000000) := by
  have h := checkLog_sound (w := (1343 / 8897)) (n := 12)
    (lo := (60844879 / 200000000)) (hi := (76056099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3777) = 1/(3777 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-76056099 / 250000000) (-60844879 / 200000000) (Real.log (3777 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21325817 / 125000000) ≤ -Real.log (125000 / 148253) ∧
    -Real.log (125000 / 148253) ≤ (170606537 / 1000000000) := by
  have h := checkLog_sound (w := (23253 / 273253)) (n := 12)
    (lo := (21325817 / 125000000)) (hi := (170606537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148253 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148253 / 125000) = 1/(125000 / 148253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21325817 / 125000000) (170606537 / 1000000000) (Real.log (148253 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (148253 / 125000) = -Real.log (125000 / 148253) := by
    rw [show ((148253 / 125000) : ℝ) = ((125000 / 148253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (205824397 / 1000000000) ≤ -Real.log (101747 / 125000) ∧
    -Real.log (101747 / 125000) ≤ (102912199 / 500000000) := by
  have h := checkLog_sound (w := (23253 / 226747)) (n := 12)
    (lo := (205824397 / 1000000000)) (hi := (102912199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 101747) = 1/(101747 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-102912199 / 500000000) (-205824397 / 1000000000) (Real.log (101747 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (34191951 / 200000000) ≤ -Real.log (1000000 / 1186443) ∧
    -Real.log (1000000 / 1186443) ≤ (42739939 / 250000000) := by
  have h := checkLog_sound (w := (186443 / 2186443)) (n := 12)
    (lo := (34191951 / 200000000)) (hi := (42739939 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186443 / 1000000) = 1/(1000000 / 1186443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (34191951 / 200000000) (42739939 / 250000000) (Real.log (1186443 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1186443 / 1000000) = -Real.log (1000000 / 1186443) := by
    rw [show ((1186443 / 1000000) : ℝ) = ((1000000 / 1186443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (206339287 / 1000000000) ≤ -Real.log (813557 / 1000000) ∧
    -Real.log (813557 / 1000000) ≤ (25792411 / 125000000) := by
  have h := checkLog_sound (w := (186443 / 1813557)) (n := 12)
    (lo := (206339287 / 1000000000)) (hi := (25792411 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813557) = 1/(813557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-25792411 / 125000000) (-206339287 / 1000000000) (Real.log (813557 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (124703919 / 1000000000) ≤ -Real.log (1000000 / 1132813) ∧
    -Real.log (1000000 / 1132813) ≤ (1558799 / 12500000) := by
  have h := checkLog_sound (w := (132813 / 2132813)) (n := 12)
    (lo := (124703919 / 1000000000)) (hi := (1558799 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1132813 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1132813 / 1000000) = 1/(1000000 / 1132813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (124703919 / 1000000000) (1558799 / 12500000) (Real.log (1132813 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1132813 / 1000000) = -Real.log (1000000 / 1132813) := by
    rw [show ((1132813 / 1000000) : ℝ) = ((1000000 / 1132813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (142500639 / 1000000000) ≤ -Real.log (867187 / 1000000) ∧
    -Real.log (867187 / 1000000) ≤ (890629 / 6250000) := by
  have h := checkLog_sound (w := (132813 / 1867187)) (n := 12)
    (lo := (142500639 / 1000000000)) (hi := (890629 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 867187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 867187) = 1/(867187 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-890629 / 6250000) (-142500639 / 1000000000) (Real.log (867187 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31243281 / 250000000) ≤ -Real.log (500000 / 566559) ∧
    -Real.log (500000 / 566559) ≤ (199957 / 1600000) := by
  have h := checkLog_sound (w := (66559 / 1066559)) (n := 12)
    (lo := (31243281 / 250000000)) (hi := (199957 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566559 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566559 / 500000) = 1/(500000 / 566559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31243281 / 250000000) (199957 / 1600000) (Real.log (566559 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (566559 / 500000) = -Real.log (500000 / 566559) := by
    rw [show ((566559 / 500000) : ℝ) = ((500000 / 566559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (35713103 / 250000000) ≤ -Real.log (433441 / 500000) ∧
    -Real.log (433441 / 500000) ≤ (142852413 / 1000000000) := by
  have h := checkLog_sound (w := (66559 / 933441)) (n := 12)
    (lo := (35713103 / 250000000)) (hi := (142852413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433441) = 1/(433441 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-142852413 / 1000000000) (-35713103 / 250000000) (Real.log (433441 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (268581781 / 500000000) ≤ -Real.log (62500000000 / 106946650781) ∧
    -Real.log (62500000000 / 106946650781) ≤ (537163563 / 1000000000) := by
  have h := checkLog_sound (w := (44446650781 / 169446650781)) (n := 12)
    (lo := (268581781 / 500000000)) (hi := (537163563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106946650781 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106946650781 / 62500000000) = 1/(62500000000 / 106946650781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (268581781 / 500000000) (537163563 / 1000000000) (Real.log (106946650781 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (106946650781 / 62500000000) = -Real.log (62500000000 / 106946650781) := by
    rw [show ((106946650781 / 62500000000) : ℝ) = ((62500000000 / 106946650781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (67302779 / 125000000) ≤ -Real.log (15625000000 / 26770336513) ∧
    -Real.log (15625000000 / 26770336513) ≤ (538422233 / 1000000000) := by
  have h := checkLog_sound (w := (11145336513 / 42395336513)) (n := 12)
    (lo := (67302779 / 125000000)) (hi := (538422233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26770336513 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26770336513 / 15625000000) = 1/(15625000000 / 26770336513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (67302779 / 125000000) (538422233 / 1000000000) (Real.log (26770336513 / 15625000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (26770336513 / 15625000000) = -Real.log (15625000000 / 26770336513) := by
    rw [show ((26770336513 / 15625000000) : ℝ) = ((15625000000 / 26770336513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (376430933 / 1000000000) ≤ -Real.log (100000000000 / 145707490147) ∧
    -Real.log (100000000000 / 145707490147) ≤ (188215467 / 500000000) := by
  have h := checkLog_sound (w := (45707490147 / 245707490147)) (n := 12)
    (lo := (376430933 / 1000000000)) (hi := (188215467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145707490147 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145707490147 / 100000000000) = 1/(100000000000 / 145707490147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (376430933 / 1000000000) (188215467 / 500000000) (Real.log (145707490147 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (145707490147 / 100000000000) = -Real.log (100000000000 / 145707490147) := by
    rw [show ((145707490147 / 100000000000) : ℝ) = ((100000000000 / 145707490147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (188649521 / 500000000) ≤ -Real.log (125000000000 / 182292543731) ∧
    -Real.log (125000000000 / 182292543731) ≤ (377299043 / 1000000000) := by
  have h := checkLog_sound (w := (57292543731 / 307292543731)) (n := 12)
    (lo := (188649521 / 500000000)) (hi := (377299043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182292543731 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182292543731 / 125000000000) = 1/(125000000000 / 182292543731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (188649521 / 500000000) (377299043 / 1000000000) (Real.log (182292543731 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (182292543731 / 125000000000) = -Real.log (125000000000 / 182292543731) := by
    rw [show ((182292543731 / 125000000000) : ℝ) = ((125000000000 / 182292543731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (267204559 / 1000000000) ≤ -Real.log (250000000000 / 326576909017) ∧
    -Real.log (250000000000 / 326576909017) ≤ (3340057 / 12500000) := by
  have h := checkLog_sound (w := (76576909017 / 576576909017)) (n := 12)
    (lo := (267204559 / 1000000000)) (hi := (3340057 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326576909017 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326576909017 / 250000000000) = 1/(250000000000 / 326576909017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (267204559 / 1000000000) (3340057 / 12500000) (Real.log (326576909017 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (326576909017 / 250000000000) = -Real.log (250000000000 / 326576909017) := by
    rw [show ((326576909017 / 250000000000) : ℝ) = ((250000000000 / 326576909017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (267825537 / 1000000000) ≤ -Real.log (500000000000 / 653559538669) ∧
    -Real.log (500000000000 / 653559538669) ≤ (133912769 / 500000000) := by
  have h := checkLog_sound (w := (153559538669 / 1153559538669)) (n := 12)
    (lo := (267825537 / 1000000000)) (hi := (133912769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653559538669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653559538669 / 500000000000) = 1/(500000000000 / 653559538669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (267825537 / 1000000000) (133912769 / 500000000) (Real.log (653559538669 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (653559538669 / 500000000000) = -Real.log (500000000000 / 653559538669) := by
    rw [show ((653559538669 / 500000000000) : ℝ) = ((500000000000 / 653559538669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2234911 / 125000000) ≤ -Real.log (245569899519 / 250000000000) ∧
    -Real.log (245569899519 / 250000000000) ≤ (17879289 / 1000000000) := by
  have h := checkLog_sound (w := (4430100481 / 495569899519)) (n := 12)
    (lo := (2234911 / 125000000)) (hi := (17879289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245569899519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245569899519) = 1/(245569899519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17879289 / 1000000000) (-2234911 / 125000000) (Real.log (245569899519 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17796719 / 1000000000) ≤ -Real.log (982360707031 / 1000000000000) ∧
    -Real.log (982360707031 / 1000000000000) ≤ (222459 / 12500000) := by
  have h := checkLog_sound (w := (17639292969 / 1982360707031)) (n := 12)
    (lo := (17796719 / 1000000000)) (hi := (222459 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982360707031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982360707031) = 1/(982360707031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-222459 / 12500000) (-17796719 / 1000000000) (Real.log (982360707031 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell021

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell022Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell022
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

theorem reflection_log_1_neg : (116933549 / 500000000) ≤ -Real.log (5120 / 6469) ∧
    -Real.log (5120 / 6469) ≤ (233867099 / 1000000000) := by
  have h := checkLog_sound (w := (1349 / 11589)) (n := 12)
    (lo := (116933549 / 500000000)) (hi := (233867099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6469 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6469 / 5120) = 1/(5120 / 6469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (116933549 / 500000000) (233867099 / 1000000000) (Real.log (6469 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6469 / 5120) = -Real.log (5120 / 6469) := by
    rw [show ((6469 / 5120) : ℝ) = ((5120 / 6469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (15290711 / 50000000) ≤ -Real.log (3771 / 5120) ∧
    -Real.log (3771 / 5120) ≤ (305814221 / 1000000000) := by
  have h := checkLog_sound (w := (1349 / 8891)) (n := 12)
    (lo := (15290711 / 50000000)) (hi := (305814221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3771) = 1/(3771 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-305814221 / 1000000000) (-15290711 / 50000000) (Real.log (3771 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5835081 / 25000000) ≤ -Real.log (2560 / 3233) ∧
    -Real.log (2560 / 3233) ≤ (233403241 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 5793)) (n := 12)
    (lo := (5835081 / 25000000)) (hi := (233403241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3233 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3233 / 2560) = 1/(2560 / 3233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5835081 / 25000000) (233403241 / 1000000000) (Real.log (3233 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3233 / 2560) = -Real.log (2560 / 3233) := by
    rw [show ((3233 / 2560) : ℝ) = ((2560 / 3233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19063687 / 62500000) ≤ -Real.log (1887 / 2560) ∧
    -Real.log (1887 / 2560) ≤ (305018993 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 4447)) (n := 12)
    (lo := (19063687 / 62500000)) (hi := (305018993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1887) = 1/(1887 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-305018993 / 1000000000) (-19063687 / 62500000) (Real.log (1887 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2671233 / 15625000) ≤ -Real.log (500000 / 593221) ∧
    -Real.log (500000 / 593221) ≤ (170958913 / 1000000000) := by
  have h := checkLog_sound (w := (93221 / 1093221)) (n := 12)
    (lo := (2671233 / 15625000)) (hi := (170958913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593221 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593221 / 500000) = 1/(500000 / 593221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2671233 / 15625000) (170958913 / 1000000000) (Real.log (593221 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (593221 / 500000) = -Real.log (500000 / 593221) := by
    rw [show ((593221 / 500000) : ℝ) = ((500000 / 593221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (206338057 / 1000000000) ≤ -Real.log (406779 / 500000) ∧
    -Real.log (406779 / 500000) ≤ (103169029 / 500000000) := by
  have h := checkLog_sound (w := (93221 / 906779)) (n := 12)
    (lo := (206338057 / 1000000000)) (hi := (103169029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406779) = 1/(406779 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-103169029 / 500000000) (-206338057 / 1000000000) (Real.log (406779 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (171312849 / 1000000000) ≤ -Real.log (500000 / 593431) ∧
    -Real.log (500000 / 593431) ≤ (3426257 / 20000000) := by
  have h := checkLog_sound (w := (93431 / 1093431)) (n := 12)
    (lo := (171312849 / 1000000000)) (hi := (3426257 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593431 / 500000) = 1/(500000 / 593431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (171312849 / 1000000000) (3426257 / 20000000) (Real.log (593431 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (593431 / 500000) = -Real.log (500000 / 593431) := by
    rw [show ((593431 / 500000) : ℝ) = ((500000 / 593431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (103427221 / 500000000) ≤ -Real.log (406569 / 500000) ∧
    -Real.log (406569 / 500000) ≤ (206854443 / 1000000000) := by
  have h := checkLog_sound (w := (93431 / 906569)) (n := 12)
    (lo := (103427221 / 500000000)) (hi := (206854443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406569) = 1/(406569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-206854443 / 1000000000) (-103427221 / 500000000) (Real.log (406569 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (62486121 / 500000000) ≤ -Real.log (1000000 / 1133117) ∧
    -Real.log (1000000 / 1133117) ≤ (124972243 / 1000000000) := by
  have h := checkLog_sound (w := (133117 / 2133117)) (n := 12)
    (lo := (62486121 / 500000000)) (hi := (124972243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133117 / 1000000) = 1/(1000000 / 1133117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (62486121 / 500000000) (124972243 / 1000000000) (Real.log (1133117 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1133117 / 1000000) = -Real.log (1000000 / 1133117) := by
    rw [show ((1133117 / 1000000) : ℝ) = ((1000000 / 1133117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (142851259 / 1000000000) ≤ -Real.log (866883 / 1000000) ∧
    -Real.log (866883 / 1000000) ≤ (7142563 / 50000000) := by
  have h := checkLog_sound (w := (133117 / 1866883)) (n := 12)
    (lo := (142851259 / 1000000000)) (hi := (7142563 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 866883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 866883) = 1/(866883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7142563 / 50000000) (-142851259 / 1000000000) (Real.log (866883 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1001931 / 8000000) ≤ -Real.log (500000 / 566711) ∧
    -Real.log (500000 / 566711) ≤ (3913793 / 31250000) := by
  have h := checkLog_sound (w := (66711 / 1066711)) (n := 12)
    (lo := (1001931 / 8000000)) (hi := (3913793 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566711 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566711 / 500000) = 1/(500000 / 566711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1001931 / 8000000) (3913793 / 31250000) (Real.log (566711 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (566711 / 500000) = -Real.log (500000 / 566711) := by
    rw [show ((566711 / 500000) : ℝ) = ((500000 / 566711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (35800789 / 250000000) ≤ -Real.log (433289 / 500000) ∧
    -Real.log (433289 / 500000) ≤ (143203157 / 1000000000) := by
  have h := checkLog_sound (w := (66711 / 933289)) (n := 12)
    (lo := (35800789 / 250000000)) (hi := (143203157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433289) = 1/(433289 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-143203157 / 1000000000) (-35800789 / 250000000) (Real.log (433289 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67302779 / 125000000) ≤ -Real.log (100000000000 / 171330153683) ∧
    -Real.log (100000000000 / 171330153683) ≤ (538422233 / 1000000000) := by
  have h := checkLog_sound (w := (71330153683 / 271330153683)) (n := 12)
    (lo := (67302779 / 125000000)) (hi := (538422233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171330153683 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171330153683 / 100000000000) = 1/(100000000000 / 171330153683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67302779 / 125000000) (538422233 / 1000000000) (Real.log (171330153683 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (171330153683 / 100000000000) = -Real.log (100000000000 / 171330153683) := by
    rw [show ((171330153683 / 100000000000) : ℝ) = ((100000000000 / 171330153683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (269840659 / 500000000) ≤ -Real.log (500000000000 / 857730045081) ∧
    -Real.log (500000000000 / 857730045081) ≤ (539681319 / 1000000000) := by
  have h := checkLog_sound (w := (357730045081 / 1357730045081)) (n := 12)
    (lo := (269840659 / 500000000)) (hi := (539681319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857730045081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857730045081 / 500000000000) = 1/(500000000000 / 857730045081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (269840659 / 500000000) (539681319 / 1000000000) (Real.log (857730045081 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (857730045081 / 500000000000) = -Real.log (500000000000 / 857730045081) := by
    rw [show ((857730045081 / 500000000000) : ℝ) = ((500000000000 / 857730045081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (37729697 / 100000000) ≤ -Real.log (100000000000 / 145833732813) ∧
    -Real.log (100000000000 / 145833732813) ≤ (377296971 / 1000000000) := by
  have h := checkLog_sound (w := (45833732813 / 245833732813)) (n := 12)
    (lo := (37729697 / 100000000)) (hi := (377296971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145833732813 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145833732813 / 100000000000) = 1/(100000000000 / 145833732813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (37729697 / 100000000) (377296971 / 1000000000) (Real.log (145833732813 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (145833732813 / 100000000000) = -Real.log (100000000000 / 145833732813) := by
    rw [show ((145833732813 / 100000000000) : ℝ) = ((100000000000 / 145833732813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (378167291 / 1000000000) ≤ -Real.log (500000000000 / 729803551181) ∧
    -Real.log (500000000000 / 729803551181) ≤ (94541823 / 250000000) := by
  have h := checkLog_sound (w := (229803551181 / 1229803551181)) (n := 12)
    (lo := (378167291 / 1000000000)) (hi := (94541823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729803551181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729803551181 / 500000000000) = 1/(500000000000 / 729803551181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (378167291 / 1000000000) (94541823 / 250000000) (Real.log (729803551181 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (729803551181 / 500000000000) = -Real.log (500000000000 / 729803551181) := by
    rw [show ((729803551181 / 500000000000) : ℝ) = ((500000000000 / 729803551181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (267823501 / 1000000000) ≤ -Real.log (50000000000 / 65355820797) ∧
    -Real.log (50000000000 / 65355820797) ≤ (133911751 / 500000000) := by
  have h := checkLog_sound (w := (15355820797 / 115355820797)) (n := 12)
    (lo := (267823501 / 1000000000)) (hi := (133911751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65355820797 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65355820797 / 50000000000) = 1/(50000000000 / 65355820797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (267823501 / 1000000000) (133911751 / 500000000) (Real.log (65355820797 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (65355820797 / 50000000000) = -Real.log (50000000000 / 65355820797) := by
    rw [show ((65355820797 / 50000000000) : ℝ) = ((50000000000 / 65355820797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (268444531 / 1000000000) ≤ -Real.log (250000000000 / 326982106631) ∧
    -Real.log (250000000000 / 326982106631) ≤ (67111133 / 250000000) := by
  have h := checkLog_sound (w := (76982106631 / 576982106631)) (n := 12)
    (lo := (268444531 / 1000000000)) (hi := (67111133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326982106631 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326982106631 / 250000000000) = 1/(250000000000 / 326982106631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (268444531 / 1000000000) (67111133 / 250000000) (Real.log (326982106631 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (326982106631 / 250000000000) = -Real.log (250000000000 / 326982106631) := by
    rw [show ((326982106631 / 250000000000) : ℝ) = ((250000000000 / 326982106631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17961781 / 1000000000) ≤ -Real.log (245549642479 / 250000000000) ∧
    -Real.log (245549642479 / 250000000000) ≤ (8980891 / 500000000) := by
  have h := checkLog_sound (w := (4450357521 / 495549642479)) (n := 12)
    (lo := (17961781 / 1000000000)) (hi := (8980891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245549642479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245549642479) = 1/(245549642479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8980891 / 500000000) (-17961781 / 1000000000) (Real.log (245549642479 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17879017 / 1000000000) ≤ -Real.log (982279864311 / 1000000000000) ∧
    -Real.log (982279864311 / 1000000000000) ≤ (8939509 / 500000000) := by
  have h := checkLog_sound (w := (17720135689 / 1982279864311)) (n := 12)
    (lo := (17879017 / 1000000000)) (hi := (8939509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982279864311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982279864311) = 1/(982279864311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8939509 / 500000000) (-17879017 / 1000000000) (Real.log (982279864311 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell022

end


