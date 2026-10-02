-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell197Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell197Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:56:32.433727+00:00
-- url     : https://prove2.me/theorems/dbe0c1ba-f335-4371-907e-c4e68c76fa9e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell197Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell198…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell197Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell198Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell199Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell200Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell201Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell202Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell203Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell204Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell197Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell198Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell199Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell200Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell201Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell202Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell203Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell204Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell197Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell198Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell199Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell200Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell201Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell202Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell203Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell204Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell197Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell198Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell199Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell200Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell201Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell202Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell203Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell204Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell197Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell197
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

theorem reflection_log_1_neg : (311898199 / 1000000000) ≤ -Real.log (2560 / 3497) ∧
    -Real.log (2560 / 3497) ≤ (1559491 / 5000000) := by
  have h := checkLog_sound (w := (937 / 6057)) (n := 12)
    (lo := (311898199 / 1000000000)) (hi := (1559491 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3497 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3497 / 2560) = 1/(2560 / 3497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (311898199 / 1000000000) (1559491 / 5000000) (Real.log (3497 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3497 / 2560) = -Real.log (2560 / 3497) := by
    rw [show ((3497 / 2560) : ℝ) = ((2560 / 3497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (455730969 / 1000000000) ≤ -Real.log (1623 / 2560) ∧
    -Real.log (1623 / 2560) ≤ (45573097 / 100000000) := by
  have h := checkLog_sound (w := (937 / 4183)) (n := 12)
    (lo := (455730969 / 1000000000)) (hi := (45573097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1623) = 1/(1623 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-45573097 / 100000000) (-455730969 / 1000000000) (Real.log (1623 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (19466823 / 62500000) ≤ -Real.log (5120 / 6991) ∧
    -Real.log (5120 / 6991) ≤ (311469169 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 12111)) (n := 12)
    (lo := (19466823 / 62500000)) (hi := (311469169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6991 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6991 / 5120) = 1/(5120 / 6991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (19466823 / 62500000) (311469169 / 1000000000) (Real.log (6991 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6991 / 5120) = -Real.log (5120 / 6991) := by
    rw [show ((6991 / 5120) : ℝ) = ((5120 / 6991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (227403591 / 500000000) ≤ -Real.log (3249 / 5120) ∧
    -Real.log (3249 / 5120) ≤ (454807183 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 8369)) (n := 12)
    (lo := (227403591 / 500000000)) (hi := (454807183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3249) = 1/(3249 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-454807183 / 1000000000) (-227403591 / 500000000) (Real.log (3249 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (11552451 / 50000000) ≤ -Real.log (1000000 / 1259921) ∧
    -Real.log (1000000 / 1259921) ≤ (231049021 / 1000000000) := by
  have h := checkLog_sound (w := (259921 / 2259921)) (n := 12)
    (lo := (11552451 / 50000000)) (hi := (231049021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259921 / 1000000) = 1/(1000000 / 1259921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (11552451 / 50000000) (231049021 / 1000000000) (Real.log (1259921 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1259921 / 1000000) = -Real.log (1000000 / 1259921) := by
    rw [show ((1259921 / 1000000) : ℝ) = ((1000000 / 1259921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (300998341 / 1000000000) ≤ -Real.log (740079 / 1000000) ∧
    -Real.log (740079 / 1000000) ≤ (150499171 / 500000000) := by
  have h := checkLog_sound (w := (259921 / 1740079)) (n := 12)
    (lo := (300998341 / 1000000000)) (hi := (150499171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 740079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 740079) = 1/(740079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-150499171 / 500000000) (-300998341 / 1000000000) (Real.log (740079 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (231384699 / 1000000000) ≤ -Real.log (125000 / 157543) ∧
    -Real.log (125000 / 157543) ≤ (2313847 / 10000000) := by
  have h := checkLog_sound (w := (32543 / 282543)) (n := 12)
    (lo := (231384699 / 1000000000)) (hi := (2313847 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157543 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157543 / 125000) = 1/(125000 / 157543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (231384699 / 1000000000) (2313847 / 10000000) (Real.log (157543 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (157543 / 125000) = -Real.log (125000 / 157543) := by
    rw [show ((157543 / 125000) : ℝ) = ((125000 / 157543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (60314013 / 200000000) ≤ -Real.log (92457 / 125000) ∧
    -Real.log (92457 / 125000) ≤ (150785033 / 500000000) := by
  have h := checkLog_sound (w := (32543 / 217457)) (n := 12)
    (lo := (60314013 / 200000000)) (hi := (150785033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 92457) = 1/(92457 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-150785033 / 500000000) (-60314013 / 200000000) (Real.log (92457 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85839647 / 500000000) ≤ -Real.log (1000000 / 1187297) ∧
    -Real.log (1000000 / 1187297) ≤ (34335859 / 200000000) := by
  have h := checkLog_sound (w := (187297 / 2187297)) (n := 12)
    (lo := (85839647 / 500000000)) (hi := (34335859 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187297 / 1000000) = 1/(1000000 / 1187297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85839647 / 500000000) (34335859 / 200000000) (Real.log (1187297 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1187297 / 1000000) = -Real.log (1000000 / 1187297) := by
    rw [show ((1187297 / 1000000) : ℝ) = ((1000000 / 1187297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (207389549 / 1000000000) ≤ -Real.log (812703 / 1000000) ∧
    -Real.log (812703 / 1000000) ≤ (4147791 / 20000000) := by
  have h := checkLog_sound (w := (187297 / 1812703)) (n := 12)
    (lo := (207389549 / 1000000000)) (hi := (4147791 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 812703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 812703) = 1/(812703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4147791 / 20000000) (-207389549 / 1000000000) (Real.log (812703 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17194541 / 100000000) ≤ -Real.log (1000000 / 1187613) ∧
    -Real.log (1000000 / 1187613) ≤ (171945411 / 1000000000) := by
  have h := checkLog_sound (w := (187613 / 2187613)) (n := 12)
    (lo := (17194541 / 100000000)) (hi := (171945411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187613 / 1000000) = 1/(1000000 / 1187613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17194541 / 100000000) (171945411 / 1000000000) (Real.log (1187613 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1187613 / 1000000) = -Real.log (1000000 / 1187613) := by
    rw [show ((1187613 / 1000000) : ℝ) = ((1000000 / 1187613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (207778451 / 1000000000) ≤ -Real.log (812387 / 1000000) ∧
    -Real.log (812387 / 1000000) ≤ (51944613 / 250000000) := by
  have h := checkLog_sound (w := (187613 / 1812387)) (n := 12)
    (lo := (207778451 / 1000000000)) (hi := (51944613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 812387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 812387) = 1/(812387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-51944613 / 250000000) (-207778451 / 1000000000) (Real.log (812387 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (15325527 / 20000000) ≤ -Real.log (500000000000 / 1075869498307) ∧
    -Real.log (500000000000 / 1075869498307) ≤ (2993267 / 3906250) := by
  have h := checkLog_sound (w := (75869498307 / 2075869498307)) (n := 12)
    (lo := (7312917 / 100000000)) (hi := (73129171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075869498307 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1075869498307 / 1000000000000) = 1/(500000000000 / 1075869498307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (15325527 / 20000000) (2993267 / 3906250) (Real.log (1075869498307 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1075869498307 / 500000000000) = -Real.log (500000000000 / 1075869498307) := by
    rw [show ((1075869498307 / 500000000000) : ℝ) = ((500000000000 / 1075869498307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (47976823 / 62500000) ≤ -Real.log (250000000000 / 538662969809) ∧
    -Real.log (250000000000 / 538662969809) ≤ (76762917 / 100000000) := by
  have h := checkLog_sound (w := (38662969809 / 1038662969809)) (n := 12)
    (lo := (18620497 / 250000000)) (hi := (74481989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538662969809 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(538662969809 / 500000000000) = 1/(250000000000 / 538662969809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (47976823 / 62500000) (76762917 / 100000000) (Real.log (538662969809 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (538662969809 / 250000000000) = -Real.log (250000000000 / 538662969809) := by
    rw [show ((538662969809 / 250000000000) : ℝ) = ((250000000000 / 538662969809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (266023681 / 500000000) ≤ -Real.log (500000000000 / 851207100863) ∧
    -Real.log (500000000000 / 851207100863) ≤ (532047363 / 1000000000) := by
  have h := checkLog_sound (w := (351207100863 / 1351207100863)) (n := 12)
    (lo := (266023681 / 500000000)) (hi := (532047363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851207100863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851207100863 / 500000000000) = 1/(500000000000 / 851207100863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (266023681 / 500000000) (532047363 / 1000000000) (Real.log (851207100863 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (851207100863 / 500000000000) = -Real.log (500000000000 / 851207100863) := by
    rw [show ((851207100863 / 500000000000) : ℝ) = ((500000000000 / 851207100863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (106590953 / 200000000) ≤ -Real.log (500000000000 / 851979839277) ∧
    -Real.log (500000000000 / 851979839277) ≤ (266477383 / 500000000) := by
  have h := checkLog_sound (w := (351979839277 / 1351979839277)) (n := 12)
    (lo := (106590953 / 200000000)) (hi := (266477383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851979839277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851979839277 / 500000000000) = 1/(500000000000 / 851979839277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (106590953 / 200000000) (266477383 / 500000000) (Real.log (851979839277 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (851979839277 / 500000000000) = -Real.log (500000000000 / 851979839277) := by
    rw [show ((851979839277 / 500000000000) : ℝ) = ((500000000000 / 851979839277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (94767211 / 250000000) ≤ -Real.log (500000000000 / 730461804619) ∧
    -Real.log (500000000000 / 730461804619) ≤ (75813769 / 200000000) := by
  have h := checkLog_sound (w := (230461804619 / 1230461804619)) (n := 12)
    (lo := (94767211 / 250000000)) (hi := (75813769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730461804619 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730461804619 / 500000000000) = 1/(500000000000 / 730461804619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (94767211 / 250000000) (75813769 / 200000000) (Real.log (730461804619 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (730461804619 / 500000000000) = -Real.log (500000000000 / 730461804619) := by
    rw [show ((730461804619 / 500000000000) : ℝ) = ((500000000000 / 730461804619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (379723861 / 1000000000) ≤ -Real.log (500000000000 / 730940426177) ∧
    -Real.log (500000000000 / 730940426177) ≤ (189861931 / 500000000) := by
  have h := checkLog_sound (w := (230940426177 / 1230940426177)) (n := 12)
    (lo := (379723861 / 1000000000)) (hi := (189861931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730940426177 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730940426177 / 500000000000) = 1/(500000000000 / 730940426177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (379723861 / 1000000000) (189861931 / 500000000) (Real.log (730940426177 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (730940426177 / 500000000000) = -Real.log (500000000000 / 730940426177) := by
    rw [show ((730940426177 / 500000000000) : ℝ) = ((500000000000 / 730940426177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (35833041 / 1000000000) ≤ -Real.log (964801362231 / 1000000000000) ∧
    -Real.log (964801362231 / 1000000000000) ≤ (17916521 / 500000000) := by
  have h := checkLog_sound (w := (35198637769 / 1964801362231)) (n := 12)
    (lo := (35833041 / 1000000000)) (hi := (17916521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964801362231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964801362231) = 1/(964801362231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17916521 / 500000000) (-35833041 / 1000000000) (Real.log (964801362231 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17855127 / 500000000) ≤ -Real.log (964919833791 / 1000000000000) ∧
    -Real.log (964919833791 / 1000000000000) ≤ (7142051 / 200000000) := by
  have h := checkLog_sound (w := (35080166209 / 1964919833791)) (n := 12)
    (lo := (17855127 / 500000000)) (hi := (7142051 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964919833791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964919833791) = 1/(964919833791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7142051 / 200000000) (-17855127 / 500000000) (Real.log (964919833791 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell197

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell198Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell198
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

theorem reflection_log_1_neg : (156163523 / 500000000) ≤ -Real.log (5120 / 6997) ∧
    -Real.log (5120 / 6997) ≤ (312327047 / 1000000000) := by
  have h := checkLog_sound (w := (1877 / 12117)) (n := 12)
    (lo := (156163523 / 500000000)) (hi := (312327047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6997 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6997 / 5120) = 1/(5120 / 6997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (156163523 / 500000000) (312327047 / 1000000000) (Real.log (6997 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6997 / 5120) = -Real.log (5120 / 6997) := by
    rw [show ((6997 / 5120) : ℝ) = ((5120 / 6997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (456655611 / 1000000000) ≤ -Real.log (3243 / 5120) ∧
    -Real.log (3243 / 5120) ≤ (114163903 / 250000000) := by
  have h := checkLog_sound (w := (1877 / 8363)) (n := 12)
    (lo := (456655611 / 1000000000)) (hi := (114163903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3243) = 1/(3243 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-114163903 / 250000000) (-456655611 / 1000000000) (Real.log (3243 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (311898199 / 1000000000) ≤ -Real.log (2560 / 3497) ∧
    -Real.log (2560 / 3497) ≤ (1559491 / 5000000) := by
  have h := checkLog_sound (w := (937 / 6057)) (n := 12)
    (lo := (311898199 / 1000000000)) (hi := (1559491 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3497 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3497 / 2560) = 1/(2560 / 3497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (311898199 / 1000000000) (1559491 / 5000000) (Real.log (3497 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3497 / 2560) = -Real.log (2560 / 3497) := by
    rw [show ((3497 / 2560) : ℝ) = ((2560 / 3497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (455730969 / 1000000000) ≤ -Real.log (1623 / 2560) ∧
    -Real.log (1623 / 2560) ≤ (45573097 / 100000000) := by
  have h := checkLog_sound (w := (937 / 4183)) (n := 12)
    (lo := (455730969 / 1000000000)) (hi := (45573097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1623) = 1/(1623 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-45573097 / 100000000) (-455730969 / 1000000000) (Real.log (1623 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (115691953 / 500000000) ≤ -Real.log (1000000 / 1260343) ∧
    -Real.log (1000000 / 1260343) ≤ (231383907 / 1000000000) := by
  have h := checkLog_sound (w := (260343 / 2260343)) (n := 12)
    (lo := (115691953 / 500000000)) (hi := (231383907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260343 / 1000000) = 1/(1000000 / 1260343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (115691953 / 500000000) (231383907 / 1000000000) (Real.log (1260343 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1260343 / 1000000) = -Real.log (1000000 / 1260343) := by
    rw [show ((1260343 / 1000000) : ℝ) = ((1000000 / 1260343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (301568713 / 1000000000) ≤ -Real.log (739657 / 1000000) ∧
    -Real.log (739657 / 1000000) ≤ (150784357 / 500000000) := by
  have h := checkLog_sound (w := (260343 / 1739657)) (n := 12)
    (lo := (301568713 / 1000000000)) (hi := (150784357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739657) = 1/(739657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-150784357 / 500000000) (-301568713 / 1000000000) (Real.log (739657 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (14482467 / 62500000) ≤ -Real.log (500000 / 630383) ∧
    -Real.log (500000 / 630383) ≤ (231719473 / 1000000000) := by
  have h := checkLog_sound (w := (130383 / 1130383)) (n := 12)
    (lo := (14482467 / 62500000)) (hi := (231719473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630383 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630383 / 500000) = 1/(500000 / 630383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (14482467 / 62500000) (231719473 / 1000000000) (Real.log (630383 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (630383 / 500000) = -Real.log (500000 / 630383) := by
    rw [show ((630383 / 500000) : ℝ) = ((500000 / 630383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (75535191 / 250000000) ≤ -Real.log (369617 / 500000) ∧
    -Real.log (369617 / 500000) ≤ (60428153 / 200000000) := by
  have h := checkLog_sound (w := (130383 / 869617)) (n := 12)
    (lo := (75535191 / 250000000)) (hi := (60428153 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 369617) = 1/(369617 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-60428153 / 200000000) (-75535191 / 250000000) (Real.log (369617 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (21493071 / 125000000) ≤ -Real.log (250000 / 296903) ∧
    -Real.log (250000 / 296903) ≤ (171944569 / 1000000000) := by
  have h := checkLog_sound (w := (46903 / 546903)) (n := 12)
    (lo := (21493071 / 125000000)) (hi := (171944569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296903 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296903 / 250000) = 1/(250000 / 296903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (21493071 / 125000000) (171944569 / 1000000000) (Real.log (296903 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (296903 / 250000) = -Real.log (250000 / 296903) := by
    rw [show ((296903 / 250000) : ℝ) = ((250000 / 296903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10388861 / 50000000) ≤ -Real.log (203097 / 250000) ∧
    -Real.log (203097 / 250000) ≤ (207777221 / 1000000000) := by
  have h := checkLog_sound (w := (46903 / 453097)) (n := 12)
    (lo := (10388861 / 50000000)) (hi := (207777221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203097) = 1/(203097 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-207777221 / 1000000000) (-10388861 / 50000000) (Real.log (203097 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (86105727 / 500000000) ≤ -Real.log (1000000 / 1187929) ∧
    -Real.log (1000000 / 1187929) ≤ (34442291 / 200000000) := by
  have h := checkLog_sound (w := (187929 / 2187929)) (n := 12)
    (lo := (86105727 / 500000000)) (hi := (34442291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187929 / 1000000) = 1/(1000000 / 1187929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (86105727 / 500000000) (34442291 / 200000000) (Real.log (1187929 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1187929 / 1000000) = -Real.log (1000000 / 1187929) := by
    rw [show ((1187929 / 1000000) : ℝ) = ((1000000 / 1187929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (13010469 / 62500000) ≤ -Real.log (812071 / 1000000) ∧
    -Real.log (812071 / 1000000) ≤ (41633501 / 200000000) := by
  have h := checkLog_sound (w := (187929 / 1812071)) (n := 12)
    (lo := (13010469 / 62500000)) (hi := (41633501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 812071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 812071) = 1/(812071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-41633501 / 200000000) (-13010469 / 62500000) (Real.log (812071 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (47976823 / 62500000) ≤ -Real.log (500000000000 / 1077325939617) ∧
    -Real.log (500000000000 / 1077325939617) ≤ (76762917 / 100000000) := by
  have h := checkLog_sound (w := (77325939617 / 2077325939617)) (n := 12)
    (lo := (18620497 / 250000000)) (hi := (74481989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077325939617 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1077325939617 / 1000000000000) = 1/(500000000000 / 1077325939617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (47976823 / 62500000) (76762917 / 100000000) (Real.log (1077325939617 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1077325939617 / 500000000000) = -Real.log (500000000000 / 1077325939617) := by
    rw [show ((1077325939617 / 500000000000) : ℝ) = ((500000000000 / 1077325939617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (768982657 / 1000000000) ≤ -Real.log (125000000000 / 269696268887) ∧
    -Real.log (125000000000 / 269696268887) ≤ (768982659 / 1000000000) := by
  have h := checkLog_sound (w := (19696268887 / 519696268887)) (n := 12)
    (lo := (75835477 / 1000000000)) (hi := (37917739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269696268887 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269696268887 / 250000000000) = 1/(125000000000 / 269696268887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (768982657 / 1000000000) (768982659 / 1000000000) (Real.log (269696268887 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (269696268887 / 125000000000) = -Real.log (125000000000 / 269696268887) := by
    rw [show ((269696268887 / 125000000000) : ℝ) = ((125000000000 / 269696268887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (532952619 / 1000000000) ≤ -Real.log (500000000000 / 851978011429) ∧
    -Real.log (500000000000 / 851978011429) ≤ (26647631 / 50000000) := by
  have h := checkLog_sound (w := (351978011429 / 1351978011429)) (n := 12)
    (lo := (532952619 / 1000000000)) (hi := (26647631 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851978011429 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851978011429 / 500000000000) = 1/(500000000000 / 851978011429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (532952619 / 1000000000) (26647631 / 50000000) (Real.log (851978011429 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (851978011429 / 500000000000) = -Real.log (500000000000 / 851978011429) := by
    rw [show ((851978011429 / 500000000000) : ℝ) = ((500000000000 / 851978011429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (133465059 / 250000000) ≤ -Real.log (100000000000 / 170550326419) ∧
    -Real.log (100000000000 / 170550326419) ≤ (533860237 / 1000000000) := by
  have h := checkLog_sound (w := (70550326419 / 270550326419)) (n := 12)
    (lo := (133465059 / 250000000)) (hi := (533860237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170550326419 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170550326419 / 100000000000) = 1/(100000000000 / 170550326419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (133465059 / 250000000) (533860237 / 1000000000) (Real.log (170550326419 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (170550326419 / 100000000000) = -Real.log (100000000000 / 170550326419) := by
    rw [show ((170550326419 / 100000000000) : ℝ) = ((100000000000 / 170550326419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (94930447 / 250000000) ≤ -Real.log (500000000000 / 730938910963) ∧
    -Real.log (500000000000 / 730938910963) ≤ (379721789 / 1000000000) := by
  have h := checkLog_sound (w := (230938910963 / 1230938910963)) (n := 12)
    (lo := (94930447 / 250000000)) (hi := (379721789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730938910963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730938910963 / 500000000000) = 1/(500000000000 / 730938910963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (94930447 / 250000000) (379721789 / 1000000000) (Real.log (730938910963 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (730938910963 / 500000000000) = -Real.log (500000000000 / 730938910963) := by
    rw [show ((730938910963 / 500000000000) : ℝ) = ((500000000000 / 730938910963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (380378959 / 1000000000) ≤ -Real.log (7812500000 / 11428428441) ∧
    -Real.log (7812500000 / 11428428441) ≤ (4754737 / 12500000) := by
  have h := checkLog_sound (w := (3615928441 / 19240928441)) (n := 12)
    (lo := (380378959 / 1000000000)) (hi := (4754737 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11428428441 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11428428441 / 7812500000) = 1/(7812500000 / 11428428441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (380378959 / 1000000000) (4754737 / 12500000) (Real.log (11428428441 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11428428441 / 7812500000) = -Real.log (7812500000 / 11428428441) := by
    rw [show ((11428428441 / 7812500000) : ℝ) = ((7812500000 / 11428428441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (35956049 / 1000000000) ≤ -Real.log (964682690959 / 1000000000000) ∧
    -Real.log (964682690959 / 1000000000000) ≤ (719121 / 20000000) := by
  have h := checkLog_sound (w := (35317309041 / 1964682690959)) (n := 12)
    (lo := (35956049 / 1000000000)) (hi := (719121 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964682690959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964682690959) = 1/(964682690959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-719121 / 20000000) (-35956049 / 1000000000) (Real.log (964682690959 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8958163 / 250000000) ≤ -Real.log (60300108591 / 62500000000) ∧
    -Real.log (60300108591 / 62500000000) ≤ (35832653 / 1000000000) := by
  have h := checkLog_sound (w := (2199891409 / 122800108591)) (n := 12)
    (lo := (8958163 / 250000000)) (hi := (35832653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60300108591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60300108591) = 1/(60300108591 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-35832653 / 1000000000) (-8958163 / 250000000) (Real.log (60300108591 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell198

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell199Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell199
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

theorem reflection_log_1_neg : (31275571 / 100000000) ≤ -Real.log (128 / 175) ∧
    -Real.log (128 / 175) ≤ (312755711 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 303)) (n := 12)
    (lo := (31275571 / 100000000)) (hi := (312755711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175 / 128) = 1/(128 / 175) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (31275571 / 100000000) (312755711 / 1000000000) (Real.log (175 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (175 / 128) = -Real.log (128 / 175) := by
    rw [show ((175 / 128) : ℝ) = ((128 / 175) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (457581109 / 1000000000) ≤ -Real.log (81 / 128) ∧
    -Real.log (81 / 128) ≤ (45758111 / 100000000) := by
  have h := checkLog_sound (w := (47 / 209)) (n := 12)
    (lo := (457581109 / 1000000000)) (hi := (45758111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 81) = 1/(81 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-45758111 / 100000000) (-457581109 / 1000000000) (Real.log (81 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (156163523 / 500000000) ≤ -Real.log (5120 / 6997) ∧
    -Real.log (5120 / 6997) ≤ (312327047 / 1000000000) := by
  have h := checkLog_sound (w := (1877 / 12117)) (n := 12)
    (lo := (156163523 / 500000000)) (hi := (312327047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6997 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6997 / 5120) = 1/(5120 / 6997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (156163523 / 500000000) (312327047 / 1000000000) (Real.log (6997 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6997 / 5120) = -Real.log (5120 / 6997) := by
    rw [show ((6997 / 5120) : ℝ) = ((5120 / 6997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (456655611 / 1000000000) ≤ -Real.log (3243 / 5120) ∧
    -Real.log (3243 / 5120) ≤ (114163903 / 250000000) := by
  have h := checkLog_sound (w := (1877 / 8363)) (n := 12)
    (lo := (456655611 / 1000000000)) (hi := (114163903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3243) = 1/(3243 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-114163903 / 250000000) (-456655611 / 1000000000) (Real.log (3243 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (231718679 / 1000000000) ≤ -Real.log (200000 / 252153) ∧
    -Real.log (200000 / 252153) ≤ (5792967 / 25000000) := by
  have h := checkLog_sound (w := (52153 / 452153)) (n := 12)
    (lo := (231718679 / 1000000000)) (hi := (5792967 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252153 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(252153 / 200000) = 1/(200000 / 252153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (231718679 / 1000000000) (5792967 / 25000000) (Real.log (252153 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (252153 / 200000) = -Real.log (200000 / 252153) := by
    rw [show ((252153 / 200000) : ℝ) = ((200000 / 252153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (302139411 / 1000000000) ≤ -Real.log (147847 / 200000) ∧
    -Real.log (147847 / 200000) ≤ (75534853 / 250000000) := by
  have h := checkLog_sound (w := (52153 / 347847)) (n := 12)
    (lo := (302139411 / 1000000000)) (hi := (75534853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 147847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 147847) = 1/(147847 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-75534853 / 250000000) (-302139411 / 1000000000) (Real.log (147847 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (232054133 / 1000000000) ≤ -Real.log (250000 / 315297) ∧
    -Real.log (250000 / 315297) ≤ (116027067 / 500000000) := by
  have h := checkLog_sound (w := (65297 / 565297)) (n := 12)
    (lo := (232054133 / 1000000000)) (hi := (116027067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315297 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315297 / 250000) = 1/(250000 / 315297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (232054133 / 1000000000) (116027067 / 500000000) (Real.log (315297 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (315297 / 250000) = -Real.log (250000 / 315297) := by
    rw [show ((315297 / 250000) : ℝ) = ((250000 / 315297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (75677947 / 250000000) ≤ -Real.log (184703 / 250000) ∧
    -Real.log (184703 / 250000) ≤ (302711789 / 1000000000) := by
  have h := checkLog_sound (w := (65297 / 434703)) (n := 12)
    (lo := (75677947 / 250000000)) (hi := (302711789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 184703) = 1/(184703 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-302711789 / 1000000000) (-75677947 / 250000000) (Real.log (184703 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (172210613 / 1000000000) ≤ -Real.log (125000 / 148491) ∧
    -Real.log (125000 / 148491) ≤ (86105307 / 500000000) := by
  have h := checkLog_sound (w := (23491 / 273491)) (n := 12)
    (lo := (172210613 / 1000000000)) (hi := (86105307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148491 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148491 / 125000) = 1/(125000 / 148491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (172210613 / 1000000000) (86105307 / 500000000) (Real.log (148491 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (148491 / 125000) = -Real.log (125000 / 148491) := by
    rw [show ((148491 / 125000) : ℝ) = ((125000 / 148491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1626299 / 7812500) ≤ -Real.log (101509 / 125000) ∧
    -Real.log (101509 / 125000) ≤ (208166273 / 1000000000) := by
  have h := checkLog_sound (w := (23491 / 226509)) (n := 12)
    (lo := (1626299 / 7812500)) (hi := (208166273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 101509) = 1/(101509 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-208166273 / 1000000000) (-1626299 / 7812500) (Real.log (101509 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (43119357 / 250000000) ≤ -Real.log (200000 / 237649) ∧
    -Real.log (200000 / 237649) ≤ (172477429 / 1000000000) := by
  have h := checkLog_sound (w := (37649 / 437649)) (n := 12)
    (lo := (43119357 / 250000000)) (hi := (172477429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237649 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237649 / 200000) = 1/(200000 / 237649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (43119357 / 250000000) (172477429 / 1000000000) (Real.log (237649 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (237649 / 200000) = -Real.log (200000 / 237649) := by
    rw [show ((237649 / 200000) : ℝ) = ((200000 / 237649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (52139177 / 250000000) ≤ -Real.log (162351 / 200000) ∧
    -Real.log (162351 / 200000) ≤ (208556709 / 1000000000) := by
  have h := checkLog_sound (w := (37649 / 362351)) (n := 12)
    (lo := (52139177 / 250000000)) (hi := (208556709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 162351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 162351) = 1/(162351 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-208556709 / 1000000000) (-52139177 / 250000000) (Real.log (162351 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (768982657 / 1000000000) ≤ -Real.log (500000000000 / 1078785075547) ∧
    -Real.log (500000000000 / 1078785075547) ≤ (768982659 / 1000000000) := by
  have h := checkLog_sound (w := (78785075547 / 2078785075547)) (n := 12)
    (lo := (75835477 / 1000000000)) (hi := (37917739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078785075547 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1078785075547 / 1000000000000) = 1/(500000000000 / 1078785075547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (768982657 / 1000000000) (768982659 / 1000000000) (Real.log (1078785075547 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1078785075547 / 500000000000) = -Real.log (500000000000 / 1078785075547) := by
    rw [show ((1078785075547 / 500000000000) : ℝ) = ((500000000000 / 1078785075547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (385168409 / 500000000) ≤ -Real.log (500000000000 / 1080246913581) ∧
    -Real.log (500000000000 / 1080246913581) ≤ (38516841 / 50000000) := by
  have h := checkLog_sound (w := (80246913581 / 2080246913581)) (n := 12)
    (lo := (38594819 / 500000000)) (hi := (77189639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080246913581 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1080246913581 / 1000000000000) = 1/(500000000000 / 1080246913581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (385168409 / 500000000) (38516841 / 50000000) (Real.log (1080246913581 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1080246913581 / 500000000000) = -Real.log (500000000000 / 1080246913581) := by
    rw [show ((1080246913581 / 500000000000) : ℝ) = ((500000000000 / 1080246913581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (53385809 / 100000000) ≤ -Real.log (6250000000 / 10659372527) ∧
    -Real.log (6250000000 / 10659372527) ≤ (533858091 / 1000000000) := by
  have h := checkLog_sound (w := (4409372527 / 16909372527)) (n := 12)
    (lo := (53385809 / 100000000)) (hi := (533858091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10659372527 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10659372527 / 6250000000) = 1/(6250000000 / 10659372527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53385809 / 100000000) (533858091 / 1000000000) (Real.log (10659372527 / 6250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (10659372527 / 6250000000) = -Real.log (6250000000 / 10659372527) := by
    rw [show ((10659372527 / 6250000000) : ℝ) = ((6250000000 / 10659372527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (267382961 / 500000000) ≤ -Real.log (50000000000 / 85352430659) ∧
    -Real.log (50000000000 / 85352430659) ≤ (534765923 / 1000000000) := by
  have h := checkLog_sound (w := (35352430659 / 135352430659)) (n := 12)
    (lo := (267382961 / 500000000)) (hi := (534765923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85352430659 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85352430659 / 50000000000) = 1/(50000000000 / 85352430659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (267382961 / 500000000) (534765923 / 1000000000) (Real.log (85352430659 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (85352430659 / 50000000000) = -Real.log (50000000000 / 85352430659) := by
    rw [show ((85352430659 / 50000000000) : ℝ) = ((50000000000 / 85352430659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (76075377 / 200000000) ≤ -Real.log (500000000000 / 731417903831) ∧
    -Real.log (500000000000 / 731417903831) ≤ (190188443 / 500000000) := by
  have h := checkLog_sound (w := (231417903831 / 1231417903831)) (n := 12)
    (lo := (76075377 / 200000000)) (hi := (190188443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731417903831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731417903831 / 500000000000) = 1/(500000000000 / 731417903831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (76075377 / 200000000) (190188443 / 500000000) (Real.log (731417903831 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (731417903831 / 500000000000) = -Real.log (500000000000 / 731417903831) := by
    rw [show ((731417903831 / 500000000000) : ℝ) = ((500000000000 / 731417903831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (381034137 / 1000000000) ≤ -Real.log (125000000000 / 182974696799) ∧
    -Real.log (125000000000 / 182974696799) ≤ (190517069 / 500000000) := by
  have h := checkLog_sound (w := (57974696799 / 307974696799)) (n := 12)
    (lo := (381034137 / 1000000000)) (hi := (190517069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182974696799 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182974696799 / 125000000000) = 1/(125000000000 / 182974696799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (381034137 / 1000000000) (190517069 / 500000000) (Real.log (182974696799 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (182974696799 / 125000000000) = -Real.log (125000000000 / 182974696799) := by
    rw [show ((182974696799 / 125000000000) : ℝ) = ((125000000000 / 182974696799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (36079279 / 1000000000) ≤ -Real.log (38582552799 / 40000000000) ∧
    -Real.log (38582552799 / 40000000000) ≤ (450991 / 12500000) := by
  have h := checkLog_sound (w := (1417447201 / 78582552799)) (n := 12)
    (lo := (36079279 / 1000000000)) (hi := (450991 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38582552799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38582552799) = 1/(38582552799 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-450991 / 12500000) (-36079279 / 1000000000) (Real.log (38582552799 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (35955659 / 1000000000) ≤ -Real.log (15073172919 / 15625000000) ∧
    -Real.log (15073172919 / 15625000000) ≤ (1797783 / 50000000) := by
  have h := checkLog_sound (w := (551827081 / 30698172919)) (n := 12)
    (lo := (35955659 / 1000000000)) (hi := (1797783 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15073172919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15073172919) = 1/(15073172919 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1797783 / 50000000) (-35955659 / 1000000000) (Real.log (15073172919 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell199

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell200Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell200
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

theorem reflection_log_1_neg : (313184189 / 1000000000) ≤ -Real.log (5120 / 7003) ∧
    -Real.log (5120 / 7003) ≤ (31318419 / 100000000) := by
  have h := checkLog_sound (w := (1883 / 12123)) (n := 12)
    (lo := (313184189 / 1000000000)) (hi := (31318419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7003 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7003 / 5120) = 1/(5120 / 7003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (313184189 / 1000000000) (31318419 / 100000000) (Real.log (7003 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7003 / 5120) = -Real.log (5120 / 7003) := by
    rw [show ((7003 / 5120) : ℝ) = ((5120 / 7003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57313433 / 125000000) ≤ -Real.log (3237 / 5120) ∧
    -Real.log (3237 / 5120) ≤ (91701493 / 200000000) := by
  have h := checkLog_sound (w := (1883 / 8357)) (n := 12)
    (lo := (57313433 / 125000000)) (hi := (91701493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3237) = 1/(3237 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-91701493 / 200000000) (-57313433 / 125000000) (Real.log (3237 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (31275571 / 100000000) ≤ -Real.log (128 / 175) ∧
    -Real.log (128 / 175) ≤ (312755711 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 303)) (n := 12)
    (lo := (31275571 / 100000000)) (hi := (312755711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175 / 128) = 1/(128 / 175) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (31275571 / 100000000) (312755711 / 1000000000) (Real.log (175 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (175 / 128) = -Real.log (128 / 175) := by
    rw [show ((175 / 128) : ℝ) = ((128 / 175) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (457581109 / 1000000000) ≤ -Real.log (81 / 128) ∧
    -Real.log (81 / 128) ≤ (45758111 / 100000000) := by
  have h := checkLog_sound (w := (47 / 209)) (n := 12)
    (lo := (457581109 / 1000000000)) (hi := (45758111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 81) = 1/(81 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-45758111 / 100000000) (-457581109 / 1000000000) (Real.log (81 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (11602667 / 50000000) ≤ -Real.log (1000000 / 1261187) ∧
    -Real.log (1000000 / 1261187) ≤ (232053341 / 1000000000) := by
  have h := checkLog_sound (w := (261187 / 2261187)) (n := 12)
    (lo := (11602667 / 50000000)) (hi := (232053341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261187 / 1000000) = 1/(1000000 / 1261187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (11602667 / 50000000) (232053341 / 1000000000) (Real.log (1261187 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1261187 / 1000000) = -Real.log (1000000 / 1261187) := by
    rw [show ((1261187 / 1000000) : ℝ) = ((1000000 / 1261187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (151355217 / 500000000) ≤ -Real.log (738813 / 1000000) ∧
    -Real.log (738813 / 1000000) ≤ (60542087 / 200000000) := by
  have h := checkLog_sound (w := (261187 / 1738813)) (n := 12)
    (lo := (151355217 / 500000000)) (hi := (60542087 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738813) = 1/(738813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-60542087 / 200000000) (-151355217 / 500000000) (Real.log (738813 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (232388683 / 1000000000) ≤ -Real.log (100000 / 126161) ∧
    -Real.log (100000 / 126161) ≤ (58097171 / 250000000) := by
  have h := checkLog_sound (w := (26161 / 226161)) (n := 12)
    (lo := (232388683 / 1000000000)) (hi := (58097171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126161 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126161 / 100000) = 1/(100000 / 126161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (232388683 / 1000000000) (58097171 / 250000000) (Real.log (126161 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (126161 / 100000) = -Real.log (100000 / 126161) := by
    rw [show ((126161 / 100000) : ℝ) = ((100000 / 126161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (151641569 / 500000000) ≤ -Real.log (73839 / 100000) ∧
    -Real.log (73839 / 100000) ≤ (303283139 / 1000000000) := by
  have h := checkLog_sound (w := (26161 / 173839)) (n := 12)
    (lo := (151641569 / 500000000)) (hi := (303283139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 73839) = 1/(73839 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-303283139 / 1000000000) (-151641569 / 500000000) (Real.log (73839 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (172476587 / 1000000000) ≤ -Real.log (250000 / 297061) ∧
    -Real.log (250000 / 297061) ≤ (43119147 / 250000000) := by
  have h := checkLog_sound (w := (47061 / 547061)) (n := 12)
    (lo := (172476587 / 1000000000)) (hi := (43119147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297061 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297061 / 250000) = 1/(250000 / 297061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (172476587 / 1000000000) (43119147 / 250000000) (Real.log (297061 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (297061 / 250000) = -Real.log (250000 / 297061) := by
    rw [show ((297061 / 250000) : ℝ) = ((250000 / 297061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (52138869 / 250000000) ≤ -Real.log (202939 / 250000) ∧
    -Real.log (202939 / 250000) ≤ (208555477 / 1000000000) := by
  have h := checkLog_sound (w := (47061 / 452939)) (n := 12)
    (lo := (52138869 / 250000000)) (hi := (208555477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202939) = 1/(202939 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-208555477 / 1000000000) (-52138869 / 250000000) (Real.log (202939 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (172743331 / 1000000000) ≤ -Real.log (1000000 / 1188561) ∧
    -Real.log (1000000 / 1188561) ≤ (43185833 / 250000000) := by
  have h := checkLog_sound (w := (188561 / 2188561)) (n := 12)
    (lo := (172743331 / 1000000000)) (hi := (43185833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1188561 / 1000000) = 1/(1000000 / 1188561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (172743331 / 1000000000) (43185833 / 250000000) (Real.log (1188561 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1188561 / 1000000) = -Real.log (1000000 / 1188561) := by
    rw [show ((1188561 / 1000000) : ℝ) = ((1000000 / 1188561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (13059129 / 62500000) ≤ -Real.log (811439 / 1000000) ∧
    -Real.log (811439 / 1000000) ≤ (41789213 / 200000000) := by
  have h := checkLog_sound (w := (188561 / 1811439)) (n := 12)
    (lo := (13059129 / 62500000)) (hi := (41789213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 811439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 811439) = 1/(811439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-41789213 / 200000000) (-13059129 / 62500000) (Real.log (811439 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (385168409 / 500000000) ≤ -Real.log (25000000000 / 54012345679) ∧
    -Real.log (25000000000 / 54012345679) ≤ (38516841 / 50000000) := by
  have h := checkLog_sound (w := (4012345679 / 104012345679)) (n := 12)
    (lo := (38594819 / 500000000)) (hi := (77189639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54012345679 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(54012345679 / 50000000000) = 1/(25000000000 / 54012345679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (385168409 / 500000000) (38516841 / 50000000) (Real.log (54012345679 / 25000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (54012345679 / 25000000000) = -Real.log (25000000000 / 54012345679) := by
    rw [show ((54012345679 / 25000000000) : ℝ) = ((25000000000 / 54012345679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (771691653 / 1000000000) ≤ -Real.log (50000000000 / 108171146123) ∧
    -Real.log (50000000000 / 108171146123) ≤ (154338331 / 200000000) := by
  have h := checkLog_sound (w := (8171146123 / 208171146123)) (n := 12)
    (lo := (78544473 / 1000000000)) (hi := (39272237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108171146123 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(108171146123 / 100000000000) = 1/(50000000000 / 108171146123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (771691653 / 1000000000) (154338331 / 200000000) (Real.log (108171146123 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (108171146123 / 50000000000) = -Real.log (50000000000 / 108171146123) := by
    rw [show ((108171146123 / 50000000000) : ℝ) = ((50000000000 / 108171146123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (21390551 / 40000000) ≤ -Real.log (500000000000 / 853522474563) ∧
    -Real.log (500000000000 / 853522474563) ≤ (2088921 / 3906250) := by
  have h := checkLog_sound (w := (353522474563 / 1353522474563)) (n := 12)
    (lo := (21390551 / 40000000)) (hi := (2088921 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853522474563 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853522474563 / 500000000000) = 1/(500000000000 / 853522474563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21390551 / 40000000) (2088921 / 3906250) (Real.log (853522474563 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (853522474563 / 500000000000) = -Real.log (500000000000 / 853522474563) := by
    rw [show ((853522474563 / 500000000000) : ℝ) = ((500000000000 / 853522474563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (535671821 / 1000000000) ≤ -Real.log (500000000000 / 854297864273) ∧
    -Real.log (500000000000 / 854297864273) ≤ (267835911 / 500000000) := by
  have h := checkLog_sound (w := (354297864273 / 1354297864273)) (n := 12)
    (lo := (535671821 / 1000000000)) (hi := (267835911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854297864273 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(854297864273 / 500000000000) = 1/(500000000000 / 854297864273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (535671821 / 1000000000) (267835911 / 500000000) (Real.log (854297864273 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (854297864273 / 500000000000) = -Real.log (500000000000 / 854297864273) := by
    rw [show ((854297864273 / 500000000000) : ℝ) = ((500000000000 / 854297864273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (381032063 / 1000000000) ≤ -Real.log (250000000000 / 365948634811) ∧
    -Real.log (250000000000 / 365948634811) ≤ (2976813 / 7812500) := by
  have h := checkLog_sound (w := (115948634811 / 615948634811)) (n := 12)
    (lo := (381032063 / 1000000000)) (hi := (2976813 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365948634811 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365948634811 / 250000000000) = 1/(250000000000 / 365948634811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (381032063 / 1000000000) (2976813 / 7812500) (Real.log (365948634811 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (365948634811 / 250000000000) = -Real.log (250000000000 / 365948634811) := by
    rw [show ((365948634811 / 250000000000) : ℝ) = ((250000000000 / 365948634811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (76337879 / 200000000) ≤ -Real.log (50000000000 / 73237852753) ∧
    -Real.log (50000000000 / 73237852753) ≤ (95422349 / 250000000) := by
  have h := checkLog_sound (w := (23237852753 / 123237852753)) (n := 12)
    (lo := (76337879 / 200000000)) (hi := (95422349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73237852753 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73237852753 / 50000000000) = 1/(50000000000 / 73237852753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (76337879 / 200000000) (95422349 / 250000000) (Real.log (73237852753 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (73237852753 / 50000000000) = -Real.log (50000000000 / 73237852753) := by
    rw [show ((73237852753 / 50000000000) : ℝ) = ((50000000000 / 73237852753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9050683 / 250000000) ≤ -Real.log (964444749279 / 1000000000000) ∧
    -Real.log (964444749279 / 1000000000000) ≤ (36202733 / 1000000000) := by
  have h := checkLog_sound (w := (35555250721 / 1964444749279)) (n := 12)
    (lo := (9050683 / 250000000)) (hi := (36202733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964444749279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964444749279) = 1/(964444749279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-36202733 / 1000000000) (-9050683 / 250000000) (Real.log (964444749279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (36078889 / 1000000000) ≤ -Real.log (60285262279 / 62500000000) ∧
    -Real.log (60285262279 / 62500000000) ≤ (3607889 / 100000000) := by
  have h := checkLog_sound (w := (2214737721 / 122785262279)) (n := 12)
    (lo := (36078889 / 1000000000)) (hi := (3607889 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60285262279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60285262279) = 1/(60285262279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3607889 / 100000000) (-36078889 / 1000000000) (Real.log (60285262279 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell200

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell201Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell201
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

theorem reflection_log_1_neg : (62722497 / 200000000) ≤ -Real.log (2560 / 3503) ∧
    -Real.log (2560 / 3503) ≤ (156806243 / 500000000) := by
  have h := checkLog_sound (w := (943 / 6063)) (n := 12)
    (lo := (62722497 / 200000000)) (hi := (156806243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3503 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3503 / 2560) = 1/(2560 / 3503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (62722497 / 200000000) (156806243 / 500000000) (Real.log (3503 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3503 / 2560) = -Real.log (2560 / 3503) := by
    rw [show ((3503 / 2560) : ℝ) = ((2560 / 3503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (459434677 / 1000000000) ≤ -Real.log (1617 / 2560) ∧
    -Real.log (1617 / 2560) ≤ (229717339 / 500000000) := by
  have h := checkLog_sound (w := (943 / 4177)) (n := 12)
    (lo := (459434677 / 1000000000)) (hi := (229717339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1617) = 1/(1617 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-229717339 / 500000000) (-459434677 / 1000000000) (Real.log (1617 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (313184189 / 1000000000) ≤ -Real.log (5120 / 7003) ∧
    -Real.log (5120 / 7003) ≤ (31318419 / 100000000) := by
  have h := checkLog_sound (w := (1883 / 12123)) (n := 12)
    (lo := (313184189 / 1000000000)) (hi := (31318419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7003 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7003 / 5120) = 1/(5120 / 7003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (313184189 / 1000000000) (31318419 / 100000000) (Real.log (7003 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7003 / 5120) = -Real.log (5120 / 7003) := by
    rw [show ((7003 / 5120) : ℝ) = ((5120 / 7003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57313433 / 125000000) ≤ -Real.log (3237 / 5120) ∧
    -Real.log (3237 / 5120) ≤ (91701493 / 200000000) := by
  have h := checkLog_sound (w := (1883 / 8357)) (n := 12)
    (lo := (57313433 / 125000000)) (hi := (91701493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3237) = 1/(3237 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-91701493 / 200000000) (-57313433 / 125000000) (Real.log (3237 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23238789 / 100000000) ≤ -Real.log (1000000 / 1261609) ∧
    -Real.log (1000000 / 1261609) ≤ (232387891 / 1000000000) := by
  have h := checkLog_sound (w := (261609 / 2261609)) (n := 12)
    (lo := (23238789 / 100000000)) (hi := (232387891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261609 / 1000000) = 1/(1000000 / 1261609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23238789 / 100000000) (232387891 / 1000000000) (Real.log (1261609 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1261609 / 1000000) = -Real.log (1000000 / 1261609) := by
    rw [show ((1261609 / 1000000) : ℝ) = ((1000000 / 1261609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (37910223 / 125000000) ≤ -Real.log (738391 / 1000000) ∧
    -Real.log (738391 / 1000000) ≤ (60656357 / 200000000) := by
  have h := checkLog_sound (w := (261609 / 1738391)) (n := 12)
    (lo := (37910223 / 125000000)) (hi := (60656357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738391) = 1/(738391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-60656357 / 200000000) (-37910223 / 125000000) (Real.log (738391 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2909039 / 12500000) ≤ -Real.log (62500 / 78877) ∧
    -Real.log (62500 / 78877) ≤ (232723121 / 1000000000) := by
  have h := checkLog_sound (w := (16377 / 141377)) (n := 12)
    (lo := (2909039 / 12500000)) (hi := (232723121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78877 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78877 / 62500) = 1/(62500 / 78877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2909039 / 12500000) (232723121 / 1000000000) (Real.log (78877 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (78877 / 62500) = -Real.log (62500 / 78877) := by
    rw [show ((78877 / 62500) : ℝ) = ((62500 / 78877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (60770963 / 200000000) ≤ -Real.log (46123 / 62500) ∧
    -Real.log (46123 / 62500) ≤ (9495463 / 31250000) := by
  have h := checkLog_sound (w := (16377 / 108623)) (n := 12)
    (lo := (60770963 / 200000000)) (hi := (9495463 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46123) = 1/(46123 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9495463 / 31250000) (-60770963 / 200000000) (Real.log (46123 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17274249 / 100000000) ≤ -Real.log (12500 / 14857) ∧
    -Real.log (12500 / 14857) ≤ (172742491 / 1000000000) := by
  have h := checkLog_sound (w := (2357 / 27357)) (n := 12)
    (lo := (17274249 / 100000000)) (hi := (172742491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14857 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14857 / 12500) = 1/(12500 / 14857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17274249 / 100000000) (172742491 / 1000000000) (Real.log (14857 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (14857 / 12500) = -Real.log (12500 / 14857) := by
    rw [show ((14857 / 12500) : ℝ) = ((12500 / 14857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (208944831 / 1000000000) ≤ -Real.log (10143 / 12500) ∧
    -Real.log (10143 / 12500) ≤ (3264763 / 15625000) := by
  have h := checkLog_sound (w := (2357 / 22643)) (n := 12)
    (lo := (208944831 / 1000000000)) (hi := (3264763 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 10143) = 1/(10143 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3264763 / 15625000) (-208944831 / 1000000000) (Real.log (10143 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (43252291 / 250000000) ≤ -Real.log (1000000 / 1188877) ∧
    -Real.log (1000000 / 1188877) ≤ (34601833 / 200000000) := by
  have h := checkLog_sound (w := (188877 / 2188877)) (n := 12)
    (lo := (43252291 / 250000000)) (hi := (34601833 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188877 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1188877 / 1000000) = 1/(1000000 / 1188877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (43252291 / 250000000) (34601833 / 200000000) (Real.log (1188877 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1188877 / 1000000) = -Real.log (1000000 / 1188877) := by
    rw [show ((1188877 / 1000000) : ℝ) = ((1000000 / 1188877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (209335571 / 1000000000) ≤ -Real.log (811123 / 1000000) ∧
    -Real.log (811123 / 1000000) ≤ (52333893 / 250000000) := by
  have h := checkLog_sound (w := (188877 / 1811123)) (n := 12)
    (lo := (209335571 / 1000000000)) (hi := (52333893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 811123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 811123) = 1/(811123 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-52333893 / 250000000) (-209335571 / 1000000000) (Real.log (811123 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (771691653 / 1000000000) ≤ -Real.log (500000000000 / 1081711461229) ∧
    -Real.log (500000000000 / 1081711461229) ≤ (154338331 / 200000000) := by
  have h := checkLog_sound (w := (81711461229 / 2081711461229)) (n := 12)
    (lo := (78544473 / 1000000000)) (hi := (39272237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081711461229 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1081711461229 / 1000000000000) = 1/(500000000000 / 1081711461229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (771691653 / 1000000000) (154338331 / 200000000) (Real.log (1081711461229 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1081711461229 / 500000000000) = -Real.log (500000000000 / 1081711461229) := by
    rw [show ((1081711461229 / 500000000000) : ℝ) = ((500000000000 / 1081711461229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (773047163 / 1000000000) ≤ -Real.log (125000000000 / 270794681509) ∧
    -Real.log (125000000000 / 270794681509) ≤ (154609433 / 200000000) := by
  have h := checkLog_sound (w := (20794681509 / 520794681509)) (n := 12)
    (lo := (79899983 / 1000000000)) (hi := (4993749 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270794681509 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(270794681509 / 250000000000) = 1/(125000000000 / 270794681509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (773047163 / 1000000000) (154609433 / 200000000) (Real.log (270794681509 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (270794681509 / 125000000000) = -Real.log (125000000000 / 270794681509) := by
    rw [show ((270794681509 / 125000000000) : ℝ) = ((125000000000 / 270794681509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (267834837 / 500000000) ≤ -Real.log (62500000000 / 106787003769) ∧
    -Real.log (62500000000 / 106787003769) ≤ (21426787 / 40000000) := by
  have h := checkLog_sound (w := (44287003769 / 169287003769)) (n := 12)
    (lo := (267834837 / 500000000)) (hi := (21426787 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106787003769 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106787003769 / 62500000000) = 1/(62500000000 / 106787003769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (267834837 / 500000000) (21426787 / 40000000) (Real.log (106787003769 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (106787003769 / 62500000000) = -Real.log (62500000000 / 106787003769) := by
    rw [show ((106787003769 / 62500000000) : ℝ) = ((62500000000 / 106787003769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (33536121 / 62500000) ≤ -Real.log (500000000000 / 855072306659) ∧
    -Real.log (500000000000 / 855072306659) ≤ (536577937 / 1000000000) := by
  have h := checkLog_sound (w := (355072306659 / 1355072306659)) (n := 12)
    (lo := (33536121 / 62500000)) (hi := (536577937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855072306659 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855072306659 / 500000000000) = 1/(500000000000 / 855072306659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (33536121 / 62500000) (536577937 / 1000000000) (Real.log (855072306659 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (855072306659 / 500000000000) = -Real.log (500000000000 / 855072306659) := by
    rw [show ((855072306659 / 500000000000) : ℝ) = ((500000000000 / 855072306659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (190843661 / 500000000) ≤ -Real.log (250000000000 / 366188504387) ∧
    -Real.log (250000000000 / 366188504387) ≤ (381687323 / 1000000000) := by
  have h := checkLog_sound (w := (116188504387 / 616188504387)) (n := 12)
    (lo := (190843661 / 500000000)) (hi := (381687323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366188504387 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366188504387 / 250000000000) = 1/(250000000000 / 366188504387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (190843661 / 500000000) (381687323 / 1000000000) (Real.log (366188504387 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (366188504387 / 250000000000) = -Real.log (250000000000 / 366188504387) := by
    rw [show ((366188504387 / 250000000000) : ℝ) = ((250000000000 / 366188504387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (76468947 / 200000000) ≤ -Real.log (250000000000 / 366429320831) ∧
    -Real.log (250000000000 / 366429320831) ≤ (11948273 / 31250000) := by
  have h := checkLog_sound (w := (116429320831 / 616429320831)) (n := 12)
    (lo := (76468947 / 200000000)) (hi := (11948273 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366429320831 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366429320831 / 250000000000) = 1/(250000000000 / 366429320831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (76468947 / 200000000) (11948273 / 31250000) (Real.log (366429320831 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (366429320831 / 250000000000) = -Real.log (250000000000 / 366429320831) := by
    rw [show ((366429320831 / 250000000000) : ℝ) = ((250000000000 / 366429320831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (36326407 / 1000000000) ≤ -Real.log (964325478871 / 1000000000000) ∧
    -Real.log (964325478871 / 1000000000000) ≤ (4540801 / 125000000) := by
  have h := checkLog_sound (w := (35674521129 / 1964325478871)) (n := 12)
    (lo := (36326407 / 1000000000)) (hi := (4540801 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964325478871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964325478871) = 1/(964325478871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4540801 / 125000000) (-36326407 / 1000000000) (Real.log (964325478871 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (36202341 / 1000000000) ≤ -Real.log (150694551 / 156250000) ∧
    -Real.log (150694551 / 156250000) ≤ (18101171 / 500000000) := by
  have h := checkLog_sound (w := (5555449 / 306944551)) (n := 12)
    (lo := (36202341 / 1000000000)) (hi := (18101171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 150694551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 150694551) = 1/(150694551 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18101171 / 500000000) (-36202341 / 1000000000) (Real.log (150694551 / 156250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell201

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell202Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell202
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

theorem reflection_log_1_neg : (157020299 / 500000000) ≤ -Real.log (5120 / 7009) ∧
    -Real.log (5120 / 7009) ≤ (314040599 / 1000000000) := by
  have h := checkLog_sound (w := (1889 / 12129)) (n := 12)
    (lo := (157020299 / 500000000)) (hi := (314040599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7009 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7009 / 5120) = 1/(5120 / 7009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (157020299 / 500000000) (314040599 / 1000000000) (Real.log (7009 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7009 / 5120) = -Real.log (5120 / 7009) := by
    rw [show ((7009 / 5120) : ℝ) = ((5120 / 7009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (899146 / 1953125) ≤ -Real.log (3231 / 5120) ∧
    -Real.log (3231 / 5120) ≤ (460362753 / 1000000000) := by
  have h := checkLog_sound (w := (1889 / 8351)) (n := 12)
    (lo := (899146 / 1953125)) (hi := (460362753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3231) = 1/(3231 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-460362753 / 1000000000) (-899146 / 1953125) (Real.log (3231 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (62722497 / 200000000) ≤ -Real.log (2560 / 3503) ∧
    -Real.log (2560 / 3503) ≤ (156806243 / 500000000) := by
  have h := checkLog_sound (w := (943 / 6063)) (n := 12)
    (lo := (62722497 / 200000000)) (hi := (156806243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3503 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3503 / 2560) = 1/(2560 / 3503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (62722497 / 200000000) (156806243 / 500000000) (Real.log (3503 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3503 / 2560) = -Real.log (2560 / 3503) := by
    rw [show ((3503 / 2560) : ℝ) = ((2560 / 3503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (459434677 / 1000000000) ≤ -Real.log (1617 / 2560) ∧
    -Real.log (1617 / 2560) ≤ (229717339 / 500000000) := by
  have h := checkLog_sound (w := (943 / 4177)) (n := 12)
    (lo := (459434677 / 1000000000)) (hi := (229717339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1617) = 1/(1617 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-229717339 / 500000000) (-459434677 / 1000000000) (Real.log (1617 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (29090291 / 125000000) ≤ -Real.log (1000000 / 1262031) ∧
    -Real.log (1000000 / 1262031) ≤ (232722329 / 1000000000) := by
  have h := checkLog_sound (w := (262031 / 2262031)) (n := 12)
    (lo := (29090291 / 125000000)) (hi := (232722329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1262031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1262031 / 1000000) = 1/(1000000 / 1262031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (29090291 / 125000000) (232722329 / 1000000000) (Real.log (1262031 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1262031 / 1000000) = -Real.log (1000000 / 1262031) := by
    rw [show ((1262031 / 1000000) : ℝ) = ((1000000 / 1262031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (15192673 / 50000000) ≤ -Real.log (737969 / 1000000) ∧
    -Real.log (737969 / 1000000) ≤ (303853461 / 1000000000) := by
  have h := checkLog_sound (w := (262031 / 1737969)) (n := 12)
    (lo := (15192673 / 50000000)) (hi := (303853461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 737969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 737969) = 1/(737969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-303853461 / 1000000000) (-15192673 / 50000000) (Real.log (737969 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (46611489 / 200000000) ≤ -Real.log (500000 / 631227) ∧
    -Real.log (500000 / 631227) ≤ (116528723 / 500000000) := by
  have h := checkLog_sound (w := (131227 / 1131227)) (n := 12)
    (lo := (46611489 / 200000000)) (hi := (116528723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631227 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631227 / 500000) = 1/(500000 / 631227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (46611489 / 200000000) (116528723 / 500000000) (Real.log (631227 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (631227 / 500000) = -Real.log (500000 / 631227) := by
    rw [show ((631227 / 500000) : ℝ) = ((500000 / 631227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (304426819 / 1000000000) ≤ -Real.log (368773 / 500000) ∧
    -Real.log (368773 / 500000) ≤ (15221341 / 50000000) := by
  have h := checkLog_sound (w := (131227 / 868773)) (n := 12)
    (lo := (304426819 / 1000000000)) (hi := (15221341 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 368773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 368773) = 1/(368773 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-15221341 / 50000000) (-304426819 / 1000000000) (Real.log (368773 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (86504161 / 500000000) ≤ -Real.log (250000 / 297219) ∧
    -Real.log (250000 / 297219) ≤ (173008323 / 1000000000) := by
  have h := checkLog_sound (w := (47219 / 547219)) (n := 12)
    (lo := (86504161 / 500000000)) (hi := (173008323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297219 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297219 / 250000) = 1/(250000 / 297219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (86504161 / 500000000) (173008323 / 1000000000) (Real.log (297219 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (297219 / 250000) = -Real.log (250000 / 297219) := by
    rw [show ((297219 / 250000) : ℝ) = ((250000 / 297219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (104667169 / 500000000) ≤ -Real.log (202781 / 250000) ∧
    -Real.log (202781 / 250000) ≤ (209334339 / 1000000000) := by
  have h := checkLog_sound (w := (47219 / 452781)) (n := 12)
    (lo := (104667169 / 500000000)) (hi := (209334339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202781) = 1/(202781 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-209334339 / 1000000000) (-104667169 / 500000000) (Real.log (202781 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (6930997 / 40000000) ≤ -Real.log (1000000 / 1189193) ∧
    -Real.log (1000000 / 1189193) ≤ (86637463 / 500000000) := by
  have h := checkLog_sound (w := (189193 / 2189193)) (n := 12)
    (lo := (6930997 / 40000000)) (hi := (86637463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189193 / 1000000) = 1/(1000000 / 1189193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (6930997 / 40000000) (86637463 / 500000000) (Real.log (1189193 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1189193 / 1000000) = -Real.log (1000000 / 1189193) := by
    rw [show ((1189193 / 1000000) : ℝ) = ((1000000 / 1189193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (20972523 / 100000000) ≤ -Real.log (810807 / 1000000) ∧
    -Real.log (810807 / 1000000) ≤ (209725231 / 1000000000) := by
  have h := checkLog_sound (w := (189193 / 1810807)) (n := 12)
    (lo := (20972523 / 100000000)) (hi := (209725231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810807) = 1/(810807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-209725231 / 1000000000) (-20972523 / 100000000) (Real.log (810807 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (773047163 / 1000000000) ≤ -Real.log (100000000000 / 216635745207) ∧
    -Real.log (100000000000 / 216635745207) ≤ (154609433 / 200000000) := by
  have h := checkLog_sound (w := (16635745207 / 416635745207)) (n := 12)
    (lo := (79899983 / 1000000000)) (hi := (4993749 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216635745207 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(216635745207 / 200000000000) = 1/(100000000000 / 216635745207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (773047163 / 1000000000) (154609433 / 200000000) (Real.log (216635745207 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (216635745207 / 100000000000) = -Real.log (100000000000 / 216635745207) := by
    rw [show ((216635745207 / 100000000000) : ℝ) = ((100000000000 / 216635745207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (15488067 / 20000000) ≤ -Real.log (31250000000 / 67790544723) ∧
    -Real.log (31250000000 / 67790544723) ≤ (96800419 / 125000000) := by
  have h := checkLog_sound (w := (5290544723 / 130290544723)) (n := 12)
    (lo := (8125617 / 100000000)) (hi := (81256171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67790544723 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(67790544723 / 62500000000) = 1/(31250000000 / 67790544723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (15488067 / 20000000) (96800419 / 125000000) (Real.log (67790544723 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (67790544723 / 31250000000) = -Real.log (31250000000 / 67790544723) := by
    rw [show ((67790544723 / 31250000000) : ℝ) = ((31250000000 / 67790544723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (134143947 / 250000000) ≤ -Real.log (500000000000 / 855070470439) ∧
    -Real.log (500000000000 / 855070470439) ≤ (536575789 / 1000000000) := by
  have h := checkLog_sound (w := (355070470439 / 1355070470439)) (n := 12)
    (lo := (134143947 / 250000000)) (hi := (536575789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855070470439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855070470439 / 500000000000) = 1/(500000000000 / 855070470439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (134143947 / 250000000) (536575789 / 1000000000) (Real.log (855070470439 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (855070470439 / 500000000000) = -Real.log (500000000000 / 855070470439) := by
    rw [show ((855070470439 / 500000000000) : ℝ) = ((500000000000 / 855070470439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (107496853 / 200000000) ≤ -Real.log (500000000000 / 855847635267) ∧
    -Real.log (500000000000 / 855847635267) ≤ (268742133 / 500000000) := by
  have h := checkLog_sound (w := (355847635267 / 1355847635267)) (n := 12)
    (lo := (107496853 / 200000000)) (hi := (268742133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855847635267 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855847635267 / 500000000000) = 1/(500000000000 / 855847635267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (107496853 / 200000000) (268742133 / 500000000) (Real.log (855847635267 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (855847635267 / 500000000000) = -Real.log (500000000000 / 855847635267) := by
    rw [show ((855847635267 / 500000000000) : ℝ) = ((500000000000 / 855847635267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (382342661 / 1000000000) ≤ -Real.log (250000000000 / 366428560861) ∧
    -Real.log (250000000000 / 366428560861) ≤ (191171331 / 500000000) := by
  have h := checkLog_sound (w := (116428560861 / 616428560861)) (n := 12)
    (lo := (382342661 / 1000000000)) (hi := (191171331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366428560861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366428560861 / 250000000000) = 1/(250000000000 / 366428560861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (382342661 / 1000000000) (191171331 / 500000000) (Real.log (366428560861 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (366428560861 / 250000000000) = -Real.log (250000000000 / 366428560861) := by
    rw [show ((366428560861 / 250000000000) : ℝ) = ((250000000000 / 366428560861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (95750039 / 250000000) ≤ -Real.log (125000000000 / 183334782507) ∧
    -Real.log (125000000000 / 183334782507) ≤ (383000157 / 1000000000) := by
  have h := checkLog_sound (w := (58334782507 / 308334782507)) (n := 12)
    (lo := (95750039 / 250000000)) (hi := (383000157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183334782507 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183334782507 / 125000000000) = 1/(125000000000 / 183334782507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (95750039 / 250000000) (383000157 / 1000000000) (Real.log (183334782507 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (183334782507 / 125000000000) = -Real.log (125000000000 / 183334782507) := by
    rw [show ((183334782507 / 125000000000) : ℝ) = ((125000000000 / 183334782507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7290061 / 200000000) ≤ -Real.log (964206008751 / 1000000000000) ∧
    -Real.log (964206008751 / 1000000000000) ≤ (18225153 / 500000000) := by
  have h := checkLog_sound (w := (35793991249 / 1964206008751)) (n := 12)
    (lo := (7290061 / 200000000)) (hi := (18225153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964206008751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964206008751) = 1/(964206008751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18225153 / 500000000) (-7290061 / 200000000) (Real.log (964206008751 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7265203 / 200000000) ≤ -Real.log (60270366039 / 62500000000) ∧
    -Real.log (60270366039 / 62500000000) ≤ (283797 / 7812500) := by
  have h := checkLog_sound (w := (2229633961 / 122770366039)) (n := 12)
    (lo := (7265203 / 200000000)) (hi := (283797 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60270366039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60270366039) = 1/(60270366039 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-283797 / 7812500) (-7265203 / 200000000) (Real.log (60270366039 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell202

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell203Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell203
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

theorem reflection_log_1_neg : (19654283 / 62500000) ≤ -Real.log (1280 / 1753) ∧
    -Real.log (1280 / 1753) ≤ (314468529 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 3033)) (n := 12)
    (lo := (19654283 / 62500000)) (hi := (314468529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1753 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1753 / 1280) = 1/(1280 / 1753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (19654283 / 62500000) (314468529 / 1000000000) (Real.log (1753 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1753 / 1280) = -Real.log (1280 / 1753) := by
    rw [show ((1753 / 1280) : ℝ) = ((1280 / 1753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57661461 / 125000000) ≤ -Real.log (807 / 1280) ∧
    -Real.log (807 / 1280) ≤ (461291689 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 2087)) (n := 12)
    (lo := (57661461 / 125000000)) (hi := (461291689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 807) = 1/(807 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-461291689 / 1000000000) (-57661461 / 125000000) (Real.log (807 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (157020299 / 500000000) ≤ -Real.log (5120 / 7009) ∧
    -Real.log (5120 / 7009) ≤ (314040599 / 1000000000) := by
  have h := checkLog_sound (w := (1889 / 12129)) (n := 12)
    (lo := (157020299 / 500000000)) (hi := (314040599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7009 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7009 / 5120) = 1/(5120 / 7009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (157020299 / 500000000) (314040599 / 1000000000) (Real.log (7009 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7009 / 5120) = -Real.log (5120 / 7009) := by
    rw [show ((7009 / 5120) : ℝ) = ((5120 / 7009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (899146 / 1953125) ≤ -Real.log (3231 / 5120) ∧
    -Real.log (3231 / 5120) ≤ (460362753 / 1000000000) := by
  have h := checkLog_sound (w := (1889 / 8351)) (n := 12)
    (lo := (899146 / 1953125)) (hi := (460362753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3231) = 1/(3231 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-460362753 / 1000000000) (-899146 / 1953125) (Real.log (3231 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (233056653 / 1000000000) ≤ -Real.log (1000000 / 1262453) ∧
    -Real.log (1000000 / 1262453) ≤ (116528327 / 500000000) := by
  have h := checkLog_sound (w := (262453 / 2262453)) (n := 12)
    (lo := (233056653 / 1000000000)) (hi := (116528327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1262453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1262453 / 1000000) = 1/(1000000 / 1262453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (233056653 / 1000000000) (116528327 / 500000000) (Real.log (1262453 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1262453 / 1000000) = -Real.log (1000000 / 1262453) := by
    rw [show ((1262453 / 1000000) : ℝ) = ((1000000 / 1262453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (304425463 / 1000000000) ≤ -Real.log (737547 / 1000000) ∧
    -Real.log (737547 / 1000000) ≤ (38053183 / 125000000) := by
  have h := checkLog_sound (w := (262453 / 1737547)) (n := 12)
    (lo := (304425463 / 1000000000)) (hi := (38053183 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 737547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 737547) = 1/(737547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-38053183 / 125000000) (-304425463 / 1000000000) (Real.log (737547 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (233391659 / 1000000000) ≤ -Real.log (250000 / 315719) ∧
    -Real.log (250000 / 315719) ≤ (11669583 / 50000000) := by
  have h := checkLog_sound (w := (65719 / 565719)) (n := 12)
    (lo := (233391659 / 1000000000)) (hi := (11669583 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315719 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315719 / 250000) = 1/(250000 / 315719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (233391659 / 1000000000) (11669583 / 50000000) (Real.log (315719 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (315719 / 250000) = -Real.log (250000 / 315719) := by
    rw [show ((315719 / 250000) : ℝ) = ((250000 / 315719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (304999151 / 1000000000) ≤ -Real.log (184281 / 250000) ∧
    -Real.log (184281 / 250000) ≤ (19062447 / 62500000) := by
  have h := checkLog_sound (w := (65719 / 434281)) (n := 12)
    (lo := (304999151 / 1000000000)) (hi := (19062447 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 184281) = 1/(184281 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-19062447 / 62500000) (-304999151 / 1000000000) (Real.log (184281 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (43318521 / 250000000) ≤ -Real.log (125000 / 148649) ∧
    -Real.log (125000 / 148649) ≤ (34654817 / 200000000) := by
  have h := checkLog_sound (w := (23649 / 273649)) (n := 12)
    (lo := (43318521 / 250000000)) (hi := (34654817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148649 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148649 / 125000) = 1/(125000 / 148649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (43318521 / 250000000) (34654817 / 200000000) (Real.log (148649 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (148649 / 125000) = -Real.log (125000 / 148649) := by
    rw [show ((148649 / 125000) : ℝ) = ((125000 / 148649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (209723997 / 1000000000) ≤ -Real.log (101351 / 125000) ∧
    -Real.log (101351 / 125000) ≤ (104861999 / 500000000) := by
  have h := checkLog_sound (w := (23649 / 226351)) (n := 12)
    (lo := (209723997 / 1000000000)) (hi := (104861999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 101351) = 1/(101351 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-104861999 / 500000000) (-209723997 / 1000000000) (Real.log (101351 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (21692577 / 125000000) ≤ -Real.log (1000000 / 1189509) ∧
    -Real.log (1000000 / 1189509) ≤ (173540617 / 1000000000) := by
  have h := checkLog_sound (w := (189509 / 2189509)) (n := 12)
    (lo := (21692577 / 125000000)) (hi := (173540617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189509 / 1000000) = 1/(1000000 / 1189509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (21692577 / 125000000) (173540617 / 1000000000) (Real.log (1189509 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1189509 / 1000000) = -Real.log (1000000 / 1189509) := by
    rw [show ((1189509 / 1000000) : ℝ) = ((1000000 / 1189509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (105057521 / 500000000) ≤ -Real.log (810491 / 1000000) ∧
    -Real.log (810491 / 1000000) ≤ (210115043 / 1000000000) := by
  have h := checkLog_sound (w := (189509 / 1810491)) (n := 12)
    (lo := (105057521 / 500000000)) (hi := (210115043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810491) = 1/(810491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-210115043 / 1000000000) (-105057521 / 500000000) (Real.log (810491 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (15488067 / 20000000) ≤ -Real.log (500000000000 / 1084648715567) ∧
    -Real.log (500000000000 / 1084648715567) ≤ (96800419 / 125000000) := by
  have h := checkLog_sound (w := (84648715567 / 2084648715567)) (n := 12)
    (lo := (8125617 / 100000000)) (hi := (81256171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084648715567 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1084648715567 / 1000000000000) = 1/(500000000000 / 1084648715567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (15488067 / 20000000) (96800419 / 125000000) (Real.log (1084648715567 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1084648715567 / 500000000000) = -Real.log (500000000000 / 1084648715567) := by
    rw [show ((1084648715567 / 500000000000) : ℝ) = ((500000000000 / 1084648715567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (96970027 / 125000000) ≤ -Real.log (500000000000 / 1086121437423) ∧
    -Real.log (500000000000 / 1086121437423) ≤ (387880109 / 500000000) := by
  have h := checkLog_sound (w := (86121437423 / 2086121437423)) (n := 12)
    (lo := (20653259 / 250000000)) (hi := (82613037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086121437423 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1086121437423 / 1000000000000) = 1/(500000000000 / 1086121437423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (96970027 / 125000000) (387880109 / 500000000) (Real.log (1086121437423 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1086121437423 / 500000000000) = -Real.log (500000000000 / 1086121437423) := by
    rw [show ((1086121437423 / 500000000000) : ℝ) = ((500000000000 / 1086121437423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (537482117 / 1000000000) ≤ -Real.log (100000000000 / 171169159389) ∧
    -Real.log (100000000000 / 171169159389) ≤ (268741059 / 500000000) := by
  have h := checkLog_sound (w := (71169159389 / 271169159389)) (n := 12)
    (lo := (537482117 / 1000000000)) (hi := (268741059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171169159389 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171169159389 / 100000000000) = 1/(100000000000 / 171169159389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (537482117 / 1000000000) (268741059 / 500000000) (Real.log (171169159389 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (171169159389 / 100000000000) = -Real.log (100000000000 / 171169159389) := by
    rw [show ((171169159389 / 100000000000) : ℝ) = ((100000000000 / 171169159389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53839081 / 100000000) ≤ -Real.log (250000000000 / 428311925809) ∧
    -Real.log (250000000000 / 428311925809) ≤ (538390811 / 1000000000) := by
  have h := checkLog_sound (w := (178311925809 / 678311925809)) (n := 12)
    (lo := (53839081 / 100000000)) (hi := (538390811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((428311925809 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(428311925809 / 250000000000) = 1/(250000000000 / 428311925809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (53839081 / 100000000) (538390811 / 1000000000) (Real.log (428311925809 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (428311925809 / 250000000000) = -Real.log (250000000000 / 428311925809) := by
    rw [show ((428311925809 / 250000000000) : ℝ) = ((250000000000 / 428311925809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (191499041 / 500000000) ≤ -Real.log (500000000000 / 733337608903) ∧
    -Real.log (500000000000 / 733337608903) ≤ (382998083 / 1000000000) := by
  have h := checkLog_sound (w := (233337608903 / 1233337608903)) (n := 12)
    (lo := (191499041 / 500000000)) (hi := (382998083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733337608903 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733337608903 / 500000000000) = 1/(500000000000 / 733337608903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (191499041 / 500000000) (382998083 / 1000000000) (Real.log (733337608903 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (733337608903 / 500000000000) = -Real.log (500000000000 / 733337608903) := by
    rw [show ((733337608903 / 500000000000) : ℝ) = ((500000000000 / 733337608903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (383655659 / 1000000000) ≤ -Real.log (250000000000 / 366909996533) ∧
    -Real.log (250000000000 / 366909996533) ≤ (19182783 / 50000000) := by
  have h := checkLog_sound (w := (116909996533 / 616909996533)) (n := 12)
    (lo := (383655659 / 1000000000)) (hi := (19182783 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366909996533 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366909996533 / 250000000000) = 1/(250000000000 / 366909996533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (383655659 / 1000000000) (19182783 / 50000000) (Real.log (366909996533 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (366909996533 / 250000000000) = -Real.log (250000000000 / 366909996533) := by
    rw [show ((366909996533 / 250000000000) : ℝ) = ((250000000000 / 366909996533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1462977 / 40000000) ≤ -Real.log (964086338919 / 1000000000000) ∧
    -Real.log (964086338919 / 1000000000000) ≤ (18287213 / 500000000) := by
  have h := checkLog_sound (w := (35913661081 / 1964086338919)) (n := 12)
    (lo := (1462977 / 40000000)) (hi := (18287213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964086338919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964086338919) = 1/(964086338919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18287213 / 500000000) (-1462977 / 40000000) (Real.log (964086338919 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4556239 / 125000000) ≤ -Real.log (15065724799 / 15625000000) ∧
    -Real.log (15065724799 / 15625000000) ≤ (36449913 / 1000000000) := by
  have h := checkLog_sound (w := (559275201 / 30690724799)) (n := 12)
    (lo := (4556239 / 125000000)) (hi := (36449913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15065724799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15065724799) = 1/(15065724799 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-36449913 / 1000000000) (-4556239 / 125000000) (Real.log (15065724799 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell203

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell204Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell204
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

theorem reflection_log_1_neg : (157448137 / 500000000) ≤ -Real.log (1024 / 1403) ∧
    -Real.log (1024 / 1403) ≤ (12595851 / 40000000) := by
  have h := checkLog_sound (w := (379 / 2427)) (n := 12)
    (lo := (157448137 / 500000000)) (hi := (12595851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1403 / 1024) = 1/(1024 / 1403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (157448137 / 500000000) (12595851 / 40000000) (Real.log (1403 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1403 / 1024) = -Real.log (1024 / 1403) := by
    rw [show ((1403 / 1024) : ℝ) = ((1024 / 1403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (28888843 / 62500000) ≤ -Real.log (645 / 1024) ∧
    -Real.log (645 / 1024) ≤ (462221489 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 1669)) (n := 12)
    (lo := (28888843 / 62500000)) (hi := (462221489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 645) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 645) = 1/(645 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-462221489 / 1000000000) (-28888843 / 62500000) (Real.log (645 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (19654283 / 62500000) ≤ -Real.log (1280 / 1753) ∧
    -Real.log (1280 / 1753) ≤ (314468529 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 3033)) (n := 12)
    (lo := (19654283 / 62500000)) (hi := (314468529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1753 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1753 / 1280) = 1/(1280 / 1753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (19654283 / 62500000) (314468529 / 1000000000) (Real.log (1753 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1753 / 1280) = -Real.log (1280 / 1753) := by
    rw [show ((1753 / 1280) : ℝ) = ((1280 / 1753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57661461 / 125000000) ≤ -Real.log (807 / 1280) ∧
    -Real.log (807 / 1280) ≤ (461291689 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 2087)) (n := 12)
    (lo := (57661461 / 125000000)) (hi := (461291689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 807) = 1/(807 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-461291689 / 1000000000) (-57661461 / 125000000) (Real.log (807 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (233390867 / 1000000000) ≤ -Real.log (8000 / 10103) ∧
    -Real.log (8000 / 10103) ≤ (58347717 / 250000000) := by
  have h := checkLog_sound (w := (2103 / 18103)) (n := 12)
    (lo := (233390867 / 1000000000)) (hi := (58347717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10103 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10103 / 8000) = 1/(8000 / 10103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (233390867 / 1000000000) (58347717 / 250000000) (Real.log (10103 / 8000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (10103 / 8000) = -Real.log (8000 / 10103) := by
    rw [show ((10103 / 8000) : ℝ) = ((8000 / 10103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (152498897 / 500000000) ≤ -Real.log (5897 / 8000) ∧
    -Real.log (5897 / 8000) ≤ (60999559 / 200000000) := by
  have h := checkLog_sound (w := (2103 / 13897)) (n := 12)
    (lo := (152498897 / 500000000)) (hi := (60999559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5897) = 1/(5897 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-60999559 / 200000000) (-152498897 / 500000000) (Real.log (5897 / 8000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (233725761 / 1000000000) ≤ -Real.log (500000 / 631649) ∧
    -Real.log (500000 / 631649) ≤ (116862881 / 500000000) := by
  have h := checkLog_sound (w := (131649 / 1131649)) (n := 12)
    (lo := (233725761 / 1000000000)) (hi := (116862881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631649 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631649 / 500000) = 1/(500000 / 631649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (233725761 / 1000000000) (116862881 / 500000000) (Real.log (631649 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (631649 / 500000) = -Real.log (500000 / 631649) := by
    rw [show ((631649 / 500000) : ℝ) = ((500000 / 631649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (30557181 / 100000000) ≤ -Real.log (368351 / 500000) ∧
    -Real.log (368351 / 500000) ≤ (305571811 / 1000000000) := by
  have h := checkLog_sound (w := (131649 / 868351)) (n := 12)
    (lo := (30557181 / 100000000)) (hi := (305571811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 368351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 368351) = 1/(368351 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-305571811 / 1000000000) (-30557181 / 100000000) (Real.log (368351 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2711559 / 15625000) ≤ -Real.log (250000 / 297377) ∧
    -Real.log (250000 / 297377) ≤ (173539777 / 1000000000) := by
  have h := checkLog_sound (w := (47377 / 547377)) (n := 12)
    (lo := (2711559 / 15625000)) (hi := (173539777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297377 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297377 / 250000) = 1/(250000 / 297377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2711559 / 15625000) (173539777 / 1000000000) (Real.log (297377 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (297377 / 250000) = -Real.log (250000 / 297377) := by
    rw [show ((297377 / 250000) : ℝ) = ((250000 / 297377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (13132113 / 62500000) ≤ -Real.log (202623 / 250000) ∧
    -Real.log (202623 / 250000) ≤ (210113809 / 1000000000) := by
  have h := checkLog_sound (w := (47377 / 452623)) (n := 12)
    (lo := (13132113 / 62500000)) (hi := (210113809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202623) = 1/(202623 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-210113809 / 1000000000) (-13132113 / 62500000) (Real.log (202623 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (173806237 / 1000000000) ≤ -Real.log (40000 / 47593) ∧
    -Real.log (40000 / 47593) ≤ (86903119 / 500000000) := by
  have h := checkLog_sound (w := (7593 / 87593)) (n := 12)
    (lo := (173806237 / 1000000000)) (hi := (86903119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47593 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47593 / 40000) = 1/(40000 / 47593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (173806237 / 1000000000) (86903119 / 500000000) (Real.log (47593 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (47593 / 40000) = -Real.log (40000 / 47593) := by
    rw [show ((47593 / 40000) : ℝ) = ((40000 / 47593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (42101001 / 200000000) ≤ -Real.log (32407 / 40000) ∧
    -Real.log (32407 / 40000) ≤ (105252503 / 500000000) := by
  have h := checkLog_sound (w := (7593 / 72407)) (n := 12)
    (lo := (42101001 / 200000000)) (hi := (105252503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32407) = 1/(32407 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-105252503 / 500000000) (-42101001 / 200000000) (Real.log (32407 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (96970027 / 125000000) ≤ -Real.log (250000000000 / 543060718711) ∧
    -Real.log (250000000000 / 543060718711) ≤ (387880109 / 500000000) := by
  have h := checkLog_sound (w := (43060718711 / 1043060718711)) (n := 12)
    (lo := (20653259 / 250000000)) (hi := (82613037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543060718711 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(543060718711 / 500000000000) = 1/(250000000000 / 543060718711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (96970027 / 125000000) (387880109 / 500000000) (Real.log (543060718711 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (543060718711 / 250000000000) = -Real.log (250000000000 / 543060718711) := by
    rw [show ((543060718711 / 250000000000) : ℝ) = ((250000000000 / 543060718711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (388558881 / 500000000) ≤ -Real.log (20000000000 / 43503875969) ∧
    -Real.log (20000000000 / 43503875969) ≤ (194279441 / 250000000) := by
  have h := checkLog_sound (w := (3503875969 / 83503875969)) (n := 12)
    (lo := (41985291 / 500000000)) (hi := (83970583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43503875969 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(43503875969 / 40000000000) = 1/(20000000000 / 43503875969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (388558881 / 500000000) (194279441 / 250000000) (Real.log (43503875969 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (43503875969 / 20000000000) = -Real.log (20000000000 / 43503875969) := by
    rw [show ((43503875969 / 20000000000) : ℝ) = ((20000000000 / 43503875969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (269194331 / 500000000) ≤ -Real.log (62500000000 / 107077751399) ∧
    -Real.log (62500000000 / 107077751399) ≤ (538388663 / 1000000000) := by
  have h := checkLog_sound (w := (44577751399 / 169577751399)) (n := 12)
    (lo := (269194331 / 500000000)) (hi := (538388663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107077751399 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107077751399 / 62500000000) = 1/(62500000000 / 107077751399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (269194331 / 500000000) (538388663 / 1000000000) (Real.log (107077751399 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (107077751399 / 62500000000) = -Real.log (62500000000 / 107077751399) := by
    rw [show ((107077751399 / 62500000000) : ℝ) = ((62500000000 / 107077751399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (134824393 / 250000000) ≤ -Real.log (12500000000 / 21435023931) ∧
    -Real.log (12500000000 / 21435023931) ≤ (539297573 / 1000000000) := by
  have h := checkLog_sound (w := (8935023931 / 33935023931)) (n := 12)
    (lo := (134824393 / 250000000)) (hi := (539297573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21435023931 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21435023931 / 12500000000) = 1/(12500000000 / 21435023931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (134824393 / 250000000) (539297573 / 1000000000) (Real.log (21435023931 / 12500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (21435023931 / 12500000000) = -Real.log (12500000000 / 21435023931) := by
    rw [show ((21435023931 / 12500000000) : ℝ) = ((12500000000 / 21435023931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (23978349 / 62500000) ≤ -Real.log (125000000000 / 183454617689) ∧
    -Real.log (125000000000 / 183454617689) ≤ (76730717 / 200000000) := by
  have h := checkLog_sound (w := (58454617689 / 308454617689)) (n := 12)
    (lo := (23978349 / 62500000)) (hi := (76730717 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183454617689 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183454617689 / 125000000000) = 1/(125000000000 / 183454617689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (23978349 / 62500000) (76730717 / 200000000) (Real.log (183454617689 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (183454617689 / 125000000000) = -Real.log (125000000000 / 183454617689) := by
    rw [show ((183454617689 / 125000000000) : ℝ) = ((125000000000 / 183454617689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (192155621 / 500000000) ≤ -Real.log (31250000000 / 45893826951) ∧
    -Real.log (31250000000 / 45893826951) ≤ (384311243 / 1000000000) := by
  have h := checkLog_sound (w := (14643826951 / 77143826951)) (n := 12)
    (lo := (192155621 / 500000000)) (hi := (384311243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45893826951 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45893826951 / 31250000000) = 1/(31250000000 / 45893826951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (192155621 / 500000000) (384311243 / 1000000000) (Real.log (45893826951 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (45893826951 / 31250000000) = -Real.log (31250000000 / 45893826951) := by
    rw [show ((45893826951 / 31250000000) : ℝ) = ((31250000000 / 45893826951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (36698767 / 1000000000) ≤ -Real.log (1542346351 / 1600000000) ∧
    -Real.log (1542346351 / 1600000000) ≤ (2293673 / 62500000) := by
  have h := checkLog_sound (w := (57653649 / 3142346351)) (n := 12)
    (lo := (36698767 / 1000000000)) (hi := (2293673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1542346351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1542346351) = 1/(1542346351 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2293673 / 62500000) (-36698767 / 1000000000) (Real.log (1542346351 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2285877 / 62500000) ≤ -Real.log (60255419871 / 62500000000) ∧
    -Real.log (60255419871 / 62500000000) ≤ (36574033 / 1000000000) := by
  have h := checkLog_sound (w := (2244580129 / 122755419871)) (n := 12)
    (lo := (2285877 / 62500000)) (hi := (36574033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60255419871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60255419871) = 1/(60255419871 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-36574033 / 1000000000) (-2285877 / 62500000) (Real.log (60255419871 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell204

end


