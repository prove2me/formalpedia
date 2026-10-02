-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell182Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell182Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:40:59.615989+00:00
-- url     : https://prove2.me/theorems/78b44211-bc6c-4121-9e09-cc97452e2e82
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell182Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell183…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell182Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell183Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell184Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell185Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell186Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell187Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell188Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell182Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell183Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell184Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell185Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell186Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell187Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell188Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell182Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell183Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell184Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell185Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell186Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell187Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell188Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell182Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell183Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell184Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell185Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell186Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell187Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell188Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell182Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell182
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

theorem reflection_log_1_neg : (12217733 / 40000000) ≤ -Real.log (5120 / 6949) ∧
    -Real.log (5120 / 6949) ≤ (152721663 / 500000000) := by
  have h := checkLog_sound (w := (1829 / 12069)) (n := 12)
    (lo := (12217733 / 40000000)) (hi := (152721663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6949 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6949 / 5120) = 1/(5120 / 6949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12217733 / 40000000) (152721663 / 500000000) (Real.log (6949 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6949 / 5120) = -Real.log (5120 / 6949) := by
    rw [show ((6949 / 5120) : ℝ) = ((5120 / 6949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (441962969 / 1000000000) ≤ -Real.log (3291 / 5120) ∧
    -Real.log (3291 / 5120) ≤ (44196297 / 100000000) := by
  have h := checkLog_sound (w := (1829 / 8411)) (n := 12)
    (lo := (441962969 / 1000000000)) (hi := (44196297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3291) = 1/(3291 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-44196297 / 100000000) (-441962969 / 1000000000) (Real.log (3291 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (61002303 / 200000000) ≤ -Real.log (2560 / 3473) ∧
    -Real.log (2560 / 3473) ≤ (76252879 / 250000000) := by
  have h := checkLog_sound (w := (913 / 6033)) (n := 12)
    (lo := (61002303 / 200000000)) (hi := (76252879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3473 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3473 / 2560) = 1/(2560 / 3473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (61002303 / 200000000) (76252879 / 250000000) (Real.log (3473 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3473 / 2560) = -Real.log (2560 / 3473) := by
    rw [show ((3473 / 2560) : ℝ) = ((2560 / 3473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (441051807 / 1000000000) ≤ -Real.log (1647 / 2560) ∧
    -Real.log (1647 / 2560) ≤ (13782869 / 31250000) := by
  have h := checkLog_sound (w := (913 / 4207)) (n := 12)
    (lo := (441051807 / 1000000000)) (hi := (13782869 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1647) = 1/(1647 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-13782869 / 31250000) (-441051807 / 1000000000) (Real.log (1647 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1808117 / 8000000) ≤ -Real.log (500000 / 626797) ∧
    -Real.log (500000 / 626797) ≤ (113007313 / 500000000) := by
  have h := checkLog_sound (w := (126797 / 1126797)) (n := 12)
    (lo := (1808117 / 8000000)) (hi := (113007313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626797 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626797 / 500000) = 1/(500000 / 626797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1808117 / 8000000) (113007313 / 500000000) (Real.log (626797 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (626797 / 500000) = -Real.log (500000 / 626797) := by
    rw [show ((626797 / 500000) : ℝ) = ((500000 / 626797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (29248559 / 100000000) ≤ -Real.log (373203 / 500000) ∧
    -Real.log (373203 / 500000) ≤ (292485591 / 1000000000) := by
  have h := checkLog_sound (w := (126797 / 873203)) (n := 12)
    (lo := (29248559 / 100000000)) (hi := (292485591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373203) = 1/(373203 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-292485591 / 1000000000) (-29248559 / 100000000) (Real.log (373203 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (113175999 / 500000000) ≤ -Real.log (1000000 / 1254017) ∧
    -Real.log (1000000 / 1254017) ≤ (226351999 / 1000000000) := by
  have h := checkLog_sound (w := (254017 / 2254017)) (n := 12)
    (lo := (113175999 / 500000000)) (hi := (226351999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254017 / 1000000) = 1/(1000000 / 1254017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (113175999 / 500000000) (226351999 / 1000000000) (Real.log (1254017 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1254017 / 1000000) = -Real.log (1000000 / 1254017) := by
    rw [show ((1254017 / 1000000) : ℝ) = ((1000000 / 1254017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (293052467 / 1000000000) ≤ -Real.log (745983 / 1000000) ∧
    -Real.log (745983 / 1000000) ≤ (73263117 / 250000000) := by
  have h := checkLog_sound (w := (254017 / 1745983)) (n := 12)
    (lo := (293052467 / 1000000000)) (hi := (73263117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745983) = 1/(745983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-73263117 / 250000000) (-293052467 / 1000000000) (Real.log (745983 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167690881 / 1000000000) ≤ -Real.log (1000000 / 1182571) ∧
    -Real.log (1000000 / 1182571) ≤ (83845441 / 500000000) := by
  have h := checkLog_sound (w := (182571 / 2182571)) (n := 12)
    (lo := (167690881 / 1000000000)) (hi := (83845441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1182571 / 1000000) = 1/(1000000 / 1182571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167690881 / 1000000000) (83845441 / 500000000) (Real.log (1182571 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1182571 / 1000000) = -Real.log (1000000 / 1182571) := by
    rw [show ((1182571 / 1000000) : ℝ) = ((1000000 / 1182571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (20159123 / 100000000) ≤ -Real.log (817429 / 1000000) ∧
    -Real.log (817429 / 1000000) ≤ (201591231 / 1000000000) := by
  have h := checkLog_sound (w := (182571 / 1817429)) (n := 12)
    (lo := (20159123 / 100000000)) (hi := (201591231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 817429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 817429) = 1/(817429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-201591231 / 1000000000) (-20159123 / 100000000) (Real.log (817429 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33591443 / 200000000) ≤ -Real.log (500000 / 591443) ∧
    -Real.log (500000 / 591443) ≤ (5248663 / 31250000) := by
  have h := checkLog_sound (w := (91443 / 1091443)) (n := 12)
    (lo := (33591443 / 200000000)) (hi := (5248663 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591443 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591443 / 500000) = 1/(500000 / 591443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33591443 / 200000000) (5248663 / 31250000) (Real.log (591443 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (591443 / 500000) = -Real.log (500000 / 591443) := by
    rw [show ((591443 / 500000) : ℝ) = ((500000 / 591443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (100988329 / 500000000) ≤ -Real.log (408557 / 500000) ∧
    -Real.log (408557 / 500000) ≤ (201976659 / 1000000000) := by
  have h := checkLog_sound (w := (91443 / 908557)) (n := 12)
    (lo := (100988329 / 500000000)) (hi := (201976659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408557) = 1/(408557 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-201976659 / 1000000000) (-100988329 / 500000000) (Real.log (408557 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (373031661 / 500000000) ≤ -Real.log (62500000000 / 131792653309) ∧
    -Real.log (62500000000 / 131792653309) ≤ (186515831 / 250000000) := by
  have h := checkLog_sound (w := (6792653309 / 256792653309)) (n := 12)
    (lo := (26458071 / 500000000)) (hi := (52916143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131792653309 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(131792653309 / 125000000000) = 1/(62500000000 / 131792653309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (373031661 / 500000000) (186515831 / 250000000) (Real.log (131792653309 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (131792653309 / 62500000000) = -Real.log (62500000000 / 131792653309) := by
    rw [show ((131792653309 / 62500000000) : ℝ) = ((62500000000 / 131792653309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (747406293 / 1000000000) ≤ -Real.log (500000000000 / 1055758128229) ∧
    -Real.log (500000000000 / 1055758128229) ≤ (149481259 / 200000000) := by
  have h := checkLog_sound (w := (55758128229 / 2055758128229)) (n := 12)
    (lo := (54259113 / 1000000000)) (hi := (27129557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1055758128229 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1055758128229 / 1000000000000) = 1/(500000000000 / 1055758128229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (747406293 / 1000000000) (149481259 / 200000000) (Real.log (1055758128229 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1055758128229 / 500000000000) = -Real.log (500000000000 / 1055758128229) := by
    rw [show ((1055758128229 / 500000000000) : ℝ) = ((500000000000 / 1055758128229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (64812527 / 125000000) ≤ -Real.log (250000000000 / 419876715889) ∧
    -Real.log (250000000000 / 419876715889) ≤ (518500217 / 1000000000) := by
  have h := checkLog_sound (w := (169876715889 / 669876715889)) (n := 12)
    (lo := (64812527 / 125000000)) (hi := (518500217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419876715889 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419876715889 / 250000000000) = 1/(250000000000 / 419876715889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (64812527 / 125000000) (518500217 / 1000000000) (Real.log (419876715889 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (419876715889 / 250000000000) = -Real.log (250000000000 / 419876715889) := by
    rw [show ((419876715889 / 250000000000) : ℝ) = ((250000000000 / 419876715889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (103880893 / 200000000) ≤ -Real.log (500000000000 / 840513121613) ∧
    -Real.log (500000000000 / 840513121613) ≤ (259702233 / 500000000) := by
  have h := checkLog_sound (w := (340513121613 / 1340513121613)) (n := 12)
    (lo := (103880893 / 200000000)) (hi := (259702233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840513121613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840513121613 / 500000000000) = 1/(500000000000 / 840513121613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (103880893 / 200000000) (259702233 / 500000000) (Real.log (840513121613 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (840513121613 / 500000000000) = -Real.log (500000000000 / 840513121613) := by
    rw [show ((840513121613 / 500000000000) : ℝ) = ((500000000000 / 840513121613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (369282111 / 1000000000) ≤ -Real.log (6250000000 / 9041847977) ∧
    -Real.log (6250000000 / 9041847977) ≤ (5770033 / 15625000) := by
  have h := checkLog_sound (w := (2791847977 / 15291847977)) (n := 12)
    (lo := (369282111 / 1000000000)) (hi := (5770033 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9041847977 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9041847977 / 6250000000) = 1/(6250000000 / 9041847977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (369282111 / 1000000000) (5770033 / 15625000) (Real.log (9041847977 / 6250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9041847977 / 6250000000) = -Real.log (6250000000 / 9041847977) := by
    rw [show ((9041847977 / 6250000000) : ℝ) = ((6250000000 / 9041847977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (184966937 / 500000000) ≤ -Real.log (20000000000 / 28952777703) ∧
    -Real.log (20000000000 / 28952777703) ≤ (2959471 / 8000000) := by
  have h := checkLog_sound (w := (8952777703 / 48952777703)) (n := 12)
    (lo := (184966937 / 500000000)) (hi := (2959471 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28952777703 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28952777703 / 20000000000) = 1/(20000000000 / 28952777703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (184966937 / 500000000) (2959471 / 8000000) (Real.log (28952777703 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28952777703 / 20000000000) = -Real.log (20000000000 / 28952777703) := by
    rw [show ((28952777703 / 20000000000) : ℝ) = ((20000000000 / 28952777703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34019443 / 1000000000) ≤ -Real.log (241638177751 / 250000000000) ∧
    -Real.log (241638177751 / 250000000000) ≤ (8504861 / 250000000) := by
  have h := checkLog_sound (w := (8361822249 / 491638177751)) (n := 12)
    (lo := (34019443 / 1000000000)) (hi := (8504861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241638177751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241638177751) = 1/(241638177751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8504861 / 250000000) (-34019443 / 1000000000) (Real.log (241638177751 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8475087 / 250000000) ≤ -Real.log (966667829959 / 1000000000000) ∧
    -Real.log (966667829959 / 1000000000000) ≤ (33900349 / 1000000000) := by
  have h := checkLog_sound (w := (33332170041 / 1966667829959)) (n := 12)
    (lo := (8475087 / 250000000)) (hi := (33900349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966667829959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966667829959) = 1/(966667829959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-33900349 / 1000000000) (-8475087 / 250000000) (Real.log (966667829959 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell182

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell183Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell183
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

theorem reflection_log_1_neg : (76468737 / 250000000) ≤ -Real.log (640 / 869) ∧
    -Real.log (640 / 869) ≤ (305874949 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1509)) (n := 12)
    (lo := (76468737 / 250000000)) (hi := (305874949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869 / 640) = 1/(640 / 869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (76468737 / 250000000) (305874949 / 1000000000) (Real.log (869 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (869 / 640) = -Real.log (640 / 869) := by
    rw [show ((869 / 640) : ℝ) = ((640 / 869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (442874961 / 1000000000) ≤ -Real.log (411 / 640) ∧
    -Real.log (411 / 640) ≤ (221437481 / 500000000) := by
  have h := checkLog_sound (w := (229 / 1051)) (n := 12)
    (lo := (442874961 / 1000000000)) (hi := (221437481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 411) = 1/(411 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-221437481 / 500000000) (-442874961 / 1000000000) (Real.log (411 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12217733 / 40000000) ≤ -Real.log (5120 / 6949) ∧
    -Real.log (5120 / 6949) ≤ (152721663 / 500000000) := by
  have h := checkLog_sound (w := (1829 / 12069)) (n := 12)
    (lo := (12217733 / 40000000)) (hi := (152721663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6949 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6949 / 5120) = 1/(5120 / 6949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12217733 / 40000000) (152721663 / 500000000) (Real.log (6949 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6949 / 5120) = -Real.log (5120 / 6949) := by
    rw [show ((6949 / 5120) : ℝ) = ((5120 / 6949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (441962969 / 1000000000) ≤ -Real.log (3291 / 5120) ∧
    -Real.log (3291 / 5120) ≤ (44196297 / 100000000) := by
  have h := checkLog_sound (w := (1829 / 8411)) (n := 12)
    (lo := (441962969 / 1000000000)) (hi := (44196297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3291) = 1/(3291 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-44196297 / 100000000) (-441962969 / 1000000000) (Real.log (3291 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (226351201 / 1000000000) ≤ -Real.log (15625 / 19594) ∧
    -Real.log (15625 / 19594) ≤ (113175601 / 500000000) := by
  have h := checkLog_sound (w := (3969 / 35219)) (n := 12)
    (lo := (226351201 / 1000000000)) (hi := (113175601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19594 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19594 / 15625) = 1/(15625 / 19594) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (226351201 / 1000000000) (113175601 / 500000000) (Real.log (19594 / 15625)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19594 / 15625) = -Real.log (15625 / 19594) := by
    rw [show ((19594 / 15625) : ℝ) = ((15625 / 19594) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (146525563 / 500000000) ≤ -Real.log (11656 / 15625) ∧
    -Real.log (11656 / 15625) ≤ (293051127 / 1000000000) := by
  have h := checkLog_sound (w := (3969 / 27281)) (n := 12)
    (lo := (146525563 / 500000000)) (hi := (293051127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11656) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11656) = 1/(11656 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-293051127 / 1000000000) (-146525563 / 500000000) (Real.log (11656 / 15625)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (11334423 / 50000000) ≤ -Real.log (1000000 / 1254439) ∧
    -Real.log (1000000 / 1254439) ≤ (226688461 / 1000000000) := by
  have h := checkLog_sound (w := (254439 / 2254439)) (n := 12)
    (lo := (11334423 / 50000000)) (hi := (226688461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254439 / 1000000) = 1/(1000000 / 1254439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (11334423 / 50000000) (226688461 / 1000000000) (Real.log (1254439 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1254439 / 1000000) = -Real.log (1000000 / 1254439) := by
    rw [show ((1254439 / 1000000) : ℝ) = ((1000000 / 1254439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (293618323 / 1000000000) ≤ -Real.log (745561 / 1000000) ∧
    -Real.log (745561 / 1000000) ≤ (73404581 / 250000000) := by
  have h := checkLog_sound (w := (254439 / 1745561)) (n := 12)
    (lo := (293618323 / 1000000000)) (hi := (73404581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745561) = 1/(745561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-73404581 / 250000000) (-293618323 / 1000000000) (Real.log (745561 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167956369 / 1000000000) ≤ -Real.log (200000 / 236577) ∧
    -Real.log (200000 / 236577) ≤ (16795637 / 100000000) := by
  have h := checkLog_sound (w := (36577 / 436577)) (n := 12)
    (lo := (167956369 / 1000000000)) (hi := (16795637 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236577 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236577 / 200000) = 1/(200000 / 236577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167956369 / 1000000000) (16795637 / 100000000) (Real.log (236577 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (236577 / 200000) = -Real.log (200000 / 236577) := by
    rw [show ((236577 / 200000) : ℝ) = ((200000 / 236577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (40395087 / 200000000) ≤ -Real.log (163423 / 200000) ∧
    -Real.log (163423 / 200000) ≤ (50493859 / 250000000) := by
  have h := checkLog_sound (w := (36577 / 363423)) (n := 12)
    (lo := (40395087 / 200000000)) (hi := (50493859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163423) = 1/(163423 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-50493859 / 250000000) (-40395087 / 200000000) (Real.log (163423 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (168223477 / 1000000000) ≤ -Real.log (1000000 / 1183201) ∧
    -Real.log (1000000 / 1183201) ≤ (84111739 / 500000000) := by
  have h := checkLog_sound (w := (183201 / 2183201)) (n := 12)
    (lo := (168223477 / 1000000000)) (hi := (84111739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183201 / 1000000) = 1/(1000000 / 1183201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (168223477 / 1000000000) (84111739 / 500000000) (Real.log (1183201 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1183201 / 1000000) = -Real.log (1000000 / 1183201) := by
    rw [show ((1183201 / 1000000) : ℝ) = ((1000000 / 1183201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (50590559 / 250000000) ≤ -Real.log (816799 / 1000000) ∧
    -Real.log (816799 / 1000000) ≤ (202362237 / 1000000000) := by
  have h := checkLog_sound (w := (183201 / 1816799)) (n := 12)
    (lo := (50590559 / 250000000)) (hi := (202362237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 816799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 816799) = 1/(816799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-202362237 / 1000000000) (-50590559 / 250000000) (Real.log (816799 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (747406293 / 1000000000) ≤ -Real.log (125000000000 / 263939532057) ∧
    -Real.log (125000000000 / 263939532057) ≤ (149481259 / 200000000) := by
  have h := checkLog_sound (w := (13939532057 / 513939532057)) (n := 12)
    (lo := (54259113 / 1000000000)) (hi := (27129557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263939532057 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(263939532057 / 250000000000) = 1/(125000000000 / 263939532057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (747406293 / 1000000000) (149481259 / 200000000) (Real.log (263939532057 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (263939532057 / 125000000000) = -Real.log (125000000000 / 263939532057) := by
    rw [show ((263939532057 / 125000000000) : ℝ) = ((125000000000 / 263939532057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (74874991 / 100000000) ≤ -Real.log (125000000000 / 264294403893) ∧
    -Real.log (125000000000 / 264294403893) ≤ (93593739 / 125000000) := by
  have h := checkLog_sound (w := (14294403893 / 514294403893)) (n := 12)
    (lo := (5560273 / 100000000)) (hi := (55602731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264294403893 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(264294403893 / 250000000000) = 1/(125000000000 / 264294403893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (74874991 / 100000000) (93593739 / 125000000) (Real.log (264294403893 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (264294403893 / 125000000000) = -Real.log (125000000000 / 264294403893) := by
    rw [show ((264294403893 / 125000000000) : ℝ) = ((125000000000 / 264294403893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (64925291 / 125000000) ≤ -Real.log (500000000000 / 840511324639) ∧
    -Real.log (500000000000 / 840511324639) ≤ (519402329 / 1000000000) := by
  have h := checkLog_sound (w := (340511324639 / 1340511324639)) (n := 12)
    (lo := (64925291 / 125000000)) (hi := (519402329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840511324639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840511324639 / 500000000000) = 1/(500000000000 / 840511324639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (64925291 / 125000000) (519402329 / 1000000000) (Real.log (840511324639 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (840511324639 / 500000000000) = -Real.log (500000000000 / 840511324639) := by
    rw [show ((840511324639 / 500000000000) : ℝ) = ((500000000000 / 840511324639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16259587 / 31250000) ≤ -Real.log (125000000000 / 210317968617) ∧
    -Real.log (125000000000 / 210317968617) ≤ (104061357 / 200000000) := by
  have h := checkLog_sound (w := (85317968617 / 335317968617)) (n := 12)
    (lo := (16259587 / 31250000)) (hi := (104061357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210317968617 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210317968617 / 125000000000) = 1/(125000000000 / 210317968617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (16259587 / 31250000) (104061357 / 200000000) (Real.log (210317968617 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (210317968617 / 125000000000) = -Real.log (125000000000 / 210317968617) := by
    rw [show ((210317968617 / 125000000000) : ℝ) = ((125000000000 / 210317968617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (92482951 / 250000000) ≤ -Real.log (250000000000 / 361908972421) ∧
    -Real.log (250000000000 / 361908972421) ≤ (73986361 / 200000000) := by
  have h := checkLog_sound (w := (111908972421 / 611908972421)) (n := 12)
    (lo := (92482951 / 250000000)) (hi := (73986361 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361908972421 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361908972421 / 250000000000) = 1/(250000000000 / 361908972421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (92482951 / 250000000) (73986361 / 200000000) (Real.log (361908972421 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (361908972421 / 250000000000) = -Real.log (250000000000 / 361908972421) := by
    rw [show ((361908972421 / 250000000000) : ℝ) = ((250000000000 / 361908972421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (185292857 / 500000000) ≤ -Real.log (500000000000 / 724291410739) ∧
    -Real.log (500000000000 / 724291410739) ≤ (74117143 / 200000000) := by
  have h := checkLog_sound (w := (224291410739 / 1224291410739)) (n := 12)
    (lo := (185292857 / 500000000)) (hi := (74117143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724291410739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724291410739 / 500000000000) = 1/(500000000000 / 724291410739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (185292857 / 500000000) (74117143 / 200000000) (Real.log (724291410739 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (724291410739 / 500000000000) = -Real.log (500000000000 / 724291410739) := by
    rw [show ((724291410739 / 500000000000) : ℝ) = ((500000000000 / 724291410739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17069379 / 500000000) ≤ -Real.log (966437393599 / 1000000000000) ∧
    -Real.log (966437393599 / 1000000000000) ≤ (34138759 / 1000000000) := by
  have h := checkLog_sound (w := (33562606401 / 1966437393599)) (n := 12)
    (lo := (17069379 / 500000000)) (hi := (34138759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966437393599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966437393599) = 1/(966437393599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-34138759 / 1000000000) (-17069379 / 500000000) (Real.log (966437393599 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6803813 / 200000000) ≤ -Real.log (38662123071 / 40000000000) ∧
    -Real.log (38662123071 / 40000000000) ≤ (17009533 / 500000000) := by
  have h := checkLog_sound (w := (1337876929 / 78662123071)) (n := 12)
    (lo := (6803813 / 200000000)) (hi := (17009533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38662123071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38662123071) = 1/(38662123071 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-17009533 / 500000000) (-6803813 / 200000000) (Real.log (38662123071 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell183

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell184Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell184
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

theorem reflection_log_1_neg : (153153193 / 500000000) ≤ -Real.log (1024 / 1391) ∧
    -Real.log (1024 / 1391) ≤ (306306387 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2415)) (n := 12)
    (lo := (153153193 / 500000000)) (hi := (306306387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1391 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1391 / 1024) = 1/(1024 / 1391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (153153193 / 500000000) (306306387 / 1000000000) (Real.log (1391 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1391 / 1024) = -Real.log (1024 / 1391) := by
    rw [show ((1391 / 1024) : ℝ) = ((1024 / 1391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (443787787 / 1000000000) ≤ -Real.log (657 / 1024) ∧
    -Real.log (657 / 1024) ≤ (110946947 / 250000000) := by
  have h := checkLog_sound (w := (367 / 1681)) (n := 12)
    (lo := (443787787 / 1000000000)) (hi := (110946947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 657) = 1/(657 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-110946947 / 250000000) (-443787787 / 1000000000) (Real.log (657 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (76468737 / 250000000) ≤ -Real.log (640 / 869) ∧
    -Real.log (640 / 869) ≤ (305874949 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1509)) (n := 12)
    (lo := (76468737 / 250000000)) (hi := (305874949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869 / 640) = 1/(640 / 869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (76468737 / 250000000) (305874949 / 1000000000) (Real.log (869 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (869 / 640) = -Real.log (640 / 869) := by
    rw [show ((869 / 640) : ℝ) = ((640 / 869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (442874961 / 1000000000) ≤ -Real.log (411 / 640) ∧
    -Real.log (411 / 640) ≤ (221437481 / 500000000) := by
  have h := checkLog_sound (w := (229 / 1051)) (n := 12)
    (lo := (442874961 / 1000000000)) (hi := (221437481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 411) = 1/(411 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-221437481 / 500000000) (-442874961 / 1000000000) (Real.log (411 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (226687663 / 1000000000) ≤ -Real.log (500000 / 627219) ∧
    -Real.log (500000 / 627219) ≤ (14167979 / 62500000) := by
  have h := checkLog_sound (w := (127219 / 1127219)) (n := 12)
    (lo := (226687663 / 1000000000)) (hi := (14167979 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627219 / 500000) = 1/(500000 / 627219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (226687663 / 1000000000) (14167979 / 62500000) (Real.log (627219 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (627219 / 500000) = -Real.log (500000 / 627219) := by
    rw [show ((627219 / 500000) : ℝ) = ((500000 / 627219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (146808491 / 500000000) ≤ -Real.log (372781 / 500000) ∧
    -Real.log (372781 / 500000) ≤ (293616983 / 1000000000) := by
  have h := checkLog_sound (w := (127219 / 872781)) (n := 12)
    (lo := (146808491 / 500000000)) (hi := (293616983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 372781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 372781) = 1/(372781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-293616983 / 1000000000) (-146808491 / 500000000) (Real.log (372781 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (56756003 / 250000000) ≤ -Real.log (50000 / 62743) ∧
    -Real.log (50000 / 62743) ≤ (227024013 / 1000000000) := by
  have h := checkLog_sound (w := (12743 / 112743)) (n := 12)
    (lo := (56756003 / 250000000)) (hi := (227024013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62743 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62743 / 50000) = 1/(50000 / 62743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (56756003 / 250000000) (227024013 / 1000000000) (Real.log (62743 / 50000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (62743 / 50000) = -Real.log (50000 / 62743) := by
    rw [show ((62743 / 50000) : ℝ) = ((50000 / 62743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (147091579 / 500000000) ≤ -Real.log (37257 / 50000) ∧
    -Real.log (37257 / 50000) ≤ (294183159 / 1000000000) := by
  have h := checkLog_sound (w := (12743 / 87257)) (n := 12)
    (lo := (147091579 / 500000000)) (hi := (294183159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37257) = 1/(37257 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-294183159 / 1000000000) (-147091579 / 500000000) (Real.log (37257 / 50000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (21027829 / 125000000) ≤ -Real.log (1250 / 1479) ∧
    -Real.log (1250 / 1479) ≤ (168222633 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 2729)) (n := 12)
    (lo := (21027829 / 125000000)) (hi := (168222633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1479 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1479 / 1250) = 1/(1250 / 1479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (21027829 / 125000000) (168222633 / 1000000000) (Real.log (1479 / 1250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1479 / 1250) = -Real.log (1250 / 1479) := by
    rw [show ((1479 / 1250) : ℝ) = ((1250 / 1479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (50590253 / 250000000) ≤ -Real.log (1021 / 1250) ∧
    -Real.log (1021 / 1250) ≤ (202361013 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 2271)) (n := 12)
    (lo := (50590253 / 250000000)) (hi := (202361013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1021) = 1/(1021 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-202361013 / 1000000000) (-50590253 / 250000000) (Real.log (1021 / 1250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (168489669 / 1000000000) ≤ -Real.log (250000 / 295879) ∧
    -Real.log (250000 / 295879) ≤ (16848967 / 100000000) := by
  have h := checkLog_sound (w := (45879 / 545879)) (n := 12)
    (lo := (168489669 / 1000000000)) (hi := (16848967 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295879 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295879 / 250000) = 1/(250000 / 295879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (168489669 / 1000000000) (16848967 / 100000000) (Real.log (295879 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (295879 / 250000) = -Real.log (250000 / 295879) := by
    rw [show ((295879 / 250000) : ℝ) = ((250000 / 295879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (101373981 / 500000000) ≤ -Real.log (204121 / 250000) ∧
    -Real.log (204121 / 250000) ≤ (202747963 / 1000000000) := by
  have h := checkLog_sound (w := (45879 / 454121)) (n := 12)
    (lo := (101373981 / 500000000)) (hi := (202747963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204121) = 1/(204121 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-202747963 / 1000000000) (-101373981 / 500000000) (Real.log (204121 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (74874991 / 100000000) ≤ -Real.log (500000000000 / 1057177615571) ∧
    -Real.log (500000000000 / 1057177615571) ≤ (93593739 / 125000000) := by
  have h := checkLog_sound (w := (57177615571 / 2057177615571)) (n := 12)
    (lo := (5560273 / 100000000)) (hi := (55602731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1057177615571 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1057177615571 / 1000000000000) = 1/(500000000000 / 1057177615571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (74874991 / 100000000) (93593739 / 125000000) (Real.log (1057177615571 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1057177615571 / 500000000000) = -Real.log (500000000000 / 1057177615571) := by
    rw [show ((1057177615571 / 500000000000) : ℝ) = ((500000000000 / 1057177615571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (187523543 / 250000000) ≤ -Real.log (250000000000 / 529299847793) ∧
    -Real.log (250000000000 / 529299847793) ≤ (375047087 / 500000000) := by
  have h := checkLog_sound (w := (29299847793 / 1029299847793)) (n := 12)
    (lo := (3559187 / 62500000)) (hi := (56946993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529299847793 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(529299847793 / 500000000000) = 1/(250000000000 / 529299847793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (187523543 / 250000000) (375047087 / 500000000) (Real.log (529299847793 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (529299847793 / 250000000000) = -Real.log (250000000000 / 529299847793) := by
    rw [show ((529299847793 / 250000000000) : ℝ) = ((250000000000 / 529299847793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (260152323 / 500000000) ≤ -Real.log (500000000000 / 841270075459) ∧
    -Real.log (500000000000 / 841270075459) ≤ (520304647 / 1000000000) := by
  have h := checkLog_sound (w := (341270075459 / 1341270075459)) (n := 12)
    (lo := (260152323 / 500000000)) (hi := (520304647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841270075459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(841270075459 / 500000000000) = 1/(500000000000 / 841270075459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (260152323 / 500000000) (520304647 / 1000000000) (Real.log (841270075459 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (841270075459 / 500000000000) = -Real.log (500000000000 / 841270075459) := by
    rw [show ((841270075459 / 500000000000) : ℝ) = ((500000000000 / 841270075459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (521207171 / 1000000000) ≤ -Real.log (500000000000 / 842029685697) ∧
    -Real.log (500000000000 / 842029685697) ≤ (130301793 / 250000000) := by
  have h := checkLog_sound (w := (342029685697 / 1342029685697)) (n := 12)
    (lo := (521207171 / 1000000000)) (hi := (130301793 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((842029685697 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(842029685697 / 500000000000) = 1/(500000000000 / 842029685697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (521207171 / 1000000000) (130301793 / 250000000) (Real.log (842029685697 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (842029685697 / 500000000000) = -Real.log (500000000000 / 842029685697) := by
    rw [show ((842029685697 / 500000000000) : ℝ) = ((500000000000 / 842029685697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (92645911 / 250000000) ≤ -Real.log (500000000000 / 724289911851) ∧
    -Real.log (500000000000 / 724289911851) ≤ (74116729 / 200000000) := by
  have h := checkLog_sound (w := (224289911851 / 1224289911851)) (n := 12)
    (lo := (92645911 / 250000000)) (hi := (74116729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724289911851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724289911851 / 500000000000) = 1/(500000000000 / 724289911851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (92645911 / 250000000) (74116729 / 200000000) (Real.log (724289911851 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (724289911851 / 500000000000) = -Real.log (500000000000 / 724289911851) := by
    rw [show ((724289911851 / 500000000000) : ℝ) = ((500000000000 / 724289911851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (371237631 / 1000000000) ≤ -Real.log (250000000000 / 362381871537) ∧
    -Real.log (250000000000 / 362381871537) ≤ (1450147 / 3906250) := by
  have h := checkLog_sound (w := (112381871537 / 612381871537)) (n := 12)
    (lo := (371237631 / 1000000000)) (hi := (1450147 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362381871537 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362381871537 / 250000000000) = 1/(250000000000 / 362381871537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (371237631 / 1000000000) (1450147 / 3906250) (Real.log (362381871537 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (362381871537 / 250000000000) = -Real.log (250000000000 / 362381871537) := by
    rw [show ((362381871537 / 250000000000) : ℝ) = ((250000000000 / 362381871537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34258293 / 1000000000) ≤ -Real.log (60395117359 / 62500000000) ∧
    -Real.log (60395117359 / 62500000000) ≤ (17129147 / 500000000) := by
  have h := checkLog_sound (w := (2104882641 / 122895117359)) (n := 12)
    (lo := (34258293 / 1000000000)) (hi := (17129147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60395117359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60395117359) = 1/(60395117359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17129147 / 500000000) (-34258293 / 1000000000) (Real.log (60395117359 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (34138379 / 1000000000) ≤ -Real.log (1510059 / 1562500) ∧
    -Real.log (1510059 / 1562500) ≤ (1706919 / 50000000) := by
  have h := checkLog_sound (w := (52441 / 3072559)) (n := 12)
    (lo := (34138379 / 1000000000)) (hi := (1706919 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1562500 / 1510059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1562500 / 1510059) = 1/(1510059 / 1562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1706919 / 50000000) (-34138379 / 1000000000) (Real.log (1510059 / 1562500)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell184

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell185Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell185
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

theorem reflection_log_1_neg : (306737637 / 1000000000) ≤ -Real.log (2560 / 3479) ∧
    -Real.log (2560 / 3479) ≤ (153368819 / 500000000) := by
  have h := checkLog_sound (w := (919 / 6039)) (n := 12)
    (lo := (306737637 / 1000000000)) (hi := (153368819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3479 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3479 / 2560) = 1/(2560 / 3479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (306737637 / 1000000000) (153368819 / 500000000) (Real.log (3479 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3479 / 2560) = -Real.log (2560 / 3479) := by
    rw [show ((3479 / 2560) : ℝ) = ((2560 / 3479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (222350723 / 500000000) ≤ -Real.log (1641 / 2560) ∧
    -Real.log (1641 / 2560) ≤ (444701447 / 1000000000) := by
  have h := checkLog_sound (w := (919 / 4201)) (n := 12)
    (lo := (222350723 / 500000000)) (hi := (444701447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1641) = 1/(1641 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-444701447 / 1000000000) (-222350723 / 500000000) (Real.log (1641 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (153153193 / 500000000) ≤ -Real.log (1024 / 1391) ∧
    -Real.log (1024 / 1391) ≤ (306306387 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2415)) (n := 12)
    (lo := (153153193 / 500000000)) (hi := (306306387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1391 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1391 / 1024) = 1/(1024 / 1391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (153153193 / 500000000) (306306387 / 1000000000) (Real.log (1391 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1391 / 1024) = -Real.log (1024 / 1391) := by
    rw [show ((1391 / 1024) : ℝ) = ((1024 / 1391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (443787787 / 1000000000) ≤ -Real.log (657 / 1024) ∧
    -Real.log (657 / 1024) ≤ (110946947 / 250000000) := by
  have h := checkLog_sound (w := (367 / 1681)) (n := 12)
    (lo := (443787787 / 1000000000)) (hi := (110946947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 657) = 1/(657 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-110946947 / 250000000) (-443787787 / 1000000000) (Real.log (657 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45404643 / 200000000) ≤ -Real.log (1000000 / 1254859) ∧
    -Real.log (1000000 / 1254859) ≤ (14188951 / 62500000) := by
  have h := checkLog_sound (w := (254859 / 2254859)) (n := 12)
    (lo := (45404643 / 200000000)) (hi := (14188951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254859 / 1000000) = 1/(1000000 / 1254859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45404643 / 200000000) (14188951 / 62500000) (Real.log (1254859 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1254859 / 1000000) = -Real.log (1000000 / 1254859) := by
    rw [show ((1254859 / 1000000) : ℝ) = ((1000000 / 1254859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (36772727 / 125000000) ≤ -Real.log (745141 / 1000000) ∧
    -Real.log (745141 / 1000000) ≤ (294181817 / 1000000000) := by
  have h := checkLog_sound (w := (254859 / 1745141)) (n := 12)
    (lo := (36772727 / 125000000)) (hi := (294181817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745141) = 1/(745141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-294181817 / 1000000000) (-36772727 / 125000000) (Real.log (745141 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (28420031 / 125000000) ≤ -Real.log (500000 / 627641) ∧
    -Real.log (500000 / 627641) ≤ (227360249 / 1000000000) := by
  have h := checkLog_sound (w := (127641 / 1127641)) (n := 12)
    (lo := (28420031 / 125000000)) (hi := (227360249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627641 / 500000) = 1/(500000 / 627641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (28420031 / 125000000) (227360249 / 1000000000) (Real.log (627641 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (627641 / 500000) = -Real.log (500000 / 627641) := by
    rw [show ((627641 / 500000) : ℝ) = ((500000 / 627641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58949931 / 200000000) ≤ -Real.log (372359 / 500000) ∧
    -Real.log (372359 / 500000) ≤ (36843707 / 125000000) := by
  have h := checkLog_sound (w := (127641 / 872359)) (n := 12)
    (lo := (58949931 / 200000000)) (hi := (36843707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 372359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 372359) = 1/(372359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-36843707 / 125000000) (-58949931 / 200000000) (Real.log (372359 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (21061103 / 125000000) ≤ -Real.log (200000 / 236703) ∧
    -Real.log (200000 / 236703) ≤ (6739553 / 40000000) := by
  have h := checkLog_sound (w := (36703 / 436703)) (n := 12)
    (lo := (21061103 / 125000000)) (hi := (6739553 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236703 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236703 / 200000) = 1/(200000 / 236703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (21061103 / 125000000) (6739553 / 40000000) (Real.log (236703 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (236703 / 200000) = -Real.log (200000 / 236703) := by
    rw [show ((236703 / 200000) : ℝ) = ((200000 / 236703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (202746737 / 1000000000) ≤ -Real.log (163297 / 200000) ∧
    -Real.log (163297 / 200000) ≤ (101373369 / 500000000) := by
  have h := checkLog_sound (w := (36703 / 363297)) (n := 12)
    (lo := (202746737 / 1000000000)) (hi := (101373369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163297) = 1/(163297 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-101373369 / 500000000) (-202746737 / 1000000000) (Real.log (163297 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33750989 / 200000000) ≤ -Real.log (100000 / 118383) ∧
    -Real.log (100000 / 118383) ≤ (84377473 / 500000000) := by
  have h := checkLog_sound (w := (18383 / 218383)) (n := 12)
    (lo := (33750989 / 200000000)) (hi := (84377473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118383 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118383 / 100000) = 1/(100000 / 118383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33750989 / 200000000) (84377473 / 500000000) (Real.log (118383 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (118383 / 100000) = -Real.log (100000 / 118383) := by
    rw [show ((118383 / 100000) : ℝ) = ((100000 / 118383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (50783153 / 250000000) ≤ -Real.log (81617 / 100000) ∧
    -Real.log (81617 / 100000) ≤ (203132613 / 1000000000) := by
  have h := checkLog_sound (w := (18383 / 181617)) (n := 12)
    (lo := (50783153 / 250000000)) (hi := (203132613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81617) = 1/(81617 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-203132613 / 1000000000) (-50783153 / 250000000) (Real.log (81617 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (187523543 / 250000000) ≤ -Real.log (100000000000 / 211719939117) ∧
    -Real.log (100000000000 / 211719939117) ≤ (375047087 / 500000000) := by
  have h := checkLog_sound (w := (11719939117 / 411719939117)) (n := 12)
    (lo := (3559187 / 62500000)) (hi := (56946993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211719939117 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(211719939117 / 200000000000) = 1/(100000000000 / 211719939117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (187523543 / 250000000) (375047087 / 500000000) (Real.log (211719939117 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (211719939117 / 100000000000) = -Real.log (100000000000 / 211719939117) := by
    rw [show ((211719939117 / 100000000000) : ℝ) = ((100000000000 / 211719939117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (751439083 / 1000000000) ≤ -Real.log (500000000000 / 1060024375381) ∧
    -Real.log (500000000000 / 1060024375381) ≤ (150287817 / 200000000) := by
  have h := checkLog_sound (w := (60024375381 / 2060024375381)) (n := 12)
    (lo := (58291903 / 1000000000)) (hi := (910811 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1060024375381 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1060024375381 / 1000000000000) = 1/(500000000000 / 1060024375381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (751439083 / 1000000000) (150287817 / 200000000) (Real.log (1060024375381 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1060024375381 / 500000000000) = -Real.log (500000000000 / 1060024375381) := by
    rw [show ((1060024375381 / 500000000000) : ℝ) = ((500000000000 / 1060024375381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (65150629 / 125000000) ≤ -Real.log (100000000000 / 168405576931) ∧
    -Real.log (100000000000 / 168405576931) ≤ (521205033 / 1000000000) := by
  have h := checkLog_sound (w := (68405576931 / 268405576931)) (n := 12)
    (lo := (65150629 / 125000000)) (hi := (521205033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168405576931 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168405576931 / 100000000000) = 1/(100000000000 / 168405576931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (65150629 / 125000000) (521205033 / 1000000000) (Real.log (168405576931 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (168405576931 / 100000000000) = -Real.log (100000000000 / 168405576931) := by
    rw [show ((168405576931 / 100000000000) : ℝ) = ((100000000000 / 168405576931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (32631869 / 62500000) ≤ -Real.log (125000000000 / 210697539203) ∧
    -Real.log (125000000000 / 210697539203) ≤ (104421981 / 200000000) := by
  have h := checkLog_sound (w := (85697539203 / 335697539203)) (n := 12)
    (lo := (32631869 / 62500000)) (hi := (104421981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210697539203 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210697539203 / 125000000000) = 1/(125000000000 / 210697539203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (32631869 / 62500000) (104421981 / 200000000) (Real.log (210697539203 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (210697539203 / 125000000000) = -Real.log (125000000000 / 210697539203) := by
    rw [show ((210697539203 / 125000000000) : ℝ) = ((125000000000 / 210697539203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (371235561 / 1000000000) ≤ -Real.log (500000000000 / 724762243029) ∧
    -Real.log (500000000000 / 724762243029) ≤ (185617781 / 500000000) := by
  have h := checkLog_sound (w := (224762243029 / 1224762243029)) (n := 12)
    (lo := (371235561 / 1000000000)) (hi := (185617781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724762243029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724762243029 / 500000000000) = 1/(500000000000 / 724762243029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (371235561 / 1000000000) (185617781 / 500000000) (Real.log (724762243029 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (724762243029 / 500000000000) = -Real.log (500000000000 / 724762243029) := by
    rw [show ((724762243029 / 500000000000) : ℝ) = ((500000000000 / 724762243029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (371887557 / 1000000000) ≤ -Real.log (1250000000 / 1813087347) ∧
    -Real.log (1250000000 / 1813087347) ≤ (185943779 / 500000000) := by
  have h := checkLog_sound (w := (563087347 / 3063087347)) (n := 12)
    (lo := (371887557 / 1000000000)) (hi := (185943779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1813087347 / 1250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1813087347 / 1250000000) = 1/(1250000000 / 1813087347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (371887557 / 1000000000) (185943779 / 500000000) (Real.log (1813087347 / 1250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1813087347 / 1250000000) = -Real.log (1250000000 / 1813087347) := by
    rw [show ((1813087347 / 1250000000) : ℝ) = ((1250000000 / 1813087347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34377667 / 1000000000) ≤ -Real.log (9662065311 / 10000000000) ∧
    -Real.log (9662065311 / 10000000000) ≤ (8594417 / 250000000) := by
  have h := checkLog_sound (w := (337934689 / 19662065311)) (n := 12)
    (lo := (34377667 / 1000000000)) (hi := (8594417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9662065311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9662065311) = 1/(9662065311 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8594417 / 250000000) (-34377667 / 1000000000) (Real.log (9662065311 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (34257913 / 1000000000) ≤ -Real.log (38652889791 / 40000000000) ∧
    -Real.log (38652889791 / 40000000000) ≤ (17128957 / 500000000) := by
  have h := checkLog_sound (w := (1347110209 / 78652889791)) (n := 12)
    (lo := (34257913 / 1000000000)) (hi := (17128957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38652889791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38652889791) = 1/(38652889791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-17128957 / 500000000) (-34257913 / 1000000000) (Real.log (38652889791 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell185

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell186Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell186
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

theorem reflection_log_1_neg : (307168703 / 1000000000) ≤ -Real.log (5120 / 6961) ∧
    -Real.log (5120 / 6961) ≤ (4799511 / 15625000) := by
  have h := checkLog_sound (w := (1841 / 12081)) (n := 12)
    (lo := (307168703 / 1000000000)) (hi := (4799511 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6961 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6961 / 5120) = 1/(5120 / 6961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (307168703 / 1000000000) (4799511 / 15625000) (Real.log (6961 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6961 / 5120) = -Real.log (5120 / 6961) := by
    rw [show ((6961 / 5120) : ℝ) = ((5120 / 6961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (445615941 / 1000000000) ≤ -Real.log (3279 / 5120) ∧
    -Real.log (3279 / 5120) ≤ (222807971 / 500000000) := by
  have h := checkLog_sound (w := (1841 / 8399)) (n := 12)
    (lo := (445615941 / 1000000000)) (hi := (222807971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3279) = 1/(3279 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-222807971 / 500000000) (-445615941 / 1000000000) (Real.log (3279 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (306737637 / 1000000000) ≤ -Real.log (2560 / 3479) ∧
    -Real.log (2560 / 3479) ≤ (153368819 / 500000000) := by
  have h := checkLog_sound (w := (919 / 6039)) (n := 12)
    (lo := (306737637 / 1000000000)) (hi := (153368819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3479 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3479 / 2560) = 1/(2560 / 3479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (306737637 / 1000000000) (153368819 / 500000000) (Real.log (3479 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3479 / 2560) = -Real.log (2560 / 3479) := by
    rw [show ((3479 / 2560) : ℝ) = ((2560 / 3479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (222350723 / 500000000) ≤ -Real.log (1641 / 2560) ∧
    -Real.log (1641 / 2560) ≤ (444701447 / 1000000000) := by
  have h := checkLog_sound (w := (919 / 4201)) (n := 12)
    (lo := (222350723 / 500000000)) (hi := (444701447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1641) = 1/(1641 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-444701447 / 1000000000) (-222350723 / 500000000) (Real.log (1641 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (227359451 / 1000000000) ≤ -Real.log (1000000 / 1255281) ∧
    -Real.log (1000000 / 1255281) ≤ (56839863 / 250000000) := by
  have h := checkLog_sound (w := (255281 / 2255281)) (n := 12)
    (lo := (227359451 / 1000000000)) (hi := (56839863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1255281 / 1000000) = 1/(1000000 / 1255281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (227359451 / 1000000000) (56839863 / 250000000) (Real.log (1255281 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1255281 / 1000000) = -Real.log (1000000 / 1255281) := by
    rw [show ((1255281 / 1000000) : ℝ) = ((1000000 / 1255281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (36843539 / 125000000) ≤ -Real.log (744719 / 1000000) ∧
    -Real.log (744719 / 1000000) ≤ (294748313 / 1000000000) := by
  have h := checkLog_sound (w := (255281 / 1744719)) (n := 12)
    (lo := (36843539 / 125000000)) (hi := (294748313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 744719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 744719) = 1/(744719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-294748313 / 1000000000) (-36843539 / 125000000) (Real.log (744719 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (227696371 / 1000000000) ≤ -Real.log (125000 / 156963) ∧
    -Real.log (125000 / 156963) ≤ (56924093 / 250000000) := by
  have h := checkLog_sound (w := (31963 / 281963)) (n := 12)
    (lo := (227696371 / 1000000000)) (hi := (56924093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156963 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156963 / 125000) = 1/(125000 / 156963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (227696371 / 1000000000) (56924093 / 250000000) (Real.log (156963 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (156963 / 125000) = -Real.log (125000 / 156963) := by
    rw [show ((156963 / 125000) : ℝ) = ((125000 / 156963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (295316473 / 1000000000) ≤ -Real.log (93037 / 125000) ∧
    -Real.log (93037 / 125000) ≤ (147658237 / 500000000) := by
  have h := checkLog_sound (w := (31963 / 218037)) (n := 12)
    (lo := (295316473 / 1000000000)) (hi := (147658237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 93037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 93037) = 1/(93037 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-147658237 / 500000000) (-295316473 / 1000000000) (Real.log (93037 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (1687541 / 10000000) ≤ -Real.log (1000000 / 1183829) ∧
    -Real.log (1000000 / 1183829) ≤ (168754101 / 1000000000) := by
  have h := checkLog_sound (w := (183829 / 2183829)) (n := 12)
    (lo := (1687541 / 10000000)) (hi := (168754101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183829 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183829 / 1000000) = 1/(1000000 / 1183829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (1687541 / 10000000) (168754101 / 1000000000) (Real.log (1183829 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1183829 / 1000000) = -Real.log (1000000 / 1183829) := by
    rw [show ((1183829 / 1000000) : ℝ) = ((1000000 / 1183829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (203131387 / 1000000000) ≤ -Real.log (816171 / 1000000) ∧
    -Real.log (816171 / 1000000) ≤ (50782847 / 250000000) := by
  have h := checkLog_sound (w := (183829 / 1816171)) (n := 12)
    (lo := (203131387 / 1000000000)) (hi := (50782847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 816171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 816171) = 1/(816171 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-50782847 / 250000000) (-203131387 / 1000000000) (Real.log (816171 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33804199 / 200000000) ≤ -Real.log (200000 / 236829) ∧
    -Real.log (200000 / 236829) ≤ (42255249 / 250000000) := by
  have h := checkLog_sound (w := (36829 / 436829)) (n := 12)
    (lo := (33804199 / 200000000)) (hi := (42255249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236829 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236829 / 200000) = 1/(200000 / 236829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33804199 / 200000000) (42255249 / 250000000) (Real.log (236829 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (236829 / 200000) = -Real.log (200000 / 236829) := by
    rw [show ((236829 / 200000) : ℝ) = ((200000 / 236829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (40703727 / 200000000) ≤ -Real.log (163171 / 200000) ∧
    -Real.log (163171 / 200000) ≤ (50879659 / 250000000) := by
  have h := checkLog_sound (w := (36829 / 363171)) (n := 12)
    (lo := (40703727 / 200000000)) (hi := (50879659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163171) = 1/(163171 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-50879659 / 250000000) (-40703727 / 200000000) (Real.log (163171 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (751439083 / 1000000000) ≤ -Real.log (25000000000 / 53001218769) ∧
    -Real.log (25000000000 / 53001218769) ≤ (150287817 / 200000000) := by
  have h := checkLog_sound (w := (3001218769 / 103001218769)) (n := 12)
    (lo := (58291903 / 1000000000)) (hi := (910811 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53001218769 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(53001218769 / 50000000000) = 1/(25000000000 / 53001218769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (751439083 / 1000000000) (150287817 / 200000000) (Real.log (53001218769 / 25000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (53001218769 / 25000000000) = -Real.log (25000000000 / 53001218769) := by
    rw [show ((53001218769 / 25000000000) : ℝ) = ((25000000000 / 53001218769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (752784643 / 1000000000) ≤ -Real.log (500000000000 / 1061451662093) ∧
    -Real.log (500000000000 / 1061451662093) ≤ (150556929 / 200000000) := by
  have h := checkLog_sound (w := (61451662093 / 2061451662093)) (n := 12)
    (lo := (59637463 / 1000000000)) (hi := (7454683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061451662093 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1061451662093 / 1000000000000) = 1/(500000000000 / 1061451662093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (752784643 / 1000000000) (150556929 / 200000000) (Real.log (1061451662093 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1061451662093 / 500000000000) = -Real.log (500000000000 / 1061451662093) := by
    rw [show ((1061451662093 / 500000000000) : ℝ) = ((500000000000 / 1061451662093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (130526941 / 250000000) ≤ -Real.log (7812500000 / 13168568027) ∧
    -Real.log (7812500000 / 13168568027) ≤ (104421553 / 200000000) := by
  have h := checkLog_sound (w := (5356068027 / 20981068027)) (n := 12)
    (lo := (130526941 / 250000000)) (hi := (104421553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13168568027 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13168568027 / 7812500000) = 1/(7812500000 / 13168568027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (130526941 / 250000000) (104421553 / 200000000) (Real.log (13168568027 / 7812500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (13168568027 / 7812500000) = -Real.log (7812500000 / 13168568027) := by
    rw [show ((13168568027 / 7812500000) : ℝ) = ((7812500000 / 13168568027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (104602569 / 200000000) ≤ -Real.log (125000000000 / 210887872567) ∧
    -Real.log (125000000000 / 210887872567) ≤ (261506423 / 500000000) := by
  have h := checkLog_sound (w := (85887872567 / 335887872567)) (n := 12)
    (lo := (104602569 / 200000000)) (hi := (261506423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210887872567 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210887872567 / 125000000000) = 1/(125000000000 / 210887872567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (104602569 / 200000000) (261506423 / 500000000) (Real.log (210887872567 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (210887872567 / 125000000000) = -Real.log (125000000000 / 210887872567) := by
    rw [show ((210887872567 / 125000000000) : ℝ) = ((125000000000 / 210887872567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (371885487 / 1000000000) ≤ -Real.log (625000000 / 906541797) ∧
    -Real.log (625000000 / 906541797) ≤ (23242843 / 62500000) := by
  have h := checkLog_sound (w := (281541797 / 1531541797)) (n := 12)
    (lo := (371885487 / 1000000000)) (hi := (23242843 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((906541797 / 625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(906541797 / 625000000) = 1/(625000000 / 906541797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (371885487 / 1000000000) (23242843 / 62500000) (Real.log (906541797 / 625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (906541797 / 625000000) = -Real.log (625000000 / 906541797) := by
    rw [show ((906541797 / 625000000) : ℝ) = ((625000000 / 906541797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (372539631 / 1000000000) ≤ -Real.log (15625000000 / 22678374987) ∧
    -Real.log (15625000000 / 22678374987) ≤ (23283727 / 62500000) := by
  have h := checkLog_sound (w := (7053374987 / 38303374987)) (n := 12)
    (lo := (372539631 / 1000000000)) (hi := (23283727 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22678374987 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22678374987 / 15625000000) = 1/(15625000000 / 22678374987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (372539631 / 1000000000) (23283727 / 62500000) (Real.log (22678374987 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (22678374987 / 15625000000) = -Real.log (15625000000 / 22678374987) := by
    rw [show ((22678374987 / 15625000000) : ℝ) = ((15625000000 / 22678374987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (862441 / 25000000) ≤ -Real.log (38643624759 / 40000000000) ∧
    -Real.log (38643624759 / 40000000000) ≤ (34497641 / 1000000000) := by
  have h := checkLog_sound (w := (1356375241 / 78643624759)) (n := 12)
    (lo := (862441 / 25000000)) (hi := (34497641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38643624759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38643624759) = 1/(38643624759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-34497641 / 1000000000) (-862441 / 25000000) (Real.log (38643624759 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17188643 / 500000000) ≤ -Real.log (966206898759 / 1000000000000) ∧
    -Real.log (966206898759 / 1000000000000) ≤ (34377287 / 1000000000) := by
  have h := checkLog_sound (w := (33793101241 / 1966206898759)) (n := 12)
    (lo := (17188643 / 500000000)) (hi := (34377287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966206898759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966206898759) = 1/(966206898759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-34377287 / 1000000000) (-17188643 / 500000000) (Real.log (966206898759 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell186

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell187Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell187
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

theorem reflection_log_1_neg : (153799791 / 500000000) ≤ -Real.log (1280 / 1741) ∧
    -Real.log (1280 / 1741) ≤ (307599583 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 3021)) (n := 12)
    (lo := (153799791 / 500000000)) (hi := (307599583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1741 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1741 / 1280) = 1/(1280 / 1741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (153799791 / 500000000) (307599583 / 1000000000) (Real.log (1741 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1741 / 1280) = -Real.log (1280 / 1741) := by
    rw [show ((1741 / 1280) : ℝ) = ((1280 / 1741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (446531273 / 1000000000) ≤ -Real.log (819 / 1280) ∧
    -Real.log (819 / 1280) ≤ (223265637 / 500000000) := by
  have h := checkLog_sound (w := (461 / 2099)) (n := 12)
    (lo := (446531273 / 1000000000)) (hi := (223265637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 819) = 1/(819 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-223265637 / 500000000) (-446531273 / 1000000000) (Real.log (819 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (307168703 / 1000000000) ≤ -Real.log (5120 / 6961) ∧
    -Real.log (5120 / 6961) ≤ (4799511 / 15625000) := by
  have h := checkLog_sound (w := (1841 / 12081)) (n := 12)
    (lo := (307168703 / 1000000000)) (hi := (4799511 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6961 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6961 / 5120) = 1/(5120 / 6961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (307168703 / 1000000000) (4799511 / 15625000) (Real.log (6961 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6961 / 5120) = -Real.log (5120 / 6961) := by
    rw [show ((6961 / 5120) : ℝ) = ((5120 / 6961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (445615941 / 1000000000) ≤ -Real.log (3279 / 5120) ∧
    -Real.log (3279 / 5120) ≤ (222807971 / 500000000) := by
  have h := checkLog_sound (w := (1841 / 8399)) (n := 12)
    (lo := (445615941 / 1000000000)) (hi := (222807971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3279) = 1/(3279 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-222807971 / 500000000) (-445615941 / 1000000000) (Real.log (3279 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (9107823 / 40000000) ≤ -Real.log (1000000 / 1255703) ∧
    -Real.log (1000000 / 1255703) ≤ (28461947 / 125000000) := by
  have h := checkLog_sound (w := (255703 / 2255703)) (n := 12)
    (lo := (9107823 / 40000000)) (hi := (28461947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1255703 / 1000000) = 1/(1000000 / 1255703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (9107823 / 40000000) (28461947 / 125000000) (Real.log (1255703 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1255703 / 1000000) = -Real.log (1000000 / 1255703) := by
    rw [show ((1255703 / 1000000) : ℝ) = ((1000000 / 1255703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (29531513 / 100000000) ≤ -Real.log (744297 / 1000000) ∧
    -Real.log (744297 / 1000000) ≤ (295315131 / 1000000000) := by
  have h := checkLog_sound (w := (255703 / 1744297)) (n := 12)
    (lo := (29531513 / 100000000)) (hi := (295315131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 744297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 744297) = 1/(744297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-295315131 / 1000000000) (-29531513 / 100000000) (Real.log (744297 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (45606317 / 200000000) ≤ -Real.log (8000 / 10049) ∧
    -Real.log (8000 / 10049) ≤ (114015793 / 500000000) := by
  have h := checkLog_sound (w := (2049 / 18049)) (n := 12)
    (lo := (45606317 / 200000000)) (hi := (114015793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10049 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10049 / 8000) = 1/(8000 / 10049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (45606317 / 200000000) (114015793 / 500000000) (Real.log (10049 / 8000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (10049 / 8000) = -Real.log (8000 / 10049) := by
    rw [show ((10049 / 8000) : ℝ) = ((8000 / 10049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (295882269 / 1000000000) ≤ -Real.log (5951 / 8000) ∧
    -Real.log (5951 / 8000) ≤ (29588227 / 100000000) := by
  have h := checkLog_sound (w := (2049 / 13951)) (n := 12)
    (lo := (295882269 / 1000000000)) (hi := (29588227 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5951) = 1/(5951 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-29588227 / 100000000) (-295882269 / 1000000000) (Real.log (5951 / 8000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (3380403 / 20000000) ≤ -Real.log (62500 / 74009) ∧
    -Real.log (62500 / 74009) ≤ (169020151 / 1000000000) := by
  have h := checkLog_sound (w := (11509 / 136509)) (n := 12)
    (lo := (3380403 / 20000000)) (hi := (169020151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74009 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74009 / 62500) = 1/(62500 / 74009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (3380403 / 20000000) (169020151 / 1000000000) (Real.log (74009 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (74009 / 62500) = -Real.log (62500 / 74009) := by
    rw [show ((74009 / 62500) : ℝ) = ((62500 / 74009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (20351741 / 100000000) ≤ -Real.log (50991 / 62500) ∧
    -Real.log (50991 / 62500) ≤ (203517411 / 1000000000) := by
  have h := checkLog_sound (w := (11509 / 113491)) (n := 12)
    (lo := (20351741 / 100000000)) (hi := (203517411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 50991) = 1/(50991 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-203517411 / 1000000000) (-20351741 / 100000000) (Real.log (50991 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84643487 / 500000000) ≤ -Real.log (50000 / 59223) ∧
    -Real.log (50000 / 59223) ≤ (6771479 / 40000000) := by
  have h := checkLog_sound (w := (9223 / 109223)) (n := 12)
    (lo := (84643487 / 500000000)) (hi := (6771479 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59223 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59223 / 50000) = 1/(50000 / 59223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84643487 / 500000000) (6771479 / 40000000) (Real.log (59223 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (59223 / 50000) = -Real.log (50000 / 59223) := by
    rw [show ((59223 / 50000) : ℝ) = ((50000 / 59223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (25488101 / 125000000) ≤ -Real.log (40777 / 50000) ∧
    -Real.log (40777 / 50000) ≤ (203904809 / 1000000000) := by
  have h := checkLog_sound (w := (9223 / 90777)) (n := 12)
    (lo := (25488101 / 125000000)) (hi := (203904809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40777) = 1/(40777 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-203904809 / 1000000000) (-25488101 / 125000000) (Real.log (40777 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (752784643 / 1000000000) ≤ -Real.log (125000000000 / 265362915523) ∧
    -Real.log (125000000000 / 265362915523) ≤ (150556929 / 200000000) := by
  have h := checkLog_sound (w := (15362915523 / 515362915523)) (n := 12)
    (lo := (59637463 / 1000000000)) (hi := (7454683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265362915523 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(265362915523 / 250000000000) = 1/(125000000000 / 265362915523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (752784643 / 1000000000) (150556929 / 200000000) (Real.log (265362915523 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (265362915523 / 125000000000) = -Real.log (125000000000 / 265362915523) := by
    rw [show ((265362915523 / 125000000000) : ℝ) = ((125000000000 / 265362915523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (150826171 / 200000000) ≤ -Real.log (250000000000 / 531440781441) ∧
    -Real.log (250000000000 / 531440781441) ≤ (754130857 / 1000000000) := by
  have h := checkLog_sound (w := (31440781441 / 1031440781441)) (n := 12)
    (lo := (2439347 / 40000000)) (hi := (15245919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((531440781441 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(531440781441 / 500000000000) = 1/(250000000000 / 531440781441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (150826171 / 200000000) (754130857 / 1000000000) (Real.log (531440781441 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (531440781441 / 250000000000) = -Real.log (250000000000 / 531440781441) := by
    rw [show ((531440781441 / 250000000000) : ℝ) = ((250000000000 / 531440781441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (104602141 / 200000000) ≤ -Real.log (500000000000 / 843549685139) ∧
    -Real.log (500000000000 / 843549685139) ≤ (261505353 / 500000000) := by
  have h := checkLog_sound (w := (343549685139 / 1343549685139)) (n := 12)
    (lo := (104602141 / 200000000)) (hi := (261505353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843549685139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843549685139 / 500000000000) = 1/(500000000000 / 843549685139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (104602141 / 200000000) (261505353 / 500000000) (Real.log (843549685139 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (843549685139 / 500000000000) = -Real.log (500000000000 / 843549685139) := by
    rw [show ((843549685139 / 500000000000) : ℝ) = ((500000000000 / 843549685139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (261956927 / 500000000) ≤ -Real.log (500000000000 / 844311880357) ∧
    -Real.log (500000000000 / 844311880357) ≤ (104782771 / 200000000) := by
  have h := checkLog_sound (w := (344311880357 / 1344311880357)) (n := 12)
    (lo := (261956927 / 500000000)) (hi := (104782771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((844311880357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(844311880357 / 500000000000) = 1/(500000000000 / 844311880357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (261956927 / 500000000) (104782771 / 200000000) (Real.log (844311880357 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (844311880357 / 500000000000) = -Real.log (500000000000 / 844311880357) := by
    rw [show ((844311880357 / 500000000000) : ℝ) = ((500000000000 / 844311880357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (9313439 / 25000000) ≤ -Real.log (20000000000 / 29028259889) ∧
    -Real.log (20000000000 / 29028259889) ≤ (372537561 / 1000000000) := by
  have h := checkLog_sound (w := (9028259889 / 49028259889)) (n := 12)
    (lo := (9313439 / 25000000)) (hi := (372537561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29028259889 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29028259889 / 20000000000) = 1/(20000000000 / 29028259889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9313439 / 25000000) (372537561 / 1000000000) (Real.log (29028259889 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (29028259889 / 20000000000) = -Real.log (20000000000 / 29028259889) := by
    rw [show ((29028259889 / 20000000000) : ℝ) = ((20000000000 / 29028259889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (186595891 / 500000000) ≤ -Real.log (125000000000 / 181545356451) ∧
    -Real.log (125000000000 / 181545356451) ≤ (373191783 / 1000000000) := by
  have h := checkLog_sound (w := (56545356451 / 306545356451)) (n := 12)
    (lo := (186595891 / 500000000)) (hi := (373191783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181545356451 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181545356451 / 125000000000) = 1/(125000000000 / 181545356451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (186595891 / 500000000) (373191783 / 1000000000) (Real.log (181545356451 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (181545356451 / 125000000000) = -Real.log (125000000000 / 181545356451) := by
    rw [show ((181545356451 / 125000000000) : ℝ) = ((125000000000 / 181545356451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34617833 / 1000000000) ≤ -Real.log (2414936271 / 2500000000) ∧
    -Real.log (2414936271 / 2500000000) ≤ (17308917 / 500000000) := by
  have h := checkLog_sound (w := (85063729 / 4914936271)) (n := 12)
    (lo := (34617833 / 1000000000)) (hi := (17308917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2414936271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2414936271) = 1/(2414936271 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17308917 / 500000000) (-34617833 / 1000000000) (Real.log (2414936271 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (34497259 / 1000000000) ≤ -Real.log (3773792919 / 3906250000) ∧
    -Real.log (3773792919 / 3906250000) ≤ (1724863 / 50000000) := by
  have h := checkLog_sound (w := (132457081 / 7680042919)) (n := 12)
    (lo := (34497259 / 1000000000)) (hi := (1724863 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3773792919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3773792919) = 1/(3773792919 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1724863 / 50000000) (-34497259 / 1000000000) (Real.log (3773792919 / 3906250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell187

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell188Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell188
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

theorem reflection_log_1_neg : (77007569 / 250000000) ≤ -Real.log (5120 / 6967) ∧
    -Real.log (5120 / 6967) ≤ (308030277 / 1000000000) := by
  have h := checkLog_sound (w := (1847 / 12087)) (n := 12)
    (lo := (77007569 / 250000000)) (hi := (308030277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6967 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6967 / 5120) = 1/(5120 / 6967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (77007569 / 250000000) (308030277 / 1000000000) (Real.log (6967 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6967 / 5120) = -Real.log (5120 / 6967) := by
    rw [show ((6967 / 5120) : ℝ) = ((5120 / 6967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (447447443 / 1000000000) ≤ -Real.log (3273 / 5120) ∧
    -Real.log (3273 / 5120) ≤ (111861861 / 250000000) := by
  have h := checkLog_sound (w := (1847 / 8393)) (n := 12)
    (lo := (447447443 / 1000000000)) (hi := (111861861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3273) = 1/(3273 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-111861861 / 250000000) (-447447443 / 1000000000) (Real.log (3273 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (153799791 / 500000000) ≤ -Real.log (1280 / 1741) ∧
    -Real.log (1280 / 1741) ≤ (307599583 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 3021)) (n := 12)
    (lo := (153799791 / 500000000)) (hi := (307599583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1741 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1741 / 1280) = 1/(1280 / 1741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (153799791 / 500000000) (307599583 / 1000000000) (Real.log (1741 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1741 / 1280) = -Real.log (1280 / 1741) := by
    rw [show ((1741 / 1280) : ℝ) = ((1280 / 1741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (446531273 / 1000000000) ≤ -Real.log (819 / 1280) ∧
    -Real.log (819 / 1280) ≤ (223265637 / 500000000) := by
  have h := checkLog_sound (w := (461 / 2099)) (n := 12)
    (lo := (446531273 / 1000000000)) (hi := (223265637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 819) = 1/(819 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-223265637 / 500000000) (-446531273 / 1000000000) (Real.log (819 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (228030789 / 1000000000) ≤ -Real.log (250000 / 314031) ∧
    -Real.log (250000 / 314031) ≤ (22803079 / 100000000) := by
  have h := checkLog_sound (w := (64031 / 564031)) (n := 12)
    (lo := (228030789 / 1000000000)) (hi := (22803079 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314031 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314031 / 250000) = 1/(250000 / 314031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (228030789 / 1000000000) (22803079 / 100000000) (Real.log (314031 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (314031 / 250000) = -Real.log (250000 / 314031) := by
    rw [show ((314031 / 250000) : ℝ) = ((250000 / 314031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (73970231 / 250000000) ≤ -Real.log (185969 / 250000) ∧
    -Real.log (185969 / 250000) ≤ (11835237 / 40000000) := by
  have h := checkLog_sound (w := (64031 / 435969)) (n := 12)
    (lo := (73970231 / 250000000)) (hi := (11835237 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 185969) = 1/(185969 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11835237 / 40000000) (-73970231 / 250000000) (Real.log (185969 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (114183741 / 500000000) ≤ -Real.log (1000000 / 1256547) ∧
    -Real.log (1000000 / 1256547) ≤ (228367483 / 1000000000) := by
  have h := checkLog_sound (w := (256547 / 2256547)) (n := 12)
    (lo := (114183741 / 500000000)) (hi := (228367483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1256547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1256547 / 1000000) = 1/(1000000 / 1256547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (114183741 / 500000000) (228367483 / 1000000000) (Real.log (1256547 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1256547 / 1000000) = -Real.log (1000000 / 1256547) := by
    rw [show ((1256547 / 1000000) : ℝ) = ((1000000 / 1256547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (296449729 / 1000000000) ≤ -Real.log (743453 / 1000000) ∧
    -Real.log (743453 / 1000000) ≤ (29644973 / 100000000) := by
  have h := checkLog_sound (w := (256547 / 1743453)) (n := 12)
    (lo := (296449729 / 1000000000)) (hi := (29644973 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 743453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 743453) = 1/(743453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-29644973 / 100000000) (-296449729 / 1000000000) (Real.log (743453 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16928613 / 100000000) ≤ -Real.log (1000000 / 1184459) ∧
    -Real.log (1000000 / 1184459) ≤ (169286131 / 1000000000) := by
  have h := checkLog_sound (w := (184459 / 2184459)) (n := 12)
    (lo := (16928613 / 100000000)) (hi := (169286131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1184459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1184459 / 1000000) = 1/(1000000 / 1184459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16928613 / 100000000) (169286131 / 1000000000) (Real.log (1184459 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1184459 / 1000000) = -Real.log (1000000 / 1184459) := by
    rw [show ((1184459 / 1000000) : ℝ) = ((1000000 / 1184459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (101951791 / 500000000) ≤ -Real.log (815541 / 1000000) ∧
    -Real.log (815541 / 1000000) ≤ (203903583 / 1000000000) := by
  have h := checkLog_sound (w := (184459 / 1815541)) (n := 12)
    (lo := (101951791 / 500000000)) (hi := (203903583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 815541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 815541) = 1/(815541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-203903583 / 1000000000) (-101951791 / 500000000) (Real.log (815541 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169552883 / 1000000000) ≤ -Real.log (40000 / 47391) ∧
    -Real.log (40000 / 47391) ≤ (42388221 / 250000000) := by
  have h := checkLog_sound (w := (7391 / 87391)) (n := 12)
    (lo := (169552883 / 1000000000)) (hi := (42388221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47391 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47391 / 40000) = 1/(40000 / 47391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169552883 / 1000000000) (42388221 / 250000000) (Real.log (47391 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (47391 / 40000) = -Real.log (40000 / 47391) := by
    rw [show ((47391 / 40000) : ℝ) = ((40000 / 47391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (20429113 / 100000000) ≤ -Real.log (32609 / 40000) ∧
    -Real.log (32609 / 40000) ≤ (204291131 / 1000000000) := by
  have h := checkLog_sound (w := (7391 / 72609)) (n := 12)
    (lo := (20429113 / 100000000)) (hi := (204291131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32609) = 1/(32609 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-204291131 / 1000000000) (-20429113 / 100000000) (Real.log (32609 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (150826171 / 200000000) ≤ -Real.log (500000000000 / 1062881562881) ∧
    -Real.log (500000000000 / 1062881562881) ≤ (754130857 / 1000000000) := by
  have h := checkLog_sound (w := (62881562881 / 2062881562881)) (n := 12)
    (lo := (2439347 / 40000000)) (hi := (15245919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1062881562881 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1062881562881 / 1000000000000) = 1/(500000000000 / 1062881562881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (150826171 / 200000000) (754130857 / 1000000000) (Real.log (1062881562881 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1062881562881 / 500000000000) = -Real.log (500000000000 / 1062881562881) := by
    rw [show ((1062881562881 / 500000000000) : ℝ) = ((500000000000 / 1062881562881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (755477719 / 1000000000) ≤ -Real.log (250000000000 / 532157042469) ∧
    -Real.log (250000000000 / 532157042469) ≤ (755477721 / 1000000000) := by
  have h := checkLog_sound (w := (32157042469 / 1032157042469)) (n := 12)
    (lo := (62330539 / 1000000000)) (hi := (3116527 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((532157042469 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(532157042469 / 500000000000) = 1/(250000000000 / 532157042469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (755477719 / 1000000000) (755477721 / 1000000000) (Real.log (532157042469 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (532157042469 / 250000000000) = -Real.log (250000000000 / 532157042469) := by
    rw [show ((532157042469 / 250000000000) : ℝ) = ((250000000000 / 532157042469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (523911713 / 1000000000) ≤ -Real.log (15625000000 / 26384689787) ∧
    -Real.log (15625000000 / 26384689787) ≤ (261955857 / 500000000) := by
  have h := checkLog_sound (w := (10759689787 / 42009689787)) (n := 12)
    (lo := (523911713 / 1000000000)) (hi := (261955857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26384689787 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26384689787 / 15625000000) = 1/(15625000000 / 26384689787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (523911713 / 1000000000) (261955857 / 500000000) (Real.log (26384689787 / 15625000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (26384689787 / 15625000000) = -Real.log (15625000000 / 26384689787) := by
    rw [show ((26384689787 / 15625000000) : ℝ) = ((15625000000 / 26384689787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (131204303 / 250000000) ≤ -Real.log (500000000000 / 845074940851) ∧
    -Real.log (500000000000 / 845074940851) ≤ (524817213 / 1000000000) := by
  have h := checkLog_sound (w := (345074940851 / 1345074940851)) (n := 12)
    (lo := (131204303 / 250000000)) (hi := (524817213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((845074940851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(845074940851 / 500000000000) = 1/(500000000000 / 845074940851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (131204303 / 250000000) (524817213 / 1000000000) (Real.log (845074940851 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (845074940851 / 500000000000) = -Real.log (500000000000 / 845074940851) := by
    rw [show ((845074940851 / 500000000000) : ℝ) = ((500000000000 / 845074940851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (23324357 / 62500000) ≤ -Real.log (125000000000 / 181544980571) ∧
    -Real.log (125000000000 / 181544980571) ≤ (373189713 / 1000000000) := by
  have h := checkLog_sound (w := (56544980571 / 306544980571)) (n := 12)
    (lo := (23324357 / 62500000)) (hi := (373189713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181544980571 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181544980571 / 125000000000) = 1/(125000000000 / 181544980571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (23324357 / 62500000) (373189713 / 1000000000) (Real.log (181544980571 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (181544980571 / 125000000000) = -Real.log (125000000000 / 181544980571) := by
    rw [show ((181544980571 / 125000000000) : ℝ) = ((125000000000 / 181544980571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (373844013 / 1000000000) ≤ -Real.log (100000000000 / 145331043577) ∧
    -Real.log (100000000000 / 145331043577) ≤ (186922007 / 500000000) := by
  have h := checkLog_sound (w := (45331043577 / 245331043577)) (n := 12)
    (lo := (373844013 / 1000000000)) (hi := (186922007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145331043577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145331043577 / 100000000000) = 1/(100000000000 / 145331043577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (373844013 / 1000000000) (186922007 / 500000000) (Real.log (145331043577 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (145331043577 / 100000000000) = -Real.log (100000000000 / 145331043577) := by
    rw [show ((145331043577 / 100000000000) : ℝ) = ((100000000000 / 145331043577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34738247 / 1000000000) ≤ -Real.log (1545373119 / 1600000000) ∧
    -Real.log (1545373119 / 1600000000) ≤ (4342281 / 125000000) := by
  have h := checkLog_sound (w := (54626881 / 3145373119)) (n := 12)
    (lo := (34738247 / 1000000000)) (hi := (4342281 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1545373119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1545373119) = 1/(1545373119 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4342281 / 125000000) (-34738247 / 1000000000) (Real.log (1545373119 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8654363 / 250000000) ≤ -Real.log (965974877319 / 1000000000000) ∧
    -Real.log (965974877319 / 1000000000000) ≤ (34617453 / 1000000000) := by
  have h := checkLog_sound (w := (34025122681 / 1965974877319)) (n := 12)
    (lo := (8654363 / 250000000)) (hi := (34617453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965974877319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965974877319) = 1/(965974877319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-34617453 / 1000000000) (-8654363 / 250000000) (Real.log (965974877319 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell188

end


