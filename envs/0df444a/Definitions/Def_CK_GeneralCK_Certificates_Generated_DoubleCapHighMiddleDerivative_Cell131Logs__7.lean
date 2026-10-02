-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell131Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell131Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:45:46.207647+00:00
-- url     : https://prove2.me/theorems/65a03564-b3c9-424e-a22e-8e0d3b33388e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell131Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell132…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell131Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell132Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell133Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell134Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell135Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell136Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell137Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell131Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell132Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell133Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell134Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell135Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell136Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell137Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell131Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell132Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell133Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell134Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell135Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell136Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell137Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell131Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell132Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell133Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell134Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell135Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell136Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell137Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell131Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell131
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

theorem reflection_log_1_neg : (70794941 / 250000000) ≤ -Real.log (1280 / 1699) ∧
    -Real.log (1280 / 1699) ≤ (56635953 / 200000000) := by
  have h := checkLog_sound (w := (419 / 2979)) (n := 12)
    (lo := (70794941 / 250000000)) (hi := (56635953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1699 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1699 / 1280) = 1/(1280 / 1699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (70794941 / 250000000) (56635953 / 200000000) (Real.log (1699 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1699 / 1280) = -Real.log (1280 / 1699) := by
    rw [show ((1699 / 1280) : ℝ) = ((1280 / 1699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (99130213 / 250000000) ≤ -Real.log (861 / 1280) ∧
    -Real.log (861 / 1280) ≤ (396520853 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2141)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 861) = 1/(861 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-396520853 / 1000000000) (-99130213 / 250000000) (Real.log (861 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (282738231 / 1000000000) ≤ -Real.log (5120 / 6793) ∧
    -Real.log (5120 / 6793) ≤ (35342279 / 125000000) := by
  have h := checkLog_sound (w := (1673 / 11913)) (n := 12)
    (lo := (282738231 / 1000000000)) (hi := (35342279 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6793 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6793 / 5120) = 1/(5120 / 6793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (282738231 / 1000000000) (35342279 / 125000000) (Real.log (6793 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6793 / 5120) = -Real.log (5120 / 6793) := by
    rw [show ((6793 / 5120) : ℝ) = ((5120 / 6793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (395650151 / 1000000000) ≤ -Real.log (3447 / 5120) ∧
    -Real.log (3447 / 5120) ≤ (49456269 / 125000000) := by
  have h := checkLog_sound (w := (1673 / 8567)) (n := 12)
    (lo := (395650151 / 1000000000)) (hi := (49456269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3447) = 1/(3447 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-49456269 / 125000000) (-395650151 / 1000000000) (Real.log (3447 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41748551 / 200000000) ≤ -Real.log (15625 / 19252) ∧
    -Real.log (15625 / 19252) ≤ (52185689 / 250000000) := by
  have h := checkLog_sound (w := (3627 / 34877)) (n := 12)
    (lo := (41748551 / 200000000)) (hi := (52185689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19252 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19252 / 15625) = 1/(15625 / 19252) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41748551 / 200000000) (52185689 / 250000000) (Real.log (19252 / 15625)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19252 / 15625) = -Real.log (15625 / 19252) := by
    rw [show ((19252 / 15625) : ℝ) = ((15625 / 19252) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (132066113 / 500000000) ≤ -Real.log (11998 / 15625) ∧
    -Real.log (11998 / 15625) ≤ (264132227 / 1000000000) := by
  have h := checkLog_sound (w := (3627 / 27623)) (n := 12)
    (lo := (132066113 / 500000000)) (hi := (264132227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11998) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11998) = 1/(11998 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-264132227 / 1000000000) (-132066113 / 500000000) (Real.log (11998 / 15625)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (104542597 / 500000000) ≤ -Real.log (20000 / 24651) ∧
    -Real.log (20000 / 24651) ≤ (41817039 / 200000000) := by
  have h := checkLog_sound (w := (4651 / 44651)) (n := 12)
    (lo := (104542597 / 500000000)) (hi := (41817039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24651 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24651 / 20000) = 1/(20000 / 24651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (104542597 / 500000000) (41817039 / 200000000) (Real.log (24651 / 20000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24651 / 20000) = -Real.log (20000 / 24651) := by
    rw [show ((24651 / 20000) : ℝ) = ((20000 / 24651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (66170487 / 250000000) ≤ -Real.log (15349 / 20000) ∧
    -Real.log (15349 / 20000) ≤ (264681949 / 1000000000) := by
  have h := checkLog_sound (w := (4651 / 35349)) (n := 12)
    (lo := (66170487 / 250000000)) (hi := (264681949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15349) = 1/(15349 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-264681949 / 1000000000) (-66170487 / 250000000) (Real.log (15349 / 20000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (154116679 / 1000000000) ≤ -Real.log (1000000 / 1166627) ∧
    -Real.log (1000000 / 1166627) ≤ (3852917 / 25000000) := by
  have h := checkLog_sound (w := (166627 / 2166627)) (n := 12)
    (lo := (154116679 / 1000000000)) (hi := (3852917 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1166627 / 1000000) = 1/(1000000 / 1166627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (154116679 / 1000000000) (3852917 / 25000000) (Real.log (1166627 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1166627 / 1000000) = -Real.log (1000000 / 1166627) := by
    rw [show ((1166627 / 1000000) : ℝ) = ((1000000 / 1166627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182273957 / 1000000000) ≤ -Real.log (833373 / 1000000) ∧
    -Real.log (833373 / 1000000) ≤ (91136979 / 500000000) := by
  have h := checkLog_sound (w := (166627 / 1833373)) (n := 12)
    (lo := (182273957 / 1000000000)) (hi := (91136979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 833373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 833373) = 1/(833373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91136979 / 500000000) (-182273957 / 1000000000) (Real.log (833373 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (154384081 / 1000000000) ≤ -Real.log (1000000 / 1166939) ∧
    -Real.log (1000000 / 1166939) ≤ (77192041 / 500000000) := by
  have h := checkLog_sound (w := (166939 / 2166939)) (n := 12)
    (lo := (154384081 / 1000000000)) (hi := (77192041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1166939 / 1000000) = 1/(1000000 / 1166939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (154384081 / 1000000000) (77192041 / 500000000) (Real.log (1166939 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1166939 / 1000000) = -Real.log (1000000 / 1166939) := by
    rw [show ((1166939 / 1000000) : ℝ) = ((1000000 / 1166939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18264841 / 100000000) ≤ -Real.log (833061 / 1000000) ∧
    -Real.log (833061 / 1000000) ≤ (182648411 / 1000000000) := by
  have h := checkLog_sound (w := (166939 / 1833061)) (n := 12)
    (lo := (18264841 / 100000000)) (hi := (182648411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 833061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 833061) = 1/(833061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-182648411 / 1000000000) (-18264841 / 100000000) (Real.log (833061 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (339194191 / 500000000) ≤ -Real.log (31250000000 / 61584348709) ∧
    -Real.log (31250000000 / 61584348709) ≤ (678388383 / 1000000000) := by
  have h := checkLog_sound (w := (30334348709 / 92834348709)) (n := 12)
    (lo := (339194191 / 500000000)) (hi := (678388383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61584348709 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61584348709 / 31250000000) = 1/(31250000000 / 61584348709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (339194191 / 500000000) (678388383 / 1000000000) (Real.log (61584348709 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61584348709 / 31250000000) = -Real.log (31250000000 / 61584348709) := by
    rw [show ((61584348709 / 31250000000) : ℝ) = ((31250000000 / 61584348709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (679700617 / 1000000000) ≤ -Real.log (500000000000 / 986643437863) ∧
    -Real.log (500000000000 / 986643437863) ≤ (339850309 / 500000000) := by
  have h := checkLog_sound (w := (486643437863 / 1486643437863)) (n := 12)
    (lo := (679700617 / 1000000000)) (hi := (339850309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986643437863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986643437863 / 500000000000) = 1/(500000000000 / 986643437863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (679700617 / 1000000000) (339850309 / 500000000) (Real.log (986643437863 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (986643437863 / 500000000000) = -Real.log (500000000000 / 986643437863) := by
    rw [show ((986643437863 / 500000000000) : ℝ) = ((500000000000 / 986643437863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (236437491 / 500000000) ≤ -Real.log (500000000000 / 802300383397) ∧
    -Real.log (500000000000 / 802300383397) ≤ (472874983 / 1000000000) := by
  have h := checkLog_sound (w := (302300383397 / 1302300383397)) (n := 12)
    (lo := (236437491 / 500000000)) (hi := (472874983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802300383397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802300383397 / 500000000000) = 1/(500000000000 / 802300383397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (236437491 / 500000000) (472874983 / 1000000000) (Real.log (802300383397 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (802300383397 / 500000000000) = -Real.log (500000000000 / 802300383397) := by
    rw [show ((802300383397 / 500000000000) : ℝ) = ((500000000000 / 802300383397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (236883571 / 500000000) ≤ -Real.log (500000000000 / 803016483159) ∧
    -Real.log (500000000000 / 803016483159) ≤ (473767143 / 1000000000) := by
  have h := checkLog_sound (w := (303016483159 / 1303016483159)) (n := 12)
    (lo := (236883571 / 500000000)) (hi := (473767143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803016483159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803016483159 / 500000000000) = 1/(500000000000 / 803016483159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (236883571 / 500000000) (473767143 / 1000000000) (Real.log (803016483159 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (803016483159 / 500000000000) = -Real.log (500000000000 / 803016483159) := by
    rw [show ((803016483159 / 500000000000) : ℝ) = ((500000000000 / 803016483159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (336390637 / 1000000000) ≤ -Real.log (250000000000 / 349971441359) ∧
    -Real.log (250000000000 / 349971441359) ≤ (168195319 / 500000000) := by
  have h := checkLog_sound (w := (99971441359 / 599971441359)) (n := 12)
    (lo := (336390637 / 1000000000)) (hi := (168195319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349971441359 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349971441359 / 250000000000) = 1/(250000000000 / 349971441359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (336390637 / 1000000000) (168195319 / 500000000) (Real.log (349971441359 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (349971441359 / 250000000000) = -Real.log (250000000000 / 349971441359) := by
    rw [show ((349971441359 / 250000000000) : ℝ) = ((250000000000 / 349971441359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (337032491 / 1000000000) ≤ -Real.log (2500000000 / 3501961441) ∧
    -Real.log (2500000000 / 3501961441) ≤ (84258123 / 250000000) := by
  have h := checkLog_sound (w := (1001961441 / 6001961441)) (n := 12)
    (lo := (337032491 / 1000000000)) (hi := (84258123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3501961441 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3501961441 / 2500000000) = 1/(2500000000 / 3501961441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (337032491 / 1000000000) (84258123 / 250000000) (Real.log (3501961441 / 2500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3501961441 / 2500000000) = -Real.log (2500000000 / 3501961441) := by
    rw [show ((3501961441 / 2500000000) : ℝ) = ((2500000000 / 3501961441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (28264329 / 1000000000) ≤ -Real.log (972131370279 / 1000000000000) ∧
    -Real.log (972131370279 / 1000000000000) ≤ (2826433 / 100000000) := by
  have h := checkLog_sound (w := (27868629721 / 1972131370279)) (n := 12)
    (lo := (28264329 / 1000000000)) (hi := (2826433 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972131370279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972131370279) = 1/(972131370279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2826433 / 100000000) (-28264329 / 1000000000) (Real.log (972131370279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14078639 / 500000000) ≤ -Real.log (972235442871 / 1000000000000) ∧
    -Real.log (972235442871 / 1000000000000) ≤ (28157279 / 1000000000) := by
  have h := checkLog_sound (w := (27764557129 / 1972235442871)) (n := 12)
    (lo := (14078639 / 500000000)) (hi := (28157279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972235442871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972235442871) = 1/(972235442871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-28157279 / 1000000000) (-14078639 / 500000000) (Real.log (972235442871 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell131

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell132Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell132
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

theorem reflection_log_1_neg : (283621103 / 1000000000) ≤ -Real.log (5120 / 6799) ∧
    -Real.log (5120 / 6799) ≤ (17726319 / 62500000) := by
  have h := checkLog_sound (w := (1679 / 11919)) (n := 12)
    (lo := (283621103 / 1000000000)) (hi := (17726319 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6799 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6799 / 5120) = 1/(5120 / 6799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (283621103 / 1000000000) (17726319 / 62500000) (Real.log (6799 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6799 / 5120) = -Real.log (5120 / 6799) := by
    rw [show ((6799 / 5120) : ℝ) = ((5120 / 6799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (49674039 / 125000000) ≤ -Real.log (3441 / 5120) ∧
    -Real.log (3441 / 5120) ≤ (397392313 / 1000000000) := by
  have h := checkLog_sound (w := (1679 / 8561)) (n := 12)
    (lo := (49674039 / 125000000)) (hi := (397392313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3441) = 1/(3441 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-397392313 / 1000000000) (-49674039 / 125000000) (Real.log (3441 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (70794941 / 250000000) ≤ -Real.log (1280 / 1699) ∧
    -Real.log (1280 / 1699) ≤ (56635953 / 200000000) := by
  have h := checkLog_sound (w := (419 / 2979)) (n := 12)
    (lo := (70794941 / 250000000)) (hi := (56635953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1699 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1699 / 1280) = 1/(1280 / 1699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (70794941 / 250000000) (56635953 / 200000000) (Real.log (1699 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1699 / 1280) = -Real.log (1280 / 1699) := by
    rw [show ((1699 / 1280) : ℝ) = ((1280 / 1699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (99130213 / 250000000) ≤ -Real.log (861 / 1280) ∧
    -Real.log (861 / 1280) ≤ (396520853 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2141)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 861) = 1/(861 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-396520853 / 1000000000) (-99130213 / 250000000) (Real.log (861 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (104542191 / 500000000) ≤ -Real.log (1000000 / 1232549) ∧
    -Real.log (1000000 / 1232549) ≤ (209084383 / 1000000000) := by
  have h := checkLog_sound (w := (232549 / 2232549)) (n := 12)
    (lo := (104542191 / 500000000)) (hi := (209084383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1232549 / 1000000) = 1/(1000000 / 1232549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (104542191 / 500000000) (209084383 / 1000000000) (Real.log (1232549 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1232549 / 1000000) = -Real.log (1000000 / 1232549) := by
    rw [show ((1232549 / 1000000) : ℝ) = ((1000000 / 1232549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (52936129 / 200000000) ≤ -Real.log (767451 / 1000000) ∧
    -Real.log (767451 / 1000000) ≤ (132340323 / 500000000) := by
  have h := checkLog_sound (w := (232549 / 1767451)) (n := 12)
    (lo := (52936129 / 200000000)) (hi := (132340323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 767451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 767451) = 1/(767451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-132340323 / 500000000) (-52936129 / 200000000) (Real.log (767451 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (52356473 / 250000000) ≤ -Real.log (100000 / 123297) ∧
    -Real.log (100000 / 123297) ≤ (209425893 / 1000000000) := by
  have h := checkLog_sound (w := (23297 / 223297)) (n := 12)
    (lo := (52356473 / 250000000)) (hi := (209425893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123297 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123297 / 100000) = 1/(100000 / 123297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (52356473 / 250000000) (209425893 / 1000000000) (Real.log (123297 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (123297 / 100000) = -Real.log (100000 / 123297) := by
    rw [show ((123297 / 100000) : ℝ) = ((100000 / 123297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (66307341 / 250000000) ≤ -Real.log (76703 / 100000) ∧
    -Real.log (76703 / 100000) ≤ (53045873 / 200000000) := by
  have h := checkLog_sound (w := (23297 / 176703)) (n := 12)
    (lo := (66307341 / 250000000)) (hi := (53045873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76703) = 1/(76703 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-53045873 / 200000000) (-66307341 / 250000000) (Real.log (76703 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (19297903 / 125000000) ≤ -Real.log (500000 / 583469) ∧
    -Real.log (500000 / 583469) ≤ (6175329 / 40000000) := by
  have h := checkLog_sound (w := (83469 / 1083469)) (n := 12)
    (lo := (19297903 / 125000000)) (hi := (6175329 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583469 / 500000) = 1/(500000 / 583469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (19297903 / 125000000) (6175329 / 40000000) (Real.log (583469 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (583469 / 500000) = -Real.log (500000 / 583469) := by
    rw [show ((583469 / 500000) : ℝ) = ((500000 / 583469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182647209 / 1000000000) ≤ -Real.log (416531 / 500000) ∧
    -Real.log (416531 / 500000) ≤ (18264721 / 100000000) := by
  have h := checkLog_sound (w := (83469 / 916531)) (n := 12)
    (lo := (182647209 / 1000000000)) (hi := (18264721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 416531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 416531) = 1/(416531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18264721 / 100000000) (-182647209 / 1000000000) (Real.log (416531 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (77325277 / 500000000) ≤ -Real.log (4000 / 4669) ∧
    -Real.log (4000 / 4669) ≤ (30930111 / 200000000) := by
  have h := checkLog_sound (w := (669 / 8669)) (n := 12)
    (lo := (77325277 / 500000000)) (hi := (30930111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4669 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4669 / 4000) = 1/(4000 / 4669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (77325277 / 500000000) (30930111 / 200000000) (Real.log (4669 / 4000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (4669 / 4000) = -Real.log (4000 / 4669) := by
    rw [show ((4669 / 4000) : ℝ) = ((4000 / 4669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (183021801 / 1000000000) ≤ -Real.log (3331 / 4000) ∧
    -Real.log (3331 / 4000) ≤ (91510901 / 500000000) := by
  have h := checkLog_sound (w := (669 / 7331)) (n := 12)
    (lo := (183021801 / 1000000000)) (hi := (91510901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3331) = 1/(3331 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-91510901 / 500000000) (-183021801 / 1000000000) (Real.log (3331 / 4000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (679700617 / 1000000000) ≤ -Real.log (250000000000 / 493321718931) ∧
    -Real.log (250000000000 / 493321718931) ≤ (339850309 / 500000000) := by
  have h := checkLog_sound (w := (243321718931 / 743321718931)) (n := 12)
    (lo := (679700617 / 1000000000)) (hi := (339850309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493321718931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493321718931 / 250000000000) = 1/(250000000000 / 493321718931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (679700617 / 1000000000) (339850309 / 500000000) (Real.log (493321718931 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (493321718931 / 250000000000) = -Real.log (250000000000 / 493321718931) := by
    rw [show ((493321718931 / 250000000000) : ℝ) = ((250000000000 / 493321718931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (136202683 / 200000000) ≤ -Real.log (62500000000 / 123492444057) ∧
    -Real.log (62500000000 / 123492444057) ≤ (85126677 / 125000000) := by
  have h := checkLog_sound (w := (60992444057 / 185992444057)) (n := 12)
    (lo := (136202683 / 200000000)) (hi := (85126677 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123492444057 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123492444057 / 62500000000) = 1/(62500000000 / 123492444057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (136202683 / 200000000) (85126677 / 125000000) (Real.log (123492444057 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (123492444057 / 62500000000) = -Real.log (62500000000 / 123492444057) := by
    rw [show ((123492444057 / 62500000000) : ℝ) = ((62500000000 / 123492444057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (473765027 / 1000000000) ≤ -Real.log (125000000000 / 200753696327) ∧
    -Real.log (125000000000 / 200753696327) ≤ (118441257 / 250000000) := by
  have h := checkLog_sound (w := (75753696327 / 325753696327)) (n := 12)
    (lo := (473765027 / 1000000000)) (hi := (118441257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200753696327 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200753696327 / 125000000000) = 1/(125000000000 / 200753696327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (473765027 / 1000000000) (118441257 / 250000000) (Real.log (200753696327 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (200753696327 / 125000000000) = -Real.log (125000000000 / 200753696327) := by
    rw [show ((200753696327 / 125000000000) : ℝ) = ((125000000000 / 200753696327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (474655257 / 1000000000) ≤ -Real.log (500000000000 / 803729971449) ∧
    -Real.log (500000000000 / 803729971449) ≤ (237327629 / 500000000) := by
  have h := checkLog_sound (w := (303729971449 / 1303729971449)) (n := 12)
    (lo := (474655257 / 1000000000)) (hi := (237327629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803729971449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803729971449 / 500000000000) = 1/(500000000000 / 803729971449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (474655257 / 1000000000) (237327629 / 500000000) (Real.log (803729971449 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (803729971449 / 500000000000) = -Real.log (500000000000 / 803729971449) := by
    rw [show ((803729971449 / 500000000000) : ℝ) = ((500000000000 / 803729971449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (168515217 / 500000000) ≤ -Real.log (500000000000 / 700390847259) ∧
    -Real.log (500000000000 / 700390847259) ≤ (67406087 / 200000000) := by
  have h := checkLog_sound (w := (200390847259 / 1200390847259)) (n := 12)
    (lo := (168515217 / 500000000)) (hi := (67406087 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700390847259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700390847259 / 500000000000) = 1/(500000000000 / 700390847259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (168515217 / 500000000) (67406087 / 200000000) (Real.log (700390847259 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (700390847259 / 500000000000) = -Real.log (500000000000 / 700390847259) := by
    rw [show ((700390847259 / 500000000000) : ℝ) = ((500000000000 / 700390847259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (84418089 / 250000000) ≤ -Real.log (125000000000 / 175210147103) ∧
    -Real.log (125000000000 / 175210147103) ≤ (337672357 / 1000000000) := by
  have h := checkLog_sound (w := (50210147103 / 300210147103)) (n := 12)
    (lo := (84418089 / 250000000)) (hi := (337672357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175210147103 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175210147103 / 125000000000) = 1/(125000000000 / 175210147103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (84418089 / 250000000) (337672357 / 1000000000) (Real.log (175210147103 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (175210147103 / 125000000000) = -Real.log (125000000000 / 175210147103) := by
    rw [show ((175210147103 / 125000000000) : ℝ) = ((125000000000 / 175210147103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (28371247 / 1000000000) ≤ -Real.log (15552439 / 16000000) ∧
    -Real.log (15552439 / 16000000) ≤ (1773203 / 62500000) := by
  have h := checkLog_sound (w := (447561 / 31552439)) (n := 12)
    (lo := (28371247 / 1000000000)) (hi := (1773203 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 15552439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 15552439) = 1/(15552439 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1773203 / 62500000) (-28371247 / 1000000000) (Real.log (15552439 / 16000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5652797 / 200000000) ≤ -Real.log (243032926039 / 250000000000) ∧
    -Real.log (243032926039 / 250000000000) ≤ (14131993 / 500000000) := by
  have h := checkLog_sound (w := (6967073961 / 493032926039)) (n := 12)
    (lo := (5652797 / 200000000)) (hi := (14131993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243032926039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243032926039) = 1/(243032926039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-14131993 / 500000000) (-5652797 / 200000000) (Real.log (243032926039 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell132

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell133Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell133
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

theorem reflection_log_1_neg : (284062247 / 1000000000) ≤ -Real.log (2560 / 3401) ∧
    -Real.log (2560 / 3401) ≤ (35507781 / 125000000) := by
  have h := checkLog_sound (w := (841 / 5961)) (n := 12)
    (lo := (284062247 / 1000000000)) (hi := (35507781 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3401 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3401 / 2560) = 1/(2560 / 3401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (284062247 / 1000000000) (35507781 / 125000000) (Real.log (3401 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3401 / 2560) = -Real.log (2560 / 3401) := by
    rw [show ((3401 / 2560) : ℝ) = ((2560 / 3401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (99566133 / 250000000) ≤ -Real.log (1719 / 2560) ∧
    -Real.log (1719 / 2560) ≤ (398264533 / 1000000000) := by
  have h := checkLog_sound (w := (841 / 4279)) (n := 12)
    (lo := (99566133 / 250000000)) (hi := (398264533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1719) = 1/(1719 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-398264533 / 1000000000) (-99566133 / 250000000) (Real.log (1719 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (283621103 / 1000000000) ≤ -Real.log (5120 / 6799) ∧
    -Real.log (5120 / 6799) ≤ (17726319 / 62500000) := by
  have h := checkLog_sound (w := (1679 / 11919)) (n := 12)
    (lo := (283621103 / 1000000000)) (hi := (17726319 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6799 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6799 / 5120) = 1/(5120 / 6799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (283621103 / 1000000000) (17726319 / 62500000) (Real.log (6799 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6799 / 5120) = -Real.log (5120 / 6799) := by
    rw [show ((6799 / 5120) : ℝ) = ((5120 / 6799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (49674039 / 125000000) ≤ -Real.log (3441 / 5120) ∧
    -Real.log (3441 / 5120) ≤ (397392313 / 1000000000) := by
  have h := checkLog_sound (w := (1679 / 8561)) (n := 12)
    (lo := (49674039 / 125000000)) (hi := (397392313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3441) = 1/(3441 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-397392313 / 1000000000) (-49674039 / 125000000) (Real.log (3441 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (209425081 / 1000000000) ≤ -Real.log (1000000 / 1232969) ∧
    -Real.log (1000000 / 1232969) ≤ (104712541 / 500000000) := by
  have h := checkLog_sound (w := (232969 / 2232969)) (n := 12)
    (lo := (209425081 / 1000000000)) (hi := (104712541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1232969 / 1000000) = 1/(1000000 / 1232969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (209425081 / 1000000000) (104712541 / 500000000) (Real.log (1232969 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1232969 / 1000000) = -Real.log (1000000 / 1232969) := by
    rw [show ((1232969 / 1000000) : ℝ) = ((1000000 / 1232969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (265228061 / 1000000000) ≤ -Real.log (767031 / 1000000) ∧
    -Real.log (767031 / 1000000) ≤ (132614031 / 500000000) := by
  have h := checkLog_sound (w := (232969 / 1767031)) (n := 12)
    (lo := (265228061 / 1000000000)) (hi := (132614031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 767031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 767031) = 1/(767031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-132614031 / 500000000) (-265228061 / 1000000000) (Real.log (767031 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8390659 / 40000000) ≤ -Real.log (100000 / 123339) ∧
    -Real.log (100000 / 123339) ≤ (52441619 / 250000000) := by
  have h := checkLog_sound (w := (23339 / 223339)) (n := 12)
    (lo := (8390659 / 40000000)) (hi := (52441619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123339 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123339 / 100000) = 1/(100000 / 123339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8390659 / 40000000) (52441619 / 250000000) (Real.log (123339 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (123339 / 100000) = -Real.log (100000 / 123339) := by
    rw [show ((123339 / 100000) : ℝ) = ((100000 / 123339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (265777081 / 1000000000) ≤ -Real.log (76661 / 100000) ∧
    -Real.log (76661 / 100000) ≤ (132888541 / 500000000) := by
  have h := checkLog_sound (w := (23339 / 176661)) (n := 12)
    (lo := (265777081 / 1000000000)) (hi := (132888541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76661) = 1/(76661 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-132888541 / 500000000) (-265777081 / 1000000000) (Real.log (76661 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (77324849 / 500000000) ≤ -Real.log (1000000 / 1167249) ∧
    -Real.log (1000000 / 1167249) ≤ (154649699 / 1000000000) := by
  have h := checkLog_sound (w := (167249 / 2167249)) (n := 12)
    (lo := (77324849 / 500000000)) (hi := (154649699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167249 / 1000000) = 1/(1000000 / 1167249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (77324849 / 500000000) (154649699 / 1000000000) (Real.log (1167249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1167249 / 1000000) = -Real.log (1000000 / 1167249) := by
    rw [show ((1167249 / 1000000) : ℝ) = ((1000000 / 1167249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (183020601 / 1000000000) ≤ -Real.log (832751 / 1000000) ∧
    -Real.log (832751 / 1000000) ≤ (91510301 / 500000000) := by
  have h := checkLog_sound (w := (167249 / 1832751)) (n := 12)
    (lo := (183020601 / 1000000000)) (hi := (91510301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 832751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 832751) = 1/(832751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91510301 / 500000000) (-183020601 / 1000000000) (Real.log (832751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (154916957 / 1000000000) ≤ -Real.log (1000000 / 1167561) ∧
    -Real.log (1000000 / 1167561) ≤ (77458479 / 500000000) := by
  have h := checkLog_sound (w := (167561 / 2167561)) (n := 12)
    (lo := (154916957 / 1000000000)) (hi := (77458479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167561 / 1000000) = 1/(1000000 / 1167561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (154916957 / 1000000000) (77458479 / 500000000) (Real.log (1167561 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1167561 / 1000000) = -Real.log (1000000 / 1167561) := by
    rw [show ((1167561 / 1000000) : ℝ) = ((1000000 / 1167561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (183395333 / 1000000000) ≤ -Real.log (832439 / 1000000) ∧
    -Real.log (832439 / 1000000) ≤ (91697667 / 500000000) := by
  have h := checkLog_sound (w := (167561 / 1832439)) (n := 12)
    (lo := (183395333 / 1000000000)) (hi := (91697667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 832439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 832439) = 1/(832439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-91697667 / 500000000) (-183395333 / 1000000000) (Real.log (832439 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136202683 / 200000000) ≤ -Real.log (100000000000 / 197587910491) ∧
    -Real.log (100000000000 / 197587910491) ≤ (85126677 / 125000000) := by
  have h := checkLog_sound (w := (97587910491 / 297587910491)) (n := 12)
    (lo := (136202683 / 200000000)) (hi := (85126677 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197587910491 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197587910491 / 100000000000) = 1/(100000000000 / 197587910491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136202683 / 200000000) (85126677 / 125000000) (Real.log (197587910491 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (197587910491 / 100000000000) = -Real.log (100000000000 / 197587910491) := by
    rw [show ((197587910491 / 100000000000) : ℝ) = ((100000000000 / 197587910491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (682326779 / 1000000000) ≤ -Real.log (500000000000 / 989237929029) ∧
    -Real.log (500000000000 / 989237929029) ≤ (34116339 / 50000000) := by
  have h := checkLog_sound (w := (489237929029 / 1489237929029)) (n := 12)
    (lo := (682326779 / 1000000000)) (hi := (34116339 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989237929029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989237929029 / 500000000000) = 1/(500000000000 / 989237929029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (682326779 / 1000000000) (34116339 / 50000000) (Real.log (989237929029 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (989237929029 / 500000000000) = -Real.log (500000000000 / 989237929029) := by
    rw [show ((989237929029 / 500000000000) : ℝ) = ((500000000000 / 989237929029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (474653143 / 1000000000) ≤ -Real.log (250000000000 / 401864135869) ∧
    -Real.log (250000000000 / 401864135869) ≤ (59331643 / 125000000) := by
  have h := checkLog_sound (w := (151864135869 / 651864135869)) (n := 12)
    (lo := (474653143 / 1000000000)) (hi := (59331643 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401864135869 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401864135869 / 250000000000) = 1/(250000000000 / 401864135869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (474653143 / 1000000000) (59331643 / 125000000) (Real.log (401864135869 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (401864135869 / 250000000000) = -Real.log (250000000000 / 401864135869) := by
    rw [show ((401864135869 / 250000000000) : ℝ) = ((250000000000 / 401864135869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (475543557 / 1000000000) ≤ -Real.log (500000000000 / 804444241531) ∧
    -Real.log (500000000000 / 804444241531) ≤ (237771779 / 500000000) := by
  have h := checkLog_sound (w := (304444241531 / 1304444241531)) (n := 12)
    (lo := (475543557 / 1000000000)) (hi := (237771779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804444241531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804444241531 / 500000000000) = 1/(500000000000 / 804444241531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (475543557 / 1000000000) (237771779 / 500000000) (Real.log (804444241531 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (804444241531 / 500000000000) = -Real.log (500000000000 / 804444241531) := by
    rw [show ((804444241531 / 500000000000) : ℝ) = ((500000000000 / 804444241531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (337670299 / 1000000000) ≤ -Real.log (100000000000 / 140167829279) ∧
    -Real.log (100000000000 / 140167829279) ≤ (3376703 / 10000000) := by
  have h := checkLog_sound (w := (40167829279 / 240167829279)) (n := 12)
    (lo := (337670299 / 1000000000)) (hi := (3376703 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140167829279 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140167829279 / 100000000000) = 1/(100000000000 / 140167829279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (337670299 / 1000000000) (3376703 / 10000000) (Real.log (140167829279 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (140167829279 / 100000000000) = -Real.log (100000000000 / 140167829279) := by
    rw [show ((140167829279 / 100000000000) : ℝ) = ((100000000000 / 140167829279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (33831229 / 100000000) ≤ -Real.log (100000000000 / 140257844719) ∧
    -Real.log (100000000000 / 140257844719) ≤ (338312291 / 1000000000) := by
  have h := checkLog_sound (w := (40257844719 / 240257844719)) (n := 12)
    (lo := (33831229 / 100000000)) (hi := (338312291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140257844719 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140257844719 / 100000000000) = 1/(100000000000 / 140257844719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (33831229 / 100000000) (338312291 / 1000000000) (Real.log (140257844719 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (140257844719 / 100000000000) = -Real.log (100000000000 / 140257844719) := by
    rw [show ((140257844719 / 100000000000) : ℝ) = ((100000000000 / 140257844719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (227827 / 8000000) ≤ -Real.log (971923311279 / 1000000000000) ∧
    -Real.log (971923311279 / 1000000000000) ≤ (3559797 / 125000000) := by
  have h := checkLog_sound (w := (28076688721 / 1971923311279)) (n := 12)
    (lo := (227827 / 8000000)) (hi := (3559797 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971923311279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971923311279) = 1/(971923311279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3559797 / 125000000) (-227827 / 8000000) (Real.log (971923311279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14185451 / 500000000) ≤ -Real.log (972027771999 / 1000000000000) ∧
    -Real.log (972027771999 / 1000000000000) ≤ (28370903 / 1000000000) := by
  have h := checkLog_sound (w := (27972228001 / 1972027771999)) (n := 12)
    (lo := (14185451 / 500000000)) (hi := (28370903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972027771999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972027771999) = 1/(972027771999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-28370903 / 1000000000) (-14185451 / 500000000) (Real.log (972027771999 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell133

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell134Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell134
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

theorem reflection_log_1_neg : (284503197 / 1000000000) ≤ -Real.log (1024 / 1361) ∧
    -Real.log (1024 / 1361) ≤ (142251599 / 500000000) := by
  have h := checkLog_sound (w := (337 / 2385)) (n := 12)
    (lo := (284503197 / 1000000000)) (hi := (142251599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1361 / 1024) = 1/(1024 / 1361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (284503197 / 1000000000) (142251599 / 500000000) (Real.log (1361 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1361 / 1024) = -Real.log (1024 / 1361) := by
    rw [show ((1361 / 1024) : ℝ) = ((1024 / 1361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (399137513 / 1000000000) ≤ -Real.log (687 / 1024) ∧
    -Real.log (687 / 1024) ≤ (199568757 / 500000000) := by
  have h := checkLog_sound (w := (337 / 1711)) (n := 12)
    (lo := (399137513 / 1000000000)) (hi := (199568757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 687) = 1/(687 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-199568757 / 500000000) (-399137513 / 1000000000) (Real.log (687 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (284062247 / 1000000000) ≤ -Real.log (2560 / 3401) ∧
    -Real.log (2560 / 3401) ≤ (35507781 / 125000000) := by
  have h := checkLog_sound (w := (841 / 5961)) (n := 12)
    (lo := (284062247 / 1000000000)) (hi := (35507781 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3401 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3401 / 2560) = 1/(2560 / 3401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (284062247 / 1000000000) (35507781 / 125000000) (Real.log (3401 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3401 / 2560) = -Real.log (2560 / 3401) := by
    rw [show ((3401 / 2560) : ℝ) = ((2560 / 3401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (99566133 / 250000000) ≤ -Real.log (1719 / 2560) ∧
    -Real.log (1719 / 2560) ≤ (398264533 / 1000000000) := by
  have h := checkLog_sound (w := (841 / 4279)) (n := 12)
    (lo := (99566133 / 250000000)) (hi := (398264533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1719) = 1/(1719 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-398264533 / 1000000000) (-99566133 / 250000000) (Real.log (1719 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41953133 / 200000000) ≤ -Real.log (1000000 / 1233389) ∧
    -Real.log (1000000 / 1233389) ≤ (104882833 / 500000000) := by
  have h := checkLog_sound (w := (233389 / 2233389)) (n := 12)
    (lo := (41953133 / 200000000)) (hi := (104882833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233389 / 1000000) = 1/(1000000 / 1233389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41953133 / 200000000) (104882833 / 500000000) (Real.log (1233389 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1233389 / 1000000) = -Real.log (1000000 / 1233389) := by
    rw [show ((1233389 / 1000000) : ℝ) = ((1000000 / 1233389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (265775777 / 1000000000) ≤ -Real.log (766611 / 1000000) ∧
    -Real.log (766611 / 1000000) ≤ (132887889 / 500000000) := by
  have h := checkLog_sound (w := (233389 / 1766611)) (n := 12)
    (lo := (265775777 / 1000000000)) (hi := (132887889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766611) = 1/(766611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-132887889 / 500000000) (-265775777 / 1000000000) (Real.log (766611 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (210107753 / 1000000000) ≤ -Real.log (1000000 / 1233811) ∧
    -Real.log (1000000 / 1233811) ≤ (105053877 / 500000000) := by
  have h := checkLog_sound (w := (233811 / 2233811)) (n := 12)
    (lo := (210107753 / 1000000000)) (hi := (105053877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233811 / 1000000) = 1/(1000000 / 1233811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (210107753 / 1000000000) (105053877 / 500000000) (Real.log (1233811 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1233811 / 1000000) = -Real.log (1000000 / 1233811) := by
    rw [show ((1233811 / 1000000) : ℝ) = ((1000000 / 1233811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (266326403 / 1000000000) ≤ -Real.log (766189 / 1000000) ∧
    -Real.log (766189 / 1000000) ≤ (66581601 / 250000000) := by
  have h := checkLog_sound (w := (233811 / 1766189)) (n := 12)
    (lo := (266326403 / 1000000000)) (hi := (66581601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766189) = 1/(766189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-66581601 / 250000000) (-266326403 / 1000000000) (Real.log (766189 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (154916101 / 1000000000) ≤ -Real.log (25000 / 29189) ∧
    -Real.log (25000 / 29189) ≤ (77458051 / 500000000) := by
  have h := checkLog_sound (w := (4189 / 54189)) (n := 12)
    (lo := (154916101 / 1000000000)) (hi := (77458051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29189 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29189 / 25000) = 1/(25000 / 29189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (154916101 / 1000000000) (77458051 / 500000000) (Real.log (29189 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (29189 / 25000) = -Real.log (25000 / 29189) := by
    rw [show ((29189 / 25000) : ℝ) = ((25000 / 29189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (183394131 / 1000000000) ≤ -Real.log (20811 / 25000) ∧
    -Real.log (20811 / 25000) ≤ (45848533 / 250000000) := by
  have h := checkLog_sound (w := (4189 / 45811)) (n := 12)
    (lo := (183394131 / 1000000000)) (hi := (45848533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20811) = 1/(20811 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-45848533 / 250000000) (-183394131 / 1000000000) (Real.log (20811 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (155183289 / 1000000000) ≤ -Real.log (15625 / 18248) ∧
    -Real.log (15625 / 18248) ≤ (15518329 / 100000000) := by
  have h := checkLog_sound (w := (2623 / 33873)) (n := 12)
    (lo := (155183289 / 1000000000)) (hi := (15518329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18248 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18248 / 15625) = 1/(15625 / 18248) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (155183289 / 1000000000) (15518329 / 100000000) (Real.log (18248 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (18248 / 15625) = -Real.log (15625 / 18248) := by
    rw [show ((18248 / 15625) : ℝ) = ((15625 / 18248) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (183769003 / 1000000000) ≤ -Real.log (13002 / 15625) ∧
    -Real.log (13002 / 15625) ≤ (45942251 / 250000000) := by
  have h := checkLog_sound (w := (2623 / 28627)) (n := 12)
    (lo := (183769003 / 1000000000)) (hi := (45942251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13002) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13002) = 1/(13002 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-45942251 / 250000000) (-183769003 / 1000000000) (Real.log (13002 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682326779 / 1000000000) ≤ -Real.log (125000000000 / 247309482257) ∧
    -Real.log (125000000000 / 247309482257) ≤ (34116339 / 50000000) := by
  have h := checkLog_sound (w := (122309482257 / 372309482257)) (n := 12)
    (lo := (682326779 / 1000000000)) (hi := (34116339 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247309482257 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247309482257 / 125000000000) = 1/(125000000000 / 247309482257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682326779 / 1000000000) (34116339 / 50000000) (Real.log (247309482257 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247309482257 / 125000000000) = -Real.log (125000000000 / 247309482257) := by
    rw [show ((247309482257 / 125000000000) : ℝ) = ((125000000000 / 247309482257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (68364071 / 100000000) ≤ -Real.log (500000000000 / 990538573509) ∧
    -Real.log (500000000000 / 990538573509) ≤ (683640711 / 1000000000) := by
  have h := checkLog_sound (w := (490538573509 / 1490538573509)) (n := 12)
    (lo := (68364071 / 100000000)) (hi := (683640711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990538573509 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990538573509 / 500000000000) = 1/(500000000000 / 990538573509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (68364071 / 100000000) (683640711 / 1000000000) (Real.log (990538573509 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (990538573509 / 500000000000) = -Real.log (500000000000 / 990538573509) := by
    rw [show ((990538573509 / 500000000000) : ℝ) = ((500000000000 / 990538573509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (237770721 / 500000000) ≤ -Real.log (250000000000 / 402221269979) ∧
    -Real.log (250000000000 / 402221269979) ≤ (475541443 / 1000000000) := by
  have h := checkLog_sound (w := (152221269979 / 652221269979)) (n := 12)
    (lo := (237770721 / 500000000)) (hi := (475541443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((402221269979 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(402221269979 / 250000000000) = 1/(250000000000 / 402221269979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (237770721 / 500000000) (475541443 / 1000000000) (Real.log (402221269979 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (402221269979 / 250000000000) = -Real.log (250000000000 / 402221269979) := by
    rw [show ((402221269979 / 250000000000) : ℝ) = ((250000000000 / 402221269979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (119108539 / 250000000) ≤ -Real.log (100000000000 / 161032199627) ∧
    -Real.log (100000000000 / 161032199627) ≤ (476434157 / 1000000000) := by
  have h := checkLog_sound (w := (61032199627 / 261032199627)) (n := 12)
    (lo := (119108539 / 250000000)) (hi := (476434157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161032199627 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161032199627 / 100000000000) = 1/(100000000000 / 161032199627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (119108539 / 250000000) (476434157 / 1000000000) (Real.log (161032199627 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (161032199627 / 100000000000) = -Real.log (100000000000 / 161032199627) := by
    rw [show ((161032199627 / 100000000000) : ℝ) = ((100000000000 / 161032199627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (42288779 / 125000000) ≤ -Real.log (1000000000 / 1402575561) ∧
    -Real.log (1000000000 / 1402575561) ≤ (338310233 / 1000000000) := by
  have h := checkLog_sound (w := (402575561 / 2402575561)) (n := 12)
    (lo := (42288779 / 125000000)) (hi := (338310233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1402575561 / 1000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1402575561 / 1000000000) = 1/(1000000000 / 1402575561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (42288779 / 125000000) (338310233 / 1000000000) (Real.log (1402575561 / 1000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1402575561 / 1000000000) = -Real.log (1000000000 / 1402575561) := by
    rw [show ((1402575561 / 1000000000) : ℝ) = ((1000000000 / 1402575561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (338952293 / 1000000000) ≤ -Real.log (125000000000 / 175434548531) ∧
    -Real.log (125000000000 / 175434548531) ≤ (169476147 / 500000000) := by
  have h := checkLog_sound (w := (50434548531 / 300434548531)) (n := 12)
    (lo := (338952293 / 1000000000)) (hi := (169476147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175434548531 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175434548531 / 125000000000) = 1/(125000000000 / 175434548531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (338952293 / 1000000000) (169476147 / 500000000) (Real.log (175434548531 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (175434548531 / 125000000000) = -Real.log (125000000000 / 175434548531) := by
    rw [show ((175434548531 / 125000000000) : ℝ) = ((125000000000 / 175434548531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (14292857 / 500000000) ≤ -Real.log (237260496 / 244140625) ∧
    -Real.log (237260496 / 244140625) ≤ (5717143 / 200000000) := by
  have h := checkLog_sound (w := (6880129 / 481401121)) (n := 12)
    (lo := (14292857 / 500000000)) (hi := (5717143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 237260496) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 237260496) = 1/(237260496 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5717143 / 200000000) (-14292857 / 500000000) (Real.log (237260496 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2847803 / 100000000) ≤ -Real.log (607452279 / 625000000) ∧
    -Real.log (607452279 / 625000000) ≤ (28478031 / 1000000000) := by
  have h := checkLog_sound (w := (17547721 / 1232452279)) (n := 12)
    (lo := (2847803 / 100000000)) (hi := (28478031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 607452279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 607452279) = 1/(607452279 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-28478031 / 1000000000) (-2847803 / 100000000) (Real.log (607452279 / 625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell134

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell135Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell135
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

theorem reflection_log_1_neg : (17808997 / 62500000) ≤ -Real.log (640 / 851) ∧
    -Real.log (640 / 851) ≤ (284943953 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1491)) (n := 12)
    (lo := (17808997 / 62500000)) (hi := (284943953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851 / 640) = 1/(640 / 851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (17808997 / 62500000) (284943953 / 1000000000) (Real.log (851 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (851 / 640) = -Real.log (640 / 851) := by
    rw [show ((851 / 640) : ℝ) = ((640 / 851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (400011257 / 1000000000) ≤ -Real.log (429 / 640) ∧
    -Real.log (429 / 640) ≤ (200005629 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 429) = 1/(429 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-200005629 / 500000000) (-400011257 / 1000000000) (Real.log (429 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (284503197 / 1000000000) ≤ -Real.log (1024 / 1361) ∧
    -Real.log (1024 / 1361) ≤ (142251599 / 500000000) := by
  have h := checkLog_sound (w := (337 / 2385)) (n := 12)
    (lo := (284503197 / 1000000000)) (hi := (142251599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1361 / 1024) = 1/(1024 / 1361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (284503197 / 1000000000) (142251599 / 500000000) (Real.log (1361 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1361 / 1024) = -Real.log (1024 / 1361) := by
    rw [show ((1361 / 1024) : ℝ) = ((1024 / 1361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (399137513 / 1000000000) ≤ -Real.log (687 / 1024) ∧
    -Real.log (687 / 1024) ≤ (199568757 / 500000000) := by
  have h := checkLog_sound (w := (337 / 1711)) (n := 12)
    (lo := (399137513 / 1000000000)) (hi := (199568757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 687) = 1/(687 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-199568757 / 500000000) (-399137513 / 1000000000) (Real.log (687 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (52526533 / 250000000) ≤ -Real.log (1000000 / 1233809) ∧
    -Real.log (1000000 / 1233809) ≤ (210106133 / 1000000000) := by
  have h := checkLog_sound (w := (233809 / 2233809)) (n := 12)
    (lo := (52526533 / 250000000)) (hi := (210106133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233809 / 1000000) = 1/(1000000 / 1233809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (52526533 / 250000000) (210106133 / 1000000000) (Real.log (1233809 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1233809 / 1000000) = -Real.log (1000000 / 1233809) := by
    rw [show ((1233809 / 1000000) : ℝ) = ((1000000 / 1233809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (266323793 / 1000000000) ≤ -Real.log (766191 / 1000000) ∧
    -Real.log (766191 / 1000000) ≤ (133161897 / 500000000) := by
  have h := checkLog_sound (w := (233809 / 1766191)) (n := 12)
    (lo := (266323793 / 1000000000)) (hi := (133161897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766191) = 1/(766191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-133161897 / 500000000) (-266323793 / 1000000000) (Real.log (766191 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (26306013 / 125000000) ≤ -Real.log (1000000 / 1234231) ∧
    -Real.log (1000000 / 1234231) ≤ (42089621 / 200000000) := by
  have h := checkLog_sound (w := (234231 / 2234231)) (n := 12)
    (lo := (26306013 / 125000000)) (hi := (42089621 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1234231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1234231 / 1000000) = 1/(1000000 / 1234231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (26306013 / 125000000) (42089621 / 200000000) (Real.log (1234231 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1234231 / 1000000) = -Real.log (1000000 / 1234231) := by
    rw [show ((1234231 / 1000000) : ℝ) = ((1000000 / 1234231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (266874721 / 1000000000) ≤ -Real.log (765769 / 1000000) ∧
    -Real.log (765769 / 1000000) ≤ (133437361 / 500000000) := by
  have h := checkLog_sound (w := (234231 / 1765769)) (n := 12)
    (lo := (266874721 / 1000000000)) (hi := (133437361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 765769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 765769) = 1/(765769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-133437361 / 500000000) (-266874721 / 1000000000) (Real.log (765769 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (155182433 / 1000000000) ≤ -Real.log (1000000 / 1167871) ∧
    -Real.log (1000000 / 1167871) ≤ (77591217 / 500000000) := by
  have h := checkLog_sound (w := (167871 / 2167871)) (n := 12)
    (lo := (155182433 / 1000000000)) (hi := (77591217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167871 / 1000000) = 1/(1000000 / 1167871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (155182433 / 1000000000) (77591217 / 500000000) (Real.log (1167871 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1167871 / 1000000) = -Real.log (1000000 / 1167871) := by
    rw [show ((1167871 / 1000000) : ℝ) = ((1000000 / 1167871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (91883901 / 500000000) ≤ -Real.log (832129 / 1000000) ∧
    -Real.log (832129 / 1000000) ≤ (183767803 / 1000000000) := by
  have h := checkLog_sound (w := (167871 / 1832129)) (n := 12)
    (lo := (91883901 / 500000000)) (hi := (183767803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 832129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 832129) = 1/(832129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-183767803 / 1000000000) (-91883901 / 500000000) (Real.log (832129 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3108991 / 20000000) ≤ -Real.log (1000000 / 1168183) ∧
    -Real.log (1000000 / 1168183) ≤ (155449551 / 1000000000) := by
  have h := checkLog_sound (w := (168183 / 2168183)) (n := 12)
    (lo := (3108991 / 20000000)) (hi := (155449551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1168183 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1168183 / 1000000) = 1/(1000000 / 1168183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3108991 / 20000000) (155449551 / 1000000000) (Real.log (1168183 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1168183 / 1000000) = -Real.log (1000000 / 1168183) := by
    rw [show ((1168183 / 1000000) : ℝ) = ((1000000 / 1168183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (92071407 / 500000000) ≤ -Real.log (831817 / 1000000) ∧
    -Real.log (831817 / 1000000) ≤ (36828563 / 200000000) := by
  have h := checkLog_sound (w := (168183 / 1831817)) (n := 12)
    (lo := (92071407 / 500000000)) (hi := (36828563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 831817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 831817) = 1/(831817 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36828563 / 200000000) (-92071407 / 500000000) (Real.log (831817 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68364071 / 100000000) ≤ -Real.log (125000000000 / 247634643377) ∧
    -Real.log (125000000000 / 247634643377) ≤ (683640711 / 1000000000) := by
  have h := checkLog_sound (w := (122634643377 / 372634643377)) (n := 12)
    (lo := (68364071 / 100000000)) (hi := (683640711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247634643377 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247634643377 / 125000000000) = 1/(125000000000 / 247634643377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68364071 / 100000000) (683640711 / 1000000000) (Real.log (247634643377 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247634643377 / 125000000000) = -Real.log (125000000000 / 247634643377) := by
    rw [show ((247634643377 / 125000000000) : ℝ) = ((125000000000 / 247634643377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (684955209 / 1000000000) ≤ -Real.log (250000000000 / 495920745921) ∧
    -Real.log (250000000000 / 495920745921) ≤ (68495521 / 100000000) := by
  have h := checkLog_sound (w := (245920745921 / 745920745921)) (n := 12)
    (lo := (684955209 / 1000000000)) (hi := (68495521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495920745921 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495920745921 / 250000000000) = 1/(250000000000 / 495920745921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (684955209 / 1000000000) (68495521 / 100000000) (Real.log (495920745921 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (495920745921 / 250000000000) = -Real.log (250000000000 / 495920745921) := by
    rw [show ((495920745921 / 250000000000) : ℝ) = ((250000000000 / 495920745921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (19057197 / 40000000) ≤ -Real.log (500000000000 / 805157591253) ∧
    -Real.log (500000000000 / 805157591253) ≤ (238214963 / 500000000) := by
  have h := checkLog_sound (w := (305157591253 / 1305157591253)) (n := 12)
    (lo := (19057197 / 40000000)) (hi := (238214963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805157591253 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805157591253 / 500000000000) = 1/(500000000000 / 805157591253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19057197 / 40000000) (238214963 / 500000000) (Real.log (805157591253 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (805157591253 / 500000000000) = -Real.log (500000000000 / 805157591253) := by
    rw [show ((805157591253 / 500000000000) : ℝ) = ((500000000000 / 805157591253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (19092913 / 40000000) ≤ -Real.log (125000000000 / 201469209383) ∧
    -Real.log (125000000000 / 201469209383) ≤ (238661413 / 500000000) := by
  have h := checkLog_sound (w := (76469209383 / 326469209383)) (n := 12)
    (lo := (19092913 / 40000000)) (hi := (238661413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201469209383 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201469209383 / 125000000000) = 1/(125000000000 / 201469209383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (19092913 / 40000000) (238661413 / 500000000) (Real.log (201469209383 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (201469209383 / 125000000000) = -Real.log (125000000000 / 201469209383) := by
    rw [show ((201469209383 / 125000000000) : ℝ) = ((125000000000 / 201469209383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (67790047 / 200000000) ≤ -Real.log (500000000000 / 701736749951) ∧
    -Real.log (500000000000 / 701736749951) ≤ (84737559 / 250000000) := by
  have h := checkLog_sound (w := (201736749951 / 1201736749951)) (n := 12)
    (lo := (67790047 / 200000000)) (hi := (84737559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701736749951 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701736749951 / 500000000000) = 1/(500000000000 / 701736749951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (67790047 / 200000000) (84737559 / 250000000) (Real.log (701736749951 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (701736749951 / 500000000000) = -Real.log (500000000000 / 701736749951) := by
    rw [show ((701736749951 / 500000000000) : ℝ) = ((500000000000 / 701736749951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (84898091 / 250000000) ≤ -Real.log (62500000000 / 87773437547) ∧
    -Real.log (62500000000 / 87773437547) ≤ (67918473 / 200000000) := by
  have h := checkLog_sound (w := (25273437547 / 150273437547)) (n := 12)
    (lo := (84898091 / 250000000)) (hi := (67918473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87773437547 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87773437547 / 62500000000) = 1/(62500000000 / 87773437547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (84898091 / 250000000) (67918473 / 200000000) (Real.log (87773437547 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (87773437547 / 62500000000) = -Real.log (62500000000 / 87773437547) := by
    rw [show ((87773437547 / 62500000000) : ℝ) = ((62500000000 / 87773437547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1793329 / 62500000) ≤ -Real.log (971714478511 / 1000000000000) ∧
    -Real.log (971714478511 / 1000000000000) ≤ (5738653 / 200000000) := by
  have h := checkLog_sound (w := (28285521489 / 1971714478511)) (n := 12)
    (lo := (1793329 / 62500000)) (hi := (5738653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971714478511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971714478511) = 1/(971714478511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5738653 / 200000000) (-1793329 / 62500000) (Real.log (971714478511 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (28585369 / 1000000000) ≤ -Real.log (971819327359 / 1000000000000) ∧
    -Real.log (971819327359 / 1000000000000) ≤ (2858537 / 100000000) := by
  have h := checkLog_sound (w := (28180672641 / 1971819327359)) (n := 12)
    (lo := (28585369 / 1000000000)) (hi := (2858537 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971819327359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971819327359) = 1/(971819327359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2858537 / 100000000) (-28585369 / 1000000000) (Real.log (971819327359 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell135

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell136Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell136
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

theorem reflection_log_1_neg : (285384513 / 1000000000) ≤ -Real.log (5120 / 6811) ∧
    -Real.log (5120 / 6811) ≤ (142692257 / 500000000) := by
  have h := checkLog_sound (w := (1691 / 11931)) (n := 12)
    (lo := (285384513 / 1000000000)) (hi := (142692257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6811 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6811 / 5120) = 1/(5120 / 6811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (285384513 / 1000000000) (142692257 / 500000000) (Real.log (6811 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6811 / 5120) = -Real.log (5120 / 6811) := by
    rw [show ((6811 / 5120) : ℝ) = ((5120 / 6811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (80177153 / 200000000) ≤ -Real.log (3429 / 5120) ∧
    -Real.log (3429 / 5120) ≤ (200442883 / 500000000) := by
  have h := checkLog_sound (w := (1691 / 8549)) (n := 12)
    (lo := (80177153 / 200000000)) (hi := (200442883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3429) = 1/(3429 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-200442883 / 500000000) (-80177153 / 200000000) (Real.log (3429 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (17808997 / 62500000) ≤ -Real.log (640 / 851) ∧
    -Real.log (640 / 851) ≤ (284943953 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1491)) (n := 12)
    (lo := (17808997 / 62500000)) (hi := (284943953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851 / 640) = 1/(640 / 851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (17808997 / 62500000) (284943953 / 1000000000) (Real.log (851 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (851 / 640) = -Real.log (640 / 851) := by
    rw [show ((851 / 640) : ℝ) = ((640 / 851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (400011257 / 1000000000) ≤ -Real.log (429 / 640) ∧
    -Real.log (429 / 640) ≤ (200005629 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 429) = 1/(429 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-200005629 / 500000000) (-400011257 / 1000000000) (Real.log (429 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (210447293 / 1000000000) ≤ -Real.log (100000 / 123423) ∧
    -Real.log (100000 / 123423) ≤ (105223647 / 500000000) := by
  have h := checkLog_sound (w := (23423 / 223423)) (n := 12)
    (lo := (210447293 / 1000000000)) (hi := (105223647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123423 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123423 / 100000) = 1/(100000 / 123423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (210447293 / 1000000000) (105223647 / 500000000) (Real.log (123423 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (123423 / 100000) = -Real.log (100000 / 123423) := by
    rw [show ((123423 / 100000) : ℝ) = ((100000 / 123423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (53374683 / 200000000) ≤ -Real.log (76577 / 100000) ∧
    -Real.log (76577 / 100000) ≤ (33359177 / 125000000) := by
  have h := checkLog_sound (w := (23423 / 176577)) (n := 12)
    (lo := (53374683 / 200000000)) (hi := (33359177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76577) = 1/(76577 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-33359177 / 125000000) (-53374683 / 200000000) (Real.log (76577 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (210788339 / 1000000000) ≤ -Real.log (1000000 / 1234651) ∧
    -Real.log (1000000 / 1234651) ≤ (10539417 / 50000000) := by
  have h := checkLog_sound (w := (234651 / 2234651)) (n := 12)
    (lo := (210788339 / 1000000000)) (hi := (10539417 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1234651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1234651 / 1000000) = 1/(1000000 / 1234651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (210788339 / 1000000000) (10539417 / 50000000) (Real.log (1234651 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1234651 / 1000000) = -Real.log (1000000 / 1234651) := by
    rw [show ((1234651 / 1000000) : ℝ) = ((1000000 / 1234651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (13371167 / 50000000) ≤ -Real.log (765349 / 1000000) ∧
    -Real.log (765349 / 1000000) ≤ (267423341 / 1000000000) := by
  have h := checkLog_sound (w := (234651 / 1765349)) (n := 12)
    (lo := (13371167 / 50000000)) (hi := (267423341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 765349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 765349) = 1/(765349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-267423341 / 1000000000) (-13371167 / 50000000) (Real.log (765349 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (77724347 / 500000000) ≤ -Real.log (500000 / 584091) ∧
    -Real.log (500000 / 584091) ≤ (31089739 / 200000000) := by
  have h := checkLog_sound (w := (84091 / 1084091)) (n := 12)
    (lo := (77724347 / 500000000)) (hi := (31089739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584091 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584091 / 500000) = 1/(500000 / 584091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (77724347 / 500000000) (31089739 / 200000000) (Real.log (584091 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (584091 / 500000) = -Real.log (500000 / 584091) := by
    rw [show ((584091 / 500000) : ℝ) = ((500000 / 584091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (46035403 / 250000000) ≤ -Real.log (415909 / 500000) ∧
    -Real.log (415909 / 500000) ≤ (184141613 / 1000000000) := by
  have h := checkLog_sound (w := (84091 / 915909)) (n := 12)
    (lo := (46035403 / 250000000)) (hi := (184141613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415909) = 1/(415909 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-184141613 / 1000000000) (-46035403 / 250000000) (Real.log (415909 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7785787 / 50000000) ≤ -Real.log (500000 / 584247) ∧
    -Real.log (500000 / 584247) ≤ (155715741 / 1000000000) := by
  have h := checkLog_sound (w := (84247 / 1084247)) (n := 12)
    (lo := (7785787 / 50000000)) (hi := (155715741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584247 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584247 / 500000) = 1/(500000 / 584247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7785787 / 50000000) (155715741 / 1000000000) (Real.log (584247 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (584247 / 500000) = -Real.log (500000 / 584247) := by
    rw [show ((584247 / 500000) : ℝ) = ((500000 / 584247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (46129191 / 250000000) ≤ -Real.log (415753 / 500000) ∧
    -Real.log (415753 / 500000) ≤ (36903353 / 200000000) := by
  have h := checkLog_sound (w := (84247 / 915753)) (n := 12)
    (lo := (46129191 / 250000000)) (hi := (36903353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415753) = 1/(415753 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36903353 / 200000000) (-46129191 / 250000000) (Real.log (415753 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684955209 / 1000000000) ≤ -Real.log (500000000000 / 991841491841) ∧
    -Real.log (500000000000 / 991841491841) ≤ (68495521 / 100000000) := by
  have h := checkLog_sound (w := (491841491841 / 1491841491841)) (n := 12)
    (lo := (684955209 / 1000000000)) (hi := (68495521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991841491841 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991841491841 / 500000000000) = 1/(500000000000 / 991841491841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684955209 / 1000000000) (68495521 / 100000000) (Real.log (991841491841 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (991841491841 / 500000000000) = -Real.log (500000000000 / 991841491841) := by
    rw [show ((991841491841 / 500000000000) : ℝ) = ((500000000000 / 991841491841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (343135139 / 500000000) ≤ -Real.log (250000000000 / 496573344999) ∧
    -Real.log (250000000000 / 496573344999) ≤ (686270279 / 1000000000) := by
  have h := checkLog_sound (w := (246573344999 / 746573344999)) (n := 12)
    (lo := (343135139 / 500000000)) (hi := (686270279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((496573344999 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(496573344999 / 250000000000) = 1/(250000000000 / 496573344999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (343135139 / 500000000) (686270279 / 1000000000) (Real.log (496573344999 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (496573344999 / 250000000000) = -Real.log (250000000000 / 496573344999) := by
    rw [show ((496573344999 / 250000000000) : ℝ) = ((250000000000 / 496573344999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (477320709 / 1000000000) ≤ -Real.log (500000000000 / 805875132219) ∧
    -Real.log (500000000000 / 805875132219) ≤ (47732071 / 100000000) := by
  have h := checkLog_sound (w := (305875132219 / 1305875132219)) (n := 12)
    (lo := (477320709 / 1000000000)) (hi := (47732071 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805875132219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805875132219 / 500000000000) = 1/(500000000000 / 805875132219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (477320709 / 1000000000) (47732071 / 100000000) (Real.log (805875132219 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (805875132219 / 500000000000) = -Real.log (500000000000 / 805875132219) := by
    rw [show ((805875132219 / 500000000000) : ℝ) = ((500000000000 / 805875132219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (478211679 / 1000000000) ≤ -Real.log (500000000000 / 806593462591) ∧
    -Real.log (500000000000 / 806593462591) ≤ (2988823 / 6250000) := by
  have h := checkLog_sound (w := (306593462591 / 1306593462591)) (n := 12)
    (lo := (478211679 / 1000000000)) (hi := (2988823 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((806593462591 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(806593462591 / 500000000000) = 1/(500000000000 / 806593462591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (478211679 / 1000000000) (2988823 / 6250000) (Real.log (806593462591 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (806593462591 / 500000000000) = -Real.log (500000000000 / 806593462591) := by
    rw [show ((806593462591 / 500000000000) : ℝ) = ((500000000000 / 806593462591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (169795153 / 500000000) ≤ -Real.log (250000000000 / 351093027561) ∧
    -Real.log (250000000000 / 351093027561) ≤ (339590307 / 1000000000) := by
  have h := checkLog_sound (w := (101093027561 / 601093027561)) (n := 12)
    (lo := (169795153 / 500000000)) (hi := (339590307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351093027561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351093027561 / 250000000000) = 1/(250000000000 / 351093027561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (169795153 / 500000000) (339590307 / 1000000000) (Real.log (351093027561 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (351093027561 / 250000000000) = -Real.log (250000000000 / 351093027561) := by
    rw [show ((351093027561 / 250000000000) : ℝ) = ((250000000000 / 351093027561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (42529063 / 125000000) ≤ -Real.log (500000000000 / 702637142727) ∧
    -Real.log (500000000000 / 702637142727) ≤ (68046501 / 200000000) := by
  have h := checkLog_sound (w := (202637142727 / 1202637142727)) (n := 12)
    (lo := (42529063 / 125000000)) (hi := (68046501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702637142727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702637142727 / 500000000000) = 1/(500000000000 / 702637142727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (42529063 / 125000000) (68046501 / 200000000) (Real.log (702637142727 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (702637142727 / 500000000000) = -Real.log (500000000000 / 702637142727) := by
    rw [show ((702637142727 / 500000000000) : ℝ) = ((500000000000 / 702637142727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (56252 / 1953125) ≤ -Real.log (242902442991 / 250000000000) ∧
    -Real.log (242902442991 / 250000000000) ≤ (1152041 / 40000000) := by
  have h := checkLog_sound (w := (7097557009 / 492902442991)) (n := 12)
    (lo := (56252 / 1953125)) (hi := (1152041 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242902442991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242902442991) = 1/(242902442991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1152041 / 40000000) (-56252 / 1953125) (Real.log (242902442991 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (28692917 / 1000000000) ≤ -Real.log (242928703719 / 250000000000) ∧
    -Real.log (242928703719 / 250000000000) ≤ (14346459 / 500000000) := by
  have h := checkLog_sound (w := (7071296281 / 492928703719)) (n := 12)
    (lo := (28692917 / 1000000000)) (hi := (14346459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242928703719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242928703719) = 1/(242928703719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-14346459 / 500000000) (-28692917 / 1000000000) (Real.log (242928703719 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell136

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell137Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell137
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

theorem reflection_log_1_neg : (3572811 / 12500000) ≤ -Real.log (2560 / 3407) ∧
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


theorem reflection_log_1 : Bounds (3572811 / 12500000) (285824881 / 1000000000) (Real.log (3407 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3407 / 2560) = -Real.log (2560 / 3407) := by
    rw [show ((3407 / 2560) : ℝ) = ((2560 / 3407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (401761039 / 1000000000) ≤ -Real.log (1713 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-5022013 / 12500000) (-401761039 / 1000000000) (Real.log (1713 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (285384513 / 1000000000) ≤ -Real.log (5120 / 6811) ∧
    -Real.log (5120 / 6811) ≤ (142692257 / 500000000) := by
  have h := checkLog_sound (w := (1691 / 11931)) (n := 12)
    (lo := (285384513 / 1000000000)) (hi := (142692257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6811 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6811 / 5120) = 1/(5120 / 6811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (285384513 / 1000000000) (142692257 / 500000000) (Real.log (6811 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6811 / 5120) = -Real.log (5120 / 6811) := by
    rw [show ((6811 / 5120) : ℝ) = ((5120 / 6811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (80177153 / 200000000) ≤ -Real.log (3429 / 5120) ∧
    -Real.log (3429 / 5120) ≤ (200442883 / 500000000) := by
  have h := checkLog_sound (w := (1691 / 8549)) (n := 12)
    (lo := (80177153 / 200000000)) (hi := (200442883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3429) = 1/(3429 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-200442883 / 500000000) (-80177153 / 200000000) (Real.log (3429 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (210787529 / 1000000000) ≤ -Real.log (20000 / 24693) ∧
    -Real.log (20000 / 24693) ≤ (21078753 / 100000000) := by
  have h := checkLog_sound (w := (4693 / 44693)) (n := 12)
    (lo := (210787529 / 1000000000)) (hi := (21078753 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24693 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24693 / 20000) = 1/(20000 / 24693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (210787529 / 1000000000) (21078753 / 100000000) (Real.log (24693 / 20000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24693 / 20000) = -Real.log (20000 / 24693) := by
    rw [show ((24693 / 20000) : ℝ) = ((20000 / 24693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (267422033 / 1000000000) ≤ -Real.log (15307 / 20000) ∧
    -Real.log (15307 / 20000) ≤ (133711017 / 500000000) := by
  have h := checkLog_sound (w := (4693 / 35307)) (n := 12)
    (lo := (267422033 / 1000000000)) (hi := (133711017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15307) = 1/(15307 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-133711017 / 500000000) (-267422033 / 1000000000) (Real.log (15307 / 20000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (211129267 / 1000000000) ≤ -Real.log (15625 / 19298) ∧
    -Real.log (15625 / 19298) ≤ (52782317 / 250000000) := by
  have h := checkLog_sound (w := (3673 / 34923)) (n := 12)
    (lo := (211129267 / 1000000000)) (hi := (52782317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19298 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19298 / 15625) = 1/(15625 / 19298) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (211129267 / 1000000000) (52782317 / 250000000) (Real.log (19298 / 15625)) := by
  have h := reflection_log_7_neg
  have he : Real.log (19298 / 15625) = -Real.log (15625 / 19298) := by
    rw [show ((19298 / 15625) : ℝ) = ((15625 / 19298) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (267973567 / 1000000000) ≤ -Real.log (11952 / 15625) ∧
    -Real.log (11952 / 15625) ≤ (4187087 / 15625000) := by
  have h := checkLog_sound (w := (3673 / 27577)) (n := 12)
    (lo := (267973567 / 1000000000)) (hi := (4187087 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11952) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11952) = 1/(11952 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4187087 / 15625000) (-267973567 / 1000000000) (Real.log (11952 / 15625)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38928721 / 250000000) ≤ -Real.log (1000000 / 1168493) ∧
    -Real.log (1000000 / 1168493) ≤ (31142977 / 200000000) := by
  have h := checkLog_sound (w := (168493 / 2168493)) (n := 12)
    (lo := (38928721 / 250000000)) (hi := (31142977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1168493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1168493 / 1000000) = 1/(1000000 / 1168493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38928721 / 250000000) (31142977 / 200000000) (Real.log (1168493 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1168493 / 1000000) = -Real.log (1000000 / 1168493) := by
    rw [show ((1168493 / 1000000) : ℝ) = ((1000000 / 1168493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (184515561 / 1000000000) ≤ -Real.log (831507 / 1000000) ∧
    -Real.log (831507 / 1000000) ≤ (92257781 / 500000000) := by
  have h := checkLog_sound (w := (168493 / 1831507)) (n := 12)
    (lo := (184515561 / 1000000000)) (hi := (92257781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 831507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 831507) = 1/(831507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-92257781 / 500000000) (-184515561 / 1000000000) (Real.log (831507 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (77991357 / 500000000) ≤ -Real.log (500000 / 584403) ∧
    -Real.log (500000 / 584403) ≤ (31196543 / 200000000) := by
  have h := checkLog_sound (w := (84403 / 1084403)) (n := 12)
    (lo := (77991357 / 500000000)) (hi := (31196543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584403 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584403 / 500000) = 1/(500000 / 584403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (77991357 / 500000000) (31196543 / 200000000) (Real.log (584403 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (584403 / 500000) = -Real.log (500000 / 584403) := by
    rw [show ((584403 / 500000) : ℝ) = ((500000 / 584403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (184892057 / 1000000000) ≤ -Real.log (415597 / 500000) ∧
    -Real.log (415597 / 500000) ≤ (92446029 / 500000000) := by
  have h := checkLog_sound (w := (84403 / 915597)) (n := 12)
    (lo := (184892057 / 1000000000)) (hi := (92446029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415597) = 1/(415597 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-92446029 / 500000000) (-184892057 / 1000000000) (Real.log (415597 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (343135139 / 500000000) ≤ -Real.log (500000000000 / 993146689997) ∧
    -Real.log (500000000000 / 993146689997) ≤ (686270279 / 1000000000) := by
  have h := checkLog_sound (w := (493146689997 / 1493146689997)) (n := 12)
    (lo := (343135139 / 500000000)) (hi := (686270279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((993146689997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(993146689997 / 500000000000) = 1/(500000000000 / 993146689997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (343135139 / 500000000) (686270279 / 1000000000) (Real.log (993146689997 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (993146689997 / 500000000000) = -Real.log (500000000000 / 993146689997) := by
    rw [show ((993146689997 / 500000000000) : ℝ) = ((500000000000 / 993146689997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (687585919 / 1000000000) ≤ -Real.log (125000000000 / 248613543491) ∧
    -Real.log (125000000000 / 248613543491) ≤ (1074353 / 1562500) := by
  have h := checkLog_sound (w := (123613543491 / 373613543491)) (n := 12)
    (lo := (687585919 / 1000000000)) (hi := (1074353 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248613543491 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248613543491 / 125000000000) = 1/(125000000000 / 248613543491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (687585919 / 1000000000) (1074353 / 1562500) (Real.log (248613543491 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (248613543491 / 125000000000) = -Real.log (125000000000 / 248613543491) := by
    rw [show ((248613543491 / 125000000000) : ℝ) = ((125000000000 / 248613543491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (239104781 / 500000000) ≤ -Real.log (250000000000 / 403295877703) ∧
    -Real.log (250000000000 / 403295877703) ≤ (478209563 / 1000000000) := by
  have h := checkLog_sound (w := (153295877703 / 653295877703)) (n := 12)
    (lo := (239104781 / 500000000)) (hi := (478209563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403295877703 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403295877703 / 250000000000) = 1/(250000000000 / 403295877703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (239104781 / 500000000) (478209563 / 1000000000) (Real.log (403295877703 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (403295877703 / 250000000000) = -Real.log (250000000000 / 403295877703) := by
    rw [show ((403295877703 / 250000000000) : ℝ) = ((250000000000 / 403295877703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (95820567 / 200000000) ≤ -Real.log (500000000000 / 807312583669) ∧
    -Real.log (500000000000 / 807312583669) ≤ (119775709 / 250000000) := by
  have h := checkLog_sound (w := (307312583669 / 1307312583669)) (n := 12)
    (lo := (95820567 / 200000000)) (hi := (119775709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807312583669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807312583669 / 500000000000) = 1/(500000000000 / 807312583669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (95820567 / 200000000) (119775709 / 250000000) (Real.log (807312583669 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (807312583669 / 500000000000) = -Real.log (500000000000 / 807312583669) := by
    rw [show ((807312583669 / 500000000000) : ℝ) = ((500000000000 / 807312583669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (170115223 / 500000000) ≤ -Real.log (62500000000 / 87829462049) ∧
    -Real.log (62500000000 / 87829462049) ≤ (340230447 / 1000000000) := by
  have h := checkLog_sound (w := (25329462049 / 150329462049)) (n := 12)
    (lo := (170115223 / 500000000)) (hi := (340230447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87829462049 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87829462049 / 62500000000) = 1/(62500000000 / 87829462049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (170115223 / 500000000) (340230447 / 1000000000) (Real.log (87829462049 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (87829462049 / 62500000000) = -Real.log (62500000000 / 87829462049) := by
    rw [show ((87829462049 / 62500000000) : ℝ) = ((62500000000 / 87829462049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (85218693 / 250000000) ≤ -Real.log (20000000000 / 28123542759) ∧
    -Real.log (20000000000 / 28123542759) ≤ (340874773 / 1000000000) := by
  have h := checkLog_sound (w := (8123542759 / 48123542759)) (n := 12)
    (lo := (85218693 / 250000000)) (hi := (340874773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28123542759 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28123542759 / 20000000000) = 1/(20000000000 / 28123542759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (85218693 / 250000000) (340874773 / 1000000000) (Real.log (28123542759 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28123542759 / 20000000000) = -Real.log (20000000000 / 28123542759) := by
    rw [show ((28123542759 / 20000000000) : ℝ) = ((20000000000 / 28123542759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (14454671 / 500000000) ≤ -Real.log (242876133591 / 250000000000) ∧
    -Real.log (242876133591 / 250000000000) ≤ (28909343 / 1000000000) := by
  have h := checkLog_sound (w := (7123866409 / 492876133591)) (n := 12)
    (lo := (14454671 / 500000000)) (hi := (28909343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242876133591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242876133591) = 1/(242876133591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-28909343 / 1000000000) (-14454671 / 500000000) (Real.log (242876133591 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (28800677 / 1000000000) ≤ -Real.log (971610108951 / 1000000000000) ∧
    -Real.log (971610108951 / 1000000000000) ≤ (14400339 / 500000000) := by
  have h := checkLog_sound (w := (28389891049 / 1971610108951)) (n := 12)
    (lo := (28800677 / 1000000000)) (hi := (14400339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971610108951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971610108951) = 1/(971610108951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-14400339 / 500000000) (-28800677 / 1000000000) (Real.log (971610108951 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell137

end


