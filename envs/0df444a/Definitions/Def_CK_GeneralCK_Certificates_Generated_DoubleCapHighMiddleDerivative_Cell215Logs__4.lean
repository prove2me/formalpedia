-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell215Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell215Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T18:11:01.959211+00:00
-- url     : https://prove2.me/theorems/b2864bdc-b37c-4805-a04f-8a49723ac335
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell215Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell216…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell215Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell216Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell217Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell218Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell215Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell216Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell217Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell218Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell215Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell216Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell217Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell218Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell215Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell216Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell217Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell218Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell215Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell215
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

theorem reflection_log_1_neg : (319589449 / 1000000000) ≤ -Real.log (640 / 881) ∧
    -Real.log (640 / 881) ≤ (6391789 / 20000000) := by
  have h := checkLog_sound (w := (241 / 1521)) (n := 12)
    (lo := (319589449 / 1000000000)) (hi := (6391789 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881 / 640) = 1/(640 / 881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (319589449 / 1000000000) (6391789 / 20000000) (Real.log (881 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (881 / 640) = -Real.log (640 / 881) := by
    rw [show ((881 / 640) : ℝ) = ((640 / 881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (472506759 / 1000000000) ≤ -Real.log (399 / 640) ∧
    -Real.log (399 / 640) ≤ (11812669 / 25000000) := by
  have h := checkLog_sound (w := (241 / 1039)) (n := 12)
    (lo := (472506759 / 1000000000)) (hi := (11812669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 399) = 1/(399 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-11812669 / 25000000) (-472506759 / 1000000000) (Real.log (399 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (159581853 / 500000000) ≤ -Real.log (1024 / 1409) ∧
    -Real.log (1024 / 1409) ≤ (319163707 / 1000000000) := by
  have h := checkLog_sound (w := (385 / 2433)) (n := 12)
    (lo := (159581853 / 500000000)) (hi := (319163707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409 / 1024) = 1/(1024 / 1409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (159581853 / 500000000) (319163707 / 1000000000) (Real.log (1409 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1409 / 1024) = -Real.log (1024 / 1409) := by
    rw [show ((1409 / 1024) : ℝ) = ((1024 / 1409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (471567351 / 1000000000) ≤ -Real.log (639 / 1024) ∧
    -Real.log (639 / 1024) ≤ (58945919 / 125000000) := by
  have h := checkLog_sound (w := (385 / 1663)) (n := 12)
    (lo := (471567351 / 1000000000)) (hi := (58945919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 639) = 1/(639 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58945919 / 125000000) (-471567351 / 1000000000) (Real.log (639 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (47412447 / 200000000) ≤ -Real.log (3125 / 3961) ∧
    -Real.log (3125 / 3961) ≤ (59265559 / 250000000) := by
  have h := checkLog_sound (w := (418 / 3543)) (n := 12)
    (lo := (47412447 / 200000000)) (hi := (59265559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3961 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3961 / 3125) = 1/(3125 / 3961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (47412447 / 200000000) (59265559 / 250000000) (Real.log (3961 / 3125)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3961 / 3125) = -Real.log (3125 / 3961) := by
    rw [show ((3961 / 3125) : ℝ) = ((3125 / 3961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (155659621 / 500000000) ≤ -Real.log (2289 / 3125) ∧
    -Real.log (2289 / 3125) ≤ (311319243 / 1000000000) := by
  have h := checkLog_sound (w := (418 / 2707)) (n := 12)
    (lo := (155659621 / 500000000)) (hi := (311319243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2289) = 1/(2289 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-311319243 / 1000000000) (-155659621 / 500000000) (Real.log (2289 / 3125)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (237396691 / 1000000000) ≤ -Real.log (125000 / 158493) ∧
    -Real.log (125000 / 158493) ≤ (59349173 / 250000000) := by
  have h := checkLog_sound (w := (33493 / 283493)) (n := 12)
    (lo := (237396691 / 1000000000)) (hi := (59349173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158493 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158493 / 125000) = 1/(125000 / 158493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (237396691 / 1000000000) (59349173 / 250000000) (Real.log (158493 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (158493 / 125000) = -Real.log (125000 / 158493) := by
    rw [show ((158493 / 125000) : ℝ) = ((125000 / 158493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (62379653 / 200000000) ≤ -Real.log (91507 / 125000) ∧
    -Real.log (91507 / 125000) ≤ (155949133 / 500000000) := by
  have h := checkLog_sound (w := (33493 / 216507)) (n := 12)
    (lo := (62379653 / 200000000)) (hi := (155949133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 91507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 91507) = 1/(91507 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-155949133 / 500000000) (-62379653 / 200000000) (Real.log (91507 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (176463599 / 1000000000) ≤ -Real.log (1000000 / 1192991) ∧
    -Real.log (1000000 / 1192991) ≤ (441159 / 2500000) := by
  have h := checkLog_sound (w := (192991 / 2192991)) (n := 12)
    (lo := (176463599 / 1000000000)) (hi := (441159 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192991 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192991 / 1000000) = 1/(1000000 / 1192991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (176463599 / 1000000000) (441159 / 2500000) (Real.log (1192991 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1192991 / 1000000) = -Real.log (1000000 / 1192991) := by
    rw [show ((1192991 / 1000000) : ℝ) = ((1000000 / 1192991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (107210229 / 500000000) ≤ -Real.log (807009 / 1000000) ∧
    -Real.log (807009 / 1000000) ≤ (214420459 / 1000000000) := by
  have h := checkLog_sound (w := (192991 / 1807009)) (n := 12)
    (lo := (107210229 / 500000000)) (hi := (214420459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807009) = 1/(807009 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-214420459 / 1000000000) (-107210229 / 500000000) (Real.log (807009 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4418253 / 25000000) ≤ -Real.log (1000000 / 1193309) ∧
    -Real.log (1000000 / 1193309) ≤ (176730121 / 1000000000) := by
  have h := checkLog_sound (w := (193309 / 2193309)) (n := 12)
    (lo := (4418253 / 25000000)) (hi := (176730121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193309 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193309 / 1000000) = 1/(1000000 / 1193309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4418253 / 25000000) (176730121 / 1000000000) (Real.log (1193309 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1193309 / 1000000) = -Real.log (1000000 / 1193309) := by
    rw [show ((1193309 / 1000000) : ℝ) = ((1000000 / 1193309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (214814583 / 1000000000) ≤ -Real.log (806691 / 1000000) ∧
    -Real.log (806691 / 1000000) ≤ (26851823 / 125000000) := by
  have h := checkLog_sound (w := (193309 / 1806691)) (n := 12)
    (lo := (214814583 / 1000000000)) (hi := (26851823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806691) = 1/(806691 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-26851823 / 125000000) (-214814583 / 1000000000) (Real.log (806691 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (49420691 / 62500000) ≤ -Real.log (500000000000 / 1102503912363) ∧
    -Real.log (500000000000 / 1102503912363) ≤ (395365529 / 500000000) := by
  have h := checkLog_sound (w := (102503912363 / 2102503912363)) (n := 12)
    (lo := (24395969 / 250000000)) (hi := (97583877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1102503912363 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1102503912363 / 1000000000000) = 1/(500000000000 / 1102503912363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (49420691 / 62500000) (395365529 / 500000000) (Real.log (1102503912363 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1102503912363 / 500000000000) = -Real.log (500000000000 / 1102503912363) := by
    rw [show ((1102503912363 / 500000000000) : ℝ) = ((500000000000 / 1102503912363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49506013 / 62500000) ≤ -Real.log (500000000000 / 1104010025063) ∧
    -Real.log (500000000000 / 1104010025063) ≤ (79209621 / 100000000) := by
  have h := checkLog_sound (w := (104010025063 / 2104010025063)) (n := 12)
    (lo := (24737257 / 250000000)) (hi := (98949029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104010025063 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1104010025063 / 1000000000000) = 1/(500000000000 / 1104010025063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (49506013 / 62500000) (79209621 / 100000000) (Real.log (1104010025063 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1104010025063 / 500000000000) = -Real.log (500000000000 / 1104010025063) := by
    rw [show ((1104010025063 / 500000000000) : ℝ) = ((500000000000 / 1104010025063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (548381477 / 1000000000) ≤ -Real.log (250000000000 / 432612494539) ∧
    -Real.log (250000000000 / 432612494539) ≤ (274190739 / 500000000) := by
  have h := checkLog_sound (w := (182612494539 / 682612494539)) (n := 12)
    (lo := (548381477 / 1000000000)) (hi := (274190739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432612494539 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432612494539 / 250000000000) = 1/(250000000000 / 432612494539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (548381477 / 1000000000) (274190739 / 500000000) (Real.log (432612494539 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (432612494539 / 250000000000) = -Real.log (250000000000 / 432612494539) := by
    rw [show ((432612494539 / 250000000000) : ℝ) = ((250000000000 / 432612494539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (137323739 / 250000000) ≤ -Real.log (100000000000 / 173203142929) ∧
    -Real.log (100000000000 / 173203142929) ≤ (549294957 / 1000000000) := by
  have h := checkLog_sound (w := (73203142929 / 273203142929)) (n := 12)
    (lo := (137323739 / 250000000)) (hi := (549294957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173203142929 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173203142929 / 100000000000) = 1/(100000000000 / 173203142929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (137323739 / 250000000) (549294957 / 1000000000) (Real.log (173203142929 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (173203142929 / 100000000000) = -Real.log (100000000000 / 173203142929) := by
    rw [show ((173203142929 / 100000000000) : ℝ) = ((100000000000 / 173203142929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (390884057 / 1000000000) ≤ -Real.log (500000000000 / 739143553541) ∧
    -Real.log (500000000000 / 739143553541) ≤ (195442029 / 500000000) := by
  have h := checkLog_sound (w := (239143553541 / 1239143553541)) (n := 12)
    (lo := (390884057 / 1000000000)) (hi := (195442029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739143553541 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739143553541 / 500000000000) = 1/(500000000000 / 739143553541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (390884057 / 1000000000) (195442029 / 500000000) (Real.log (739143553541 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (739143553541 / 500000000000) = -Real.log (500000000000 / 739143553541) := by
    rw [show ((739143553541 / 500000000000) : ℝ) = ((500000000000 / 739143553541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3058943 / 7812500) ≤ -Real.log (500000000000 / 739632027629) ∧
    -Real.log (500000000000 / 739632027629) ≤ (78308941 / 200000000) := by
  have h := checkLog_sound (w := (239632027629 / 1239632027629)) (n := 12)
    (lo := (3058943 / 7812500)) (hi := (78308941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739632027629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739632027629 / 500000000000) = 1/(500000000000 / 739632027629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3058943 / 7812500) (78308941 / 200000000) (Real.log (739632027629 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (739632027629 / 500000000000) = -Real.log (500000000000 / 739632027629) := by
    rw [show ((739632027629 / 500000000000) : ℝ) = ((500000000000 / 739632027629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (38084463 / 1000000000) ≤ -Real.log (962631630519 / 1000000000000) ∧
    -Real.log (962631630519 / 1000000000000) ≤ (2380279 / 62500000) := by
  have h := checkLog_sound (w := (37368369481 / 1962631630519)) (n := 12)
    (lo := (38084463 / 1000000000)) (hi := (2380279 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962631630519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962631630519) = 1/(962631630519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2380279 / 62500000) (-38084463 / 1000000000) (Real.log (962631630519 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37956859 / 1000000000) ≤ -Real.log (962754473919 / 1000000000000) ∧
    -Real.log (962754473919 / 1000000000000) ≤ (1897843 / 50000000) := by
  have h := checkLog_sound (w := (37245526081 / 1962754473919)) (n := 12)
    (lo := (37956859 / 1000000000)) (hi := (1897843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962754473919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962754473919) = 1/(962754473919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1897843 / 50000000) (-37956859 / 1000000000) (Real.log (962754473919 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell215

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell216Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell216
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

theorem reflection_log_1_neg : (320015011 / 1000000000) ≤ -Real.log (5120 / 7051) ∧
    -Real.log (5120 / 7051) ≤ (80003753 / 250000000) := by
  have h := checkLog_sound (w := (1931 / 12171)) (n := 12)
    (lo := (320015011 / 1000000000)) (hi := (80003753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7051 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7051 / 5120) = 1/(5120 / 7051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (320015011 / 1000000000) (80003753 / 250000000) (Real.log (7051 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7051 / 5120) = -Real.log (5120 / 7051) := by
    rw [show ((7051 / 5120) : ℝ) = ((5120 / 7051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (473447051 / 1000000000) ≤ -Real.log (3189 / 5120) ∧
    -Real.log (3189 / 5120) ≤ (118361763 / 250000000) := by
  have h := checkLog_sound (w := (1931 / 8309)) (n := 12)
    (lo := (473447051 / 1000000000)) (hi := (118361763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3189) = 1/(3189 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-118361763 / 250000000) (-473447051 / 1000000000) (Real.log (3189 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (319589449 / 1000000000) ≤ -Real.log (640 / 881) ∧
    -Real.log (640 / 881) ≤ (6391789 / 20000000) := by
  have h := checkLog_sound (w := (241 / 1521)) (n := 12)
    (lo := (319589449 / 1000000000)) (hi := (6391789 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881 / 640) = 1/(640 / 881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (319589449 / 1000000000) (6391789 / 20000000) (Real.log (881 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (881 / 640) = -Real.log (640 / 881) := by
    rw [show ((881 / 640) : ℝ) = ((640 / 881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (472506759 / 1000000000) ≤ -Real.log (399 / 640) ∧
    -Real.log (399 / 640) ≤ (11812669 / 25000000) := by
  have h := checkLog_sound (w := (241 / 1039)) (n := 12)
    (lo := (472506759 / 1000000000)) (hi := (11812669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 399) = 1/(399 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-11812669 / 25000000) (-472506759 / 1000000000) (Real.log (399 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (118697951 / 500000000) ≤ -Real.log (1000000 / 1267943) ∧
    -Real.log (1000000 / 1267943) ≤ (237395903 / 1000000000) := by
  have h := checkLog_sound (w := (267943 / 2267943)) (n := 12)
    (lo := (118697951 / 500000000)) (hi := (237395903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267943 / 1000000) = 1/(1000000 / 1267943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (118697951 / 500000000) (237395903 / 1000000000) (Real.log (1267943 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1267943 / 1000000) = -Real.log (1000000 / 1267943) := by
    rw [show ((1267943 / 1000000) : ℝ) = ((1000000 / 1267943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (311896899 / 1000000000) ≤ -Real.log (732057 / 1000000) ∧
    -Real.log (732057 / 1000000) ≤ (3118969 / 10000000) := by
  have h := checkLog_sound (w := (267943 / 1732057)) (n := 12)
    (lo := (311896899 / 1000000000)) (hi := (3118969 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732057) = 1/(732057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3118969 / 10000000) (-311896899 / 1000000000) (Real.log (732057 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (237729457 / 1000000000) ≤ -Real.log (500000 / 634183) ∧
    -Real.log (500000 / 634183) ≤ (118864729 / 500000000) := by
  have h := checkLog_sound (w := (134183 / 1134183)) (n := 12)
    (lo := (237729457 / 1000000000)) (hi := (118864729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634183 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634183 / 500000) = 1/(500000 / 634183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (237729457 / 1000000000) (118864729 / 500000000) (Real.log (634183 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (634183 / 500000) = -Real.log (500000 / 634183) := by
    rw [show ((634183 / 500000) : ℝ) = ((500000 / 634183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (31247489 / 100000000) ≤ -Real.log (365817 / 500000) ∧
    -Real.log (365817 / 500000) ≤ (312474891 / 1000000000) := by
  have h := checkLog_sound (w := (134183 / 865817)) (n := 12)
    (lo := (31247489 / 100000000)) (hi := (312474891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365817) = 1/(365817 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-312474891 / 1000000000) (-31247489 / 100000000) (Real.log (365817 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (88364641 / 500000000) ≤ -Real.log (250000 / 298327) ∧
    -Real.log (250000 / 298327) ≤ (176729283 / 1000000000) := by
  have h := checkLog_sound (w := (48327 / 548327)) (n := 12)
    (lo := (88364641 / 500000000)) (hi := (176729283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298327 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298327 / 250000) = 1/(250000 / 298327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (88364641 / 500000000) (176729283 / 1000000000) (Real.log (298327 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (298327 / 250000) = -Real.log (250000 / 298327) := by
    rw [show ((298327 / 250000) : ℝ) = ((250000 / 298327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (6712917 / 31250000) ≤ -Real.log (201673 / 250000) ∧
    -Real.log (201673 / 250000) ≤ (42962669 / 200000000) := by
  have h := checkLog_sound (w := (48327 / 451673)) (n := 12)
    (lo := (6712917 / 31250000)) (hi := (42962669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201673) = 1/(201673 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-42962669 / 200000000) (-6712917 / 31250000) (Real.log (201673 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (176995733 / 1000000000) ≤ -Real.log (500000 / 596813) ∧
    -Real.log (500000 / 596813) ≤ (88497867 / 500000000) := by
  have h := checkLog_sound (w := (96813 / 1096813)) (n := 12)
    (lo := (176995733 / 1000000000)) (hi := (88497867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596813 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596813 / 500000) = 1/(500000 / 596813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (176995733 / 1000000000) (88497867 / 500000000) (Real.log (596813 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (596813 / 500000) = -Real.log (500000 / 596813) := by
    rw [show ((596813 / 500000) : ℝ) = ((500000 / 596813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (26900953 / 125000000) ≤ -Real.log (403187 / 500000) ∧
    -Real.log (403187 / 500000) ≤ (1721661 / 8000000) := by
  have h := checkLog_sound (w := (96813 / 903187)) (n := 12)
    (lo := (26900953 / 125000000)) (hi := (1721661 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403187) = 1/(403187 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1721661 / 8000000) (-26900953 / 125000000) (Real.log (403187 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (49506013 / 62500000) ≤ -Real.log (250000000000 / 552005012531) ∧
    -Real.log (250000000000 / 552005012531) ≤ (79209621 / 100000000) := by
  have h := checkLog_sound (w := (52005012531 / 1052005012531)) (n := 12)
    (lo := (24737257 / 250000000)) (hi := (98949029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552005012531 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(552005012531 / 500000000000) = 1/(250000000000 / 552005012531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (49506013 / 62500000) (79209621 / 100000000) (Real.log (552005012531 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (552005012531 / 250000000000) = -Real.log (250000000000 / 552005012531) := by
    rw [show ((552005012531 / 250000000000) : ℝ) = ((250000000000 / 552005012531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (396731031 / 500000000) ≤ -Real.log (100000000000 / 221103794293) ∧
    -Real.log (100000000000 / 221103794293) ≤ (49591379 / 62500000) := by
  have h := checkLog_sound (w := (21103794293 / 421103794293)) (n := 12)
    (lo := (50157441 / 500000000)) (hi := (100314883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221103794293 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(221103794293 / 200000000000) = 1/(100000000000 / 221103794293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (396731031 / 500000000) (49591379 / 62500000) (Real.log (221103794293 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (221103794293 / 100000000000) = -Real.log (100000000000 / 221103794293) := by
    rw [show ((221103794293 / 100000000000) : ℝ) = ((100000000000 / 221103794293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (549292801 / 1000000000) ≤ -Real.log (62500000000 / 108251731081) ∧
    -Real.log (62500000000 / 108251731081) ≤ (274646401 / 500000000) := by
  have h := checkLog_sound (w := (45751731081 / 170751731081)) (n := 12)
    (lo := (549292801 / 1000000000)) (hi := (274646401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108251731081 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108251731081 / 62500000000) = 1/(62500000000 / 108251731081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (549292801 / 1000000000) (274646401 / 500000000) (Real.log (108251731081 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (108251731081 / 62500000000) = -Real.log (62500000000 / 108251731081) := by
    rw [show ((108251731081 / 62500000000) : ℝ) = ((62500000000 / 108251731081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (550204347 / 1000000000) ≤ -Real.log (50000000000 / 86680362039) ∧
    -Real.log (50000000000 / 86680362039) ≤ (137551087 / 250000000) := by
  have h := checkLog_sound (w := (36680362039 / 136680362039)) (n := 12)
    (lo := (550204347 / 1000000000)) (hi := (137551087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86680362039 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86680362039 / 50000000000) = 1/(50000000000 / 86680362039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (550204347 / 1000000000) (137551087 / 250000000) (Real.log (86680362039 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (86680362039 / 50000000000) = -Real.log (50000000000 / 86680362039) := by
    rw [show ((86680362039 / 50000000000) : ℝ) = ((50000000000 / 86680362039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (195771313 / 500000000) ≤ -Real.log (500000000000 / 739630490943) ∧
    -Real.log (500000000000 / 739630490943) ≤ (391542627 / 1000000000) := by
  have h := checkLog_sound (w := (239630490943 / 1239630490943)) (n := 12)
    (lo := (195771313 / 500000000)) (hi := (391542627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739630490943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739630490943 / 500000000000) = 1/(500000000000 / 739630490943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (195771313 / 500000000) (391542627 / 1000000000) (Real.log (739630490943 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (739630490943 / 500000000000) = -Real.log (500000000000 / 739630490943) := by
    rw [show ((739630490943 / 500000000000) : ℝ) = ((500000000000 / 739630490943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (392203357 / 1000000000) ≤ -Real.log (500000000000 / 740119349087) ∧
    -Real.log (500000000000 / 740119349087) ≤ (196101679 / 500000000) := by
  have h := checkLog_sound (w := (240119349087 / 1240119349087)) (n := 12)
    (lo := (392203357 / 1000000000)) (hi := (196101679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740119349087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740119349087 / 500000000000) = 1/(500000000000 / 740119349087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (392203357 / 1000000000) (196101679 / 500000000) (Real.log (740119349087 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (740119349087 / 500000000000) = -Real.log (500000000000 / 740119349087) := by
    rw [show ((740119349087 / 500000000000) : ℝ) = ((500000000000 / 740119349087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (38211891 / 1000000000) ≤ -Real.log (240627243031 / 250000000000) ∧
    -Real.log (240627243031 / 250000000000) ≤ (9552973 / 250000000) := by
  have h := checkLog_sound (w := (9372756969 / 490627243031)) (n := 12)
    (lo := (38211891 / 1000000000)) (hi := (9552973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240627243031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240627243031) = 1/(240627243031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9552973 / 250000000) (-38211891 / 1000000000) (Real.log (240627243031 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (38084061 / 1000000000) ≤ -Real.log (60164501071 / 62500000000) ∧
    -Real.log (60164501071 / 62500000000) ≤ (19042031 / 500000000) := by
  have h := checkLog_sound (w := (2335498929 / 122664501071)) (n := 12)
    (lo := (38084061 / 1000000000)) (hi := (19042031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60164501071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60164501071) = 1/(60164501071 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19042031 / 500000000) (-38084061 / 1000000000) (Real.log (60164501071 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell216

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell217Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell217
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

theorem reflection_log_1_neg : (40055049 / 125000000) ≤ -Real.log (2560 / 3527) ∧
    -Real.log (2560 / 3527) ≤ (320440393 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 6087)) (n := 12)
    (lo := (40055049 / 125000000)) (hi := (320440393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3527 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3527 / 2560) = 1/(2560 / 3527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (40055049 / 125000000) (320440393 / 1000000000) (Real.log (3527 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3527 / 2560) = -Real.log (2560 / 3527) := by
    rw [show ((3527 / 2560) : ℝ) = ((2560 / 3527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (474388227 / 1000000000) ≤ -Real.log (1593 / 2560) ∧
    -Real.log (1593 / 2560) ≤ (118597057 / 250000000) := by
  have h := checkLog_sound (w := (967 / 4153)) (n := 12)
    (lo := (474388227 / 1000000000)) (hi := (118597057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1593) = 1/(1593 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-118597057 / 250000000) (-474388227 / 1000000000) (Real.log (1593 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (320015011 / 1000000000) ≤ -Real.log (5120 / 7051) ∧
    -Real.log (5120 / 7051) ≤ (80003753 / 250000000) := by
  have h := checkLog_sound (w := (1931 / 12171)) (n := 12)
    (lo := (320015011 / 1000000000)) (hi := (80003753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7051 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7051 / 5120) = 1/(5120 / 7051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (320015011 / 1000000000) (80003753 / 250000000) (Real.log (7051 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7051 / 5120) = -Real.log (5120 / 7051) := by
    rw [show ((7051 / 5120) : ℝ) = ((5120 / 7051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (473447051 / 1000000000) ≤ -Real.log (3189 / 5120) ∧
    -Real.log (3189 / 5120) ≤ (118361763 / 250000000) := by
  have h := checkLog_sound (w := (1931 / 8309)) (n := 12)
    (lo := (473447051 / 1000000000)) (hi := (118361763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3189) = 1/(3189 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-118361763 / 250000000) (-473447051 / 1000000000) (Real.log (3189 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (237728669 / 1000000000) ≤ -Real.log (200000 / 253673) ∧
    -Real.log (200000 / 253673) ≤ (23772867 / 100000000) := by
  have h := checkLog_sound (w := (53673 / 453673)) (n := 12)
    (lo := (237728669 / 1000000000)) (hi := (23772867 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253673 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(253673 / 200000) = 1/(200000 / 253673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (237728669 / 1000000000) (23772867 / 100000000) (Real.log (253673 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (253673 / 200000) = -Real.log (200000 / 253673) := by
    rw [show ((253673 / 200000) : ℝ) = ((200000 / 253673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (312473523 / 1000000000) ≤ -Real.log (146327 / 200000) ∧
    -Real.log (146327 / 200000) ≤ (78118381 / 250000000) := by
  have h := checkLog_sound (w := (53673 / 346327)) (n := 12)
    (lo := (312473523 / 1000000000)) (hi := (78118381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 146327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 146327) = 1/(146327 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-78118381 / 250000000) (-312473523 / 1000000000) (Real.log (146327 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (119031451 / 500000000) ≤ -Real.log (1000000 / 1268789) ∧
    -Real.log (1000000 / 1268789) ≤ (238062903 / 1000000000) := by
  have h := checkLog_sound (w := (268789 / 2268789)) (n := 12)
    (lo := (119031451 / 500000000)) (hi := (238062903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1268789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1268789 / 1000000) = 1/(1000000 / 1268789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (119031451 / 500000000) (238062903 / 1000000000) (Real.log (1268789 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1268789 / 1000000) = -Real.log (1000000 / 1268789) := by
    rw [show ((1268789 / 1000000) : ℝ) = ((1000000 / 1268789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (62610643 / 200000000) ≤ -Real.log (731211 / 1000000) ∧
    -Real.log (731211 / 1000000) ≤ (9782913 / 31250000) := by
  have h := checkLog_sound (w := (268789 / 1731211)) (n := 12)
    (lo := (62610643 / 200000000)) (hi := (9782913 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 731211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 731211) = 1/(731211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9782913 / 31250000) (-62610643 / 200000000) (Real.log (731211 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35398979 / 200000000) ≤ -Real.log (8000 / 9549) ∧
    -Real.log (8000 / 9549) ≤ (11062181 / 62500000) := by
  have h := checkLog_sound (w := (1549 / 17549)) (n := 12)
    (lo := (35398979 / 200000000)) (hi := (11062181 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9549 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9549 / 8000) = 1/(8000 / 9549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35398979 / 200000000) (11062181 / 62500000) (Real.log (9549 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (9549 / 8000) = -Real.log (8000 / 9549) := by
    rw [show ((9549 / 8000) : ℝ) = ((8000 / 9549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (13450399 / 62500000) ≤ -Real.log (6451 / 8000) ∧
    -Real.log (6451 / 8000) ≤ (43041277 / 200000000) := by
  have h := checkLog_sound (w := (1549 / 14451)) (n := 12)
    (lo := (13450399 / 62500000)) (hi := (43041277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 6451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 6451) = 1/(6451 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-43041277 / 200000000) (-13450399 / 62500000) (Real.log (6451 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7090451 / 40000000) ≤ -Real.log (1000000 / 1193943) ∧
    -Real.log (1000000 / 1193943) ≤ (44315319 / 250000000) := by
  have h := checkLog_sound (w := (193943 / 2193943)) (n := 12)
    (lo := (7090451 / 40000000)) (hi := (44315319 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193943 / 1000000) = 1/(1000000 / 1193943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7090451 / 40000000) (44315319 / 250000000) (Real.log (1193943 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1193943 / 1000000) = -Real.log (1000000 / 1193943) := by
    rw [show ((1193943 / 1000000) : ℝ) = ((1000000 / 1193943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (215600819 / 1000000000) ≤ -Real.log (806057 / 1000000) ∧
    -Real.log (806057 / 1000000) ≤ (10780041 / 50000000) := by
  have h := checkLog_sound (w := (193943 / 1806057)) (n := 12)
    (lo := (215600819 / 1000000000)) (hi := (10780041 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806057) = 1/(806057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-10780041 / 50000000) (-215600819 / 1000000000) (Real.log (806057 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (396731031 / 500000000) ≤ -Real.log (62500000000 / 138189871433) ∧
    -Real.log (62500000000 / 138189871433) ≤ (49591379 / 62500000) := by
  have h := checkLog_sound (w := (13189871433 / 263189871433)) (n := 12)
    (lo := (50157441 / 500000000)) (hi := (100314883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138189871433 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(138189871433 / 125000000000) = 1/(62500000000 / 138189871433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (396731031 / 500000000) (49591379 / 62500000) (Real.log (138189871433 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (138189871433 / 62500000000) = -Real.log (62500000000 / 138189871433) := by
    rw [show ((138189871433 / 62500000000) : ℝ) = ((62500000000 / 138189871433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (794828619 / 1000000000) ≤ -Real.log (250000000000 / 553515379787) ∧
    -Real.log (250000000000 / 553515379787) ≤ (794828621 / 1000000000) := by
  have h := checkLog_sound (w := (53515379787 / 1053515379787)) (n := 12)
    (lo := (101681439 / 1000000000)) (hi := (635509 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((553515379787 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(553515379787 / 500000000000) = 1/(250000000000 / 553515379787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (794828619 / 1000000000) (794828621 / 1000000000) (Real.log (553515379787 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (553515379787 / 250000000000) = -Real.log (250000000000 / 553515379787) := by
    rw [show ((553515379787 / 250000000000) : ℝ) = ((250000000000 / 553515379787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (34387637 / 62500000) ≤ -Real.log (500000000000 / 866801752239) ∧
    -Real.log (500000000000 / 866801752239) ≤ (550202193 / 1000000000) := by
  have h := checkLog_sound (w := (366801752239 / 1366801752239)) (n := 12)
    (lo := (34387637 / 62500000)) (hi := (550202193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((866801752239 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(866801752239 / 500000000000) = 1/(500000000000 / 866801752239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (34387637 / 62500000) (550202193 / 1000000000) (Real.log (866801752239 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (866801752239 / 500000000000) = -Real.log (500000000000 / 866801752239) := by
    rw [show ((866801752239 / 500000000000) : ℝ) = ((500000000000 / 866801752239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (551116117 / 1000000000) ≤ -Real.log (100000000000 / 173518861177) ∧
    -Real.log (100000000000 / 173518861177) ≤ (275558059 / 500000000) := by
  have h := checkLog_sound (w := (73518861177 / 273518861177)) (n := 12)
    (lo := (551116117 / 1000000000)) (hi := (275558059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173518861177 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173518861177 / 100000000000) = 1/(100000000000 / 173518861177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (551116117 / 1000000000) (275558059 / 500000000) (Real.log (173518861177 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (173518861177 / 100000000000) = -Real.log (100000000000 / 173518861177) := by
    rw [show ((173518861177 / 100000000000) : ℝ) = ((100000000000 / 173518861177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (392201279 / 1000000000) ≤ -Real.log (62500000000 / 92514726399) ∧
    -Real.log (62500000000 / 92514726399) ≤ (1225629 / 3125000) := by
  have h := checkLog_sound (w := (30014726399 / 155014726399)) (n := 12)
    (lo := (392201279 / 1000000000)) (hi := (1225629 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92514726399 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92514726399 / 62500000000) = 1/(62500000000 / 92514726399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (392201279 / 1000000000) (1225629 / 3125000) (Real.log (92514726399 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (92514726399 / 62500000000) = -Real.log (62500000000 / 92514726399) := by
    rw [show ((92514726399 / 62500000000) : ℝ) = ((62500000000 / 92514726399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (196431047 / 500000000) ≤ -Real.log (125000000000 / 185151763461) ∧
    -Real.log (125000000000 / 185151763461) ≤ (78572419 / 200000000) := by
  have h := checkLog_sound (w := (60151763461 / 310151763461)) (n := 12)
    (lo := (196431047 / 500000000)) (hi := (78572419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185151763461 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185151763461 / 125000000000) = 1/(125000000000 / 185151763461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (196431047 / 500000000) (78572419 / 200000000) (Real.log (185151763461 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (185151763461 / 125000000000) = -Real.log (125000000000 / 185151763461) := by
    rw [show ((185151763461 / 125000000000) : ℝ) = ((125000000000 / 185151763461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4792443 / 125000000) ≤ -Real.log (962386112751 / 1000000000000) ∧
    -Real.log (962386112751 / 1000000000000) ≤ (7667909 / 200000000) := by
  have h := checkLog_sound (w := (37613887249 / 1962386112751)) (n := 12)
    (lo := (4792443 / 125000000)) (hi := (7667909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962386112751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962386112751) = 1/(962386112751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-7667909 / 200000000) (-4792443 / 125000000) (Real.log (962386112751 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1194109 / 31250000) ≤ -Real.log (61600599 / 64000000) ∧
    -Real.log (61600599 / 64000000) ≤ (38211489 / 1000000000) := by
  have h := checkLog_sound (w := (2399401 / 125600599)) (n := 12)
    (lo := (1194109 / 31250000)) (hi := (38211489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64000000 / 61600599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64000000 / 61600599) = 1/(61600599 / 64000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-38211489 / 1000000000) (-1194109 / 31250000) (Real.log (61600599 / 64000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell217

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell218Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell218
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

theorem reflection_log_1_neg : (40108199 / 125000000) ≤ -Real.log (5120 / 7057) ∧
    -Real.log (5120 / 7057) ≤ (320865593 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 12177)) (n := 12)
    (lo := (40108199 / 125000000)) (hi := (320865593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7057 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7057 / 5120) = 1/(5120 / 7057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (40108199 / 125000000) (320865593 / 1000000000) (Real.log (7057 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7057 / 5120) = -Real.log (5120 / 7057) := by
    rw [show ((7057 / 5120) : ℝ) = ((5120 / 7057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (47533029 / 100000000) ≤ -Real.log (3183 / 5120) ∧
    -Real.log (3183 / 5120) ≤ (475330291 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 8303)) (n := 12)
    (lo := (47533029 / 100000000)) (hi := (475330291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3183) = 1/(3183 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-475330291 / 1000000000) (-47533029 / 100000000) (Real.log (3183 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (40055049 / 125000000) ≤ -Real.log (2560 / 3527) ∧
    -Real.log (2560 / 3527) ≤ (320440393 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 6087)) (n := 12)
    (lo := (40055049 / 125000000)) (hi := (320440393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3527 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3527 / 2560) = 1/(2560 / 3527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (40055049 / 125000000) (320440393 / 1000000000) (Real.log (3527 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3527 / 2560) = -Real.log (2560 / 3527) := by
    rw [show ((3527 / 2560) : ℝ) = ((2560 / 3527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (474388227 / 1000000000) ≤ -Real.log (1593 / 2560) ∧
    -Real.log (1593 / 2560) ≤ (118597057 / 250000000) := by
  have h := checkLog_sound (w := (967 / 4153)) (n := 12)
    (lo := (474388227 / 1000000000)) (hi := (118597057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1593) = 1/(1593 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-118597057 / 250000000) (-474388227 / 1000000000) (Real.log (1593 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (119031057 / 500000000) ≤ -Real.log (250000 / 317197) ∧
    -Real.log (250000 / 317197) ≤ (47612423 / 200000000) := by
  have h := checkLog_sound (w := (67197 / 567197)) (n := 12)
    (lo := (119031057 / 500000000)) (hi := (47612423 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317197 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317197 / 250000) = 1/(250000 / 317197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (119031057 / 500000000) (47612423 / 200000000) (Real.log (317197 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (317197 / 250000) = -Real.log (250000 / 317197) := by
    rw [show ((317197 / 250000) : ℝ) = ((250000 / 317197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (313051847 / 1000000000) ≤ -Real.log (182803 / 250000) ∧
    -Real.log (182803 / 250000) ≤ (39131481 / 125000000) := by
  have h := checkLog_sound (w := (67197 / 432803)) (n := 12)
    (lo := (313051847 / 1000000000)) (hi := (39131481 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 182803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 182803) = 1/(182803 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-39131481 / 125000000) (-313051847 / 1000000000) (Real.log (182803 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (238395447 / 1000000000) ≤ -Real.log (1000000 / 1269211) ∧
    -Real.log (1000000 / 1269211) ≤ (29799431 / 125000000) := by
  have h := checkLog_sound (w := (269211 / 2269211)) (n := 12)
    (lo := (238395447 / 1000000000)) (hi := (29799431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269211 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269211 / 1000000) = 1/(1000000 / 1269211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (238395447 / 1000000000) (29799431 / 125000000) (Real.log (1269211 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1269211 / 1000000) = -Real.log (1000000 / 1269211) := by
    rw [show ((1269211 / 1000000) : ℝ) = ((1000000 / 1269211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (156815253 / 500000000) ≤ -Real.log (730789 / 1000000) ∧
    -Real.log (730789 / 1000000) ≤ (313630507 / 1000000000) := by
  have h := checkLog_sound (w := (269211 / 1730789)) (n := 12)
    (lo := (156815253 / 500000000)) (hi := (313630507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 730789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 730789) = 1/(730789 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-313630507 / 1000000000) (-156815253 / 500000000) (Real.log (730789 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (177260437 / 1000000000) ≤ -Real.log (500000 / 596971) ∧
    -Real.log (500000 / 596971) ≤ (88630219 / 500000000) := by
  have h := checkLog_sound (w := (96971 / 1096971)) (n := 12)
    (lo := (177260437 / 1000000000)) (hi := (88630219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596971 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596971 / 500000) = 1/(500000 / 596971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (177260437 / 1000000000) (88630219 / 500000000) (Real.log (596971 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (596971 / 500000) = -Real.log (500000 / 596971) := by
    rw [show ((596971 / 500000) : ℝ) = ((500000 / 596971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (107799789 / 500000000) ≤ -Real.log (403029 / 500000) ∧
    -Real.log (403029 / 500000) ≤ (215599579 / 1000000000) := by
  have h := checkLog_sound (w := (96971 / 903029)) (n := 12)
    (lo := (107799789 / 500000000)) (hi := (215599579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403029) = 1/(403029 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-215599579 / 1000000000) (-107799789 / 500000000) (Real.log (403029 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (5547737 / 31250000) ≤ -Real.log (1000000 / 1194261) ∧
    -Real.log (1000000 / 1194261) ≤ (35505517 / 200000000) := by
  have h := checkLog_sound (w := (194261 / 2194261)) (n := 12)
    (lo := (5547737 / 31250000)) (hi := (35505517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194261 / 1000000) = 1/(1000000 / 1194261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (5547737 / 31250000) (35505517 / 200000000) (Real.log (1194261 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1194261 / 1000000) = -Real.log (1000000 / 1194261) := by
    rw [show ((1194261 / 1000000) : ℝ) = ((1000000 / 1194261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (21599541 / 100000000) ≤ -Real.log (805739 / 1000000) ∧
    -Real.log (805739 / 1000000) ≤ (215995411 / 1000000000) := by
  have h := checkLog_sound (w := (194261 / 1805739)) (n := 12)
    (lo := (21599541 / 100000000)) (hi := (215995411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805739) = 1/(805739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-215995411 / 1000000000) (-21599541 / 100000000) (Real.log (805739 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (794828619 / 1000000000) ≤ -Real.log (500000000000 / 1107030759573) ∧
    -Real.log (500000000000 / 1107030759573) ≤ (794828621 / 1000000000) := by
  have h := checkLog_sound (w := (107030759573 / 2107030759573)) (n := 12)
    (lo := (101681439 / 1000000000)) (hi := (635509 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1107030759573 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1107030759573 / 1000000000000) = 1/(500000000000 / 1107030759573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (794828619 / 1000000000) (794828621 / 1000000000) (Real.log (1107030759573 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1107030759573 / 500000000000) = -Real.log (500000000000 / 1107030759573) := by
    rw [show ((1107030759573 / 500000000000) : ℝ) = ((500000000000 / 1107030759573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (796195883 / 1000000000) ≤ -Real.log (31250000000 / 69284087339) ∧
    -Real.log (31250000000 / 69284087339) ≤ (159239177 / 200000000) := by
  have h := checkLog_sound (w := (6784087339 / 131784087339)) (n := 12)
    (lo := (103048703 / 1000000000)) (hi := (201267 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69284087339 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(69284087339 / 62500000000) = 1/(31250000000 / 69284087339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (796195883 / 1000000000) (159239177 / 200000000) (Real.log (69284087339 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (69284087339 / 31250000000) = -Real.log (31250000000 / 69284087339) := by
    rw [show ((69284087339 / 31250000000) : ℝ) = ((31250000000 / 69284087339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (551113961 / 1000000000) ≤ -Real.log (125000000000 / 216898108893) ∧
    -Real.log (125000000000 / 216898108893) ≤ (275556981 / 500000000) := by
  have h := checkLog_sound (w := (91898108893 / 341898108893)) (n := 12)
    (lo := (551113961 / 1000000000)) (hi := (275556981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216898108893 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216898108893 / 125000000000) = 1/(125000000000 / 216898108893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (551113961 / 1000000000) (275556981 / 500000000) (Real.log (216898108893 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (216898108893 / 125000000000) = -Real.log (125000000000 / 216898108893) := by
    rw [show ((216898108893 / 125000000000) : ℝ) = ((125000000000 / 216898108893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (276012977 / 500000000) ≤ -Real.log (500000000000 / 868384034243) ∧
    -Real.log (500000000000 / 868384034243) ≤ (110405191 / 200000000) := by
  have h := checkLog_sound (w := (368384034243 / 1368384034243)) (n := 12)
    (lo := (276012977 / 500000000)) (hi := (110405191 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((868384034243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(868384034243 / 500000000000) = 1/(500000000000 / 868384034243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (276012977 / 500000000) (110405191 / 200000000) (Real.log (868384034243 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (868384034243 / 500000000000) = -Real.log (500000000000 / 868384034243) := by
    rw [show ((868384034243 / 500000000000) : ℝ) = ((500000000000 / 868384034243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (24553751 / 62500000) ≤ -Real.log (500000000000 / 740605514739) ∧
    -Real.log (500000000000 / 740605514739) ≤ (392860017 / 1000000000) := by
  have h := checkLog_sound (w := (240605514739 / 1240605514739)) (n := 12)
    (lo := (24553751 / 62500000)) (hi := (392860017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740605514739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740605514739 / 500000000000) = 1/(500000000000 / 740605514739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (24553751 / 62500000) (392860017 / 1000000000) (Real.log (740605514739 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (740605514739 / 500000000000) = -Real.log (500000000000 / 740605514739) := by
    rw [show ((740605514739 / 500000000000) : ℝ) = ((500000000000 / 740605514739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (196761497 / 500000000) ≤ -Real.log (500000000000 / 741096682673) ∧
    -Real.log (500000000000 / 741096682673) ≤ (78704599 / 200000000) := by
  have h := checkLog_sound (w := (241096682673 / 1241096682673)) (n := 12)
    (lo := (196761497 / 500000000)) (hi := (78704599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741096682673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741096682673 / 500000000000) = 1/(500000000000 / 741096682673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (196761497 / 500000000) (78704599 / 200000000) (Real.log (741096682673 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (741096682673 / 500000000000) = -Real.log (500000000000 / 741096682673) := by
    rw [show ((741096682673 / 500000000000) : ℝ) = ((500000000000 / 741096682673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (19233913 / 500000000) ≤ -Real.log (962262663879 / 1000000000000) ∧
    -Real.log (962262663879 / 1000000000000) ≤ (38467827 / 1000000000) := by
  have h := checkLog_sound (w := (37737336121 / 1962262663879)) (n := 12)
    (lo := (19233913 / 500000000)) (hi := (38467827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962262663879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962262663879) = 1/(962262663879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-38467827 / 1000000000) (-19233913 / 500000000) (Real.log (962262663879 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (38339141 / 1000000000) ≤ -Real.log (240596625159 / 250000000000) ∧
    -Real.log (240596625159 / 250000000000) ≤ (19169571 / 500000000) := by
  have h := checkLog_sound (w := (9403374841 / 490596625159)) (n := 12)
    (lo := (38339141 / 1000000000)) (hi := (19169571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240596625159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240596625159) = 1/(240596625159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19169571 / 500000000) (-38339141 / 1000000000) (Real.log (240596625159 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell218

end


