-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell169Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell169Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:44:24.26378+00:00
-- url     : https://prove2.me/theorems/51f01464-4705-485f-960a-70f9711d9f81
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell169Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell170…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell169Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell170Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell171Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell172Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell173Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell174Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell169Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell170Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell171Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell172Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell173Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell174Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell169Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell170Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell171Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell172Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell173Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell174Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell169Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell170Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell171Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell172Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell173Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell174Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell169Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell169
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

theorem reflection_log_1_neg : (149907599 / 500000000) ≤ -Real.log (512 / 691) ∧
    -Real.log (512 / 691) ≤ (299815199 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 1203)) (n := 12)
    (lo := (149907599 / 500000000)) (hi := (299815199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691 / 512) = 1/(512 / 691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (149907599 / 500000000) (299815199 / 1000000000) (Real.log (691 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (691 / 512) = -Real.log (512 / 691) := by
    rw [show ((691 / 512) : ℝ) = ((512 / 691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (86036427 / 200000000) ≤ -Real.log (333 / 512) ∧
    -Real.log (333 / 512) ≤ (53772767 / 125000000) := by
  have h := checkLog_sound (w := (179 / 845)) (n := 12)
    (lo := (86036427 / 200000000)) (hi := (53772767 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 333) = 1/(333 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-53772767 / 125000000) (-86036427 / 200000000) (Real.log (333 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (299380951 / 1000000000) ≤ -Real.log (5120 / 6907) ∧
    -Real.log (5120 / 6907) ≤ (37422619 / 125000000) := by
  have h := checkLog_sound (w := (1787 / 12027)) (n := 12)
    (lo := (299380951 / 1000000000)) (hi := (37422619 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6907 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6907 / 5120) = 1/(5120 / 6907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (299380951 / 1000000000) (37422619 / 125000000) (Real.log (6907 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6907 / 5120) = -Real.log (5120 / 6907) := by
    rw [show ((6907 / 5120) : ℝ) = ((5120 / 6907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (429281639 / 1000000000) ≤ -Real.log (3333 / 5120) ∧
    -Real.log (3333 / 5120) ≤ (10732041 / 25000000) := by
  have h := checkLog_sound (w := (1787 / 8453)) (n := 12)
    (lo := (429281639 / 1000000000)) (hi := (10732041 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3333) = 1/(3333 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10732041 / 25000000) (-429281639 / 1000000000) (Real.log (3333 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (44327203 / 200000000) ≤ -Real.log (1000000 / 1248117) ∧
    -Real.log (1000000 / 1248117) ≤ (13852251 / 62500000) := by
  have h := checkLog_sound (w := (248117 / 2248117)) (n := 12)
    (lo := (44327203 / 200000000)) (hi := (13852251 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248117 / 1000000) = 1/(1000000 / 1248117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (44327203 / 200000000) (13852251 / 62500000) (Real.log (1248117 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1248117 / 1000000) = -Real.log (1000000 / 1248117) := by
    rw [show ((1248117 / 1000000) : ℝ) = ((1000000 / 1248117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (35646819 / 125000000) ≤ -Real.log (751883 / 1000000) ∧
    -Real.log (751883 / 1000000) ≤ (285174553 / 1000000000) := by
  have h := checkLog_sound (w := (248117 / 1751883)) (n := 12)
    (lo := (35646819 / 125000000)) (hi := (285174553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 751883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 751883) = 1/(751883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-285174553 / 1000000000) (-35646819 / 125000000) (Real.log (751883 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (221974067 / 1000000000) ≤ -Real.log (1000000 / 1248539) ∧
    -Real.log (1000000 / 1248539) ≤ (55493517 / 250000000) := by
  have h := checkLog_sound (w := (248539 / 2248539)) (n := 12)
    (lo := (221974067 / 1000000000)) (hi := (55493517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248539 / 1000000) = 1/(1000000 / 1248539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (221974067 / 1000000000) (55493517 / 250000000) (Real.log (1248539 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1248539 / 1000000) = -Real.log (1000000 / 1248539) := by
    rw [show ((1248539 / 1000000) : ℝ) = ((1000000 / 1248539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (285735967 / 1000000000) ≤ -Real.log (751461 / 1000000) ∧
    -Real.log (751461 / 1000000) ≤ (8929249 / 31250000) := by
  have h := checkLog_sound (w := (248539 / 1751461)) (n := 12)
    (lo := (285735967 / 1000000000)) (hi := (8929249 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 751461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 751461) = 1/(751461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-8929249 / 31250000) (-285735967 / 1000000000) (Real.log (751461 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (164233109 / 1000000000) ≤ -Real.log (1000000 / 1178489) ∧
    -Real.log (1000000 / 1178489) ≤ (16423311 / 100000000) := by
  have h := checkLog_sound (w := (178489 / 2178489)) (n := 12)
    (lo := (164233109 / 1000000000)) (hi := (16423311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1178489 / 1000000) = 1/(1000000 / 1178489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (164233109 / 1000000000) (16423311 / 100000000) (Real.log (1178489 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1178489 / 1000000) = -Real.log (1000000 / 1178489) := by
    rw [show ((1178489 / 1000000) : ℝ) = ((1000000 / 1178489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (196609951 / 1000000000) ≤ -Real.log (821511 / 1000000) ∧
    -Real.log (821511 / 1000000) ≤ (6144061 / 31250000) := by
  have h := checkLog_sound (w := (178489 / 1821511)) (n := 12)
    (lo := (196609951 / 1000000000)) (hi := (6144061 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 821511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 821511) = 1/(821511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-6144061 / 31250000) (-196609951 / 1000000000) (Real.log (821511 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (41124879 / 250000000) ≤ -Real.log (1000000 / 1178803) ∧
    -Real.log (1000000 / 1178803) ≤ (164499517 / 1000000000) := by
  have h := checkLog_sound (w := (178803 / 2178803)) (n := 12)
    (lo := (41124879 / 250000000)) (hi := (164499517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1178803 / 1000000) = 1/(1000000 / 1178803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (41124879 / 250000000) (164499517 / 1000000000) (Real.log (1178803 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1178803 / 1000000) = -Real.log (1000000 / 1178803) := by
    rw [show ((1178803 / 1000000) : ℝ) = ((1000000 / 1178803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (196992247 / 1000000000) ≤ -Real.log (821197 / 1000000) ∧
    -Real.log (821197 / 1000000) ≤ (24624031 / 125000000) := by
  have h := checkLog_sound (w := (178803 / 1821197)) (n := 12)
    (lo := (196992247 / 1000000000)) (hi := (24624031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 821197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 821197) = 1/(821197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-24624031 / 125000000) (-196992247 / 1000000000) (Real.log (821197 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (72866259 / 100000000) ≤ -Real.log (500000000000 / 1036153615361) ∧
    -Real.log (500000000000 / 1036153615361) ≤ (11385353 / 15625000) := by
  have h := checkLog_sound (w := (36153615361 / 2036153615361)) (n := 12)
    (lo := (3551541 / 100000000)) (hi := (35515411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1036153615361 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1036153615361 / 1000000000000) = 1/(500000000000 / 1036153615361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (72866259 / 100000000) (11385353 / 15625000) (Real.log (1036153615361 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1036153615361 / 500000000000) = -Real.log (500000000000 / 1036153615361) := by
    rw [show ((1036153615361 / 500000000000) : ℝ) = ((500000000000 / 1036153615361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (729997333 / 1000000000) ≤ -Real.log (250000000000 / 518768768769) ∧
    -Real.log (250000000000 / 518768768769) ≤ (145999467 / 200000000) := by
  have h := checkLog_sound (w := (18768768769 / 1018768768769)) (n := 12)
    (lo := (36850153 / 1000000000)) (hi := (18425077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((518768768769 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(518768768769 / 500000000000) = 1/(250000000000 / 518768768769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (729997333 / 1000000000) (145999467 / 200000000) (Real.log (518768768769 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (518768768769 / 250000000000) = -Real.log (250000000000 / 518768768769) := by
    rw [show ((518768768769 / 250000000000) : ℝ) = ((250000000000 / 518768768769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (506810567 / 1000000000) ≤ -Real.log (20000000000 / 33199766453) ∧
    -Real.log (20000000000 / 33199766453) ≤ (63351321 / 125000000) := by
  have h := checkLog_sound (w := (13199766453 / 53199766453)) (n := 12)
    (lo := (506810567 / 1000000000)) (hi := (63351321 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33199766453 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33199766453 / 20000000000) = 1/(20000000000 / 33199766453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (506810567 / 1000000000) (63351321 / 125000000) (Real.log (33199766453 / 20000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (33199766453 / 20000000000) = -Real.log (20000000000 / 33199766453) := by
    rw [show ((33199766453 / 20000000000) : ℝ) = ((20000000000 / 33199766453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (101542007 / 200000000) ≤ -Real.log (500000000000 / 830741049769) ∧
    -Real.log (500000000000 / 830741049769) ≤ (126927509 / 250000000) := by
  have h := checkLog_sound (w := (330741049769 / 1330741049769)) (n := 12)
    (lo := (101542007 / 200000000)) (hi := (126927509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((830741049769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(830741049769 / 500000000000) = 1/(500000000000 / 830741049769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (101542007 / 200000000) (126927509 / 250000000) (Real.log (830741049769 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (830741049769 / 500000000000) = -Real.log (500000000000 / 830741049769) := by
    rw [show ((830741049769 / 500000000000) : ℝ) = ((500000000000 / 830741049769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (18042153 / 50000000) ≤ -Real.log (250000000000 / 358634577017) ∧
    -Real.log (250000000000 / 358634577017) ≤ (360843061 / 1000000000) := by
  have h := checkLog_sound (w := (108634577017 / 608634577017)) (n := 12)
    (lo := (18042153 / 50000000)) (hi := (360843061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358634577017 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358634577017 / 250000000000) = 1/(250000000000 / 358634577017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (18042153 / 50000000) (360843061 / 1000000000) (Real.log (358634577017 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (358634577017 / 250000000000) = -Real.log (250000000000 / 358634577017) := by
    rw [show ((358634577017 / 250000000000) : ℝ) = ((250000000000 / 358634577017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (361491763 / 1000000000) ≤ -Real.log (100000000000 / 143546919923) ∧
    -Real.log (100000000000 / 143546919923) ≤ (90372941 / 250000000) := by
  have h := checkLog_sound (w := (43546919923 / 243546919923)) (n := 12)
    (lo := (361491763 / 1000000000)) (hi := (90372941 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143546919923 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143546919923 / 100000000000) = 1/(100000000000 / 143546919923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (361491763 / 1000000000) (90372941 / 250000000) (Real.log (143546919923 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (143546919923 / 100000000000) = -Real.log (100000000000 / 143546919923) := by
    rw [show ((143546919923 / 100000000000) : ℝ) = ((100000000000 / 143546919923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3249273 / 100000000) ≤ -Real.log (968029487191 / 1000000000000) ∧
    -Real.log (968029487191 / 1000000000000) ≤ (32492731 / 1000000000) := by
  have h := checkLog_sound (w := (31970512809 / 1968029487191)) (n := 12)
    (lo := (3249273 / 100000000)) (hi := (32492731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968029487191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968029487191) = 1/(968029487191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-32492731 / 1000000000) (-3249273 / 100000000) (Real.log (968029487191 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16188421 / 500000000) ≤ -Real.log (968141676879 / 1000000000000) ∧
    -Real.log (968141676879 / 1000000000000) ≤ (32376843 / 1000000000) := by
  have h := checkLog_sound (w := (31858323121 / 1968141676879)) (n := 12)
    (lo := (16188421 / 500000000)) (hi := (32376843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968141676879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968141676879) = 1/(968141676879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32376843 / 1000000000) (-16188421 / 500000000) (Real.log (968141676879 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell169

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell170Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell170
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

theorem reflection_log_1_neg : (300249257 / 1000000000) ≤ -Real.log (5120 / 6913) ∧
    -Real.log (5120 / 6913) ≤ (150124629 / 500000000) := by
  have h := checkLog_sound (w := (1793 / 12033)) (n := 12)
    (lo := (300249257 / 1000000000)) (hi := (150124629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6913 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6913 / 5120) = 1/(5120 / 6913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (300249257 / 1000000000) (150124629 / 500000000) (Real.log (6913 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6913 / 5120) = -Real.log (5120 / 6913) := by
    rw [show ((6913 / 5120) : ℝ) = ((5120 / 6913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (215541721 / 500000000) ≤ -Real.log (3327 / 5120) ∧
    -Real.log (3327 / 5120) ≤ (431083443 / 1000000000) := by
  have h := checkLog_sound (w := (1793 / 8447)) (n := 12)
    (lo := (215541721 / 500000000)) (hi := (431083443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3327) = 1/(3327 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-431083443 / 1000000000) (-215541721 / 500000000) (Real.log (3327 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (149907599 / 500000000) ≤ -Real.log (512 / 691) ∧
    -Real.log (512 / 691) ≤ (299815199 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 1203)) (n := 12)
    (lo := (149907599 / 500000000)) (hi := (299815199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691 / 512) = 1/(512 / 691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (149907599 / 500000000) (299815199 / 1000000000) (Real.log (691 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (691 / 512) = -Real.log (512 / 691) := by
    rw [show ((691 / 512) : ℝ) = ((512 / 691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (86036427 / 200000000) ≤ -Real.log (333 / 512) ∧
    -Real.log (333 / 512) ≤ (53772767 / 125000000) := by
  have h := checkLog_sound (w := (179 / 845)) (n := 12)
    (lo := (86036427 / 200000000)) (hi := (53772767 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 333) = 1/(333 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-53772767 / 125000000) (-86036427 / 200000000) (Real.log (333 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (110986633 / 500000000) ≤ -Real.log (500000 / 624269) ∧
    -Real.log (500000 / 624269) ≤ (221973267 / 1000000000) := by
  have h := checkLog_sound (w := (124269 / 1124269)) (n := 12)
    (lo := (110986633 / 500000000)) (hi := (221973267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624269 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624269 / 500000) = 1/(500000 / 624269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (110986633 / 500000000) (221973267 / 1000000000) (Real.log (624269 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (624269 / 500000) = -Real.log (500000 / 624269) := by
    rw [show ((624269 / 500000) : ℝ) = ((500000 / 624269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (71433659 / 250000000) ≤ -Real.log (375731 / 500000) ∧
    -Real.log (375731 / 500000) ≤ (285734637 / 1000000000) := by
  have h := checkLog_sound (w := (124269 / 875731)) (n := 12)
    (lo := (71433659 / 250000000)) (hi := (285734637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375731) = 1/(375731 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-285734637 / 1000000000) (-71433659 / 250000000) (Real.log (375731 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (44462241 / 200000000) ≤ -Real.log (3125 / 3903) ∧
    -Real.log (3125 / 3903) ≤ (111155603 / 500000000) := by
  have h := checkLog_sound (w := (389 / 3514)) (n := 12)
    (lo := (44462241 / 200000000)) (hi := (111155603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3903 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3903 / 3125) = 1/(3125 / 3903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (44462241 / 200000000) (111155603 / 500000000) (Real.log (3903 / 3125)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3903 / 3125) = -Real.log (3125 / 3903) := by
    rw [show ((3903 / 3125) : ℝ) = ((3125 / 3903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (143148183 / 500000000) ≤ -Real.log (2347 / 3125) ∧
    -Real.log (2347 / 3125) ≤ (286296367 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 2736)) (n := 12)
    (lo := (143148183 / 500000000)) (hi := (286296367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2347) = 1/(2347 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-286296367 / 1000000000) (-143148183 / 500000000) (Real.log (2347 / 3125)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (41124667 / 250000000) ≤ -Real.log (500000 / 589401) ∧
    -Real.log (500000 / 589401) ≤ (164498669 / 1000000000) := by
  have h := checkLog_sound (w := (89401 / 1089401)) (n := 12)
    (lo := (41124667 / 250000000)) (hi := (164498669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589401 / 500000) = 1/(500000 / 589401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (41124667 / 250000000) (164498669 / 1000000000) (Real.log (589401 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (589401 / 500000) = -Real.log (500000 / 589401) := by
    rw [show ((589401 / 500000) : ℝ) = ((500000 / 589401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (196991029 / 1000000000) ≤ -Real.log (410599 / 500000) ∧
    -Real.log (410599 / 500000) ≤ (19699103 / 100000000) := by
  have h := checkLog_sound (w := (89401 / 910599)) (n := 12)
    (lo := (196991029 / 1000000000)) (hi := (19699103 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 410599) = 1/(410599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-19699103 / 100000000) (-196991029 / 1000000000) (Real.log (410599 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (164765853 / 1000000000) ≤ -Real.log (1000000 / 1179117) ∧
    -Real.log (1000000 / 1179117) ≤ (82382927 / 500000000) := by
  have h := checkLog_sound (w := (179117 / 2179117)) (n := 12)
    (lo := (164765853 / 1000000000)) (hi := (82382927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179117 / 1000000) = 1/(1000000 / 1179117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (164765853 / 1000000000) (82382927 / 500000000) (Real.log (1179117 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1179117 / 1000000) = -Real.log (1000000 / 1179117) := by
    rw [show ((1179117 / 1000000) : ℝ) = ((1000000 / 1179117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6167959 / 31250000) ≤ -Real.log (820883 / 1000000) ∧
    -Real.log (820883 / 1000000) ≤ (197374689 / 1000000000) := by
  have h := checkLog_sound (w := (179117 / 1820883)) (n := 12)
    (lo := (6167959 / 31250000)) (hi := (197374689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820883) = 1/(820883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-197374689 / 1000000000) (-6167959 / 31250000) (Real.log (820883 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (729997333 / 1000000000) ≤ -Real.log (500000000000 / 1037537537537) ∧
    -Real.log (500000000000 / 1037537537537) ≤ (145999467 / 200000000) := by
  have h := checkLog_sound (w := (37537537537 / 2037537537537)) (n := 12)
    (lo := (36850153 / 1000000000)) (hi := (18425077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1037537537537 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1037537537537 / 1000000000000) = 1/(500000000000 / 1037537537537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (729997333 / 1000000000) (145999467 / 200000000) (Real.log (1037537537537 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1037537537537 / 500000000000) = -Real.log (500000000000 / 1037537537537) := by
    rw [show ((1037537537537 / 500000000000) : ℝ) = ((500000000000 / 1037537537537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (731332699 / 1000000000) ≤ -Real.log (125000000000 / 259730988879) ∧
    -Real.log (125000000000 / 259730988879) ≤ (731332701 / 1000000000) := by
  have h := checkLog_sound (w := (9730988879 / 509730988879)) (n := 12)
    (lo := (38185519 / 1000000000)) (hi := (477319 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259730988879 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259730988879 / 250000000000) = 1/(125000000000 / 259730988879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (731332699 / 1000000000) (731332701 / 1000000000) (Real.log (259730988879 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (259730988879 / 125000000000) = -Real.log (125000000000 / 259730988879) := by
    rw [show ((259730988879 / 125000000000) : ℝ) = ((125000000000 / 259730988879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (507707903 / 1000000000) ≤ -Real.log (250000000000 / 415369639449) ∧
    -Real.log (250000000000 / 415369639449) ≤ (991617 / 1953125) := by
  have h := checkLog_sound (w := (165369639449 / 665369639449)) (n := 12)
    (lo := (507707903 / 1000000000)) (hi := (991617 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415369639449 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415369639449 / 250000000000) = 1/(250000000000 / 415369639449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (507707903 / 1000000000) (991617 / 1953125) (Real.log (415369639449 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (415369639449 / 250000000000) = -Real.log (250000000000 / 415369639449) := by
    rw [show ((415369639449 / 250000000000) : ℝ) = ((250000000000 / 415369639449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (508607571 / 1000000000) ≤ -Real.log (500000000000 / 831487004687) ∧
    -Real.log (500000000000 / 831487004687) ≤ (127151893 / 250000000) := by
  have h := checkLog_sound (w := (331487004687 / 1331487004687)) (n := 12)
    (lo := (508607571 / 1000000000)) (hi := (127151893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831487004687 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831487004687 / 500000000000) = 1/(500000000000 / 831487004687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (508607571 / 1000000000) (127151893 / 250000000) (Real.log (831487004687 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (831487004687 / 500000000000) = -Real.log (500000000000 / 831487004687) := by
    rw [show ((831487004687 / 500000000000) : ℝ) = ((500000000000 / 831487004687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (361489697 / 1000000000) ≤ -Real.log (500000000000 / 717733116739) ∧
    -Real.log (500000000000 / 717733116739) ≤ (180744849 / 500000000) := by
  have h := checkLog_sound (w := (217733116739 / 1217733116739)) (n := 12)
    (lo := (361489697 / 1000000000)) (hi := (180744849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717733116739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717733116739 / 500000000000) = 1/(500000000000 / 717733116739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (361489697 / 1000000000) (180744849 / 500000000) (Real.log (717733116739 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (717733116739 / 500000000000) = -Real.log (500000000000 / 717733116739) := by
    rw [show ((717733116739 / 500000000000) : ℝ) = ((500000000000 / 717733116739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (181070271 / 500000000) ≤ -Real.log (125000000000 / 179550100319) ∧
    -Real.log (125000000000 / 179550100319) ≤ (362140543 / 1000000000) := by
  have h := checkLog_sound (w := (54550100319 / 304550100319)) (n := 12)
    (lo := (181070271 / 500000000)) (hi := (362140543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179550100319 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179550100319 / 125000000000) = 1/(125000000000 / 179550100319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (181070271 / 500000000) (362140543 / 1000000000) (Real.log (179550100319 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (179550100319 / 125000000000) = -Real.log (125000000000 / 179550100319) := by
    rw [show ((179550100319 / 125000000000) : ℝ) = ((125000000000 / 179550100319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6521767 / 200000000) ≤ -Real.log (967917100311 / 1000000000000) ∧
    -Real.log (967917100311 / 1000000000000) ≤ (8152209 / 250000000) := by
  have h := checkLog_sound (w := (32082899689 / 1967917100311)) (n := 12)
    (lo := (6521767 / 200000000)) (hi := (8152209 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967917100311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967917100311) = 1/(967917100311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8152209 / 250000000) (-6521767 / 200000000) (Real.log (967917100311 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (812309 / 25000000) ≤ -Real.log (242007461199 / 250000000000) ∧
    -Real.log (242007461199 / 250000000000) ≤ (32492361 / 1000000000) := by
  have h := checkLog_sound (w := (7992538801 / 492007461199)) (n := 12)
    (lo := (812309 / 25000000)) (hi := (32492361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242007461199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242007461199) = 1/(242007461199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32492361 / 1000000000) (-812309 / 25000000) (Real.log (242007461199 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell170

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell171Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell171
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

theorem reflection_log_1_neg : (37585391 / 125000000) ≤ -Real.log (1280 / 1729) ∧
    -Real.log (1280 / 1729) ≤ (300683129 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 3009)) (n := 12)
    (lo := (37585391 / 125000000)) (hi := (300683129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1729 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1729 / 1280) = 1/(1280 / 1729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (37585391 / 125000000) (300683129 / 1000000000) (Real.log (1729 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1729 / 1280) = -Real.log (1280 / 1729) := by
    rw [show ((1729 / 1280) : ℝ) = ((1280 / 1729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (215992781 / 500000000) ≤ -Real.log (831 / 1280) ∧
    -Real.log (831 / 1280) ≤ (431985563 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 2111)) (n := 12)
    (lo := (215992781 / 500000000)) (hi := (431985563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 831) = 1/(831 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-431985563 / 1000000000) (-215992781 / 500000000) (Real.log (831 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (300249257 / 1000000000) ≤ -Real.log (5120 / 6913) ∧
    -Real.log (5120 / 6913) ≤ (150124629 / 500000000) := by
  have h := checkLog_sound (w := (1793 / 12033)) (n := 12)
    (lo := (300249257 / 1000000000)) (hi := (150124629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6913 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6913 / 5120) = 1/(5120 / 6913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (300249257 / 1000000000) (150124629 / 500000000) (Real.log (6913 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6913 / 5120) = -Real.log (5120 / 6913) := by
    rw [show ((6913 / 5120) : ℝ) = ((5120 / 6913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (215541721 / 500000000) ≤ -Real.log (3327 / 5120) ∧
    -Real.log (3327 / 5120) ≤ (431083443 / 1000000000) := by
  have h := checkLog_sound (w := (1793 / 8447)) (n := 12)
    (lo := (215541721 / 500000000)) (hi := (431083443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3327) = 1/(3327 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-431083443 / 1000000000) (-215541721 / 500000000) (Real.log (3327 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (222309603 / 1000000000) ≤ -Real.log (500000 / 624479) ∧
    -Real.log (500000 / 624479) ≤ (55577401 / 250000000) := by
  have h := checkLog_sound (w := (124479 / 1124479)) (n := 12)
    (lo := (222309603 / 1000000000)) (hi := (55577401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624479 / 500000) = 1/(500000 / 624479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (222309603 / 1000000000) (55577401 / 250000000) (Real.log (624479 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (624479 / 500000) = -Real.log (500000 / 624479) := by
    rw [show ((624479 / 500000) : ℝ) = ((500000 / 624479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (286293703 / 1000000000) ≤ -Real.log (375521 / 500000) ∧
    -Real.log (375521 / 500000) ≤ (35786713 / 125000000) := by
  have h := checkLog_sound (w := (124479 / 875521)) (n := 12)
    (lo := (286293703 / 1000000000)) (hi := (35786713 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375521) = 1/(375521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-35786713 / 125000000) (-286293703 / 1000000000) (Real.log (375521 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (222649029 / 1000000000) ≤ -Real.log (500000 / 624691) ∧
    -Real.log (500000 / 624691) ≤ (22264903 / 100000000) := by
  have h := checkLog_sound (w := (124691 / 1124691)) (n := 12)
    (lo := (222649029 / 1000000000)) (hi := (22264903 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624691 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624691 / 500000) = 1/(500000 / 624691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (222649029 / 1000000000) (22264903 / 100000000) (Real.log (624691 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (624691 / 500000) = -Real.log (500000 / 624691) := by
    rw [show ((624691 / 500000) : ℝ) = ((500000 / 624691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (286858411 / 1000000000) ≤ -Real.log (375309 / 500000) ∧
    -Real.log (375309 / 500000) ≤ (71714603 / 250000000) := by
  have h := checkLog_sound (w := (124691 / 875309)) (n := 12)
    (lo := (286858411 / 1000000000)) (hi := (71714603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375309) = 1/(375309 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-71714603 / 250000000) (-286858411 / 1000000000) (Real.log (375309 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32953001 / 200000000) ≤ -Real.log (250000 / 294779) ∧
    -Real.log (250000 / 294779) ≤ (82382503 / 500000000) := by
  have h := checkLog_sound (w := (44779 / 544779)) (n := 12)
    (lo := (32953001 / 200000000)) (hi := (82382503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294779 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294779 / 250000) = 1/(250000 / 294779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32953001 / 200000000) (82382503 / 500000000) (Real.log (294779 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (294779 / 250000) = -Real.log (250000 / 294779) := by
    rw [show ((294779 / 250000) : ℝ) = ((250000 / 294779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (19737347 / 100000000) ≤ -Real.log (205221 / 250000) ∧
    -Real.log (205221 / 250000) ≤ (197373471 / 1000000000) := by
  have h := checkLog_sound (w := (44779 / 455221)) (n := 12)
    (lo := (19737347 / 100000000)) (hi := (197373471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 205221) = 1/(205221 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-197373471 / 1000000000) (-19737347 / 100000000) (Real.log (205221 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (82516059 / 500000000) ≤ -Real.log (1000000 / 1179431) ∧
    -Real.log (1000000 / 1179431) ≤ (165032119 / 1000000000) := by
  have h := checkLog_sound (w := (179431 / 2179431)) (n := 12)
    (lo := (82516059 / 500000000)) (hi := (165032119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179431 / 1000000) = 1/(1000000 / 1179431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (82516059 / 500000000) (165032119 / 1000000000) (Real.log (1179431 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1179431 / 1000000) = -Real.log (1000000 / 1179431) := by
    rw [show ((1179431 / 1000000) : ℝ) = ((1000000 / 1179431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (49439319 / 250000000) ≤ -Real.log (820569 / 1000000) ∧
    -Real.log (820569 / 1000000) ≤ (197757277 / 1000000000) := by
  have h := checkLog_sound (w := (179431 / 1820569)) (n := 12)
    (lo := (49439319 / 250000000)) (hi := (197757277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820569) = 1/(820569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-197757277 / 1000000000) (-49439319 / 250000000) (Real.log (820569 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (731332699 / 1000000000) ≤ -Real.log (100000000000 / 207784791103) ∧
    -Real.log (100000000000 / 207784791103) ≤ (731332701 / 1000000000) := by
  have h := checkLog_sound (w := (7784791103 / 407784791103)) (n := 12)
    (lo := (38185519 / 1000000000)) (hi := (477319 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207784791103 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(207784791103 / 200000000000) = 1/(100000000000 / 207784791103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (731332699 / 1000000000) (731332701 / 1000000000) (Real.log (207784791103 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (207784791103 / 100000000000) = -Real.log (100000000000 / 207784791103) := by
    rw [show ((207784791103 / 100000000000) : ℝ) = ((100000000000 / 207784791103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (73266869 / 100000000) ≤ -Real.log (500000000000 / 1040312876053) ∧
    -Real.log (500000000000 / 1040312876053) ≤ (183167173 / 250000000) := by
  have h := checkLog_sound (w := (40312876053 / 2040312876053)) (n := 12)
    (lo := (3952151 / 100000000)) (hi := (39521511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1040312876053 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1040312876053 / 1000000000000) = 1/(500000000000 / 1040312876053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (73266869 / 100000000) (183167173 / 250000000) (Real.log (1040312876053 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1040312876053 / 500000000000) = -Real.log (500000000000 / 1040312876053) := by
    rw [show ((1040312876053 / 500000000000) : ℝ) = ((500000000000 / 1040312876053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (508603307 / 1000000000) ≤ -Real.log (25000000000 / 41574172949) ∧
    -Real.log (25000000000 / 41574172949) ≤ (127150827 / 250000000) := by
  have h := checkLog_sound (w := (16574172949 / 66574172949)) (n := 12)
    (lo := (508603307 / 1000000000)) (hi := (127150827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41574172949 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41574172949 / 25000000000) = 1/(25000000000 / 41574172949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (508603307 / 1000000000) (127150827 / 250000000) (Real.log (41574172949 / 25000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (41574172949 / 25000000000) = -Real.log (25000000000 / 41574172949) := by
    rw [show ((41574172949 / 25000000000) : ℝ) = ((25000000000 / 41574172949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (6368843 / 12500000) ≤ -Real.log (500000000000 / 832235571223) ∧
    -Real.log (500000000000 / 832235571223) ≤ (509507441 / 1000000000) := by
  have h := checkLog_sound (w := (332235571223 / 1332235571223)) (n := 12)
    (lo := (6368843 / 12500000)) (hi := (509507441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832235571223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(832235571223 / 500000000000) = 1/(500000000000 / 832235571223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (6368843 / 12500000) (509507441 / 1000000000) (Real.log (832235571223 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (832235571223 / 500000000000) = -Real.log (500000000000 / 832235571223) := by
    rw [show ((832235571223 / 500000000000) : ℝ) = ((500000000000 / 832235571223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14485539 / 40000000) ≤ -Real.log (31250000000 / 44887432329) ∧
    -Real.log (31250000000 / 44887432329) ≤ (90534619 / 250000000) := by
  have h := checkLog_sound (w := (13637432329 / 76137432329)) (n := 12)
    (lo := (14485539 / 40000000)) (hi := (90534619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44887432329 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44887432329 / 31250000000) = 1/(31250000000 / 44887432329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14485539 / 40000000) (90534619 / 250000000) (Real.log (44887432329 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (44887432329 / 31250000000) = -Real.log (31250000000 / 44887432329) := by
    rw [show ((44887432329 / 31250000000) : ℝ) = ((31250000000 / 44887432329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (72557879 / 200000000) ≤ -Real.log (20000000000 / 28746662377) ∧
    -Real.log (20000000000 / 28746662377) ≤ (90697349 / 250000000) := by
  have h := checkLog_sound (w := (8746662377 / 48746662377)) (n := 12)
    (lo := (72557879 / 200000000)) (hi := (90697349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28746662377 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28746662377 / 20000000000) = 1/(20000000000 / 28746662377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (72557879 / 200000000) (90697349 / 250000000) (Real.log (28746662377 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28746662377 / 20000000000) = -Real.log (20000000000 / 28746662377) := by
    rw [show ((28746662377 / 20000000000) : ℝ) = ((20000000000 / 28746662377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16362579 / 500000000) ≤ -Real.log (967804516239 / 1000000000000) ∧
    -Real.log (967804516239 / 1000000000000) ≤ (32725159 / 1000000000) := by
  have h := checkLog_sound (w := (32195483761 / 1967804516239)) (n := 12)
    (lo := (16362579 / 500000000)) (hi := (32725159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967804516239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967804516239) = 1/(967804516239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-32725159 / 1000000000) (-16362579 / 500000000) (Real.log (967804516239 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6521693 / 200000000) ≤ -Real.log (60494841159 / 62500000000) ∧
    -Real.log (60494841159 / 62500000000) ≤ (16304233 / 500000000) := by
  have h := checkLog_sound (w := (2005158841 / 122994841159)) (n := 12)
    (lo := (6521693 / 200000000)) (hi := (16304233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60494841159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60494841159) = 1/(60494841159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-16304233 / 500000000) (-6521693 / 200000000) (Real.log (60494841159 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell171

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell172Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell172
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

theorem reflection_log_1_neg : (301116811 / 1000000000) ≤ -Real.log (5120 / 6919) ∧
    -Real.log (5120 / 6919) ≤ (75279203 / 250000000) := by
  have h := checkLog_sound (w := (1799 / 12039)) (n := 12)
    (lo := (301116811 / 1000000000)) (hi := (75279203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6919 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6919 / 5120) = 1/(5120 / 6919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (301116811 / 1000000000) (75279203 / 250000000) (Real.log (6919 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6919 / 5120) = -Real.log (5120 / 6919) := by
    rw [show ((6919 / 5120) : ℝ) = ((5120 / 6919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (27055531 / 62500000) ≤ -Real.log (3321 / 5120) ∧
    -Real.log (3321 / 5120) ≤ (432888497 / 1000000000) := by
  have h := checkLog_sound (w := (1799 / 8441)) (n := 12)
    (lo := (27055531 / 62500000)) (hi := (432888497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3321) = 1/(3321 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-432888497 / 1000000000) (-27055531 / 62500000) (Real.log (3321 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (37585391 / 125000000) ≤ -Real.log (1280 / 1729) ∧
    -Real.log (1280 / 1729) ≤ (300683129 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 3009)) (n := 12)
    (lo := (37585391 / 125000000)) (hi := (300683129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1729 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1729 / 1280) = 1/(1280 / 1729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (37585391 / 125000000) (300683129 / 1000000000) (Real.log (1729 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1729 / 1280) = -Real.log (1280 / 1729) := by
    rw [show ((1729 / 1280) : ℝ) = ((1280 / 1729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (215992781 / 500000000) ≤ -Real.log (831 / 1280) ∧
    -Real.log (831 / 1280) ≤ (431985563 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 2111)) (n := 12)
    (lo := (215992781 / 500000000)) (hi := (431985563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 831) = 1/(831 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-431985563 / 1000000000) (-215992781 / 500000000) (Real.log (831 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (55661857 / 250000000) ≤ -Real.log (50000 / 62469) ∧
    -Real.log (50000 / 62469) ≤ (222647429 / 1000000000) := by
  have h := checkLog_sound (w := (12469 / 112469)) (n := 12)
    (lo := (55661857 / 250000000)) (hi := (222647429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62469 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62469 / 50000) = 1/(50000 / 62469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (55661857 / 250000000) (222647429 / 1000000000) (Real.log (62469 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (62469 / 50000) = -Real.log (50000 / 62469) := by
    rw [show ((62469 / 50000) : ℝ) = ((50000 / 62469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (286855747 / 1000000000) ≤ -Real.log (37531 / 50000) ∧
    -Real.log (37531 / 50000) ≤ (71713937 / 250000000) := by
  have h := checkLog_sound (w := (12469 / 87531)) (n := 12)
    (lo := (286855747 / 1000000000)) (hi := (71713937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37531) = 1/(37531 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71713937 / 250000000) (-286855747 / 1000000000) (Real.log (37531 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (111492969 / 500000000) ≤ -Real.log (1000000 / 1249803) ∧
    -Real.log (1000000 / 1249803) ≤ (222985939 / 1000000000) := by
  have h := checkLog_sound (w := (249803 / 2249803)) (n := 12)
    (lo := (111492969 / 500000000)) (hi := (222985939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249803 / 1000000) = 1/(1000000 / 1249803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (111492969 / 500000000) (222985939 / 1000000000) (Real.log (1249803 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1249803 / 1000000) = -Real.log (1000000 / 1249803) := by
    rw [show ((1249803 / 1000000) : ℝ) = ((1000000 / 1249803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3592743 / 12500000) ≤ -Real.log (750197 / 1000000) ∧
    -Real.log (750197 / 1000000) ≤ (287419441 / 1000000000) := by
  have h := checkLog_sound (w := (249803 / 1750197)) (n := 12)
    (lo := (3592743 / 12500000)) (hi := (287419441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750197) = 1/(750197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-287419441 / 1000000000) (-3592743 / 12500000) (Real.log (750197 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16503127 / 100000000) ≤ -Real.log (100000 / 117943) ∧
    -Real.log (100000 / 117943) ≤ (165031271 / 1000000000) := by
  have h := checkLog_sound (w := (17943 / 217943)) (n := 12)
    (lo := (16503127 / 100000000)) (hi := (165031271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117943 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117943 / 100000) = 1/(100000 / 117943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16503127 / 100000000) (165031271 / 1000000000) (Real.log (117943 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (117943 / 100000) = -Real.log (100000 / 117943) := by
    rw [show ((117943 / 100000) : ℝ) = ((100000 / 117943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (98878029 / 500000000) ≤ -Real.log (82057 / 100000) ∧
    -Real.log (82057 / 100000) ≤ (197756059 / 1000000000) := by
  have h := checkLog_sound (w := (17943 / 182057)) (n := 12)
    (lo := (98878029 / 500000000)) (hi := (197756059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82057) = 1/(82057 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-197756059 / 1000000000) (-98878029 / 500000000) (Real.log (82057 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (165298313 / 1000000000) ≤ -Real.log (200000 / 235949) ∧
    -Real.log (200000 / 235949) ≤ (82649157 / 500000000) := by
  have h := checkLog_sound (w := (35949 / 435949)) (n := 12)
    (lo := (165298313 / 1000000000)) (hi := (82649157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235949 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235949 / 200000) = 1/(200000 / 235949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (165298313 / 1000000000) (82649157 / 500000000) (Real.log (235949 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (235949 / 200000) = -Real.log (200000 / 235949) := by
    rw [show ((235949 / 200000) : ℝ) = ((200000 / 235949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (198140011 / 1000000000) ≤ -Real.log (164051 / 200000) ∧
    -Real.log (164051 / 200000) ≤ (49535003 / 250000000) := by
  have h := checkLog_sound (w := (35949 / 364051)) (n := 12)
    (lo := (198140011 / 1000000000)) (hi := (49535003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 164051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 164051) = 1/(164051 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-49535003 / 250000000) (-198140011 / 1000000000) (Real.log (164051 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (73266869 / 100000000) ≤ -Real.log (125000000000 / 260078219013) ∧
    -Real.log (125000000000 / 260078219013) ≤ (183167173 / 250000000) := by
  have h := checkLog_sound (w := (10078219013 / 510078219013)) (n := 12)
    (lo := (3952151 / 100000000)) (hi := (39521511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((260078219013 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(260078219013 / 250000000000) = 1/(125000000000 / 260078219013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (73266869 / 100000000) (183167173 / 250000000) (Real.log (260078219013 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (260078219013 / 125000000000) = -Real.log (125000000000 / 260078219013) := by
    rw [show ((260078219013 / 125000000000) : ℝ) = ((125000000000 / 260078219013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (734005307 / 1000000000) ≤ -Real.log (125000000000 / 260426076483) ∧
    -Real.log (125000000000 / 260426076483) ≤ (734005309 / 1000000000) := by
  have h := checkLog_sound (w := (10426076483 / 510426076483)) (n := 12)
    (lo := (40858127 / 1000000000)) (hi := (2553633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((260426076483 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(260426076483 / 250000000000) = 1/(125000000000 / 260426076483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (734005307 / 1000000000) (734005309 / 1000000000) (Real.log (260426076483 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (260426076483 / 125000000000) = -Real.log (125000000000 / 260426076483) := by
    rw [show ((260426076483 / 125000000000) : ℝ) = ((125000000000 / 260426076483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (20380127 / 40000000) ≤ -Real.log (62500000000 / 104029002691) ∧
    -Real.log (62500000000 / 104029002691) ≤ (63687897 / 125000000) := by
  have h := checkLog_sound (w := (41529002691 / 166529002691)) (n := 12)
    (lo := (20380127 / 40000000)) (hi := (63687897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104029002691 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104029002691 / 62500000000) = 1/(62500000000 / 104029002691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (20380127 / 40000000) (63687897 / 125000000) (Real.log (104029002691 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (104029002691 / 62500000000) = -Real.log (62500000000 / 104029002691) := by
    rw [show ((104029002691 / 62500000000) : ℝ) = ((62500000000 / 104029002691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (510405379 / 1000000000) ≤ -Real.log (500000000000 / 832983203079) ∧
    -Real.log (500000000000 / 832983203079) ≤ (25520269 / 50000000) := by
  have h := checkLog_sound (w := (332983203079 / 1332983203079)) (n := 12)
    (lo := (510405379 / 1000000000)) (hi := (25520269 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832983203079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(832983203079 / 500000000000) = 1/(500000000000 / 832983203079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (510405379 / 1000000000) (25520269 / 50000000) (Real.log (832983203079 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (832983203079 / 500000000000) = -Real.log (500000000000 / 832983203079) := by
    rw [show ((832983203079 / 500000000000) : ℝ) = ((500000000000 / 832983203079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (362787329 / 1000000000) ≤ -Real.log (500000000000 / 718665074277) ∧
    -Real.log (500000000000 / 718665074277) ≤ (36278733 / 100000000) := by
  have h := checkLog_sound (w := (218665074277 / 1218665074277)) (n := 12)
    (lo := (362787329 / 1000000000)) (hi := (36278733 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718665074277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718665074277 / 500000000000) = 1/(500000000000 / 718665074277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (362787329 / 1000000000) (36278733 / 100000000) (Real.log (718665074277 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (718665074277 / 500000000000) = -Real.log (500000000000 / 718665074277) := by
    rw [show ((718665074277 / 500000000000) : ℝ) = ((500000000000 / 718665074277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (90859581 / 250000000) ≤ -Real.log (500000000000 / 719133074471) ∧
    -Real.log (500000000000 / 719133074471) ≤ (14537533 / 40000000) := by
  have h := checkLog_sound (w := (219133074471 / 1219133074471)) (n := 12)
    (lo := (90859581 / 250000000)) (hi := (14537533 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719133074471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719133074471 / 500000000000) = 1/(500000000000 / 719133074471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (90859581 / 250000000) (14537533 / 40000000) (Real.log (719133074471 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (719133074471 / 500000000000) = -Real.log (500000000000 / 719133074471) := by
    rw [show ((719133074471 / 500000000000) : ℝ) = ((500000000000 / 719133074471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16420849 / 500000000) ≤ -Real.log (38707669399 / 40000000000) ∧
    -Real.log (38707669399 / 40000000000) ≤ (32841699 / 1000000000) := by
  have h := checkLog_sound (w := (1292330601 / 78707669399)) (n := 12)
    (lo := (16420849 / 500000000)) (hi := (32841699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38707669399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38707669399) = 1/(38707669399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-32841699 / 1000000000) (-16420849 / 500000000) (Real.log (38707669399 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (32724787 / 1000000000) ≤ -Real.log (9678048751 / 10000000000) ∧
    -Real.log (9678048751 / 10000000000) ≤ (8181197 / 250000000) := by
  have h := checkLog_sound (w := (321951249 / 19678048751)) (n := 12)
    (lo := (32724787 / 1000000000)) (hi := (8181197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9678048751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9678048751) = 1/(9678048751 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8181197 / 250000000) (-32724787 / 1000000000) (Real.log (9678048751 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell172

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell173Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell173
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

theorem reflection_log_1_neg : (150775153 / 500000000) ≤ -Real.log (2560 / 3461) ∧
    -Real.log (2560 / 3461) ≤ (301550307 / 1000000000) := by
  have h := checkLog_sound (w := (901 / 6021)) (n := 12)
    (lo := (150775153 / 500000000)) (hi := (301550307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3461 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3461 / 2560) = 1/(2560 / 3461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (150775153 / 500000000) (301550307 / 1000000000) (Real.log (3461 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3461 / 2560) = -Real.log (2560 / 3461) := by
    rw [show ((3461 / 2560) : ℝ) = ((2560 / 3461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (433792247 / 1000000000) ≤ -Real.log (1659 / 2560) ∧
    -Real.log (1659 / 2560) ≤ (54224031 / 125000000) := by
  have h := checkLog_sound (w := (901 / 4219)) (n := 12)
    (lo := (433792247 / 1000000000)) (hi := (54224031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1659) = 1/(1659 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-54224031 / 125000000) (-433792247 / 1000000000) (Real.log (1659 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (301116811 / 1000000000) ≤ -Real.log (5120 / 6919) ∧
    -Real.log (5120 / 6919) ≤ (75279203 / 250000000) := by
  have h := checkLog_sound (w := (1799 / 12039)) (n := 12)
    (lo := (301116811 / 1000000000)) (hi := (75279203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6919 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6919 / 5120) = 1/(5120 / 6919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (301116811 / 1000000000) (75279203 / 250000000) (Real.log (6919 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6919 / 5120) = -Real.log (5120 / 6919) := by
    rw [show ((6919 / 5120) : ℝ) = ((5120 / 6919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (27055531 / 62500000) ≤ -Real.log (3321 / 5120) ∧
    -Real.log (3321 / 5120) ≤ (432888497 / 1000000000) := by
  have h := checkLog_sound (w := (1799 / 8441)) (n := 12)
    (lo := (27055531 / 62500000)) (hi := (432888497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3321) = 1/(3321 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-432888497 / 1000000000) (-27055531 / 62500000) (Real.log (3321 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (111492569 / 500000000) ≤ -Real.log (500000 / 624901) ∧
    -Real.log (500000 / 624901) ≤ (222985139 / 1000000000) := by
  have h := checkLog_sound (w := (124901 / 1124901)) (n := 12)
    (lo := (111492569 / 500000000)) (hi := (222985139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624901 / 500000) = 1/(500000 / 624901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (111492569 / 500000000) (222985139 / 1000000000) (Real.log (624901 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (624901 / 500000) = -Real.log (500000 / 624901) := by
    rw [show ((624901 / 500000) : ℝ) = ((500000 / 624901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (287418107 / 1000000000) ≤ -Real.log (375099 / 500000) ∧
    -Real.log (375099 / 500000) ≤ (71854527 / 250000000) := by
  have h := checkLog_sound (w := (124901 / 875099)) (n := 12)
    (lo := (287418107 / 1000000000)) (hi := (71854527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375099) = 1/(375099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71854527 / 250000000) (-287418107 / 1000000000) (Real.log (375099 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (44664547 / 200000000) ≤ -Real.log (62500 / 78139) ∧
    -Real.log (62500 / 78139) ≤ (13957671 / 62500000) := by
  have h := checkLog_sound (w := (15639 / 140639)) (n := 12)
    (lo := (44664547 / 200000000)) (hi := (13957671 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78139 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78139 / 62500) = 1/(62500 / 78139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (44664547 / 200000000) (13957671 / 62500000) (Real.log (78139 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (78139 / 62500) = -Real.log (62500 / 78139) := by
    rw [show ((78139 / 62500) : ℝ) = ((62500 / 78139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (287980783 / 1000000000) ≤ -Real.log (46861 / 62500) ∧
    -Real.log (46861 / 62500) ≤ (17998799 / 62500000) := by
  have h := checkLog_sound (w := (15639 / 109361)) (n := 12)
    (lo := (287980783 / 1000000000)) (hi := (17998799 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46861) = 1/(46861 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-17998799 / 62500000) (-287980783 / 1000000000) (Real.log (46861 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (33059493 / 200000000) ≤ -Real.log (31250 / 36867) ∧
    -Real.log (31250 / 36867) ≤ (82648733 / 500000000) := by
  have h := checkLog_sound (w := (5617 / 68117)) (n := 12)
    (lo := (33059493 / 200000000)) (hi := (82648733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36867 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36867 / 31250) = 1/(31250 / 36867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (33059493 / 200000000) (82648733 / 500000000) (Real.log (36867 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (36867 / 31250) = -Real.log (31250 / 36867) := by
    rw [show ((36867 / 31250) : ℝ) = ((31250 / 36867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (24767349 / 125000000) ≤ -Real.log (25633 / 31250) ∧
    -Real.log (25633 / 31250) ≤ (198138793 / 1000000000) := by
  have h := checkLog_sound (w := (5617 / 56883)) (n := 12)
    (lo := (24767349 / 125000000)) (hi := (198138793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25633) = 1/(25633 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-198138793 / 1000000000) (-24767349 / 125000000) (Real.log (25633 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (165563589 / 1000000000) ≤ -Real.log (500000 / 590029) ∧
    -Real.log (500000 / 590029) ≤ (16556359 / 100000000) := by
  have h := checkLog_sound (w := (90029 / 1090029)) (n := 12)
    (lo := (165563589 / 1000000000)) (hi := (16556359 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590029 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590029 / 500000) = 1/(500000 / 590029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (165563589 / 1000000000) (16556359 / 100000000) (Real.log (590029 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (590029 / 500000) = -Real.log (500000 / 590029) := by
    rw [show ((590029 / 500000) : ℝ) = ((500000 / 590029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (24815209 / 125000000) ≤ -Real.log (409971 / 500000) ∧
    -Real.log (409971 / 500000) ≤ (198521673 / 1000000000) := by
  have h := checkLog_sound (w := (90029 / 909971)) (n := 12)
    (lo := (24815209 / 125000000)) (hi := (198521673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409971) = 1/(409971 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-198521673 / 1000000000) (-24815209 / 125000000) (Real.log (409971 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (734005307 / 1000000000) ≤ -Real.log (500000000000 / 1041704305931) ∧
    -Real.log (500000000000 / 1041704305931) ≤ (734005309 / 1000000000) := by
  have h := checkLog_sound (w := (41704305931 / 2041704305931)) (n := 12)
    (lo := (40858127 / 1000000000)) (hi := (2553633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1041704305931 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1041704305931 / 1000000000000) = 1/(500000000000 / 1041704305931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (734005307 / 1000000000) (734005309 / 1000000000) (Real.log (1041704305931 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1041704305931 / 500000000000) = -Real.log (500000000000 / 1041704305931) := by
    rw [show ((1041704305931 / 500000000000) : ℝ) = ((500000000000 / 1041704305931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (91917819 / 125000000) ≤ -Real.log (12500000000 / 26077456299) ∧
    -Real.log (12500000000 / 26077456299) ≤ (367671277 / 500000000) := by
  have h := checkLog_sound (w := (1077456299 / 51077456299)) (n := 12)
    (lo := (10548843 / 250000000)) (hi := (42195373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26077456299 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(26077456299 / 25000000000) = 1/(12500000000 / 26077456299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (91917819 / 125000000) (367671277 / 500000000) (Real.log (26077456299 / 12500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (26077456299 / 12500000000) = -Real.log (12500000000 / 26077456299) := by
    rw [show ((26077456299 / 12500000000) : ℝ) = ((12500000000 / 26077456299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (255201623 / 500000000) ≤ -Real.log (125000000000 / 208245356559) ∧
    -Real.log (125000000000 / 208245356559) ≤ (510403247 / 1000000000) := by
  have h := checkLog_sound (w := (83245356559 / 333245356559)) (n := 12)
    (lo := (255201623 / 500000000)) (hi := (510403247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208245356559 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(208245356559 / 125000000000) = 1/(125000000000 / 208245356559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (255201623 / 500000000) (510403247 / 1000000000) (Real.log (208245356559 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (208245356559 / 125000000000) = -Real.log (125000000000 / 208245356559) := by
    rw [show ((208245356559 / 125000000000) : ℝ) = ((125000000000 / 208245356559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (255651759 / 500000000) ≤ -Real.log (500000000000 / 833731674527) ∧
    -Real.log (500000000000 / 833731674527) ≤ (511303519 / 1000000000) := by
  have h := checkLog_sound (w := (333731674527 / 1333731674527)) (n := 12)
    (lo := (255651759 / 500000000)) (hi := (511303519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833731674527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833731674527 / 500000000000) = 1/(500000000000 / 833731674527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (255651759 / 500000000) (511303519 / 1000000000) (Real.log (833731674527 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (833731674527 / 500000000000) = -Real.log (500000000000 / 833731674527) := by
    rw [show ((833731674527 / 500000000000) : ℝ) = ((500000000000 / 833731674527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (181718129 / 500000000) ≤ -Real.log (500000000000 / 719131588187) ∧
    -Real.log (500000000000 / 719131588187) ≤ (363436259 / 1000000000) := by
  have h := checkLog_sound (w := (219131588187 / 1219131588187)) (n := 12)
    (lo := (181718129 / 500000000)) (hi := (363436259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719131588187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719131588187 / 500000000000) = 1/(500000000000 / 719131588187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (181718129 / 500000000) (363436259 / 1000000000) (Real.log (719131588187 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (719131588187 / 500000000000) = -Real.log (500000000000 / 719131588187) := by
    rw [show ((719131588187 / 500000000000) : ℝ) = ((500000000000 / 719131588187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (182042631 / 500000000) ≤ -Real.log (125000000000 / 179899614851) ∧
    -Real.log (125000000000 / 179899614851) ≤ (364085263 / 1000000000) := by
  have h := checkLog_sound (w := (54899614851 / 304899614851)) (n := 12)
    (lo := (182042631 / 500000000)) (hi := (364085263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179899614851 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179899614851 / 125000000000) = 1/(125000000000 / 179899614851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (182042631 / 500000000) (364085263 / 1000000000) (Real.log (179899614851 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (179899614851 / 125000000000) = -Real.log (125000000000 / 179899614851) := by
    rw [show ((179899614851 / 125000000000) : ℝ) = ((125000000000 / 179899614851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (32958083 / 1000000000) ≤ -Real.log (241894779159 / 250000000000) ∧
    -Real.log (241894779159 / 250000000000) ≤ (8239521 / 250000000) := by
  have h := checkLog_sound (w := (8105220841 / 491894779159)) (n := 12)
    (lo := (32958083 / 1000000000)) (hi := (8239521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241894779159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241894779159) = 1/(241894779159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8239521 / 250000000) (-32958083 / 1000000000) (Real.log (241894779159 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16420663 / 500000000) ≤ -Real.log (945011811 / 976562500) ∧
    -Real.log (945011811 / 976562500) ≤ (32841327 / 1000000000) := by
  have h := checkLog_sound (w := (31550689 / 1921574311)) (n := 12)
    (lo := (16420663 / 500000000)) (hi := (32841327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 945011811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 945011811) = 1/(945011811 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32841327 / 1000000000) (-16420663 / 500000000) (Real.log (945011811 / 976562500)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell173

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell174Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell174
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

theorem reflection_log_1_neg : (301983613 / 1000000000) ≤ -Real.log (1024 / 1385) ∧
    -Real.log (1024 / 1385) ≤ (150991807 / 500000000) := by
  have h := checkLog_sound (w := (361 / 2409)) (n := 12)
    (lo := (301983613 / 1000000000)) (hi := (150991807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1385 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1385 / 1024) = 1/(1024 / 1385) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (301983613 / 1000000000) (150991807 / 500000000) (Real.log (1385 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1385 / 1024) = -Real.log (1024 / 1385) := by
    rw [show ((1385 / 1024) : ℝ) = ((1024 / 1385) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (86939363 / 200000000) ≤ -Real.log (663 / 1024) ∧
    -Real.log (663 / 1024) ≤ (27168551 / 62500000) := by
  have h := checkLog_sound (w := (361 / 1687)) (n := 12)
    (lo := (86939363 / 200000000)) (hi := (27168551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 663) = 1/(663 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-27168551 / 62500000) (-86939363 / 200000000) (Real.log (663 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (150775153 / 500000000) ≤ -Real.log (2560 / 3461) ∧
    -Real.log (2560 / 3461) ≤ (301550307 / 1000000000) := by
  have h := checkLog_sound (w := (901 / 6021)) (n := 12)
    (lo := (150775153 / 500000000)) (hi := (301550307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3461 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3461 / 2560) = 1/(2560 / 3461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (150775153 / 500000000) (301550307 / 1000000000) (Real.log (3461 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3461 / 2560) = -Real.log (2560 / 3461) := by
    rw [show ((3461 / 2560) : ℝ) = ((2560 / 3461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (433792247 / 1000000000) ≤ -Real.log (1659 / 2560) ∧
    -Real.log (1659 / 2560) ≤ (54224031 / 125000000) := by
  have h := checkLog_sound (w := (901 / 4219)) (n := 12)
    (lo := (433792247 / 1000000000)) (hi := (54224031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1659) = 1/(1659 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-54224031 / 125000000) (-433792247 / 1000000000) (Real.log (1659 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (44664387 / 200000000) ≤ -Real.log (1000000 / 1250223) ∧
    -Real.log (1000000 / 1250223) ≤ (13957621 / 62500000) := by
  have h := checkLog_sound (w := (250223 / 2250223)) (n := 12)
    (lo := (44664387 / 200000000)) (hi := (13957621 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250223 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250223 / 1000000) = 1/(1000000 / 1250223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (44664387 / 200000000) (13957621 / 62500000) (Real.log (1250223 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1250223 / 1000000) = -Real.log (1000000 / 1250223) := by
    rw [show ((1250223 / 1000000) : ℝ) = ((1000000 / 1250223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (287979449 / 1000000000) ≤ -Real.log (749777 / 1000000) ∧
    -Real.log (749777 / 1000000) ≤ (5759589 / 20000000) := by
  have h := checkLog_sound (w := (250223 / 1749777)) (n := 12)
    (lo := (287979449 / 1000000000)) (hi := (5759589 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 749777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 749777) = 1/(749777 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5759589 / 20000000) (-287979449 / 1000000000) (Real.log (749777 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (111829709 / 500000000) ≤ -Real.log (200000 / 250129) ∧
    -Real.log (200000 / 250129) ≤ (223659419 / 1000000000) := by
  have h := checkLog_sound (w := (50129 / 450129)) (n := 12)
    (lo := (111829709 / 500000000)) (hi := (223659419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250129 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250129 / 200000) = 1/(200000 / 250129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (111829709 / 500000000) (223659419 / 1000000000) (Real.log (250129 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (250129 / 200000) = -Real.log (200000 / 250129) := by
    rw [show ((250129 / 200000) : ℝ) = ((200000 / 250129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (144271221 / 500000000) ≤ -Real.log (149871 / 200000) ∧
    -Real.log (149871 / 200000) ≤ (288542443 / 1000000000) := by
  have h := checkLog_sound (w := (50129 / 349871)) (n := 12)
    (lo := (144271221 / 500000000)) (hi := (288542443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 149871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 149871) = 1/(149871 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-288542443 / 1000000000) (-144271221 / 500000000) (Real.log (149871 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (82781371 / 500000000) ≤ -Real.log (1000000 / 1180057) ∧
    -Real.log (1000000 / 1180057) ≤ (165562743 / 1000000000) := by
  have h := checkLog_sound (w := (180057 / 2180057)) (n := 12)
    (lo := (82781371 / 500000000)) (hi := (165562743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180057 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1180057 / 1000000) = 1/(1000000 / 1180057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (82781371 / 500000000) (165562743 / 1000000000) (Real.log (1180057 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1180057 / 1000000) = -Real.log (1000000 / 1180057) := by
    rw [show ((1180057 / 1000000) : ℝ) = ((1000000 / 1180057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (198520453 / 1000000000) ≤ -Real.log (819943 / 1000000) ∧
    -Real.log (819943 / 1000000) ≤ (99260227 / 500000000) := by
  have h := checkLog_sound (w := (180057 / 1819943)) (n := 12)
    (lo := (198520453 / 1000000000)) (hi := (99260227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 819943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 819943) = 1/(819943 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-99260227 / 500000000) (-198520453 / 1000000000) (Real.log (819943 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (165829643 / 1000000000) ≤ -Real.log (250000 / 295093) ∧
    -Real.log (250000 / 295093) ≤ (41457411 / 250000000) := by
  have h := checkLog_sound (w := (45093 / 545093)) (n := 12)
    (lo := (165829643 / 1000000000)) (hi := (41457411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295093 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295093 / 250000) = 1/(250000 / 295093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (165829643 / 1000000000) (41457411 / 250000000) (Real.log (295093 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (295093 / 250000) = -Real.log (250000 / 295093) := by
    rw [show ((295093 / 250000) : ℝ) = ((250000 / 295093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1989047 / 10000000) ≤ -Real.log (204907 / 250000) ∧
    -Real.log (204907 / 250000) ≤ (198904701 / 1000000000) := by
  have h := checkLog_sound (w := (45093 / 454907)) (n := 12)
    (lo := (1989047 / 10000000)) (hi := (198904701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204907) = 1/(204907 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-198904701 / 1000000000) (-1989047 / 10000000) (Real.log (204907 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (91917819 / 125000000) ≤ -Real.log (500000000000 / 1043098251959) ∧
    -Real.log (500000000000 / 1043098251959) ≤ (367671277 / 500000000) := by
  have h := checkLog_sound (w := (43098251959 / 2043098251959)) (n := 12)
    (lo := (10548843 / 250000000)) (hi := (42195373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1043098251959 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1043098251959 / 1000000000000) = 1/(500000000000 / 1043098251959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (91917819 / 125000000) (367671277 / 500000000) (Real.log (1043098251959 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1043098251959 / 500000000000) = -Real.log (500000000000 / 1043098251959) := by
    rw [show ((1043098251959 / 500000000000) : ℝ) = ((500000000000 / 1043098251959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (736680427 / 1000000000) ≤ -Real.log (250000000000 / 522247360483) ∧
    -Real.log (250000000000 / 522247360483) ≤ (736680429 / 1000000000) := by
  have h := checkLog_sound (w := (22247360483 / 1022247360483)) (n := 12)
    (lo := (43533247 / 1000000000)) (hi := (680207 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((522247360483 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(522247360483 / 500000000000) = 1/(250000000000 / 522247360483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (736680427 / 1000000000) (736680429 / 1000000000) (Real.log (522247360483 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (522247360483 / 250000000000) = -Real.log (250000000000 / 522247360483) := by
    rw [show ((522247360483 / 250000000000) : ℝ) = ((250000000000 / 522247360483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (102260277 / 200000000) ≤ -Real.log (62500000000 / 104216236961) ∧
    -Real.log (62500000000 / 104216236961) ≤ (255650693 / 500000000) := by
  have h := checkLog_sound (w := (41716236961 / 166716236961)) (n := 12)
    (lo := (102260277 / 200000000)) (hi := (255650693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104216236961 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104216236961 / 62500000000) = 1/(62500000000 / 104216236961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (102260277 / 200000000) (255650693 / 500000000) (Real.log (104216236961 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (104216236961 / 62500000000) = -Real.log (62500000000 / 104216236961) := by
    rw [show ((104216236961 / 62500000000) : ℝ) = ((62500000000 / 104216236961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25610093 / 50000000) ≤ -Real.log (500000000000 / 834480986983) ∧
    -Real.log (500000000000 / 834480986983) ≤ (512201861 / 1000000000) := by
  have h := checkLog_sound (w := (334480986983 / 1334480986983)) (n := 12)
    (lo := (25610093 / 50000000)) (hi := (512201861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834480986983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(834480986983 / 500000000000) = 1/(500000000000 / 834480986983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (25610093 / 50000000) (512201861 / 1000000000) (Real.log (834480986983 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (834480986983 / 500000000000) = -Real.log (500000000000 / 834480986983) := by
    rw [show ((834480986983 / 500000000000) : ℝ) = ((500000000000 / 834480986983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (72816639 / 200000000) ≤ -Real.log (31250000000 / 44974810749) ∧
    -Real.log (31250000000 / 44974810749) ≤ (91020799 / 250000000) := by
  have h := checkLog_sound (w := (13724810749 / 76224810749)) (n := 12)
    (lo := (72816639 / 200000000)) (hi := (91020799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44974810749 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44974810749 / 31250000000) = 1/(31250000000 / 44974810749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (72816639 / 200000000) (91020799 / 250000000) (Real.log (44974810749 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (44974810749 / 31250000000) = -Real.log (31250000000 / 44974810749) := by
    rw [show ((44974810749 / 31250000000) : ℝ) = ((31250000000 / 44974810749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (364734343 / 1000000000) ≤ -Real.log (500000000000 / 720065688337) ∧
    -Real.log (500000000000 / 720065688337) ≤ (45591793 / 125000000) := by
  have h := checkLog_sound (w := (220065688337 / 1220065688337)) (n := 12)
    (lo := (364734343 / 1000000000)) (hi := (45591793 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720065688337 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720065688337 / 500000000000) = 1/(500000000000 / 720065688337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (364734343 / 1000000000) (45591793 / 125000000) (Real.log (720065688337 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (720065688337 / 500000000000) = -Real.log (500000000000 / 720065688337) := by
    rw [show ((720065688337 / 500000000000) : ℝ) = ((500000000000 / 720065688337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33075057 / 1000000000) ≤ -Real.log (60466621351 / 62500000000) ∧
    -Real.log (60466621351 / 62500000000) ≤ (16537529 / 500000000) := by
  have h := checkLog_sound (w := (2033378649 / 122966621351)) (n := 12)
    (lo := (33075057 / 1000000000)) (hi := (16537529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60466621351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60466621351) = 1/(60466621351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16537529 / 500000000) (-33075057 / 1000000000) (Real.log (60466621351 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3295771 / 100000000) ≤ -Real.log (967579476751 / 1000000000000) ∧
    -Real.log (967579476751 / 1000000000000) ≤ (32957711 / 1000000000) := by
  have h := checkLog_sound (w := (32420523249 / 1967579476751)) (n := 12)
    (lo := (3295771 / 100000000)) (hi := (32957711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967579476751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967579476751) = 1/(967579476751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32957711 / 1000000000) (-3295771 / 100000000) (Real.log (967579476751 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell174

end


