-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell005Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell005Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:10:50.302604+00:00
-- url     : https://prove2.me/theorems/e73b9b8b-b607-4f5f-9150-ad84acbd069a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell005Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell006…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell005Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell006Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell007Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell008Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell009Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell005Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell006Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell007Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell008Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell009Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell005Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell006Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell007Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell008Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell009Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell005Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell006Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell007Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell008Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell009Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell005Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell005
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

theorem reflection_log_1_neg : (225952103 / 1000000000) ≤ -Real.log (2560 / 3209) ∧
    -Real.log (2560 / 3209) ≤ (28244013 / 125000000) := by
  have h := checkLog_sound (w := (649 / 5769)) (n := 12)
    (lo := (225952103 / 1000000000)) (hi := (28244013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3209 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3209 / 2560) = 1/(2560 / 3209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (225952103 / 1000000000) (28244013 / 125000000) (Real.log (3209 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3209 / 2560) = -Real.log (2560 / 3209) := by
    rw [show ((3209 / 2560) : ℝ) = ((2560 / 3209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (292380593 / 1000000000) ≤ -Real.log (1911 / 2560) ∧
    -Real.log (1911 / 2560) ≤ (146190297 / 500000000) := by
  have h := checkLog_sound (w := (649 / 4471)) (n := 12)
    (lo := (292380593 / 1000000000)) (hi := (146190297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1911) = 1/(1911 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-146190297 / 500000000) (-292380593 / 1000000000) (Real.log (1911 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (225484559 / 1000000000) ≤ -Real.log (1024 / 1283) ∧
    -Real.log (1024 / 1283) ≤ (2818557 / 12500000) := by
  have h := checkLog_sound (w := (259 / 2307)) (n := 12)
    (lo := (225484559 / 1000000000)) (hi := (2818557 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283 / 1024) = 1/(1024 / 1283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (225484559 / 1000000000) (2818557 / 12500000) (Real.log (1283 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1283 / 1024) = -Real.log (1024 / 1283) := by
    rw [show ((1283 / 1024) : ℝ) = ((1024 / 1283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (291595971 / 1000000000) ≤ -Real.log (765 / 1024) ∧
    -Real.log (765 / 1024) ≤ (72898993 / 250000000) := by
  have h := checkLog_sound (w := (259 / 1789)) (n := 12)
    (lo := (291595971 / 1000000000)) (hi := (72898993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 765) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 765) = 1/(765 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-72898993 / 250000000) (-291595971 / 1000000000) (Real.log (765 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10309579 / 62500000) ≤ -Real.log (500000 / 589669) ∧
    -Real.log (500000 / 589669) ≤ (32990653 / 200000000) := by
  have h := checkLog_sound (w := (89669 / 1089669)) (n := 12)
    (lo := (10309579 / 62500000)) (hi := (32990653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589669 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589669 / 500000) = 1/(500000 / 589669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10309579 / 62500000) (32990653 / 200000000) (Real.log (589669 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (589669 / 500000) = -Real.log (500000 / 589669) := by
    rw [show ((589669 / 500000) : ℝ) = ((500000 / 589669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (197643947 / 1000000000) ≤ -Real.log (410331 / 500000) ∧
    -Real.log (410331 / 500000) ≤ (49410987 / 250000000) := by
  have h := checkLog_sound (w := (89669 / 910331)) (n := 12)
    (lo := (197643947 / 1000000000)) (hi := (49410987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 410331) = 1/(410331 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-49410987 / 250000000) (-197643947 / 1000000000) (Real.log (410331 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (165307637 / 1000000000) ≤ -Real.log (250000 / 294939) ∧
    -Real.log (250000 / 294939) ≤ (82653819 / 500000000) := by
  have h := checkLog_sound (w := (44939 / 544939)) (n := 12)
    (lo := (165307637 / 1000000000)) (hi := (82653819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294939 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294939 / 250000) = 1/(250000 / 294939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (165307637 / 1000000000) (82653819 / 500000000) (Real.log (294939 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (294939 / 250000) = -Real.log (250000 / 294939) := by
    rw [show ((294939 / 250000) : ℝ) = ((250000 / 294939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (99076711 / 500000000) ≤ -Real.log (205061 / 250000) ∧
    -Real.log (205061 / 250000) ≤ (198153423 / 1000000000) := by
  have h := checkLog_sound (w := (44939 / 455061)) (n := 12)
    (lo := (99076711 / 500000000)) (hi := (198153423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 205061) = 1/(205061 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-198153423 / 1000000000) (-99076711 / 500000000) (Real.log (205061 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15050339 / 125000000) ≤ -Real.log (1000000 / 1127951) ∧
    -Real.log (1000000 / 1127951) ≤ (120402713 / 1000000000) := by
  have h := checkLog_sound (w := (127951 / 2127951)) (n := 12)
    (lo := (15050339 / 125000000)) (hi := (120402713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1127951 / 1000000) = 1/(1000000 / 1127951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15050339 / 125000000) (120402713 / 1000000000) (Real.log (1127951 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1127951 / 1000000) = -Real.log (1000000 / 1127951) := by
    rw [show ((1127951 / 1000000) : ℝ) = ((1000000 / 1127951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (136909663 / 1000000000) ≤ -Real.log (872049 / 1000000) ∧
    -Real.log (872049 / 1000000) ≤ (4278427 / 31250000) := by
  have h := checkLog_sound (w := (127951 / 1872049)) (n := 12)
    (lo := (136909663 / 1000000000)) (hi := (4278427 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 872049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 872049) = 1/(872049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4278427 / 31250000) (-136909663 / 1000000000) (Real.log (872049 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (120673077 / 1000000000) ≤ -Real.log (15625 / 17629) ∧
    -Real.log (15625 / 17629) ≤ (60336539 / 500000000) := by
  have h := checkLog_sound (w := (1002 / 16627)) (n := 12)
    (lo := (120673077 / 1000000000)) (hi := (60336539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17629 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17629 / 15625) = 1/(15625 / 17629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (120673077 / 1000000000) (60336539 / 500000000) (Real.log (17629 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (17629 / 15625) = -Real.log (15625 / 17629) := by
    rw [show ((17629 / 15625) : ℝ) = ((15625 / 17629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (34314869 / 250000000) ≤ -Real.log (13621 / 15625) ∧
    -Real.log (13621 / 15625) ≤ (137259477 / 1000000000) := by
  have h := checkLog_sound (w := (1002 / 14623)) (n := 12)
    (lo := (34314869 / 250000000)) (hi := (137259477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13621) = 1/(13621 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-137259477 / 1000000000) (-34314869 / 250000000) (Real.log (13621 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51708053 / 100000000) ≤ -Real.log (500000000000 / 838562091503) ∧
    -Real.log (500000000000 / 838562091503) ≤ (517080531 / 1000000000) := by
  have h := checkLog_sound (w := (338562091503 / 1338562091503)) (n := 12)
    (lo := (51708053 / 100000000)) (hi := (517080531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838562091503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838562091503 / 500000000000) = 1/(500000000000 / 838562091503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51708053 / 100000000) (517080531 / 1000000000) (Real.log (838562091503 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (838562091503 / 500000000000) = -Real.log (500000000000 / 838562091503) := by
    rw [show ((838562091503 / 500000000000) : ℝ) = ((500000000000 / 838562091503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (64791587 / 125000000) ≤ -Real.log (100000000000 / 167922553637) ∧
    -Real.log (100000000000 / 167922553637) ≤ (518332697 / 1000000000) := by
  have h := checkLog_sound (w := (67922553637 / 267922553637)) (n := 12)
    (lo := (64791587 / 125000000)) (hi := (518332697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167922553637 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167922553637 / 100000000000) = 1/(100000000000 / 167922553637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (64791587 / 125000000) (518332697 / 1000000000) (Real.log (167922553637 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (167922553637 / 100000000000) = -Real.log (100000000000 / 167922553637) := by
    rw [show ((167922553637 / 100000000000) : ℝ) = ((100000000000 / 167922553637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (362597211 / 1000000000) ≤ -Real.log (100000000000 / 143705691259) ∧
    -Real.log (100000000000 / 143705691259) ≤ (90649303 / 250000000) := by
  have h := checkLog_sound (w := (43705691259 / 243705691259)) (n := 12)
    (lo := (362597211 / 1000000000)) (hi := (90649303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143705691259 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143705691259 / 100000000000) = 1/(100000000000 / 143705691259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (362597211 / 1000000000) (90649303 / 250000000) (Real.log (143705691259 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (143705691259 / 100000000000) = -Real.log (100000000000 / 143705691259) := by
    rw [show ((143705691259 / 100000000000) : ℝ) = ((100000000000 / 143705691259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (363461059 / 1000000000) ≤ -Real.log (50000000000 / 71914942383) ∧
    -Real.log (50000000000 / 71914942383) ≤ (18173053 / 50000000) := by
  have h := checkLog_sound (w := (21914942383 / 121914942383)) (n := 12)
    (lo := (363461059 / 1000000000)) (hi := (18173053 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71914942383 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71914942383 / 50000000000) = 1/(50000000000 / 71914942383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (363461059 / 1000000000) (18173053 / 50000000) (Real.log (71914942383 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (71914942383 / 50000000000) = -Real.log (50000000000 / 71914942383) := by
    rw [show ((71914942383 / 50000000000) : ℝ) = ((50000000000 / 71914942383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (32164047 / 125000000) ≤ -Real.log (250000000000 / 323362276661) ∧
    -Real.log (250000000000 / 323362276661) ≤ (257312377 / 1000000000) := by
  have h := checkLog_sound (w := (73362276661 / 573362276661)) (n := 12)
    (lo := (32164047 / 125000000)) (hi := (257312377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323362276661 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323362276661 / 250000000000) = 1/(250000000000 / 323362276661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (32164047 / 125000000) (257312377 / 1000000000) (Real.log (323362276661 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (323362276661 / 250000000000) = -Real.log (250000000000 / 323362276661) := by
    rw [show ((323362276661 / 250000000000) : ℝ) = ((250000000000 / 323362276661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (257932553 / 1000000000) ≤ -Real.log (125000000000 / 161781440423) ∧
    -Real.log (125000000000 / 161781440423) ≤ (128966277 / 500000000) := by
  have h := checkLog_sound (w := (36781440423 / 286781440423)) (n := 12)
    (lo := (257932553 / 1000000000)) (hi := (128966277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161781440423 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161781440423 / 125000000000) = 1/(125000000000 / 161781440423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (257932553 / 1000000000) (128966277 / 500000000) (Real.log (161781440423 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (161781440423 / 125000000000) = -Real.log (125000000000 / 161781440423) := by
    rw [show ((161781440423 / 125000000000) : ℝ) = ((125000000000 / 161781440423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8293199 / 500000000) ≤ -Real.log (240124609 / 244140625) ∧
    -Real.log (240124609 / 244140625) ≤ (16586399 / 1000000000) := by
  have h := checkLog_sound (w := (2008008 / 242132617)) (n := 12)
    (lo := (8293199 / 500000000)) (hi := (16586399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 240124609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 240124609) = 1/(240124609 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16586399 / 1000000000) (-8293199 / 500000000) (Real.log (240124609 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16506951 / 1000000000) ≤ -Real.log (983628541599 / 1000000000000) ∧
    -Real.log (983628541599 / 1000000000000) ≤ (2063369 / 125000000) := by
  have h := checkLog_sound (w := (16371458401 / 1983628541599)) (n := 12)
    (lo := (16506951 / 1000000000)) (hi := (2063369 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983628541599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983628541599) = 1/(983628541599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2063369 / 125000000) (-16506951 / 1000000000) (Real.log (983628541599 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell005

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell006Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell006
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

theorem reflection_log_1_neg : (226419429 / 1000000000) ≤ -Real.log (5120 / 6421) ∧
    -Real.log (5120 / 6421) ≤ (22641943 / 100000000) := by
  have h := checkLog_sound (w := (1301 / 11541)) (n := 12)
    (lo := (226419429 / 1000000000)) (hi := (22641943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6421 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6421 / 5120) = 1/(5120 / 6421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (226419429 / 1000000000) (22641943 / 100000000) (Real.log (6421 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6421 / 5120) = -Real.log (5120 / 6421) := by
    rw [show ((6421 / 5120) : ℝ) = ((5120 / 6421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (29316583 / 100000000) ≤ -Real.log (3819 / 5120) ∧
    -Real.log (3819 / 5120) ≤ (293165831 / 1000000000) := by
  have h := checkLog_sound (w := (1301 / 8939)) (n := 12)
    (lo := (29316583 / 100000000)) (hi := (293165831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3819) = 1/(3819 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-293165831 / 1000000000) (-29316583 / 100000000) (Real.log (3819 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (225952103 / 1000000000) ≤ -Real.log (2560 / 3209) ∧
    -Real.log (2560 / 3209) ≤ (28244013 / 125000000) := by
  have h := checkLog_sound (w := (649 / 5769)) (n := 12)
    (lo := (225952103 / 1000000000)) (hi := (28244013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3209 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3209 / 2560) = 1/(2560 / 3209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (225952103 / 1000000000) (28244013 / 125000000) (Real.log (3209 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3209 / 2560) = -Real.log (2560 / 3209) := by
    rw [show ((3209 / 2560) : ℝ) = ((2560 / 3209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (292380593 / 1000000000) ≤ -Real.log (1911 / 2560) ∧
    -Real.log (1911 / 2560) ≤ (146190297 / 500000000) := by
  have h := checkLog_sound (w := (649 / 4471)) (n := 12)
    (lo := (292380593 / 1000000000)) (hi := (146190297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1911) = 1/(1911 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-146190297 / 500000000) (-292380593 / 1000000000) (Real.log (1911 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (165306789 / 1000000000) ≤ -Real.log (200000 / 235951) ∧
    -Real.log (200000 / 235951) ≤ (16530679 / 100000000) := by
  have h := checkLog_sound (w := (35951 / 435951)) (n := 12)
    (lo := (165306789 / 1000000000)) (hi := (16530679 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235951 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235951 / 200000) = 1/(200000 / 235951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (165306789 / 1000000000) (16530679 / 100000000) (Real.log (235951 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (235951 / 200000) = -Real.log (200000 / 235951) := by
    rw [show ((235951 / 200000) : ℝ) = ((200000 / 235951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (99076101 / 500000000) ≤ -Real.log (164049 / 200000) ∧
    -Real.log (164049 / 200000) ≤ (198152203 / 1000000000) := by
  have h := checkLog_sound (w := (35951 / 364049)) (n := 12)
    (lo := (99076101 / 500000000)) (hi := (198152203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 164049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 164049) = 1/(164049 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-198152203 / 1000000000) (-99076101 / 500000000) (Real.log (164049 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (33132377 / 200000000) ≤ -Real.log (500000 / 590087) ∧
    -Real.log (500000 / 590087) ≤ (82830943 / 500000000) := by
  have h := checkLog_sound (w := (90087 / 1090087)) (n := 12)
    (lo := (33132377 / 200000000)) (hi := (82830943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590087 / 500000) = 1/(500000 / 590087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (33132377 / 200000000) (82830943 / 500000000) (Real.log (590087 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (590087 / 500000) = -Real.log (500000 / 590087) := by
    rw [show ((590087 / 500000) : ℝ) = ((500000 / 590087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (49665789 / 250000000) ≤ -Real.log (409913 / 500000) ∧
    -Real.log (409913 / 500000) ≤ (198663157 / 1000000000) := by
  have h := checkLog_sound (w := (90087 / 909913)) (n := 12)
    (lo := (49665789 / 250000000)) (hi := (198663157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409913) = 1/(409913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-198663157 / 1000000000) (-49665789 / 250000000) (Real.log (409913 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (120672191 / 1000000000) ≤ -Real.log (200000 / 225651) ∧
    -Real.log (200000 / 225651) ≤ (1885503 / 15625000) := by
  have h := checkLog_sound (w := (25651 / 425651)) (n := 12)
    (lo := (120672191 / 1000000000)) (hi := (1885503 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225651 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225651 / 200000) = 1/(200000 / 225651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (120672191 / 1000000000) (1885503 / 15625000) (Real.log (225651 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (225651 / 200000) = -Real.log (200000 / 225651) := by
    rw [show ((225651 / 200000) : ℝ) = ((200000 / 225651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (137258329 / 1000000000) ≤ -Real.log (174349 / 200000) ∧
    -Real.log (174349 / 200000) ≤ (13725833 / 100000000) := by
  have h := checkLog_sound (w := (25651 / 374349)) (n := 12)
    (lo := (137258329 / 1000000000)) (hi := (13725833 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 174349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 174349) = 1/(174349 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13725833 / 100000000) (-137258329 / 1000000000) (Real.log (174349 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (120941597 / 1000000000) ≤ -Real.log (1000000 / 1128559) ∧
    -Real.log (1000000 / 1128559) ≤ (60470799 / 500000000) := by
  have h := checkLog_sound (w := (128559 / 2128559)) (n := 12)
    (lo := (120941597 / 1000000000)) (hi := (60470799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1128559 / 1000000) = 1/(1000000 / 1128559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (120941597 / 1000000000) (60470799 / 500000000) (Real.log (1128559 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1128559 / 1000000) = -Real.log (1000000 / 1128559) := by
    rw [show ((1128559 / 1000000) : ℝ) = ((1000000 / 1128559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27521423 / 200000000) ≤ -Real.log (871441 / 1000000) ∧
    -Real.log (871441 / 1000000) ≤ (34401779 / 250000000) := by
  have h := checkLog_sound (w := (128559 / 1871441)) (n := 12)
    (lo := (27521423 / 200000000)) (hi := (34401779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 871441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 871441) = 1/(871441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-34401779 / 250000000) (-27521423 / 200000000) (Real.log (871441 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (64791587 / 125000000) ≤ -Real.log (62500000000 / 104951596023) ∧
    -Real.log (62500000000 / 104951596023) ≤ (518332697 / 1000000000) := by
  have h := checkLog_sound (w := (42451596023 / 167451596023)) (n := 12)
    (lo := (64791587 / 125000000)) (hi := (518332697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104951596023 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104951596023 / 62500000000) = 1/(62500000000 / 104951596023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (64791587 / 125000000) (518332697 / 1000000000) (Real.log (104951596023 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (104951596023 / 62500000000) = -Real.log (62500000000 / 104951596023) := by
    rw [show ((104951596023 / 62500000000) : ℝ) = ((62500000000 / 104951596023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (25979263 / 50000000) ≤ -Real.log (20000000000 / 33626603823) ∧
    -Real.log (20000000000 / 33626603823) ≤ (519585261 / 1000000000) := by
  have h := checkLog_sound (w := (13626603823 / 53626603823)) (n := 12)
    (lo := (25979263 / 50000000)) (hi := (519585261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33626603823 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33626603823 / 20000000000) = 1/(20000000000 / 33626603823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (25979263 / 50000000) (519585261 / 1000000000) (Real.log (33626603823 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (33626603823 / 20000000000) = -Real.log (20000000000 / 33626603823) := by
    rw [show ((33626603823 / 20000000000) : ℝ) = ((20000000000 / 33626603823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22716187 / 62500000) ≤ -Real.log (250000000000 / 359573968753) ∧
    -Real.log (250000000000 / 359573968753) ≤ (363458993 / 1000000000) := by
  have h := checkLog_sound (w := (109573968753 / 609573968753)) (n := 12)
    (lo := (22716187 / 62500000)) (hi := (363458993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359573968753 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359573968753 / 250000000000) = 1/(250000000000 / 359573968753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22716187 / 62500000) (363458993 / 1000000000) (Real.log (359573968753 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (359573968753 / 250000000000) = -Real.log (250000000000 / 359573968753) := by
    rw [show ((359573968753 / 250000000000) : ℝ) = ((250000000000 / 359573968753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (364325041 / 1000000000) ≤ -Real.log (62500000000 / 89971378073) ∧
    -Real.log (62500000000 / 89971378073) ≤ (182162521 / 500000000) := by
  have h := checkLog_sound (w := (27471378073 / 152471378073)) (n := 12)
    (lo := (364325041 / 1000000000)) (hi := (182162521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89971378073 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89971378073 / 62500000000) = 1/(62500000000 / 89971378073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (364325041 / 1000000000) (182162521 / 500000000) (Real.log (89971378073 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (89971378073 / 62500000000) = -Real.log (62500000000 / 89971378073) := by
    rw [show ((89971378073 / 62500000000) : ℝ) = ((62500000000 / 89971378073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (6448263 / 25000000) ≤ -Real.log (100000000000 / 129424889159) ∧
    -Real.log (100000000000 / 129424889159) ≤ (257930521 / 1000000000) := by
  have h := checkLog_sound (w := (29424889159 / 229424889159)) (n := 12)
    (lo := (6448263 / 25000000)) (hi := (257930521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129424889159 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(129424889159 / 100000000000) = 1/(100000000000 / 129424889159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (6448263 / 25000000) (257930521 / 1000000000) (Real.log (129424889159 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (129424889159 / 100000000000) = -Real.log (100000000000 / 129424889159) := by
    rw [show ((129424889159 / 100000000000) : ℝ) = ((100000000000 / 129424889159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (258548713 / 1000000000) ≤ -Real.log (62500000000 / 80940577159) ∧
    -Real.log (62500000000 / 80940577159) ≤ (129274357 / 500000000) := by
  have h := checkLog_sound (w := (18440577159 / 143440577159)) (n := 12)
    (lo := (258548713 / 1000000000)) (hi := (129274357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80940577159 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80940577159 / 62500000000) = 1/(62500000000 / 80940577159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (258548713 / 1000000000) (129274357 / 500000000) (Real.log (80940577159 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (80940577159 / 62500000000) = -Real.log (62500000000 / 80940577159) := by
    rw [show ((80940577159 / 62500000000) : ℝ) = ((62500000000 / 80940577159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16665517 / 1000000000) ≤ -Real.log (983472583519 / 1000000000000) ∧
    -Real.log (983472583519 / 1000000000000) ≤ (8332759 / 500000000) := by
  have h := checkLog_sound (w := (16527416481 / 1983472583519)) (n := 12)
    (lo := (16665517 / 1000000000)) (hi := (8332759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983472583519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983472583519) = 1/(983472583519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8332759 / 500000000) (-16665517 / 1000000000) (Real.log (983472583519 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16586137 / 1000000000) ≤ -Real.log (39342026199 / 40000000000) ∧
    -Real.log (39342026199 / 40000000000) ≤ (8293069 / 500000000) := by
  have h := checkLog_sound (w := (657973801 / 79342026199)) (n := 12)
    (lo := (16586137 / 1000000000)) (hi := (8293069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39342026199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39342026199) = 1/(39342026199 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8293069 / 500000000) (-16586137 / 1000000000) (Real.log (39342026199 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell006

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell007Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell007
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

theorem reflection_log_1_neg : (226886537 / 1000000000) ≤ -Real.log (640 / 803) ∧
    -Real.log (640 / 803) ≤ (113443269 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1443)) (n := 12)
    (lo := (226886537 / 1000000000)) (hi := (113443269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803 / 640) = 1/(640 / 803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (226886537 / 1000000000) (113443269 / 500000000) (Real.log (803 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (803 / 640) = -Real.log (640 / 803) := by
    rw [show ((803 / 640) : ℝ) = ((640 / 803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (58790337 / 200000000) ≤ -Real.log (477 / 640) ∧
    -Real.log (477 / 640) ≤ (146975843 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1117)) (n := 12)
    (lo := (58790337 / 200000000)) (hi := (146975843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 477) = 1/(477 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-146975843 / 500000000) (-58790337 / 200000000) (Real.log (477 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (226419429 / 1000000000) ≤ -Real.log (5120 / 6421) ∧
    -Real.log (5120 / 6421) ≤ (22641943 / 100000000) := by
  have h := checkLog_sound (w := (1301 / 11541)) (n := 12)
    (lo := (226419429 / 1000000000)) (hi := (22641943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6421 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6421 / 5120) = 1/(5120 / 6421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (226419429 / 1000000000) (22641943 / 100000000) (Real.log (6421 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6421 / 5120) = -Real.log (5120 / 6421) := by
    rw [show ((6421 / 5120) : ℝ) = ((5120 / 6421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (29316583 / 100000000) ≤ -Real.log (3819 / 5120) ∧
    -Real.log (3819 / 5120) ≤ (293165831 / 1000000000) := by
  have h := checkLog_sound (w := (1301 / 8939)) (n := 12)
    (lo := (29316583 / 100000000)) (hi := (293165831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3819) = 1/(3819 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-293165831 / 1000000000) (-29316583 / 100000000) (Real.log (3819 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (165661037 / 1000000000) ≤ -Real.log (1000000 / 1180173) ∧
    -Real.log (1000000 / 1180173) ≤ (82830519 / 500000000) := by
  have h := checkLog_sound (w := (180173 / 2180173)) (n := 12)
    (lo := (165661037 / 1000000000)) (hi := (82830519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1180173 / 1000000) = 1/(1000000 / 1180173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (165661037 / 1000000000) (82830519 / 500000000) (Real.log (1180173 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1180173 / 1000000) = -Real.log (1000000 / 1180173) := by
    rw [show ((1180173 / 1000000) : ℝ) = ((1000000 / 1180173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12416371 / 62500000) ≤ -Real.log (819827 / 1000000) ∧
    -Real.log (819827 / 1000000) ≤ (198661937 / 1000000000) := by
  have h := checkLog_sound (w := (180173 / 1819827)) (n := 12)
    (lo := (12416371 / 62500000)) (hi := (198661937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 819827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 819827) = 1/(819827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-198661937 / 1000000000) (-12416371 / 62500000) (Real.log (819827 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (166016007 / 1000000000) ≤ -Real.log (62500 / 73787) ∧
    -Real.log (62500 / 73787) ≤ (20752001 / 125000000) := by
  have h := checkLog_sound (w := (11287 / 136287)) (n := 12)
    (lo := (166016007 / 1000000000)) (hi := (20752001 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73787 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73787 / 62500) = 1/(62500 / 73787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (166016007 / 1000000000) (20752001 / 125000000) (Real.log (73787 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (73787 / 62500) = -Real.log (62500 / 73787) := by
    rw [show ((73787 / 62500) : ℝ) = ((62500 / 73787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3983463 / 20000000) ≤ -Real.log (51213 / 62500) ∧
    -Real.log (51213 / 62500) ≤ (199173151 / 1000000000) := by
  have h := checkLog_sound (w := (11287 / 113713)) (n := 12)
    (lo := (3983463 / 20000000)) (hi := (199173151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 51213) = 1/(51213 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-199173151 / 1000000000) (-3983463 / 20000000) (Real.log (51213 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (120940711 / 1000000000) ≤ -Real.log (500000 / 564279) ∧
    -Real.log (500000 / 564279) ≤ (15117589 / 125000000) := by
  have h := checkLog_sound (w := (64279 / 1064279)) (n := 12)
    (lo := (120940711 / 1000000000)) (hi := (15117589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564279 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564279 / 500000) = 1/(500000 / 564279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (120940711 / 1000000000) (15117589 / 125000000) (Real.log (564279 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (564279 / 500000) = -Real.log (500000 / 564279) := by
    rw [show ((564279 / 500000) : ℝ) = ((500000 / 564279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8600373 / 62500000) ≤ -Real.log (435721 / 500000) ∧
    -Real.log (435721 / 500000) ≤ (137605969 / 1000000000) := by
  have h := checkLog_sound (w := (64279 / 935721)) (n := 12)
    (lo := (8600373 / 62500000)) (hi := (137605969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435721) = 1/(435721 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-137605969 / 1000000000) (-8600373 / 62500000) (Real.log (435721 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (121210931 / 1000000000) ≤ -Real.log (1000000 / 1128863) ∧
    -Real.log (1000000 / 1128863) ≤ (30302733 / 250000000) := by
  have h := checkLog_sound (w := (128863 / 2128863)) (n := 12)
    (lo := (121210931 / 1000000000)) (hi := (30302733 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1128863 / 1000000) = 1/(1000000 / 1128863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (121210931 / 1000000000) (30302733 / 250000000) (Real.log (1128863 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1128863 / 1000000) = -Real.log (1000000 / 1128863) := by
    rw [show ((1128863 / 1000000) : ℝ) = ((1000000 / 1128863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (17244503 / 125000000) ≤ -Real.log (871137 / 1000000) ∧
    -Real.log (871137 / 1000000) ≤ (5518241 / 40000000) := by
  have h := checkLog_sound (w := (128863 / 1871137)) (n := 12)
    (lo := (17244503 / 125000000)) (hi := (5518241 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 871137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 871137) = 1/(871137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5518241 / 40000000) (-17244503 / 125000000) (Real.log (871137 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (25979263 / 50000000) ≤ -Real.log (250000000000 / 420332547787) ∧
    -Real.log (250000000000 / 420332547787) ≤ (519585261 / 1000000000) := by
  have h := checkLog_sound (w := (170332547787 / 670332547787)) (n := 12)
    (lo := (25979263 / 50000000)) (hi := (519585261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420332547787 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(420332547787 / 250000000000) = 1/(250000000000 / 420332547787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (25979263 / 50000000) (519585261 / 1000000000) (Real.log (420332547787 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (420332547787 / 250000000000) = -Real.log (250000000000 / 420332547787) := by
    rw [show ((420332547787 / 250000000000) : ℝ) = ((250000000000 / 420332547787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (520838223 / 1000000000) ≤ -Real.log (500000000000 / 841719077569) ∧
    -Real.log (500000000000 / 841719077569) ≤ (32552389 / 62500000) := by
  have h := checkLog_sound (w := (341719077569 / 1341719077569)) (n := 12)
    (lo := (520838223 / 1000000000)) (hi := (32552389 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841719077569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(841719077569 / 500000000000) = 1/(500000000000 / 841719077569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (520838223 / 1000000000) (32552389 / 62500000) (Real.log (841719077569 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (841719077569 / 500000000000) = -Real.log (500000000000 / 841719077569) := by
    rw [show ((841719077569 / 500000000000) : ℝ) = ((500000000000 / 841719077569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (182161487 / 500000000) ≤ -Real.log (500000000000 / 719769536743) ∧
    -Real.log (500000000000 / 719769536743) ≤ (14572919 / 40000000) := by
  have h := checkLog_sound (w := (219769536743 / 1219769536743)) (n := 12)
    (lo := (182161487 / 500000000)) (hi := (14572919 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719769536743 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719769536743 / 500000000000) = 1/(500000000000 / 719769536743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (182161487 / 500000000) (14572919 / 40000000) (Real.log (719769536743 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (719769536743 / 500000000000) = -Real.log (500000000000 / 719769536743) := by
    rw [show ((719769536743 / 500000000000) : ℝ) = ((500000000000 / 719769536743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (182594579 / 500000000) ≤ -Real.log (125000000000 / 180098314881) ∧
    -Real.log (125000000000 / 180098314881) ≤ (365189159 / 1000000000) := by
  have h := checkLog_sound (w := (55098314881 / 305098314881)) (n := 12)
    (lo := (182594579 / 500000000)) (hi := (365189159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180098314881 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180098314881 / 125000000000) = 1/(125000000000 / 180098314881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (182594579 / 500000000) (365189159 / 1000000000) (Real.log (180098314881 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (180098314881 / 125000000000) = -Real.log (125000000000 / 180098314881) := by
    rw [show ((180098314881 / 125000000000) : ℝ) = ((125000000000 / 180098314881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (258546679 / 1000000000) ≤ -Real.log (25000000000 / 32376165023) ∧
    -Real.log (25000000000 / 32376165023) ≤ (6463667 / 25000000) := by
  have h := checkLog_sound (w := (7376165023 / 57376165023)) (n := 12)
    (lo := (258546679 / 1000000000)) (hi := (6463667 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32376165023 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32376165023 / 25000000000) = 1/(25000000000 / 32376165023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (258546679 / 1000000000) (6463667 / 25000000) (Real.log (32376165023 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (32376165023 / 25000000000) = -Real.log (25000000000 / 32376165023) := by
    rw [show ((32376165023 / 25000000000) : ℝ) = ((25000000000 / 32376165023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (51833391 / 200000000) ≤ -Real.log (125000000000 / 161981267011) ∧
    -Real.log (125000000000 / 161981267011) ≤ (64791739 / 250000000) := by
  have h := checkLog_sound (w := (36981267011 / 286981267011)) (n := 12)
    (lo := (51833391 / 200000000)) (hi := (64791739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161981267011 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161981267011 / 125000000000) = 1/(125000000000 / 161981267011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (51833391 / 200000000) (64791739 / 250000000) (Real.log (161981267011 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (161981267011 / 125000000000) = -Real.log (125000000000 / 161981267011) := by
    rw [show ((161981267011 / 125000000000) : ℝ) = ((125000000000 / 161981267011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4186273 / 250000000) ≤ -Real.log (983394327231 / 1000000000000) ∧
    -Real.log (983394327231 / 1000000000000) ≤ (16745093 / 1000000000) := by
  have h := checkLog_sound (w := (16605672769 / 1983394327231)) (n := 12)
    (lo := (4186273 / 250000000)) (hi := (16745093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983394327231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983394327231) = 1/(983394327231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16745093 / 1000000000) (-4186273 / 250000000) (Real.log (983394327231 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2083157 / 125000000) ≤ -Real.log (245868210159 / 250000000000) ∧
    -Real.log (245868210159 / 250000000000) ≤ (16665257 / 1000000000) := by
  have h := checkLog_sound (w := (4131789841 / 495868210159)) (n := 12)
    (lo := (2083157 / 125000000)) (hi := (16665257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245868210159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245868210159) = 1/(245868210159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-16665257 / 1000000000) (-2083157 / 125000000) (Real.log (245868210159 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell007

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell008Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell008
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

theorem reflection_log_1_neg : (227353427 / 1000000000) ≤ -Real.log (5120 / 6427) ∧
    -Real.log (5120 / 6427) ≤ (56838357 / 250000000) := by
  have h := checkLog_sound (w := (1307 / 11547)) (n := 12)
    (lo := (227353427 / 1000000000)) (hi := (56838357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6427 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6427 / 5120) = 1/(5120 / 6427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (227353427 / 1000000000) (56838357 / 250000000) (Real.log (6427 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6427 / 5120) = -Real.log (5120 / 6427) := by
    rw [show ((6427 / 5120) : ℝ) = ((5120 / 6427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (147369079 / 500000000) ≤ -Real.log (3813 / 5120) ∧
    -Real.log (3813 / 5120) ≤ (294738159 / 1000000000) := by
  have h := checkLog_sound (w := (1307 / 8933)) (n := 12)
    (lo := (147369079 / 500000000)) (hi := (294738159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3813) = 1/(3813 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-294738159 / 1000000000) (-147369079 / 500000000) (Real.log (3813 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (226886537 / 1000000000) ≤ -Real.log (640 / 803) ∧
    -Real.log (640 / 803) ≤ (113443269 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1443)) (n := 12)
    (lo := (226886537 / 1000000000)) (hi := (113443269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803 / 640) = 1/(640 / 803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (226886537 / 1000000000) (113443269 / 500000000) (Real.log (803 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (803 / 640) = -Real.log (640 / 803) := by
    rw [show ((803 / 640) : ℝ) = ((640 / 803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (58790337 / 200000000) ≤ -Real.log (477 / 640) ∧
    -Real.log (477 / 640) ≤ (146975843 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1117)) (n := 12)
    (lo := (58790337 / 200000000)) (hi := (146975843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 477) = 1/(477 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-146975843 / 500000000) (-58790337 / 200000000) (Real.log (477 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (4150379 / 25000000) ≤ -Real.log (1000000 / 1180591) ∧
    -Real.log (1000000 / 1180591) ≤ (166015161 / 1000000000) := by
  have h := checkLog_sound (w := (180591 / 2180591)) (n := 12)
    (lo := (4150379 / 25000000)) (hi := (166015161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1180591 / 1000000) = 1/(1000000 / 1180591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (4150379 / 25000000) (166015161 / 1000000000) (Real.log (1180591 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1180591 / 1000000) = -Real.log (1000000 / 1180591) := by
    rw [show ((1180591 / 1000000) : ℝ) = ((1000000 / 1180591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (19917193 / 100000000) ≤ -Real.log (819409 / 1000000) ∧
    -Real.log (819409 / 1000000) ≤ (199171931 / 1000000000) := by
  have h := checkLog_sound (w := (180591 / 1819409)) (n := 12)
    (lo := (19917193 / 100000000)) (hi := (199171931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 819409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 819409) = 1/(819409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-199171931 / 1000000000) (-19917193 / 100000000) (Real.log (819409 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41592501 / 250000000) ≤ -Real.log (100000 / 118101) ∧
    -Real.log (100000 / 118101) ≤ (33274001 / 200000000) := by
  have h := checkLog_sound (w := (18101 / 218101)) (n := 12)
    (lo := (41592501 / 250000000)) (hi := (33274001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118101 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118101 / 100000) = 1/(100000 / 118101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41592501 / 250000000) (33274001 / 200000000) (Real.log (118101 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (118101 / 100000) = -Real.log (100000 / 118101) := by
    rw [show ((118101 / 100000) : ℝ) = ((100000 / 118101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (39936681 / 200000000) ≤ -Real.log (81899 / 100000) ∧
    -Real.log (81899 / 100000) ≤ (99841703 / 500000000) := by
  have h := checkLog_sound (w := (18101 / 181899)) (n := 12)
    (lo := (39936681 / 200000000)) (hi := (99841703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81899) = 1/(81899 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-99841703 / 500000000) (-39936681 / 200000000) (Real.log (81899 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (24242009 / 200000000) ≤ -Real.log (500000 / 564431) ∧
    -Real.log (500000 / 564431) ≤ (60605023 / 500000000) := by
  have h := checkLog_sound (w := (64431 / 1064431)) (n := 12)
    (lo := (24242009 / 200000000)) (hi := (60605023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564431 / 500000) = 1/(500000 / 564431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (24242009 / 200000000) (60605023 / 500000000) (Real.log (564431 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (564431 / 500000) = -Real.log (500000 / 564431) := by
    rw [show ((564431 / 500000) : ℝ) = ((500000 / 564431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (34488719 / 250000000) ≤ -Real.log (435569 / 500000) ∧
    -Real.log (435569 / 500000) ≤ (137954877 / 1000000000) := by
  have h := checkLog_sound (w := (64431 / 935569)) (n := 12)
    (lo := (34488719 / 250000000)) (hi := (137954877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435569) = 1/(435569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-137954877 / 1000000000) (-34488719 / 250000000) (Real.log (435569 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (121479307 / 1000000000) ≤ -Real.log (500000 / 564583) ∧
    -Real.log (500000 / 564583) ≤ (30369827 / 250000000) := by
  have h := checkLog_sound (w := (64583 / 1064583)) (n := 12)
    (lo := (121479307 / 1000000000)) (hi := (30369827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564583 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564583 / 500000) = 1/(500000 / 564583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (121479307 / 1000000000) (30369827 / 250000000) (Real.log (564583 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (564583 / 500000) = -Real.log (500000 / 564583) := by
    rw [show ((564583 / 500000) : ℝ) = ((500000 / 564583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27660781 / 200000000) ≤ -Real.log (435417 / 500000) ∧
    -Real.log (435417 / 500000) ≤ (69151953 / 500000000) := by
  have h := checkLog_sound (w := (64583 / 935417)) (n := 12)
    (lo := (27660781 / 200000000)) (hi := (69151953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435417) = 1/(435417 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-69151953 / 500000000) (-27660781 / 200000000) (Real.log (435417 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (520838223 / 1000000000) ≤ -Real.log (7812500000 / 13151860587) ∧
    -Real.log (7812500000 / 13151860587) ≤ (32552389 / 62500000) := by
  have h := checkLog_sound (w := (5339360587 / 20964360587)) (n := 12)
    (lo := (520838223 / 1000000000)) (hi := (32552389 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13151860587 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13151860587 / 7812500000) = 1/(7812500000 / 13151860587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (520838223 / 1000000000) (32552389 / 62500000) (Real.log (13151860587 / 7812500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (13151860587 / 7812500000) = -Real.log (7812500000 / 13151860587) := by
    rw [show ((13151860587 / 7812500000) : ℝ) = ((7812500000 / 13151860587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (104418317 / 200000000) ≤ -Real.log (50000000000 / 84277471807) ∧
    -Real.log (50000000000 / 84277471807) ≤ (261045793 / 500000000) := by
  have h := checkLog_sound (w := (34277471807 / 134277471807)) (n := 12)
    (lo := (104418317 / 200000000)) (hi := (261045793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84277471807 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84277471807 / 50000000000) = 1/(50000000000 / 84277471807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (104418317 / 200000000) (261045793 / 500000000) (Real.log (84277471807 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (84277471807 / 50000000000) = -Real.log (50000000000 / 84277471807) := by
    rw [show ((84277471807 / 50000000000) : ℝ) = ((50000000000 / 84277471807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (36518709 / 100000000) ≤ -Real.log (250000000000 / 360195885083) ∧
    -Real.log (250000000000 / 360195885083) ≤ (365187091 / 1000000000) := by
  have h := checkLog_sound (w := (110195885083 / 610195885083)) (n := 12)
    (lo := (36518709 / 100000000)) (hi := (365187091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360195885083 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360195885083 / 250000000000) = 1/(250000000000 / 360195885083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (36518709 / 100000000) (365187091 / 1000000000) (Real.log (360195885083 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (360195885083 / 250000000000) = -Real.log (250000000000 / 360195885083) := by
    rw [show ((360195885083 / 250000000000) : ℝ) = ((250000000000 / 360195885083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (366053409 / 1000000000) ≤ -Real.log (62500000000 / 90127016203) ∧
    -Real.log (62500000000 / 90127016203) ≤ (36605341 / 100000000) := by
  have h := checkLog_sound (w := (27627016203 / 152627016203)) (n := 12)
    (lo := (366053409 / 1000000000)) (hi := (36605341 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90127016203 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90127016203 / 62500000000) = 1/(62500000000 / 90127016203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (366053409 / 1000000000) (36605341 / 100000000) (Real.log (90127016203 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (90127016203 / 62500000000) = -Real.log (62500000000 / 90127016203) := by
    rw [show ((90127016203 / 62500000000) : ℝ) = ((62500000000 / 90127016203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (259164921 / 1000000000) ≤ -Real.log (62500000000 / 80990468789) ∧
    -Real.log (62500000000 / 80990468789) ≤ (129582461 / 500000000) := by
  have h := checkLog_sound (w := (18490468789 / 143490468789)) (n := 12)
    (lo := (259164921 / 1000000000)) (hi := (129582461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80990468789 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80990468789 / 62500000000) = 1/(62500000000 / 80990468789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (259164921 / 1000000000) (129582461 / 500000000) (Real.log (80990468789 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (80990468789 / 62500000000) = -Real.log (62500000000 / 80990468789) := by
    rw [show ((80990468789 / 62500000000) : ℝ) = ((62500000000 / 80990468789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (64945803 / 250000000) ≤ -Real.log (62500000000 / 81040559969) ∧
    -Real.log (62500000000 / 81040559969) ≤ (259783213 / 1000000000) := by
  have h := checkLog_sound (w := (18540559969 / 143540559969)) (n := 12)
    (lo := (64945803 / 250000000)) (hi := (259783213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81040559969 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81040559969 / 62500000000) = 1/(62500000000 / 81040559969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (64945803 / 250000000) (259783213 / 1000000000) (Real.log (81040559969 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (81040559969 / 62500000000) = -Real.log (62500000000 / 81040559969) := by
    rw [show ((81040559969 / 62500000000) : ℝ) = ((62500000000 / 81040559969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8412299 / 500000000) ≤ -Real.log (245829036111 / 250000000000) ∧
    -Real.log (245829036111 / 250000000000) ≤ (16824599 / 1000000000) := by
  have h := checkLog_sound (w := (4170963889 / 495829036111)) (n := 12)
    (lo := (8412299 / 500000000)) (hi := (16824599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245829036111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245829036111) = 1/(245829036111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16824599 / 1000000000) (-8412299 / 500000000) (Real.log (245829036111 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1674483 / 100000000) ≤ -Real.log (245848646239 / 250000000000) ∧
    -Real.log (245848646239 / 250000000000) ≤ (16744831 / 1000000000) := by
  have h := checkLog_sound (w := (4151353761 / 495848646239)) (n := 12)
    (lo := (1674483 / 100000000)) (hi := (16744831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245848646239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245848646239) = 1/(245848646239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-16744831 / 1000000000) (-1674483 / 100000000) (Real.log (245848646239 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell008

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell009Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell009
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

theorem reflection_log_1_neg : (227820099 / 1000000000) ≤ -Real.log (512 / 643) ∧
    -Real.log (512 / 643) ≤ (2278201 / 10000000) := by
  have h := checkLog_sound (w := (131 / 1155)) (n := 12)
    (lo := (227820099 / 1000000000)) (hi := (2278201 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643 / 512) = 1/(512 / 643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (227820099 / 1000000000) (2278201 / 10000000) (Real.log (643 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (643 / 512) = -Real.log (512 / 643) := by
    rw [show ((643 / 512) : ℝ) = ((512 / 643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (295525249 / 1000000000) ≤ -Real.log (381 / 512) ∧
    -Real.log (381 / 512) ≤ (1182101 / 4000000) := by
  have h := checkLog_sound (w := (131 / 893)) (n := 12)
    (lo := (295525249 / 1000000000)) (hi := (1182101 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 381) = 1/(381 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1182101 / 4000000) (-295525249 / 1000000000) (Real.log (381 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (227353427 / 1000000000) ≤ -Real.log (5120 / 6427) ∧
    -Real.log (5120 / 6427) ≤ (56838357 / 250000000) := by
  have h := checkLog_sound (w := (1307 / 11547)) (n := 12)
    (lo := (227353427 / 1000000000)) (hi := (56838357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6427 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6427 / 5120) = 1/(5120 / 6427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (227353427 / 1000000000) (56838357 / 250000000) (Real.log (6427 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6427 / 5120) = -Real.log (5120 / 6427) := by
    rw [show ((6427 / 5120) : ℝ) = ((5120 / 6427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (147369079 / 500000000) ≤ -Real.log (3813 / 5120) ∧
    -Real.log (3813 / 5120) ≤ (294738159 / 1000000000) := by
  have h := checkLog_sound (w := (1307 / 8933)) (n := 12)
    (lo := (147369079 / 500000000)) (hi := (294738159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3813) = 1/(3813 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-294738159 / 1000000000) (-147369079 / 500000000) (Real.log (3813 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (166369157 / 1000000000) ≤ -Real.log (1000000 / 1181009) ∧
    -Real.log (1000000 / 1181009) ≤ (83184579 / 500000000) := by
  have h := checkLog_sound (w := (181009 / 2181009)) (n := 12)
    (lo := (166369157 / 1000000000)) (hi := (83184579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181009 / 1000000) = 1/(1000000 / 1181009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (166369157 / 1000000000) (83184579 / 500000000) (Real.log (1181009 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1181009 / 1000000) = -Real.log (1000000 / 1181009) := by
    rw [show ((1181009 / 1000000) : ℝ) = ((1000000 / 1181009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (24960273 / 125000000) ≤ -Real.log (818991 / 1000000) ∧
    -Real.log (818991 / 1000000) ≤ (39936437 / 200000000) := by
  have h := checkLog_sound (w := (181009 / 1818991)) (n := 12)
    (lo := (24960273 / 125000000)) (hi := (39936437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818991) = 1/(818991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-39936437 / 200000000) (-24960273 / 125000000) (Real.log (818991 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41680969 / 250000000) ≤ -Real.log (250000 / 295357) ∧
    -Real.log (250000 / 295357) ≤ (166723877 / 1000000000) := by
  have h := checkLog_sound (w := (45357 / 545357)) (n := 12)
    (lo := (41680969 / 250000000)) (hi := (166723877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295357 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295357 / 250000) = 1/(250000 / 295357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41680969 / 250000000) (166723877 / 1000000000) (Real.log (295357 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (295357 / 250000) = -Real.log (250000 / 295357) := by
    rw [show ((295357 / 250000) : ℝ) = ((250000 / 295357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (312803 / 1562500) ≤ -Real.log (204643 / 250000) ∧
    -Real.log (204643 / 250000) ≤ (200193921 / 1000000000) := by
  have h := checkLog_sound (w := (45357 / 454643)) (n := 12)
    (lo := (312803 / 1562500)) (hi := (200193921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204643) = 1/(204643 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-200193921 / 1000000000) (-312803 / 1562500) (Real.log (204643 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (121478421 / 1000000000) ≤ -Real.log (200000 / 225833) ∧
    -Real.log (200000 / 225833) ≤ (60739211 / 500000000) := by
  have h := checkLog_sound (w := (25833 / 425833)) (n := 12)
    (lo := (121478421 / 1000000000)) (hi := (60739211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225833 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225833 / 200000) = 1/(200000 / 225833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (121478421 / 1000000000) (60739211 / 500000000) (Real.log (225833 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (225833 / 200000) = -Real.log (200000 / 225833) := by
    rw [show ((225833 / 200000) : ℝ) = ((200000 / 225833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (138302757 / 1000000000) ≤ -Real.log (174167 / 200000) ∧
    -Real.log (174167 / 200000) ≤ (69151379 / 500000000) := by
  have h := checkLog_sound (w := (25833 / 374167)) (n := 12)
    (lo := (138302757 / 1000000000)) (hi := (69151379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 174167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 174167) = 1/(174167 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-69151379 / 500000000) (-138302757 / 1000000000) (Real.log (174167 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7609281 / 62500000) ≤ -Real.log (100000 / 112947) ∧
    -Real.log (100000 / 112947) ≤ (121748497 / 1000000000) := by
  have h := checkLog_sound (w := (12947 / 212947)) (n := 12)
    (lo := (7609281 / 62500000)) (hi := (121748497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112947 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(112947 / 100000) = 1/(100000 / 112947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7609281 / 62500000) (121748497 / 1000000000) (Real.log (112947 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (112947 / 100000) = -Real.log (100000 / 112947) := by
    rw [show ((112947 / 100000) : ℝ) = ((100000 / 112947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (138653057 / 1000000000) ≤ -Real.log (87053 / 100000) ∧
    -Real.log (87053 / 100000) ≤ (69326529 / 500000000) := by
  have h := checkLog_sound (w := (12947 / 187053)) (n := 12)
    (lo := (138653057 / 1000000000)) (hi := (69326529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 87053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 87053) = 1/(87053 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-69326529 / 500000000) (-138653057 / 1000000000) (Real.log (87053 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (104418317 / 200000000) ≤ -Real.log (500000000000 / 842774718069) ∧
    -Real.log (500000000000 / 842774718069) ≤ (261045793 / 500000000) := by
  have h := checkLog_sound (w := (342774718069 / 1342774718069)) (n := 12)
    (lo := (104418317 / 200000000)) (hi := (261045793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((842774718069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(842774718069 / 500000000000) = 1/(500000000000 / 842774718069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (104418317 / 200000000) (261045793 / 500000000) (Real.log (842774718069 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (842774718069 / 500000000000) = -Real.log (500000000000 / 842774718069) := by
    rw [show ((842774718069 / 500000000000) : ℝ) = ((500000000000 / 842774718069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (523345349 / 1000000000) ≤ -Real.log (250000000000 / 421916010499) ∧
    -Real.log (250000000000 / 421916010499) ≤ (10466907 / 20000000) := by
  have h := checkLog_sound (w := (171916010499 / 671916010499)) (n := 12)
    (lo := (523345349 / 1000000000)) (hi := (10466907 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421916010499 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421916010499 / 250000000000) = 1/(250000000000 / 421916010499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (523345349 / 1000000000) (10466907 / 20000000) (Real.log (421916010499 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (421916010499 / 250000000000) = -Real.log (250000000000 / 421916010499) := by
    rw [show ((421916010499 / 250000000000) : ℝ) = ((250000000000 / 421916010499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (183025671 / 500000000) ≤ -Real.log (62500000000 / 90126829843) ∧
    -Real.log (62500000000 / 90126829843) ≤ (366051343 / 1000000000) := by
  have h := checkLog_sound (w := (27626829843 / 152626829843)) (n := 12)
    (lo := (183025671 / 500000000)) (hi := (366051343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90126829843 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90126829843 / 62500000000) = 1/(62500000000 / 90126829843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (183025671 / 500000000) (366051343 / 1000000000) (Real.log (90126829843 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (90126829843 / 62500000000) = -Real.log (62500000000 / 90126829843) := by
    rw [show ((90126829843 / 62500000000) : ℝ) = ((62500000000 / 90126829843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (91729449 / 250000000) ≤ -Real.log (250000000000 / 360819817927) ∧
    -Real.log (250000000000 / 360819817927) ≤ (366917797 / 1000000000) := by
  have h := checkLog_sound (w := (110819817927 / 610819817927)) (n := 12)
    (lo := (91729449 / 250000000)) (hi := (366917797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360819817927 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360819817927 / 250000000000) = 1/(250000000000 / 360819817927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (91729449 / 250000000) (366917797 / 1000000000) (Real.log (360819817927 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (360819817927 / 250000000000) = -Real.log (250000000000 / 360819817927) := by
    rw [show ((360819817927 / 250000000000) : ℝ) = ((250000000000 / 360819817927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (259781179 / 1000000000) ≤ -Real.log (500000000000 / 648323161103) ∧
    -Real.log (500000000000 / 648323161103) ≤ (12989059 / 50000000) := by
  have h := checkLog_sound (w := (148323161103 / 1148323161103)) (n := 12)
    (lo := (259781179 / 1000000000)) (hi := (12989059 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648323161103 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(648323161103 / 500000000000) = 1/(500000000000 / 648323161103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (259781179 / 1000000000) (12989059 / 50000000) (Real.log (648323161103 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (648323161103 / 500000000000) = -Real.log (500000000000 / 648323161103) := by
    rw [show ((648323161103 / 500000000000) : ℝ) = ((500000000000 / 648323161103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (260401553 / 1000000000) ≤ -Real.log (50000000000 / 64872548907) ∧
    -Real.log (50000000000 / 64872548907) ≤ (130200777 / 500000000) := by
  have h := checkLog_sound (w := (14872548907 / 114872548907)) (n := 12)
    (lo := (260401553 / 1000000000)) (hi := (130200777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64872548907 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64872548907 / 50000000000) = 1/(50000000000 / 64872548907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (260401553 / 1000000000) (130200777 / 500000000) (Real.log (64872548907 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (64872548907 / 50000000000) = -Real.log (50000000000 / 64872548907) := by
    rw [show ((64872548907 / 50000000000) : ℝ) = ((50000000000 / 64872548907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16904561 / 1000000000) ≤ -Real.log (9832375191 / 10000000000) ∧
    -Real.log (9832375191 / 10000000000) ≤ (8452281 / 500000000) := by
  have h := checkLog_sound (w := (167624809 / 19832375191)) (n := 12)
    (lo := (16904561 / 1000000000)) (hi := (8452281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9832375191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9832375191) = 1/(9832375191 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8452281 / 500000000) (-16904561 / 1000000000) (Real.log (9832375191 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3364867 / 200000000) ≤ -Real.log (39332656111 / 40000000000) ∧
    -Real.log (39332656111 / 40000000000) ≤ (1051521 / 62500000) := by
  have h := checkLog_sound (w := (667343889 / 79332656111)) (n := 12)
    (lo := (3364867 / 200000000)) (hi := (1051521 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39332656111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39332656111) = 1/(39332656111 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1051521 / 62500000) (-3364867 / 200000000) (Real.log (39332656111 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell009

end


