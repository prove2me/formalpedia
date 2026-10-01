-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0344Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0344Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:14:57.866932+00:00
-- url     : https://prove2.me/theorems/a9c4db6a-0725-4c40-aa91-94a54c7b4d5a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0344Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0345Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0344Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0345Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0346Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0347Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0348Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0349Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0350Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0344Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0345Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0346Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0347Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0348Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0349Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0350Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0344Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0345Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0346Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0347Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0348Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0349Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0350Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0344Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0345Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0346Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0347Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0348Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0349Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0350Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0344Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0344
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

theorem reflection_log_1_neg : (53391647 / 250000000) ≤ -Real.log (5120 / 6339) ∧
    -Real.log (5120 / 6339) ≤ (213566589 / 1000000000) := by
  have h := checkLog_sound (w := (1219 / 11459)) (n := 12)
    (lo := (53391647 / 250000000)) (hi := (213566589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6339 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6339 / 5120) = 1/(5120 / 6339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (53391647 / 250000000) (213566589 / 1000000000) (Real.log (6339 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6339 / 5120) = -Real.log (5120 / 6339) := by
    rw [show ((6339 / 5120) : ℝ) = ((5120 / 6339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (67980377 / 250000000) ≤ -Real.log (3901 / 5120) ∧
    -Real.log (3901 / 5120) ≤ (271921509 / 1000000000) := by
  have h := checkLog_sound (w := (1219 / 9021)) (n := 12)
    (lo := (67980377 / 250000000)) (hi := (271921509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3901) = 1/(3901 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-271921509 / 1000000000) (-67980377 / 250000000) (Real.log (3901 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (213329929 / 1000000000) ≤ -Real.log (2048 / 2535) ∧
    -Real.log (2048 / 2535) ≤ (21332993 / 100000000) := by
  have h := checkLog_sound (w := (487 / 4583)) (n := 12)
    (lo := (213329929 / 1000000000)) (hi := (21332993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2535 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2535 / 2048) = 1/(2048 / 2535) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (213329929 / 1000000000) (21332993 / 100000000) (Real.log (2535 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2535 / 2048) = -Real.log (2048 / 2535) := by
    rw [show ((2535 / 2048) : ℝ) = ((2048 / 2535) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (54307413 / 200000000) ≤ -Real.log (1561 / 2048) ∧
    -Real.log (1561 / 2048) ≤ (135768533 / 500000000) := by
  have h := checkLog_sound (w := (487 / 3609)) (n := 12)
    (lo := (54307413 / 200000000)) (hi := (135768533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1561) = 1/(1561 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-135768533 / 500000000) (-54307413 / 200000000) (Real.log (1561 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (77890433 / 200000000) ≤ -Real.log (2560 / 3779) ∧
    -Real.log (2560 / 3779) ≤ (194726083 / 500000000) := by
  have h := checkLog_sound (w := (1219 / 6339)) (n := 12)
    (lo := (77890433 / 200000000)) (hi := (194726083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3779 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3779 / 2560) = 1/(2560 / 3779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (77890433 / 200000000) (194726083 / 500000000) (Real.log (3779 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3779 / 2560) = -Real.log (2560 / 3779) := by
    rw [show ((3779 / 2560) : ℝ) = ((2560 / 3779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (323295827 / 500000000) ≤ -Real.log (1341 / 2560) ∧
    -Real.log (1341 / 2560) ≤ (129318331 / 200000000) := by
  have h := checkLog_sound (w := (1219 / 3901)) (n := 12)
    (lo := (323295827 / 500000000)) (hi := (129318331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1341) = 1/(1341 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-129318331 / 200000000) (-323295827 / 500000000) (Real.log (1341 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97263789 / 250000000) ≤ -Real.log (1024 / 1511) ∧
    -Real.log (1024 / 1511) ≤ (389055157 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 2535)) (n := 12)
    (lo := (97263789 / 250000000)) (hi := (389055157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1511 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1511 / 1024) = 1/(1024 / 1511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97263789 / 250000000) (389055157 / 1000000000) (Real.log (1511 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1511 / 1024) = -Real.log (1024 / 1511) := by
    rw [show ((1511 / 1024) : ℝ) = ((1024 / 1511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (645473711 / 1000000000) ≤ -Real.log (537 / 1024) ∧
    -Real.log (537 / 1024) ≤ (40342107 / 62500000) := by
  have h := checkLog_sound (w := (487 / 1561)) (n := 12)
    (lo := (645473711 / 1000000000)) (hi := (40342107 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 537) = 1/(537 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-40342107 / 62500000) (-645473711 / 1000000000) (Real.log (537 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36564857 / 125000000) ≤ -Real.log (500000 / 669899) ∧
    -Real.log (500000 / 669899) ≤ (292518857 / 1000000000) := by
  have h := checkLog_sound (w := (169899 / 1169899)) (n := 12)
    (lo := (36564857 / 125000000)) (hi := (292518857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669899 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669899 / 500000) = 1/(500000 / 669899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36564857 / 125000000) (292518857 / 1000000000) (Real.log (669899 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (669899 / 500000) = -Real.log (500000 / 669899) := by
    rw [show ((669899 / 500000) : ℝ) = ((500000 / 669899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41520943 / 100000000) ≤ -Real.log (330101 / 500000) ∧
    -Real.log (330101 / 500000) ≤ (415209431 / 1000000000) := by
  have h := checkLog_sound (w := (169899 / 830101)) (n := 12)
    (lo := (41520943 / 100000000)) (hi := (415209431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330101) = 1/(330101 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-415209431 / 1000000000) (-41520943 / 100000000) (Real.log (330101 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146419501 / 500000000) ≤ -Real.log (1000000 / 1340227) ∧
    -Real.log (1000000 / 1340227) ≤ (292839003 / 1000000000) := by
  have h := checkLog_sound (w := (340227 / 2340227)) (n := 12)
    (lo := (146419501 / 500000000)) (hi := (292839003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1340227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1340227 / 1000000) = 1/(1000000 / 1340227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146419501 / 500000000) (292839003 / 1000000000) (Real.log (1340227 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1340227 / 1000000) = -Real.log (1000000 / 1340227) := by
    rw [show ((1340227 / 1000000) : ℝ) = ((1000000 / 1340227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (207929721 / 500000000) ≤ -Real.log (659773 / 1000000) ∧
    -Real.log (659773 / 1000000) ≤ (415859443 / 1000000000) := by
  have h := checkLog_sound (w := (340227 / 1659773)) (n := 12)
    (lo := (207929721 / 500000000)) (hi := (415859443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 659773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 659773) = 1/(659773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-415859443 / 1000000000) (-207929721 / 500000000) (Real.log (659773 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (110852859 / 500000000) ≤ -Real.log (250000 / 312051) ∧
    -Real.log (250000 / 312051) ≤ (221705719 / 1000000000) := by
  have h := checkLog_sound (w := (62051 / 562051)) (n := 12)
    (lo := (110852859 / 500000000)) (hi := (221705719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312051 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312051 / 250000) = 1/(250000 / 312051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (110852859 / 500000000) (221705719 / 1000000000) (Real.log (312051 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (312051 / 250000) = -Real.log (250000 / 312051) := by
    rw [show ((312051 / 250000) : ℝ) = ((250000 / 312051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (71322567 / 250000000) ≤ -Real.log (187949 / 250000) ∧
    -Real.log (187949 / 250000) ≤ (285290269 / 1000000000) := by
  have h := checkLog_sound (w := (62051 / 437949)) (n := 12)
    (lo := (71322567 / 250000000)) (hi := (285290269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187949) = 1/(187949 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-285290269 / 1000000000) (-71322567 / 250000000) (Real.log (187949 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (221974067 / 1000000000) ≤ -Real.log (1000000 / 1248539) ∧
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


theorem reflection_log_15 : Bounds (221974067 / 1000000000) (55493517 / 250000000) (Real.log (1248539 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1248539 / 1000000) = -Real.log (1000000 / 1248539) := by
    rw [show ((1248539 / 1000000) : ℝ) = ((1000000 / 1248539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (285735967 / 1000000000) ≤ -Real.log (751461 / 1000000) ∧
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


theorem reflection_log_16 : Bounds (-8929249 / 31250000) (-285735967 / 1000000000) (Real.log (751461 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (141545657 / 200000000) ≤ -Real.log (250000000000 / 507343964423) ∧
    -Real.log (250000000000 / 507343964423) ≤ (707728287 / 1000000000) := by
  have h := checkLog_sound (w := (7343964423 / 1007343964423)) (n := 12)
    (lo := (2916221 / 200000000)) (hi := (7290553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((507343964423 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(507343964423 / 500000000000) = 1/(250000000000 / 507343964423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (141545657 / 200000000) (707728287 / 1000000000) (Real.log (507343964423 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (507343964423 / 250000000000) = -Real.log (250000000000 / 507343964423) := by
    rw [show ((507343964423 / 250000000000) : ℝ) = ((250000000000 / 507343964423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (177174611 / 250000000) ≤ -Real.log (500000000000 / 1015672814741) ∧
    -Real.log (500000000000 / 1015672814741) ≤ (354349223 / 500000000) := by
  have h := checkLog_sound (w := (15672814741 / 2015672814741)) (n := 12)
    (lo := (485977 / 31250000)) (hi := (3110253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1015672814741 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1015672814741 / 1000000000000) = 1/(500000000000 / 1015672814741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (177174611 / 250000000) (354349223 / 500000000) (Real.log (1015672814741 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1015672814741 / 500000000000) = -Real.log (500000000000 / 1015672814741) := by
    rw [show ((1015672814741 / 500000000000) : ℝ) = ((500000000000 / 1015672814741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (253497993 / 500000000) ≤ -Real.log (500000000000 / 830148072083) ∧
    -Real.log (500000000000 / 830148072083) ≤ (506995987 / 1000000000) := by
  have h := checkLog_sound (w := (330148072083 / 1330148072083)) (n := 12)
    (lo := (253497993 / 500000000)) (hi := (506995987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((830148072083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(830148072083 / 500000000000) = 1/(500000000000 / 830148072083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (253497993 / 500000000) (506995987 / 1000000000) (Real.log (830148072083 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (830148072083 / 500000000000) = -Real.log (500000000000 / 830148072083) := by
    rw [show ((830148072083 / 500000000000) : ℝ) = ((500000000000 / 830148072083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (101542007 / 200000000) ≤ -Real.log (500000000000 / 830741049769) ∧
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


theorem reflection_log_20 : Bounds (101542007 / 200000000) (126927509 / 250000000) (Real.log (830741049769 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (830741049769 / 500000000000) = -Real.log (500000000000 / 830741049769) := by
    rw [show ((830741049769 / 500000000000) : ℝ) = ((500000000000 / 830741049769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0344

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0345Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0345
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

theorem reflection_log_1_neg : (213329929 / 1000000000) ≤ -Real.log (2048 / 2535) ∧
    -Real.log (2048 / 2535) ≤ (21332993 / 100000000) := by
  have h := checkLog_sound (w := (487 / 4583)) (n := 12)
    (lo := (213329929 / 1000000000)) (hi := (21332993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2535 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2535 / 2048) = 1/(2048 / 2535) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (213329929 / 1000000000) (21332993 / 100000000) (Real.log (2535 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2535 / 2048) = -Real.log (2048 / 2535) := by
    rw [show ((2535 / 2048) : ℝ) = ((2048 / 2535) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (54307413 / 200000000) ≤ -Real.log (1561 / 2048) ∧
    -Real.log (1561 / 2048) ≤ (135768533 / 500000000) := by
  have h := checkLog_sound (w := (487 / 3609)) (n := 12)
    (lo := (54307413 / 200000000)) (hi := (135768533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1561) = 1/(1561 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-135768533 / 500000000) (-54307413 / 200000000) (Real.log (1561 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42618643 / 200000000) ≤ -Real.log (80 / 99) ∧
    -Real.log (80 / 99) ≤ (6659163 / 31250000) := by
  have h := checkLog_sound (w := (19 / 179)) (n := 12)
    (lo := (42618643 / 200000000)) (hi := (6659163 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99 / 80) = 1/(80 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42618643 / 200000000) (6659163 / 31250000) (Real.log (99 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (99 / 80) = -Real.log (80 / 99) := by
    rw [show ((99 / 80) : ℝ) = ((80 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (27115277 / 100000000) ≤ -Real.log (61 / 80) ∧
    -Real.log (61 / 80) ≤ (271152771 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 141)) (n := 12)
    (lo := (27115277 / 100000000)) (hi := (271152771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 61) = 1/(61 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-271152771 / 1000000000) (-27115277 / 100000000) (Real.log (61 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (97263789 / 250000000) ≤ -Real.log (1024 / 1511) ∧
    -Real.log (1024 / 1511) ≤ (389055157 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 2535)) (n := 12)
    (lo := (97263789 / 250000000)) (hi := (389055157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1511 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1511 / 1024) = 1/(1024 / 1511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (97263789 / 250000000) (389055157 / 1000000000) (Real.log (1511 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1511 / 1024) = -Real.log (1024 / 1511) := by
    rw [show ((1511 / 1024) : ℝ) = ((1024 / 1511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (645473711 / 1000000000) ≤ -Real.log (537 / 1024) ∧
    -Real.log (537 / 1024) ≤ (40342107 / 62500000) := by
  have h := checkLog_sound (w := (487 / 1561)) (n := 12)
    (lo := (645473711 / 1000000000)) (hi := (40342107 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 537) = 1/(537 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-40342107 / 62500000) (-645473711 / 1000000000) (Real.log (537 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (388657989 / 1000000000) ≤ -Real.log (40 / 59) ∧
    -Real.log (40 / 59) ≤ (38865799 / 100000000) := by
  have h := checkLog_sound (w := (19 / 99)) (n := 12)
    (lo := (388657989 / 1000000000)) (hi := (38865799 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59 / 40) = 1/(40 / 59) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (388657989 / 1000000000) (38865799 / 100000000) (Real.log (59 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (59 / 40) = -Real.log (40 / 59) := by
    rw [show ((59 / 40) : ℝ) = ((40 / 59) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (80544627 / 125000000) ≤ -Real.log (21 / 40) ∧
    -Real.log (21 / 40) ≤ (644357017 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 21) = 1/(21 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-644357017 / 1000000000) (-80544627 / 125000000) (Real.log (21 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (146099677 / 500000000) ≤ -Real.log (100000 / 133937) ∧
    -Real.log (100000 / 133937) ≤ (58439871 / 200000000) := by
  have h := checkLog_sound (w := (33937 / 233937)) (n := 12)
    (lo := (146099677 / 500000000)) (hi := (58439871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133937 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133937 / 100000) = 1/(100000 / 133937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (146099677 / 500000000) (58439871 / 200000000) (Real.log (133937 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (133937 / 100000) = -Real.log (100000 / 133937) := by
    rw [show ((133937 / 100000) : ℝ) = ((100000 / 133937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (414561353 / 1000000000) ≤ -Real.log (66063 / 100000) ∧
    -Real.log (66063 / 100000) ≤ (207280677 / 500000000) := by
  have h := checkLog_sound (w := (33937 / 166063)) (n := 12)
    (lo := (414561353 / 1000000000)) (hi := (207280677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 66063) = 1/(66063 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-207280677 / 500000000) (-414561353 / 1000000000) (Real.log (66063 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146259801 / 500000000) ≤ -Real.log (1000000 / 1339799) ∧
    -Real.log (1000000 / 1339799) ≤ (292519603 / 1000000000) := by
  have h := checkLog_sound (w := (339799 / 2339799)) (n := 12)
    (lo := (146259801 / 500000000)) (hi := (292519603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1339799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1339799 / 1000000) = 1/(1000000 / 1339799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146259801 / 500000000) (292519603 / 1000000000) (Real.log (1339799 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1339799 / 1000000) = -Real.log (1000000 / 1339799) := by
    rw [show ((1339799 / 1000000) : ℝ) = ((1000000 / 1339799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6487671 / 15625000) ≤ -Real.log (660201 / 1000000) ∧
    -Real.log (660201 / 1000000) ≤ (83042189 / 200000000) := by
  have h := checkLog_sound (w := (339799 / 1660201)) (n := 12)
    (lo := (6487671 / 15625000)) (hi := (83042189 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 660201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 660201) = 1/(660201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-83042189 / 200000000) (-6487671 / 15625000) (Real.log (660201 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (221438899 / 1000000000) ≤ -Real.log (1000000 / 1247871) ∧
    -Real.log (1000000 / 1247871) ≤ (2214389 / 10000000) := by
  have h := checkLog_sound (w := (247871 / 2247871)) (n := 12)
    (lo := (221438899 / 1000000000)) (hi := (2214389 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247871 / 1000000) = 1/(1000000 / 1247871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (221438899 / 1000000000) (2214389 / 10000000) (Real.log (1247871 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1247871 / 1000000) = -Real.log (1000000 / 1247871) := by
    rw [show ((1247871 / 1000000) : ℝ) = ((1000000 / 1247871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (284847427 / 1000000000) ≤ -Real.log (752129 / 1000000) ∧
    -Real.log (752129 / 1000000) ≤ (71211857 / 250000000) := by
  have h := checkLog_sound (w := (247871 / 1752129)) (n := 12)
    (lo := (284847427 / 1000000000)) (hi := (71211857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 752129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 752129) = 1/(752129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-71211857 / 250000000) (-284847427 / 1000000000) (Real.log (752129 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (221706519 / 1000000000) ≤ -Real.log (200000 / 249641) ∧
    -Real.log (200000 / 249641) ≤ (5542663 / 25000000) := by
  have h := checkLog_sound (w := (49641 / 449641)) (n := 12)
    (lo := (221706519 / 1000000000)) (hi := (5542663 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249641 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249641 / 200000) = 1/(200000 / 249641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (221706519 / 1000000000) (5542663 / 25000000) (Real.log (249641 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (249641 / 200000) = -Real.log (200000 / 249641) := by
    rw [show ((249641 / 200000) : ℝ) = ((200000 / 249641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (142645799 / 500000000) ≤ -Real.log (150359 / 200000) ∧
    -Real.log (150359 / 200000) ≤ (285291599 / 1000000000) := by
  have h := checkLog_sound (w := (49641 / 350359)) (n := 12)
    (lo := (142645799 / 500000000)) (hi := (285291599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 150359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 150359) = 1/(150359 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-285291599 / 1000000000) (-142645799 / 500000000) (Real.log (150359 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (706760707 / 1000000000) ≤ -Real.log (62500000000 / 126713326673) ∧
    -Real.log (62500000000 / 126713326673) ≤ (706760709 / 1000000000) := by
  have h := checkLog_sound (w := (1713326673 / 251713326673)) (n := 12)
    (lo := (13613527 / 1000000000)) (hi := (1701691 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126713326673 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126713326673 / 125000000000) = 1/(62500000000 / 126713326673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (706760707 / 1000000000) (706760709 / 1000000000) (Real.log (126713326673 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (126713326673 / 62500000000) = -Real.log (62500000000 / 126713326673) := by
    rw [show ((126713326673 / 62500000000) : ℝ) = ((62500000000 / 126713326673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (707730547 / 1000000000) ≤ -Real.log (50000000000 / 101469022313) ∧
    -Real.log (50000000000 / 101469022313) ≤ (707730549 / 1000000000) := by
  have h := checkLog_sound (w := (1469022313 / 201469022313)) (n := 12)
    (lo := (14583367 / 1000000000)) (hi := (1822921 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101469022313 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(101469022313 / 100000000000) = 1/(50000000000 / 101469022313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (707730547 / 1000000000) (707730549 / 1000000000) (Real.log (101469022313 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (101469022313 / 50000000000) = -Real.log (50000000000 / 101469022313) := by
    rw [show ((101469022313 / 50000000000) : ℝ) = ((50000000000 / 101469022313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (253143163 / 500000000) ≤ -Real.log (500000000000 / 829559158069) ∧
    -Real.log (500000000000 / 829559158069) ≤ (506286327 / 1000000000) := by
  have h := checkLog_sound (w := (329559158069 / 1329559158069)) (n := 12)
    (lo := (253143163 / 500000000)) (hi := (506286327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829559158069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829559158069 / 500000000000) = 1/(500000000000 / 829559158069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (253143163 / 500000000) (506286327 / 1000000000) (Real.log (829559158069 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (829559158069 / 500000000000) = -Real.log (500000000000 / 829559158069) := by
    rw [show ((829559158069 / 500000000000) : ℝ) = ((500000000000 / 829559158069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (506998117 / 1000000000) ≤ -Real.log (25000000000 / 41507492069) ∧
    -Real.log (25000000000 / 41507492069) ≤ (253499059 / 500000000) := by
  have h := checkLog_sound (w := (16507492069 / 66507492069)) (n := 12)
    (lo := (506998117 / 1000000000)) (hi := (253499059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41507492069 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41507492069 / 25000000000) = 1/(25000000000 / 41507492069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (506998117 / 1000000000) (253499059 / 500000000) (Real.log (41507492069 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (41507492069 / 25000000000) = -Real.log (25000000000 / 41507492069) := by
    rw [show ((41507492069 / 25000000000) : ℝ) = ((25000000000 / 41507492069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0345

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0346Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0346
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

theorem reflection_log_1_neg : (42618643 / 200000000) ≤ -Real.log (80 / 99) ∧
    -Real.log (80 / 99) ≤ (6659163 / 31250000) := by
  have h := checkLog_sound (w := (19 / 179)) (n := 12)
    (lo := (42618643 / 200000000)) (hi := (6659163 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99 / 80) = 1/(80 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42618643 / 200000000) (6659163 / 31250000) (Real.log (99 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (99 / 80) = -Real.log (80 / 99) := by
    rw [show ((99 / 80) : ℝ) = ((80 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (27115277 / 100000000) ≤ -Real.log (61 / 80) ∧
    -Real.log (61 / 80) ≤ (271152771 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 141)) (n := 12)
    (lo := (27115277 / 100000000)) (hi := (271152771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 61) = 1/(61 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-271152771 / 1000000000) (-27115277 / 100000000) (Real.log (61 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42571289 / 200000000) ≤ -Real.log (10240 / 12669) ∧
    -Real.log (10240 / 12669) ≤ (106428223 / 500000000) := by
  have h := checkLog_sound (w := (2429 / 22909)) (n := 12)
    (lo := (42571289 / 200000000)) (hi := (106428223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12669 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12669 / 10240) = 1/(10240 / 12669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42571289 / 200000000) (106428223 / 500000000) (Real.log (12669 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12669 / 10240) = -Real.log (10240 / 12669) := by
    rw [show ((12669 / 10240) : ℝ) = ((10240 / 12669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (135384311 / 500000000) ≤ -Real.log (7811 / 10240) ∧
    -Real.log (7811 / 10240) ≤ (270768623 / 1000000000) := by
  have h := checkLog_sound (w := (2429 / 18051)) (n := 12)
    (lo := (135384311 / 500000000)) (hi := (270768623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7811) = 1/(7811 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-270768623 / 1000000000) (-135384311 / 500000000) (Real.log (7811 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (388657989 / 1000000000) ≤ -Real.log (40 / 59) ∧
    -Real.log (40 / 59) ≤ (38865799 / 100000000) := by
  have h := checkLog_sound (w := (19 / 99)) (n := 12)
    (lo := (388657989 / 1000000000)) (hi := (38865799 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59 / 40) = 1/(40 / 59) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (388657989 / 1000000000) (38865799 / 100000000) (Real.log (59 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (59 / 40) = -Real.log (40 / 59) := by
    rw [show ((59 / 40) : ℝ) = ((40 / 59) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (80544627 / 125000000) ≤ -Real.log (21 / 40) ∧
    -Real.log (21 / 40) ≤ (644357017 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 21) = 1/(21 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-644357017 / 1000000000) (-80544627 / 125000000) (Real.log (21 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (77652133 / 200000000) ≤ -Real.log (5120 / 7549) ∧
    -Real.log (5120 / 7549) ≤ (194130333 / 500000000) := by
  have h := checkLog_sound (w := (2429 / 12669)) (n := 12)
    (lo := (77652133 / 200000000)) (hi := (194130333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7549 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7549 / 5120) = 1/(5120 / 7549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (77652133 / 200000000) (194130333 / 500000000) (Real.log (7549 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7549 / 5120) = -Real.log (5120 / 7549) := by
    rw [show ((7549 / 5120) : ℝ) = ((5120 / 7549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (643241567 / 1000000000) ≤ -Real.log (2691 / 5120) ∧
    -Real.log (2691 / 5120) ≤ (20101299 / 31250000) := by
  have h := checkLog_sound (w := (2429 / 7811)) (n := 12)
    (lo := (643241567 / 1000000000)) (hi := (20101299 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2691) = 1/(2691 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20101299 / 31250000) (-643241567 / 1000000000) (Real.log (2691 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (291879003 / 1000000000) ≤ -Real.log (1000000 / 1338941) ∧
    -Real.log (1000000 / 1338941) ≤ (72969751 / 250000000) := by
  have h := checkLog_sound (w := (338941 / 2338941)) (n := 12)
    (lo := (291879003 / 1000000000)) (hi := (72969751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1338941 / 1000000) = 1/(1000000 / 1338941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (291879003 / 1000000000) (72969751 / 250000000) (Real.log (1338941 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1338941 / 1000000) = -Real.log (1000000 / 1338941) := by
    rw [show ((1338941 / 1000000) : ℝ) = ((1000000 / 1338941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (51739023 / 125000000) ≤ -Real.log (661059 / 1000000) ∧
    -Real.log (661059 / 1000000) ≤ (82782437 / 200000000) := by
  have h := checkLog_sound (w := (338941 / 1661059)) (n := 12)
    (lo := (51739023 / 125000000)) (hi := (82782437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 661059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 661059) = 1/(661059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-82782437 / 200000000) (-51739023 / 125000000) (Real.log (661059 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (2922001 / 10000000) ≤ -Real.log (1000000 / 1339371) ∧
    -Real.log (1000000 / 1339371) ≤ (292200101 / 1000000000) := by
  have h := checkLog_sound (w := (339371 / 2339371)) (n := 12)
    (lo := (2922001 / 10000000)) (hi := (292200101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1339371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1339371 / 1000000) = 1/(1000000 / 1339371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (2922001 / 10000000) (292200101 / 1000000000) (Real.log (1339371 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1339371 / 1000000) = -Real.log (1000000 / 1339371) := by
    rw [show ((1339371 / 1000000) : ℝ) = ((1000000 / 1339371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (414562867 / 1000000000) ≤ -Real.log (660629 / 1000000) ∧
    -Real.log (660629 / 1000000) ≤ (103640717 / 250000000) := by
  have h := checkLog_sound (w := (339371 / 1660629)) (n := 12)
    (lo := (414562867 / 1000000000)) (hi := (103640717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 660629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 660629) = 1/(660629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-103640717 / 250000000) (-414562867 / 1000000000) (Real.log (660629 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (221171207 / 1000000000) ≤ -Real.log (1000000 / 1247537) ∧
    -Real.log (1000000 / 1247537) ≤ (27646401 / 125000000) := by
  have h := checkLog_sound (w := (247537 / 2247537)) (n := 12)
    (lo := (221171207 / 1000000000)) (hi := (27646401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247537 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247537 / 1000000) = 1/(1000000 / 1247537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (221171207 / 1000000000) (27646401 / 125000000) (Real.log (1247537 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1247537 / 1000000) = -Real.log (1000000 / 1247537) := by
    rw [show ((1247537 / 1000000) : ℝ) = ((1000000 / 1247537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (284403453 / 1000000000) ≤ -Real.log (752463 / 1000000) ∧
    -Real.log (752463 / 1000000) ≤ (142201727 / 500000000) := by
  have h := checkLog_sound (w := (247537 / 1752463)) (n := 12)
    (lo := (284403453 / 1000000000)) (hi := (142201727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 752463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 752463) = 1/(752463 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-142201727 / 500000000) (-284403453 / 1000000000) (Real.log (752463 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (2214397 / 10000000) ≤ -Real.log (15625 / 19498) ∧
    -Real.log (15625 / 19498) ≤ (221439701 / 1000000000) := by
  have h := checkLog_sound (w := (3873 / 35123)) (n := 12)
    (lo := (2214397 / 10000000)) (hi := (221439701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19498 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19498 / 15625) = 1/(15625 / 19498) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (2214397 / 10000000) (221439701 / 1000000000) (Real.log (19498 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (19498 / 15625) = -Real.log (15625 / 19498) := by
    rw [show ((19498 / 15625) : ℝ) = ((15625 / 19498) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (71212189 / 250000000) ≤ -Real.log (11752 / 15625) ∧
    -Real.log (11752 / 15625) ≤ (284848757 / 1000000000) := by
  have h := checkLog_sound (w := (3873 / 27377)) (n := 12)
    (lo := (71212189 / 250000000)) (hi := (284848757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11752) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11752) = 1/(11752 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-284848757 / 1000000000) (-71212189 / 250000000) (Real.log (11752 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (352895593 / 500000000) ≤ -Real.log (500000000000 / 1012724280283) ∧
    -Real.log (500000000000 / 1012724280283) ≤ (176447797 / 250000000) := by
  have h := checkLog_sound (w := (12724280283 / 2012724280283)) (n := 12)
    (lo := (6322003 / 500000000)) (hi := (12644007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1012724280283 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1012724280283 / 1000000000000) = 1/(500000000000 / 1012724280283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (352895593 / 500000000) (176447797 / 250000000) (Real.log (1012724280283 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1012724280283 / 500000000000) = -Real.log (500000000000 / 1012724280283) := by
    rw [show ((1012724280283 / 500000000000) : ℝ) = ((500000000000 / 1012724280283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (706762967 / 1000000000) ≤ -Real.log (62500000000 / 126713613087) ∧
    -Real.log (62500000000 / 126713613087) ≤ (706762969 / 1000000000) := by
  have h := checkLog_sound (w := (1713613087 / 251713613087)) (n := 12)
    (lo := (13615787 / 1000000000)) (hi := (3403947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126713613087 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126713613087 / 125000000000) = 1/(62500000000 / 126713613087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (706762967 / 1000000000) (706762969 / 1000000000) (Real.log (126713613087 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (126713613087 / 62500000000) = -Real.log (62500000000 / 126713613087) := by
    rw [show ((126713613087 / 62500000000) : ℝ) = ((62500000000 / 126713613087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25278733 / 50000000) ≤ -Real.log (25000000000 / 41448449957) ∧
    -Real.log (25000000000 / 41448449957) ≤ (505574661 / 1000000000) := by
  have h := checkLog_sound (w := (16448449957 / 66448449957)) (n := 12)
    (lo := (25278733 / 50000000)) (hi := (505574661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41448449957 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41448449957 / 25000000000) = 1/(25000000000 / 41448449957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (25278733 / 50000000) (505574661 / 1000000000) (Real.log (41448449957 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (41448449957 / 25000000000) = -Real.log (25000000000 / 41448449957) := by
    rw [show ((41448449957 / 25000000000) : ℝ) = ((25000000000 / 41448449957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (506288457 / 1000000000) ≤ -Real.log (2500000000 / 4147804629) ∧
    -Real.log (2500000000 / 4147804629) ≤ (253144229 / 500000000) := by
  have h := checkLog_sound (w := (1647804629 / 6647804629)) (n := 12)
    (lo := (506288457 / 1000000000)) (hi := (253144229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4147804629 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4147804629 / 2500000000) = 1/(2500000000 / 4147804629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (506288457 / 1000000000) (253144229 / 500000000) (Real.log (4147804629 / 2500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4147804629 / 2500000000) = -Real.log (2500000000 / 4147804629) := by
    rw [show ((4147804629 / 2500000000) : ℝ) = ((2500000000 / 4147804629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0346

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0347Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0347
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

theorem reflection_log_1_neg : (42571289 / 200000000) ≤ -Real.log (10240 / 12669) ∧
    -Real.log (10240 / 12669) ≤ (106428223 / 500000000) := by
  have h := checkLog_sound (w := (2429 / 22909)) (n := 12)
    (lo := (42571289 / 200000000)) (hi := (106428223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12669 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12669 / 10240) = 1/(10240 / 12669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42571289 / 200000000) (106428223 / 500000000) (Real.log (12669 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12669 / 10240) = -Real.log (10240 / 12669) := by
    rw [show ((12669 / 10240) : ℝ) = ((10240 / 12669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (135384311 / 500000000) ≤ -Real.log (7811 / 10240) ∧
    -Real.log (7811 / 10240) ≤ (270768623 / 1000000000) := by
  have h := checkLog_sound (w := (2429 / 18051)) (n := 12)
    (lo := (135384311 / 500000000)) (hi := (270768623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7811) = 1/(7811 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-270768623 / 1000000000) (-135384311 / 500000000) (Real.log (7811 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (106309809 / 500000000) ≤ -Real.log (5120 / 6333) ∧
    -Real.log (5120 / 6333) ≤ (212619619 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 11453)) (n := 12)
    (lo := (106309809 / 500000000)) (hi := (212619619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6333 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6333 / 5120) = 1/(5120 / 6333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (106309809 / 500000000) (212619619 / 1000000000) (Real.log (6333 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6333 / 5120) = -Real.log (5120 / 6333) := by
    rw [show ((6333 / 5120) : ℝ) = ((5120 / 6333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (135192311 / 500000000) ≤ -Real.log (3907 / 5120) ∧
    -Real.log (3907 / 5120) ≤ (270384623 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 9027)) (n := 12)
    (lo := (135192311 / 500000000)) (hi := (270384623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3907) = 1/(3907 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-270384623 / 1000000000) (-135192311 / 500000000) (Real.log (3907 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (77652133 / 200000000) ≤ -Real.log (5120 / 7549) ∧
    -Real.log (5120 / 7549) ≤ (194130333 / 500000000) := by
  have h := checkLog_sound (w := (2429 / 12669)) (n := 12)
    (lo := (77652133 / 200000000)) (hi := (194130333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7549 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7549 / 5120) = 1/(5120 / 7549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (77652133 / 200000000) (194130333 / 500000000) (Real.log (7549 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7549 / 5120) = -Real.log (5120 / 7549) := by
    rw [show ((7549 / 5120) : ℝ) = ((5120 / 7549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (643241567 / 1000000000) ≤ -Real.log (2691 / 5120) ∧
    -Real.log (2691 / 5120) ≤ (20101299 / 31250000) := by
  have h := checkLog_sound (w := (2429 / 7811)) (n := 12)
    (lo := (643241567 / 1000000000)) (hi := (20101299 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2691) = 1/(2691 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-20101299 / 31250000) (-643241567 / 1000000000) (Real.log (2691 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (193931591 / 500000000) ≤ -Real.log (2560 / 3773) ∧
    -Real.log (2560 / 3773) ≤ (387863183 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 6333)) (n := 12)
    (lo := (193931591 / 500000000)) (hi := (387863183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3773 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3773 / 2560) = 1/(2560 / 3773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (193931591 / 500000000) (387863183 / 1000000000) (Real.log (3773 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3773 / 2560) = -Real.log (2560 / 3773) := by
    rw [show ((3773 / 2560) : ℝ) = ((2560 / 3773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (642127361 / 1000000000) ≤ -Real.log (1347 / 2560) ∧
    -Real.log (1347 / 2560) ≤ (321063681 / 500000000) := by
  have h := checkLog_sound (w := (1213 / 3907)) (n := 12)
    (lo := (642127361 / 1000000000)) (hi := (321063681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1347) = 1/(1347 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-321063681 / 500000000) (-642127361 / 1000000000) (Real.log (1347 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2277807 / 7812500) ≤ -Real.log (1000000 / 1338513) ∧
    -Real.log (1000000 / 1338513) ≤ (291559297 / 1000000000) := by
  have h := checkLog_sound (w := (338513 / 2338513)) (n := 12)
    (lo := (2277807 / 7812500)) (hi := (291559297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1338513 / 1000000) = 1/(1000000 / 1338513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2277807 / 7812500) (291559297 / 1000000000) (Real.log (1338513 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1338513 / 1000000) = -Real.log (1000000 / 1338513) := by
    rw [show ((1338513 / 1000000) : ℝ) = ((1000000 / 1338513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (413264947 / 1000000000) ≤ -Real.log (661487 / 1000000) ∧
    -Real.log (661487 / 1000000) ≤ (103316237 / 250000000) := by
  have h := checkLog_sound (w := (338513 / 1661487)) (n := 12)
    (lo := (413264947 / 1000000000)) (hi := (103316237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 661487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 661487) = 1/(661487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-103316237 / 250000000) (-413264947 / 1000000000) (Real.log (661487 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (18242531 / 62500000) ≤ -Real.log (1000000 / 1338943) ∧
    -Real.log (1000000 / 1338943) ≤ (291880497 / 1000000000) := by
  have h := checkLog_sound (w := (338943 / 2338943)) (n := 12)
    (lo := (18242531 / 62500000)) (hi := (291880497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1338943 / 1000000) = 1/(1000000 / 1338943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (18242531 / 62500000) (291880497 / 1000000000) (Real.log (1338943 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1338943 / 1000000) = -Real.log (1000000 / 1338943) := by
    rw [show ((1338943 / 1000000) : ℝ) = ((1000000 / 1338943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (413915209 / 1000000000) ≤ -Real.log (661057 / 1000000) ∧
    -Real.log (661057 / 1000000) ≤ (41391521 / 100000000) := by
  have h := checkLog_sound (w := (338943 / 1661057)) (n := 12)
    (lo := (413915209 / 1000000000)) (hi := (41391521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 661057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 661057) = 1/(661057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-41391521 / 100000000) (-413915209 / 1000000000) (Real.log (661057 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (44180849 / 200000000) ≤ -Real.log (250000 / 311801) ∧
    -Real.log (250000 / 311801) ≤ (110452123 / 500000000) := by
  have h := checkLog_sound (w := (61801 / 561801)) (n := 12)
    (lo := (44180849 / 200000000)) (hi := (110452123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311801 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311801 / 250000) = 1/(250000 / 311801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (44180849 / 200000000) (110452123 / 500000000) (Real.log (311801 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (311801 / 250000) = -Real.log (250000 / 311801) := by
    rw [show ((311801 / 250000) : ℝ) = ((250000 / 311801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (70990251 / 250000000) ≤ -Real.log (188199 / 250000) ∧
    -Real.log (188199 / 250000) ≤ (56792201 / 200000000) := by
  have h := checkLog_sound (w := (61801 / 438199)) (n := 12)
    (lo := (70990251 / 250000000)) (hi := (56792201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188199) = 1/(188199 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-56792201 / 200000000) (-70990251 / 250000000) (Real.log (188199 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (221172009 / 1000000000) ≤ -Real.log (500000 / 623769) ∧
    -Real.log (500000 / 623769) ≤ (22117201 / 100000000) := by
  have h := checkLog_sound (w := (123769 / 1123769)) (n := 12)
    (lo := (221172009 / 1000000000)) (hi := (22117201 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623769 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623769 / 500000) = 1/(500000 / 623769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (221172009 / 1000000000) (22117201 / 100000000) (Real.log (623769 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (623769 / 500000) = -Real.log (500000 / 623769) := by
    rw [show ((623769 / 500000) : ℝ) = ((500000 / 623769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (284404781 / 1000000000) ≤ -Real.log (376231 / 500000) ∧
    -Real.log (376231 / 500000) ≤ (142202391 / 500000000) := by
  have h := checkLog_sound (w := (123769 / 876231)) (n := 12)
    (lo := (284404781 / 1000000000)) (hi := (142202391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 376231) = 1/(376231 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-142202391 / 500000000) (-284404781 / 1000000000) (Real.log (376231 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (704824243 / 1000000000) ≤ -Real.log (250000000000 / 505872753357) ∧
    -Real.log (250000000000 / 505872753357) ≤ (140964849 / 200000000) := by
  have h := checkLog_sound (w := (5872753357 / 1005872753357)) (n := 12)
    (lo := (11677063 / 1000000000)) (hi := (1459633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((505872753357 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(505872753357 / 500000000000) = 1/(250000000000 / 505872753357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (704824243 / 1000000000) (140964849 / 200000000) (Real.log (505872753357 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (505872753357 / 250000000000) = -Real.log (250000000000 / 505872753357) := by
    rw [show ((505872753357 / 250000000000) : ℝ) = ((250000000000 / 505872753357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (352897853 / 500000000) ≤ -Real.log (500000000000 / 1012728856967) ∧
    -Real.log (500000000000 / 1012728856967) ≤ (176448927 / 250000000) := by
  have h := checkLog_sound (w := (12728856967 / 2012728856967)) (n := 12)
    (lo := (6324263 / 500000000)) (hi := (12648527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1012728856967 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1012728856967 / 1000000000000) = 1/(500000000000 / 1012728856967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (352897853 / 500000000) (176448927 / 250000000) (Real.log (1012728856967 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1012728856967 / 500000000000) = -Real.log (500000000000 / 1012728856967) := by
    rw [show ((1012728856967 / 500000000000) : ℝ) = ((500000000000 / 1012728856967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2019461 / 4000000) ≤ -Real.log (250000000000 / 414190564243) ∧
    -Real.log (250000000000 / 414190564243) ≤ (504865251 / 1000000000) := by
  have h := checkLog_sound (w := (164190564243 / 664190564243)) (n := 12)
    (lo := (2019461 / 4000000)) (hi := (504865251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414190564243 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414190564243 / 250000000000) = 1/(250000000000 / 414190564243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2019461 / 4000000) (504865251 / 1000000000) (Real.log (414190564243 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (414190564243 / 250000000000) = -Real.log (250000000000 / 414190564243) := by
    rw [show ((414190564243 / 250000000000) : ℝ) = ((250000000000 / 414190564243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (505576791 / 1000000000) ≤ -Real.log (250000000000 / 414485382651) ∧
    -Real.log (250000000000 / 414485382651) ≤ (63197099 / 125000000) := by
  have h := checkLog_sound (w := (164485382651 / 664485382651)) (n := 12)
    (lo := (505576791 / 1000000000)) (hi := (63197099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414485382651 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414485382651 / 250000000000) = 1/(250000000000 / 414485382651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (505576791 / 1000000000) (63197099 / 125000000) (Real.log (414485382651 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (414485382651 / 250000000000) = -Real.log (250000000000 / 414485382651) := by
    rw [show ((414485382651 / 250000000000) : ℝ) = ((250000000000 / 414485382651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0347

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0348Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0348
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

theorem reflection_log_1_neg : (106309809 / 500000000) ≤ -Real.log (5120 / 6333) ∧
    -Real.log (5120 / 6333) ≤ (212619619 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 11453)) (n := 12)
    (lo := (106309809 / 500000000)) (hi := (212619619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6333 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6333 / 5120) = 1/(5120 / 6333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (106309809 / 500000000) (212619619 / 1000000000) (Real.log (6333 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6333 / 5120) = -Real.log (5120 / 6333) := by
    rw [show ((6333 / 5120) : ℝ) = ((5120 / 6333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (135192311 / 500000000) ≤ -Real.log (3907 / 5120) ∧
    -Real.log (3907 / 5120) ≤ (270384623 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 9027)) (n := 12)
    (lo := (135192311 / 500000000)) (hi := (270384623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3907) = 1/(3907 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-270384623 / 1000000000) (-135192311 / 500000000) (Real.log (3907 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42476547 / 200000000) ≤ -Real.log (10240 / 12663) ∧
    -Real.log (10240 / 12663) ≤ (13273921 / 62500000) := by
  have h := checkLog_sound (w := (2423 / 22903)) (n := 12)
    (lo := (42476547 / 200000000)) (hi := (13273921 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12663 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12663 / 10240) = 1/(10240 / 12663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42476547 / 200000000) (13273921 / 62500000) (Real.log (12663 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12663 / 10240) = -Real.log (10240 / 12663) := by
    rw [show ((12663 / 10240) : ℝ) = ((10240 / 12663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (27000077 / 100000000) ≤ -Real.log (7817 / 10240) ∧
    -Real.log (7817 / 10240) ≤ (270000771 / 1000000000) := by
  have h := checkLog_sound (w := (2423 / 18057)) (n := 12)
    (lo := (27000077 / 100000000)) (hi := (270000771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7817) = 1/(7817 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-270000771 / 1000000000) (-27000077 / 100000000) (Real.log (7817 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (193931591 / 500000000) ≤ -Real.log (2560 / 3773) ∧
    -Real.log (2560 / 3773) ≤ (387863183 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 6333)) (n := 12)
    (lo := (193931591 / 500000000)) (hi := (387863183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3773 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3773 / 2560) = 1/(2560 / 3773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (193931591 / 500000000) (387863183 / 1000000000) (Real.log (3773 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3773 / 2560) = -Real.log (2560 / 3773) := by
    rw [show ((3773 / 2560) : ℝ) = ((2560 / 3773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (642127361 / 1000000000) ≤ -Real.log (1347 / 2560) ∧
    -Real.log (1347 / 2560) ≤ (321063681 / 500000000) := by
  have h := checkLog_sound (w := (1213 / 3907)) (n := 12)
    (lo := (642127361 / 1000000000)) (hi := (321063681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1347) = 1/(1347 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-321063681 / 500000000) (-642127361 / 1000000000) (Real.log (1347 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (387465541 / 1000000000) ≤ -Real.log (5120 / 7543) ∧
    -Real.log (5120 / 7543) ≤ (193732771 / 500000000) := by
  have h := checkLog_sound (w := (2423 / 12663)) (n := 12)
    (lo := (387465541 / 1000000000)) (hi := (193732771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7543 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7543 / 5120) = 1/(5120 / 7543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (387465541 / 1000000000) (193732771 / 500000000) (Real.log (7543 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7543 / 5120) = -Real.log (5120 / 7543) := by
    rw [show ((7543 / 5120) : ℝ) = ((5120 / 7543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (320507197 / 500000000) ≤ -Real.log (2697 / 5120) ∧
    -Real.log (2697 / 5120) ≤ (128202879 / 200000000) := by
  have h := checkLog_sound (w := (2423 / 7817)) (n := 12)
    (lo := (320507197 / 500000000)) (hi := (128202879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2697) = 1/(2697 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-128202879 / 200000000) (-320507197 / 500000000) (Real.log (2697 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (291239487 / 1000000000) ≤ -Real.log (200000 / 267617) ∧
    -Real.log (200000 / 267617) ≤ (4550617 / 15625000) := by
  have h := checkLog_sound (w := (67617 / 467617)) (n := 12)
    (lo := (291239487 / 1000000000)) (hi := (4550617 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267617 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267617 / 200000) = 1/(200000 / 267617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (291239487 / 1000000000) (4550617 / 15625000) (Real.log (267617 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (267617 / 200000) = -Real.log (200000 / 267617) := by
    rw [show ((267617 / 200000) : ℝ) = ((200000 / 267617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41261813 / 100000000) ≤ -Real.log (132383 / 200000) ∧
    -Real.log (132383 / 200000) ≤ (412618131 / 1000000000) := by
  have h := checkLog_sound (w := (67617 / 332383)) (n := 12)
    (lo := (41261813 / 100000000)) (hi := (412618131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 132383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 132383) = 1/(132383 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-412618131 / 1000000000) (-41261813 / 100000000) (Real.log (132383 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (291560043 / 1000000000) ≤ -Real.log (500000 / 669257) ∧
    -Real.log (500000 / 669257) ≤ (72890011 / 250000000) := by
  have h := checkLog_sound (w := (169257 / 1169257)) (n := 12)
    (lo := (291560043 / 1000000000)) (hi := (72890011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669257 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669257 / 500000) = 1/(500000 / 669257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (291560043 / 1000000000) (72890011 / 250000000) (Real.log (669257 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (669257 / 500000) = -Real.log (500000 / 669257) := by
    rw [show ((669257 / 500000) : ℝ) = ((500000 / 669257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (413266459 / 1000000000) ≤ -Real.log (330743 / 500000) ∧
    -Real.log (330743 / 500000) ≤ (20663323 / 50000000) := by
  have h := checkLog_sound (w := (169257 / 830743)) (n := 12)
    (lo := (413266459 / 1000000000)) (hi := (20663323 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330743) = 1/(330743 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-20663323 / 50000000) (-413266459 / 1000000000) (Real.log (330743 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (220637213 / 1000000000) ≤ -Real.log (1000000 / 1246871) ∧
    -Real.log (1000000 / 1246871) ≤ (110318607 / 500000000) := by
  have h := checkLog_sound (w := (246871 / 2246871)) (n := 12)
    (lo := (220637213 / 1000000000)) (hi := (110318607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246871 / 1000000) = 1/(1000000 / 1246871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (220637213 / 1000000000) (110318607 / 500000000) (Real.log (1246871 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1246871 / 1000000) = -Real.log (1000000 / 1246871) := by
    rw [show ((1246871 / 1000000) : ℝ) = ((1000000 / 1246871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (283518751 / 1000000000) ≤ -Real.log (753129 / 1000000) ∧
    -Real.log (753129 / 1000000) ≤ (8859961 / 31250000) := by
  have h := checkLog_sound (w := (246871 / 1753129)) (n := 12)
    (lo := (283518751 / 1000000000)) (hi := (8859961 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753129) = 1/(753129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8859961 / 31250000) (-283518751 / 1000000000) (Real.log (753129 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (220905047 / 1000000000) ≤ -Real.log (200000 / 249441) ∧
    -Real.log (200000 / 249441) ≤ (27613131 / 125000000) := by
  have h := checkLog_sound (w := (49441 / 449441)) (n := 12)
    (lo := (220905047 / 1000000000)) (hi := (27613131 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249441 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249441 / 200000) = 1/(200000 / 249441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (220905047 / 1000000000) (27613131 / 125000000) (Real.log (249441 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (249441 / 200000) = -Real.log (200000 / 249441) := by
    rw [show ((249441 / 200000) : ℝ) = ((200000 / 249441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (70990583 / 250000000) ≤ -Real.log (150559 / 200000) ∧
    -Real.log (150559 / 200000) ≤ (283962333 / 1000000000) := by
  have h := checkLog_sound (w := (49441 / 350559)) (n := 12)
    (lo := (70990583 / 250000000)) (hi := (283962333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 150559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 150559) = 1/(150559 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-283962333 / 1000000000) (-70990583 / 250000000) (Real.log (150559 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (43991101 / 62500000) ≤ -Real.log (7812500000 / 15793249983) ∧
    -Real.log (7812500000 / 15793249983) ≤ (351928809 / 500000000) := by
  have h := checkLog_sound (w := (168249983 / 31418249983)) (n := 12)
    (lo := (2677609 / 250000000)) (hi := (10710437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15793249983 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15793249983 / 15625000000) = 1/(7812500000 / 15793249983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (43991101 / 62500000) (351928809 / 500000000) (Real.log (15793249983 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (15793249983 / 7812500000) = -Real.log (7812500000 / 15793249983) := by
    rw [show ((15793249983 / 7812500000) : ℝ) = ((7812500000 / 15793249983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (352413251 / 500000000) ≤ -Real.log (500000000000 / 1011747792093) ∧
    -Real.log (500000000000 / 1011747792093) ≤ (88103313 / 125000000) := by
  have h := checkLog_sound (w := (11747792093 / 2011747792093)) (n := 12)
    (lo := (5839661 / 500000000)) (hi := (11679323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1011747792093 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1011747792093 / 1000000000000) = 1/(500000000000 / 1011747792093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (352413251 / 500000000) (88103313 / 125000000) (Real.log (1011747792093 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1011747792093 / 500000000000) = -Real.log (500000000000 / 1011747792093) := by
    rw [show ((1011747792093 / 500000000000) : ℝ) = ((500000000000 / 1011747792093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (126038991 / 250000000) ≤ -Real.log (125000000000 / 206948444423) ∧
    -Real.log (125000000000 / 206948444423) ≤ (100831193 / 200000000) := by
  have h := checkLog_sound (w := (81948444423 / 331948444423)) (n := 12)
    (lo := (126038991 / 250000000)) (hi := (100831193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206948444423 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206948444423 / 125000000000) = 1/(125000000000 / 206948444423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (126038991 / 250000000) (100831193 / 200000000) (Real.log (206948444423 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (206948444423 / 125000000000) = -Real.log (125000000000 / 206948444423) := by
    rw [show ((206948444423 / 125000000000) : ℝ) = ((125000000000 / 206948444423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (25243369 / 50000000) ≤ -Real.log (250000000000 / 414191446543) ∧
    -Real.log (250000000000 / 414191446543) ≤ (504867381 / 1000000000) := by
  have h := checkLog_sound (w := (164191446543 / 664191446543)) (n := 12)
    (lo := (25243369 / 50000000)) (hi := (504867381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414191446543 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414191446543 / 250000000000) = 1/(250000000000 / 414191446543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (25243369 / 50000000) (504867381 / 1000000000) (Real.log (414191446543 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (414191446543 / 250000000000) = -Real.log (250000000000 / 414191446543) := by
    rw [show ((414191446543 / 250000000000) : ℝ) = ((250000000000 / 414191446543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0348

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0349Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0349
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

theorem reflection_log_1_neg : (42476547 / 200000000) ≤ -Real.log (10240 / 12663) ∧
    -Real.log (10240 / 12663) ≤ (13273921 / 62500000) := by
  have h := checkLog_sound (w := (2423 / 22903)) (n := 12)
    (lo := (42476547 / 200000000)) (hi := (13273921 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12663 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12663 / 10240) = 1/(10240 / 12663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42476547 / 200000000) (13273921 / 62500000) (Real.log (12663 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12663 / 10240) = -Real.log (10240 / 12663) := by
    rw [show ((12663 / 10240) : ℝ) = ((10240 / 12663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (27000077 / 100000000) ≤ -Real.log (7817 / 10240) ∧
    -Real.log (7817 / 10240) ≤ (270000771 / 1000000000) := by
  have h := checkLog_sound (w := (2423 / 18057)) (n := 12)
    (lo := (27000077 / 100000000)) (hi := (270000771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7817) = 1/(7817 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-270000771 / 1000000000) (-27000077 / 100000000) (Real.log (7817 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (212145797 / 1000000000) ≤ -Real.log (512 / 633) ∧
    -Real.log (512 / 633) ≤ (106072899 / 500000000) := by
  have h := checkLog_sound (w := (121 / 1145)) (n := 12)
    (lo := (212145797 / 1000000000)) (hi := (106072899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633 / 512) = 1/(512 / 633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (212145797 / 1000000000) (106072899 / 500000000) (Real.log (633 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (633 / 512) = -Real.log (512 / 633) := by
    rw [show ((633 / 512) : ℝ) = ((512 / 633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (53923413 / 200000000) ≤ -Real.log (391 / 512) ∧
    -Real.log (391 / 512) ≤ (134808533 / 500000000) := by
  have h := checkLog_sound (w := (121 / 903)) (n := 12)
    (lo := (53923413 / 200000000)) (hi := (134808533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 391) = 1/(391 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-134808533 / 500000000) (-53923413 / 200000000) (Real.log (391 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (387465541 / 1000000000) ≤ -Real.log (5120 / 7543) ∧
    -Real.log (5120 / 7543) ≤ (193732771 / 500000000) := by
  have h := checkLog_sound (w := (2423 / 12663)) (n := 12)
    (lo := (387465541 / 1000000000)) (hi := (193732771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7543 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7543 / 5120) = 1/(5120 / 7543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (387465541 / 1000000000) (193732771 / 500000000) (Real.log (7543 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7543 / 5120) = -Real.log (5120 / 7543) := by
    rw [show ((7543 / 5120) : ℝ) = ((5120 / 7543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (320507197 / 500000000) ≤ -Real.log (2697 / 5120) ∧
    -Real.log (2697 / 5120) ≤ (128202879 / 200000000) := by
  have h := checkLog_sound (w := (2423 / 7817)) (n := 12)
    (lo := (320507197 / 500000000)) (hi := (128202879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2697) = 1/(2697 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-128202879 / 200000000) (-320507197 / 500000000) (Real.log (2697 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (193533871 / 500000000) ≤ -Real.log (256 / 377) ∧
    -Real.log (256 / 377) ≤ (387067743 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 633)) (n := 12)
    (lo := (193533871 / 500000000)) (hi := (387067743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377 / 256) = 1/(256 / 377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (193533871 / 500000000) (387067743 / 1000000000) (Real.log (377 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (377 / 256) = -Real.log (256 / 377) := by
    rw [show ((377 / 256) : ℝ) = ((256 / 377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (319951333 / 500000000) ≤ -Real.log (135 / 256) ∧
    -Real.log (135 / 256) ≤ (639902667 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 391)) (n := 12)
    (lo := (319951333 / 500000000)) (hi := (639902667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 135) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 135) = 1/(135 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-639902667 / 1000000000) (-319951333 / 500000000) (Real.log (135 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36364947 / 125000000) ≤ -Real.log (1000000 / 1337657) ∧
    -Real.log (1000000 / 1337657) ≤ (290919577 / 1000000000) := by
  have h := checkLog_sound (w := (337657 / 2337657)) (n := 12)
    (lo := (36364947 / 125000000)) (hi := (290919577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337657 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337657 / 1000000) = 1/(1000000 / 1337657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36364947 / 125000000) (290919577 / 1000000000) (Real.log (1337657 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1337657 / 1000000) = -Real.log (1000000 / 1337657) := by
    rw [show ((1337657 / 1000000) : ℝ) = ((1000000 / 1337657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41197173 / 100000000) ≤ -Real.log (662343 / 1000000) ∧
    -Real.log (662343 / 1000000) ≤ (411971731 / 1000000000) := by
  have h := checkLog_sound (w := (337657 / 1662343)) (n := 12)
    (lo := (41197173 / 100000000)) (hi := (411971731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 662343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 662343) = 1/(662343 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-411971731 / 1000000000) (-41197173 / 100000000) (Real.log (662343 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145620117 / 500000000) ≤ -Real.log (500000 / 669043) ∧
    -Real.log (500000 / 669043) ≤ (58248047 / 200000000) := by
  have h := checkLog_sound (w := (169043 / 1169043)) (n := 12)
    (lo := (145620117 / 500000000)) (hi := (58248047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669043 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669043 / 500000) = 1/(500000 / 669043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145620117 / 500000000) (58248047 / 200000000) (Real.log (669043 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (669043 / 500000) = -Real.log (500000 / 669043) := by
    rw [show ((669043 / 500000) : ℝ) = ((500000 / 669043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (10315491 / 25000000) ≤ -Real.log (330957 / 500000) ∧
    -Real.log (330957 / 500000) ≤ (412619641 / 1000000000) := by
  have h := checkLog_sound (w := (169043 / 830957)) (n := 12)
    (lo := (10315491 / 25000000)) (hi := (412619641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330957) = 1/(330957 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-412619641 / 1000000000) (-10315491 / 25000000) (Real.log (330957 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (55092527 / 250000000) ≤ -Real.log (500000 / 623269) ∧
    -Real.log (500000 / 623269) ≤ (220370109 / 1000000000) := by
  have h := checkLog_sound (w := (123269 / 1123269)) (n := 12)
    (lo := (55092527 / 250000000)) (hi := (220370109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623269 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623269 / 500000) = 1/(500000 / 623269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (55092527 / 250000000) (220370109 / 1000000000) (Real.log (623269 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (623269 / 500000) = -Real.log (500000 / 623269) := by
    rw [show ((623269 / 500000) : ℝ) = ((500000 / 623269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (283076693 / 1000000000) ≤ -Real.log (376731 / 500000) ∧
    -Real.log (376731 / 500000) ≤ (141538347 / 500000000) := by
  have h := checkLog_sound (w := (123269 / 876731)) (n := 12)
    (lo := (283076693 / 1000000000)) (hi := (141538347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 376731) = 1/(376731 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-141538347 / 500000000) (-283076693 / 1000000000) (Real.log (376731 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (44127603 / 200000000) ≤ -Real.log (125000 / 155859) ∧
    -Real.log (125000 / 155859) ≤ (3447469 / 15625000) := by
  have h := checkLog_sound (w := (30859 / 280859)) (n := 12)
    (lo := (44127603 / 200000000)) (hi := (3447469 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155859 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155859 / 125000) = 1/(125000 / 155859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (44127603 / 200000000) (3447469 / 15625000) (Real.log (155859 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (155859 / 125000) = -Real.log (125000 / 155859) := by
    rw [show ((155859 / 125000) : ℝ) = ((125000 / 155859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (141760039 / 500000000) ≤ -Real.log (94141 / 125000) ∧
    -Real.log (94141 / 125000) ≤ (283520079 / 1000000000) := by
  have h := checkLog_sound (w := (30859 / 219141)) (n := 12)
    (lo := (141760039 / 500000000)) (hi := (283520079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94141) = 1/(94141 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-283520079 / 1000000000) (-141760039 / 500000000) (Real.log (94141 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (140578261 / 200000000) ≤ -Real.log (500000000000 / 1009791754423) ∧
    -Real.log (500000000000 / 1009791754423) ≤ (702891307 / 1000000000) := by
  have h := checkLog_sound (w := (9791754423 / 2009791754423)) (n := 12)
    (lo := (77953 / 8000000)) (hi := (4872063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1009791754423 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1009791754423 / 1000000000000) = 1/(500000000000 / 1009791754423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (140578261 / 200000000) (702891307 / 1000000000) (Real.log (1009791754423 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1009791754423 / 500000000000) = -Real.log (500000000000 / 1009791754423) := by
    rw [show ((1009791754423 / 500000000000) : ℝ) = ((500000000000 / 1009791754423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (351929937 / 500000000) ≤ -Real.log (62500000000 / 126346285167) ∧
    -Real.log (62500000000 / 126346285167) ≤ (175964969 / 250000000) := by
  have h := checkLog_sound (w := (1346285167 / 251346285167)) (n := 12)
    (lo := (5356347 / 500000000)) (hi := (2142539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126346285167 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126346285167 / 125000000000) = 1/(62500000000 / 126346285167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (351929937 / 500000000) (175964969 / 250000000) (Real.log (126346285167 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (126346285167 / 62500000000) = -Real.log (62500000000 / 126346285167) := by
    rw [show ((126346285167 / 62500000000) : ℝ) = ((62500000000 / 126346285167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (251723401 / 500000000) ≤ -Real.log (50000000000 / 82720694607) ∧
    -Real.log (50000000000 / 82720694607) ≤ (503446803 / 1000000000) := by
  have h := checkLog_sound (w := (32720694607 / 132720694607)) (n := 12)
    (lo := (251723401 / 500000000)) (hi := (503446803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82720694607 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82720694607 / 50000000000) = 1/(50000000000 / 82720694607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (251723401 / 500000000) (503446803 / 1000000000) (Real.log (82720694607 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (82720694607 / 50000000000) = -Real.log (50000000000 / 82720694607) := by
    rw [show ((82720694607 / 50000000000) : ℝ) = ((50000000000 / 82720694607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (504158093 / 1000000000) ≤ -Real.log (125000000000 / 206948885183) ∧
    -Real.log (125000000000 / 206948885183) ≤ (252079047 / 500000000) := by
  have h := checkLog_sound (w := (81948885183 / 331948885183)) (n := 12)
    (lo := (504158093 / 1000000000)) (hi := (252079047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206948885183 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206948885183 / 125000000000) = 1/(125000000000 / 206948885183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (504158093 / 1000000000) (252079047 / 500000000) (Real.log (206948885183 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (206948885183 / 125000000000) = -Real.log (125000000000 / 206948885183) := by
    rw [show ((206948885183 / 125000000000) : ℝ) = ((125000000000 / 206948885183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0349

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0350Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0350
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

theorem reflection_log_1_neg : (212145797 / 1000000000) ≤ -Real.log (512 / 633) ∧
    -Real.log (512 / 633) ≤ (106072899 / 500000000) := by
  have h := checkLog_sound (w := (121 / 1145)) (n := 12)
    (lo := (212145797 / 1000000000)) (hi := (106072899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633 / 512) = 1/(512 / 633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (212145797 / 1000000000) (106072899 / 500000000) (Real.log (633 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (633 / 512) = -Real.log (512 / 633) := by
    rw [show ((633 / 512) : ℝ) = ((512 / 633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (53923413 / 200000000) ≤ -Real.log (391 / 512) ∧
    -Real.log (391 / 512) ≤ (134808533 / 500000000) := by
  have h := checkLog_sound (w := (121 / 903)) (n := 12)
    (lo := (53923413 / 200000000)) (hi := (134808533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 391) = 1/(391 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-134808533 / 500000000) (-53923413 / 200000000) (Real.log (391 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (105954401 / 500000000) ≤ -Real.log (10240 / 12657) ∧
    -Real.log (10240 / 12657) ≤ (211908803 / 1000000000) := by
  have h := checkLog_sound (w := (2417 / 22897)) (n := 12)
    (lo := (105954401 / 500000000)) (hi := (211908803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12657 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12657 / 10240) = 1/(10240 / 12657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (105954401 / 500000000) (211908803 / 1000000000) (Real.log (12657 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12657 / 10240) = -Real.log (10240 / 12657) := by
    rw [show ((12657 / 10240) : ℝ) = ((10240 / 12657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (134616753 / 500000000) ≤ -Real.log (7823 / 10240) ∧
    -Real.log (7823 / 10240) ≤ (269233507 / 1000000000) := by
  have h := checkLog_sound (w := (2417 / 18063)) (n := 12)
    (lo := (134616753 / 500000000)) (hi := (269233507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7823) = 1/(7823 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-269233507 / 1000000000) (-134616753 / 500000000) (Real.log (7823 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (193533871 / 500000000) ≤ -Real.log (256 / 377) ∧
    -Real.log (256 / 377) ≤ (387067743 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 633)) (n := 12)
    (lo := (193533871 / 500000000)) (hi := (387067743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377 / 256) = 1/(256 / 377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (193533871 / 500000000) (387067743 / 1000000000) (Real.log (377 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (377 / 256) = -Real.log (256 / 377) := by
    rw [show ((377 / 256) : ℝ) = ((256 / 377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (319951333 / 500000000) ≤ -Real.log (135 / 256) ∧
    -Real.log (135 / 256) ≤ (639902667 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 391)) (n := 12)
    (lo := (319951333 / 500000000)) (hi := (639902667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 135) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 135) = 1/(135 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-639902667 / 1000000000) (-319951333 / 500000000) (Real.log (135 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (77333957 / 200000000) ≤ -Real.log (5120 / 7537) ∧
    -Real.log (5120 / 7537) ≤ (193334893 / 500000000) := by
  have h := checkLog_sound (w := (2417 / 12657)) (n := 12)
    (lo := (77333957 / 200000000)) (hi := (193334893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7537 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7537 / 5120) = 1/(5120 / 7537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (77333957 / 200000000) (193334893 / 500000000) (Real.log (7537 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7537 / 5120) = -Real.log (5120 / 7537) := by
    rw [show ((7537 / 5120) : ℝ) = ((5120 / 7537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (638792171 / 1000000000) ≤ -Real.log (2703 / 5120) ∧
    -Real.log (2703 / 5120) ≤ (159698043 / 250000000) := by
  have h := checkLog_sound (w := (2417 / 7823)) (n := 12)
    (lo := (638792171 / 1000000000)) (hi := (159698043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2703) = 1/(2703 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-159698043 / 250000000) (-638792171 / 1000000000) (Real.log (2703 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (145299781 / 500000000) ≤ -Real.log (1000000 / 1337229) ∧
    -Real.log (1000000 / 1337229) ≤ (290599563 / 1000000000) := by
  have h := checkLog_sound (w := (337229 / 2337229)) (n := 12)
    (lo := (145299781 / 500000000)) (hi := (290599563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337229 / 1000000) = 1/(1000000 / 1337229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (145299781 / 500000000) (290599563 / 1000000000) (Real.log (1337229 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1337229 / 1000000) = -Real.log (1000000 / 1337229) := by
    rw [show ((1337229 / 1000000) : ℝ) = ((1000000 / 1337229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (102831437 / 250000000) ≤ -Real.log (662771 / 1000000) ∧
    -Real.log (662771 / 1000000) ≤ (411325749 / 1000000000) := by
  have h := checkLog_sound (w := (337229 / 1662771)) (n := 12)
    (lo := (102831437 / 250000000)) (hi := (411325749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 662771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 662771) = 1/(662771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-411325749 / 1000000000) (-102831437 / 250000000) (Real.log (662771 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (290920323 / 1000000000) ≤ -Real.log (500000 / 668829) ∧
    -Real.log (500000 / 668829) ≤ (72730081 / 250000000) := by
  have h := checkLog_sound (w := (168829 / 1168829)) (n := 12)
    (lo := (290920323 / 1000000000)) (hi := (72730081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668829 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668829 / 500000) = 1/(500000 / 668829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (290920323 / 1000000000) (72730081 / 250000000) (Real.log (668829 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (668829 / 500000) = -Real.log (500000 / 668829) := by
    rw [show ((668829 / 500000) : ℝ) = ((500000 / 668829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (10299331 / 25000000) ≤ -Real.log (331171 / 500000) ∧
    -Real.log (331171 / 500000) ≤ (411973241 / 1000000000) := by
  have h := checkLog_sound (w := (168829 / 831171)) (n := 12)
    (lo := (10299331 / 25000000)) (hi := (411973241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 331171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 331171) = 1/(331171 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-411973241 / 1000000000) (-10299331 / 25000000) (Real.log (331171 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (44020747 / 200000000) ≤ -Real.log (500000 / 623103) ∧
    -Real.log (500000 / 623103) ≤ (27512967 / 125000000) := by
  have h := checkLog_sound (w := (123103 / 1123103)) (n := 12)
    (lo := (44020747 / 200000000)) (hi := (27512967 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623103 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623103 / 500000) = 1/(500000 / 623103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (44020747 / 200000000) (27512967 / 125000000) (Real.log (623103 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (623103 / 500000) = -Real.log (500000 / 623103) := by
    rw [show ((623103 / 500000) : ℝ) = ((500000 / 623103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (282636157 / 1000000000) ≤ -Real.log (376897 / 500000) ∧
    -Real.log (376897 / 500000) ≤ (141318079 / 500000000) := by
  have h := checkLog_sound (w := (123103 / 876897)) (n := 12)
    (lo := (282636157 / 1000000000)) (hi := (141318079 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 376897) = 1/(376897 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-141318079 / 500000000) (-282636157 / 1000000000) (Real.log (376897 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (220370911 / 1000000000) ≤ -Real.log (1000000 / 1246539) ∧
    -Real.log (1000000 / 1246539) ≤ (6886591 / 31250000) := by
  have h := checkLog_sound (w := (246539 / 2246539)) (n := 12)
    (lo := (220370911 / 1000000000)) (hi := (6886591 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246539 / 1000000) = 1/(1000000 / 1246539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (220370911 / 1000000000) (6886591 / 31250000) (Real.log (1246539 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1246539 / 1000000) = -Real.log (1000000 / 1246539) := by
    rw [show ((1246539 / 1000000) : ℝ) = ((1000000 / 1246539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (14153901 / 50000000) ≤ -Real.log (753461 / 1000000) ∧
    -Real.log (753461 / 1000000) ≤ (283078021 / 1000000000) := by
  have h := checkLog_sound (w := (246539 / 1753461)) (n := 12)
    (lo := (14153901 / 50000000)) (hi := (283078021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753461) = 1/(753461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-283078021 / 1000000000) (-14153901 / 50000000) (Real.log (753461 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (70192531 / 100000000) ≤ -Real.log (1250000000 / 2522041927) ∧
    -Real.log (1250000000 / 2522041927) ≤ (10967583 / 15625000) := by
  have h := checkLog_sound (w := (22041927 / 5022041927)) (n := 12)
    (lo := (877813 / 100000000)) (hi := (8778131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2522041927 / 2500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2522041927 / 2500000000) = 1/(1250000000 / 2522041927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (70192531 / 100000000) (10967583 / 15625000) (Real.log (2522041927 / 1250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2522041927 / 1250000000) = -Real.log (1250000000 / 2522041927) := by
    rw [show ((2522041927 / 1250000000) : ℝ) = ((1250000000 / 2522041927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (702893563 / 1000000000) ≤ -Real.log (250000000000 / 504897016949) ∧
    -Real.log (250000000000 / 504897016949) ≤ (140578713 / 200000000) := by
  have h := checkLog_sound (w := (4897016949 / 1004897016949)) (n := 12)
    (lo := (9746383 / 1000000000)) (hi := (609149 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((504897016949 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(504897016949 / 500000000000) = 1/(250000000000 / 504897016949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (702893563 / 1000000000) (140578713 / 200000000) (Real.log (504897016949 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (504897016949 / 250000000000) = -Real.log (250000000000 / 504897016949) := by
    rw [show ((504897016949 / 250000000000) : ℝ) = ((250000000000 / 504897016949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (502739893 / 1000000000) ≤ -Real.log (100000000000 / 165324478571) ∧
    -Real.log (100000000000 / 165324478571) ≤ (251369947 / 500000000) := by
  have h := checkLog_sound (w := (65324478571 / 265324478571)) (n := 12)
    (lo := (502739893 / 1000000000)) (hi := (251369947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165324478571 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165324478571 / 100000000000) = 1/(100000000000 / 165324478571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (502739893 / 1000000000) (251369947 / 500000000) (Real.log (165324478571 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (165324478571 / 100000000000) = -Real.log (100000000000 / 165324478571) := by
    rw [show ((165324478571 / 100000000000) : ℝ) = ((100000000000 / 165324478571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (503448931 / 1000000000) ≤ -Real.log (500000000000 / 827208707551) ∧
    -Real.log (500000000000 / 827208707551) ≤ (125862233 / 250000000) := by
  have h := checkLog_sound (w := (327208707551 / 1327208707551)) (n := 12)
    (lo := (503448931 / 1000000000)) (hi := (125862233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827208707551 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827208707551 / 500000000000) = 1/(500000000000 / 827208707551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (503448931 / 1000000000) (125862233 / 250000000) (Real.log (827208707551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (827208707551 / 500000000000) = -Real.log (500000000000 / 827208707551) := by
    rw [show ((827208707551 / 500000000000) : ℝ) = ((500000000000 / 827208707551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0350

end


