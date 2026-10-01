-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0428Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0428Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:23:07.205931+00:00
-- url     : https://prove2.me/theorems/029f2510-4599-4a02-8d10-66c99a751f4c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0428Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0429Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0428Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0429Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0430Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0431Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0432Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0433Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0434Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0428Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0429Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0430Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0431Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0432Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0433Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0434Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0428Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0429Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0430Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0431Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0432Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0433Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0434Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0428Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0429Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0430Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0431Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0432Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0433Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0434Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0428Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0428
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

theorem reflection_log_1_neg : (24186179 / 125000000) ≤ -Real.log (5120 / 6213) ∧
    -Real.log (5120 / 6213) ≤ (193489433 / 1000000000) := by
  have h := checkLog_sound (w := (1093 / 11333)) (n := 12)
    (lo := (24186179 / 125000000)) (hi := (193489433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6213 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6213 / 5120) = 1/(5120 / 6213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24186179 / 125000000) (193489433 / 1000000000) (Real.log (6213 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6213 / 5120) = -Real.log (5120 / 6213) := by
    rw [show ((6213 / 5120) : ℝ) = ((5120 / 6213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (240132757 / 1000000000) ≤ -Real.log (4027 / 5120) ∧
    -Real.log (4027 / 5120) ≤ (120066379 / 500000000) := by
  have h := checkLog_sound (w := (1093 / 9147)) (n := 12)
    (lo := (240132757 / 1000000000)) (hi := (120066379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4027) = 1/(4027 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-120066379 / 500000000) (-240132757 / 1000000000) (Real.log (4027 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (193247973 / 1000000000) ≤ -Real.log (10240 / 12423) ∧
    -Real.log (10240 / 12423) ≤ (96623987 / 500000000) := by
  have h := checkLog_sound (w := (2183 / 22663)) (n := 12)
    (lo := (193247973 / 1000000000)) (hi := (96623987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12423 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12423 / 10240) = 1/(10240 / 12423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (193247973 / 1000000000) (96623987 / 500000000) (Real.log (12423 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12423 / 10240) = -Real.log (10240 / 12423) := by
    rw [show ((12423 / 10240) : ℝ) = ((10240 / 12423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (11988017 / 50000000) ≤ -Real.log (8057 / 10240) ∧
    -Real.log (8057 / 10240) ≤ (239760341 / 1000000000) := by
  have h := checkLog_sound (w := (2183 / 18297)) (n := 12)
    (lo := (11988017 / 50000000)) (hi := (239760341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8057) = 1/(8057 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-239760341 / 1000000000) (-11988017 / 50000000) (Real.log (8057 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (355541489 / 1000000000) ≤ -Real.log (2560 / 3653) ∧
    -Real.log (2560 / 3653) ≤ (35554149 / 100000000) := by
  have h := checkLog_sound (w := (1093 / 6213)) (n := 12)
    (lo := (355541489 / 1000000000)) (hi := (35554149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3653 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3653 / 2560) = 1/(2560 / 3653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (355541489 / 1000000000) (35554149 / 100000000) (Real.log (3653 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3653 / 2560) = -Real.log (2560 / 3653) := by
    rw [show ((3653 / 2560) : ℝ) = ((2560 / 3653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (556787759 / 1000000000) ≤ -Real.log (1467 / 2560) ∧
    -Real.log (1467 / 2560) ≤ (6959847 / 12500000) := by
  have h := checkLog_sound (w := (1093 / 4027)) (n := 12)
    (lo := (556787759 / 1000000000)) (hi := (6959847 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1467) = 1/(1467 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6959847 / 12500000) (-556787759 / 1000000000) (Real.log (1467 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (355130783 / 1000000000) ≤ -Real.log (5120 / 7303) ∧
    -Real.log (5120 / 7303) ≤ (11097837 / 31250000) := by
  have h := checkLog_sound (w := (2183 / 12423)) (n := 12)
    (lo := (355130783 / 1000000000)) (hi := (11097837 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7303 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7303 / 5120) = 1/(5120 / 7303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (355130783 / 1000000000) (11097837 / 31250000) (Real.log (7303 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7303 / 5120) = -Real.log (5120 / 7303) := by
    rw [show ((7303 / 5120) : ℝ) = ((5120 / 7303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (277882893 / 500000000) ≤ -Real.log (2937 / 5120) ∧
    -Real.log (2937 / 5120) ≤ (555765787 / 1000000000) := by
  have h := checkLog_sound (w := (2183 / 8057)) (n := 12)
    (lo := (277882893 / 500000000)) (hi := (555765787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2937) = 1/(2937 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-555765787 / 1000000000) (-277882893 / 500000000) (Real.log (2937 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (53081311 / 200000000) ≤ -Real.log (1000000 / 1303961) ∧
    -Real.log (1000000 / 1303961) ≤ (66351639 / 250000000) := by
  have h := checkLog_sound (w := (303961 / 2303961)) (n := 12)
    (lo := (53081311 / 200000000)) (hi := (66351639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303961 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303961 / 1000000) = 1/(1000000 / 1303961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (53081311 / 200000000) (66351639 / 250000000) (Real.log (1303961 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1303961 / 1000000) = -Real.log (1000000 / 1303961) := by
    rw [show ((1303961 / 1000000) : ℝ) = ((1000000 / 1303961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72469917 / 200000000) ≤ -Real.log (696039 / 1000000) ∧
    -Real.log (696039 / 1000000) ≤ (181174793 / 500000000) := by
  have h := checkLog_sound (w := (303961 / 1696039)) (n := 12)
    (lo := (72469917 / 200000000)) (hi := (181174793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 696039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 696039) = 1/(696039 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-181174793 / 500000000) (-72469917 / 200000000) (Real.log (696039 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (132866599 / 500000000) ≤ -Real.log (1000000 / 1304387) ∧
    -Real.log (1000000 / 1304387) ≤ (265733199 / 1000000000) := by
  have h := checkLog_sound (w := (304387 / 2304387)) (n := 12)
    (lo := (132866599 / 500000000)) (hi := (265733199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1304387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1304387 / 1000000) = 1/(1000000 / 1304387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (132866599 / 500000000) (265733199 / 1000000000) (Real.log (1304387 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1304387 / 1000000) = -Real.log (1000000 / 1304387) := by
    rw [show ((1304387 / 1000000) : ℝ) = ((1000000 / 1304387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (362961807 / 1000000000) ≤ -Real.log (695613 / 1000000) ∧
    -Real.log (695613 / 1000000) ≤ (22685113 / 62500000) := by
  have h := checkLog_sound (w := (304387 / 1695613)) (n := 12)
    (lo := (362961807 / 1000000000)) (hi := (22685113 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 695613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 695613) = 1/(695613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22685113 / 62500000) (-362961807 / 1000000000) (Real.log (695613 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (199322059 / 1000000000) ≤ -Real.log (40000 / 48823) ∧
    -Real.log (40000 / 48823) ≤ (9966103 / 50000000) := by
  have h := checkLog_sound (w := (8823 / 88823)) (n := 12)
    (lo := (199322059 / 1000000000)) (hi := (9966103 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48823 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48823 / 40000) = 1/(40000 / 48823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (199322059 / 1000000000) (9966103 / 50000000) (Real.log (48823 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (48823 / 40000) = -Real.log (40000 / 48823) := by
    rw [show ((48823 / 40000) : ℝ) = ((40000 / 48823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (24919881 / 100000000) ≤ -Real.log (31177 / 40000) ∧
    -Real.log (31177 / 40000) ≤ (249198811 / 1000000000) := by
  have h := checkLog_sound (w := (8823 / 71177)) (n := 12)
    (lo := (24919881 / 100000000)) (hi := (249198811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31177) = 1/(31177 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-249198811 / 1000000000) (-24919881 / 100000000) (Real.log (31177 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19958911 / 100000000) ≤ -Real.log (1000000 / 1220901) ∧
    -Real.log (1000000 / 1220901) ≤ (199589111 / 1000000000) := by
  have h := checkLog_sound (w := (220901 / 2220901)) (n := 12)
    (lo := (19958911 / 100000000)) (hi := (199589111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1220901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1220901 / 1000000) = 1/(1000000 / 1220901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19958911 / 100000000) (199589111 / 1000000000) (Real.log (1220901 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1220901 / 1000000) = -Real.log (1000000 / 1220901) := by
    rw [show ((1220901 / 1000000) : ℝ) = ((1000000 / 1220901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (49923431 / 200000000) ≤ -Real.log (779099 / 1000000) ∧
    -Real.log (779099 / 1000000) ≤ (62404289 / 250000000) := by
  have h := checkLog_sound (w := (220901 / 1779099)) (n := 12)
    (lo := (49923431 / 200000000)) (hi := (62404289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 779099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 779099) = 1/(779099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-62404289 / 250000000) (-49923431 / 200000000) (Real.log (779099 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (31387807 / 50000000) ≤ -Real.log (62500000000 / 117087638049) ∧
    -Real.log (62500000000 / 117087638049) ≤ (627756141 / 1000000000) := by
  have h := checkLog_sound (w := (54587638049 / 179587638049)) (n := 12)
    (lo := (31387807 / 50000000)) (hi := (627756141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117087638049 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117087638049 / 62500000000) = 1/(62500000000 / 117087638049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (31387807 / 50000000) (627756141 / 1000000000) (Real.log (117087638049 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (117087638049 / 62500000000) = -Real.log (62500000000 / 117087638049) := by
    rw [show ((117087638049 / 62500000000) : ℝ) = ((62500000000 / 117087638049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (314347503 / 500000000) ≤ -Real.log (250000000000 / 468790476889) ∧
    -Real.log (250000000000 / 468790476889) ≤ (628695007 / 1000000000) := by
  have h := checkLog_sound (w := (218790476889 / 718790476889)) (n := 12)
    (lo := (314347503 / 500000000)) (hi := (628695007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((468790476889 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(468790476889 / 250000000000) = 1/(250000000000 / 468790476889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (314347503 / 500000000) (628695007 / 1000000000) (Real.log (468790476889 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (468790476889 / 250000000000) = -Real.log (250000000000 / 468790476889) := by
    rw [show ((468790476889 / 250000000000) : ℝ) = ((250000000000 / 468790476889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (448520869 / 1000000000) ≤ -Real.log (500000000000 / 782997081181) ∧
    -Real.log (500000000000 / 782997081181) ≤ (44852087 / 100000000) := by
  have h := checkLog_sound (w := (282997081181 / 1282997081181)) (n := 12)
    (lo := (448520869 / 1000000000)) (hi := (44852087 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782997081181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782997081181 / 500000000000) = 1/(500000000000 / 782997081181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (448520869 / 1000000000) (44852087 / 100000000) (Real.log (782997081181 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (782997081181 / 500000000000) = -Real.log (500000000000 / 782997081181) := by
    rw [show ((782997081181 / 500000000000) : ℝ) = ((500000000000 / 782997081181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (89841253 / 200000000) ≤ -Real.log (100000000000 / 156706785659) ∧
    -Real.log (100000000000 / 156706785659) ≤ (224603133 / 500000000) := by
  have h := checkLog_sound (w := (56706785659 / 256706785659)) (n := 12)
    (lo := (89841253 / 200000000)) (hi := (224603133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156706785659 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156706785659 / 100000000000) = 1/(100000000000 / 156706785659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (89841253 / 200000000) (224603133 / 500000000) (Real.log (156706785659 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (156706785659 / 100000000000) = -Real.log (100000000000 / 156706785659) := by
    rw [show ((156706785659 / 100000000000) : ℝ) = ((100000000000 / 156706785659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0428

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0429Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0429
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

theorem reflection_log_1_neg : (193247973 / 1000000000) ≤ -Real.log (10240 / 12423) ∧
    -Real.log (10240 / 12423) ≤ (96623987 / 500000000) := by
  have h := checkLog_sound (w := (2183 / 22663)) (n := 12)
    (lo := (193247973 / 1000000000)) (hi := (96623987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12423 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12423 / 10240) = 1/(10240 / 12423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (193247973 / 1000000000) (96623987 / 500000000) (Real.log (12423 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12423 / 10240) = -Real.log (10240 / 12423) := by
    rw [show ((12423 / 10240) : ℝ) = ((10240 / 12423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (11988017 / 50000000) ≤ -Real.log (8057 / 10240) ∧
    -Real.log (8057 / 10240) ≤ (239760341 / 1000000000) := by
  have h := checkLog_sound (w := (2183 / 18297)) (n := 12)
    (lo := (11988017 / 50000000)) (hi := (239760341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8057) = 1/(8057 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-239760341 / 1000000000) (-11988017 / 50000000) (Real.log (8057 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24125807 / 125000000) ≤ -Real.log (512 / 621) ∧
    -Real.log (512 / 621) ≤ (193006457 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1133)) (n := 12)
    (lo := (24125807 / 125000000)) (hi := (193006457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621 / 512) = 1/(512 / 621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24125807 / 125000000) (193006457 / 1000000000) (Real.log (621 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (621 / 512) = -Real.log (512 / 621) := by
    rw [show ((621 / 512) : ℝ) = ((512 / 621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (239388063 / 1000000000) ≤ -Real.log (403 / 512) ∧
    -Real.log (403 / 512) ≤ (7480877 / 31250000) := by
  have h := checkLog_sound (w := (109 / 915)) (n := 12)
    (lo := (239388063 / 1000000000)) (hi := (7480877 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 403) = 1/(403 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7480877 / 31250000) (-239388063 / 1000000000) (Real.log (403 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (355130783 / 1000000000) ≤ -Real.log (5120 / 7303) ∧
    -Real.log (5120 / 7303) ≤ (11097837 / 31250000) := by
  have h := checkLog_sound (w := (2183 / 12423)) (n := 12)
    (lo := (355130783 / 1000000000)) (hi := (11097837 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7303 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7303 / 5120) = 1/(5120 / 7303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (355130783 / 1000000000) (11097837 / 31250000) (Real.log (7303 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7303 / 5120) = -Real.log (5120 / 7303) := by
    rw [show ((7303 / 5120) : ℝ) = ((5120 / 7303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (277882893 / 500000000) ≤ -Real.log (2937 / 5120) ∧
    -Real.log (2937 / 5120) ≤ (555765787 / 1000000000) := by
  have h := checkLog_sound (w := (2183 / 8057)) (n := 12)
    (lo := (277882893 / 500000000)) (hi := (555765787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2937) = 1/(2937 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-555765787 / 1000000000) (-277882893 / 500000000) (Real.log (2937 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (354719909 / 1000000000) ≤ -Real.log (256 / 365) ∧
    -Real.log (256 / 365) ≤ (35471991 / 100000000) := by
  have h := checkLog_sound (w := (109 / 621)) (n := 12)
    (lo := (354719909 / 1000000000)) (hi := (35471991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365 / 256) = 1/(256 / 365) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (354719909 / 1000000000) (35471991 / 100000000) (Real.log (365 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (365 / 256) = -Real.log (256 / 365) := by
    rw [show ((365 / 256) : ℝ) = ((256 / 365) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (554744857 / 1000000000) ≤ -Real.log (147 / 256) ∧
    -Real.log (147 / 256) ≤ (277372429 / 500000000) := by
  have h := checkLog_sound (w := (109 / 403)) (n := 12)
    (lo := (554744857 / 1000000000)) (hi := (277372429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 147) = 1/(147 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-277372429 / 500000000) (-554744857 / 1000000000) (Real.log (147 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (265080571 / 1000000000) ≤ -Real.log (62500 / 81471) ∧
    -Real.log (62500 / 81471) ≤ (66270143 / 250000000) := by
  have h := checkLog_sound (w := (18971 / 143971)) (n := 12)
    (lo := (265080571 / 1000000000)) (hi := (66270143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81471 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81471 / 62500) = 1/(62500 / 81471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (265080571 / 1000000000) (66270143 / 250000000) (Real.log (81471 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (81471 / 62500) = -Real.log (62500 / 81471) := by
    rw [show ((81471 / 62500) : ℝ) = ((62500 / 81471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (180869587 / 500000000) ≤ -Real.log (43529 / 62500) ∧
    -Real.log (43529 / 62500) ≤ (14469567 / 40000000) := by
  have h := checkLog_sound (w := (18971 / 106029)) (n := 12)
    (lo := (180869587 / 500000000)) (hi := (14469567 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 43529) = 1/(43529 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-14469567 / 40000000) (-180869587 / 500000000) (Real.log (43529 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (265407321 / 1000000000) ≤ -Real.log (500000 / 651981) ∧
    -Real.log (500000 / 651981) ≤ (132703661 / 500000000) := by
  have h := checkLog_sound (w := (151981 / 1151981)) (n := 12)
    (lo := (265407321 / 1000000000)) (hi := (132703661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651981 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651981 / 500000) = 1/(500000 / 651981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (265407321 / 1000000000) (132703661 / 500000000) (Real.log (651981 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (651981 / 500000) = -Real.log (500000 / 651981) := by
    rw [show ((651981 / 500000) : ℝ) = ((500000 / 651981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (181175511 / 500000000) ≤ -Real.log (348019 / 500000) ∧
    -Real.log (348019 / 500000) ≤ (362351023 / 1000000000) := by
  have h := checkLog_sound (w := (151981 / 848019)) (n := 12)
    (lo := (181175511 / 500000000)) (hi := (362351023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 348019) = 1/(348019 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-362351023 / 1000000000) (-181175511 / 500000000) (Real.log (348019 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7962263 / 40000000) ≤ -Real.log (1000000 / 1220251) ∧
    -Real.log (1000000 / 1220251) ≤ (3110259 / 15625000) := by
  have h := checkLog_sound (w := (220251 / 2220251)) (n := 12)
    (lo := (7962263 / 40000000)) (hi := (3110259 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1220251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1220251 / 1000000) = 1/(1000000 / 1220251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7962263 / 40000000) (3110259 / 15625000) (Real.log (1220251 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1220251 / 1000000) = -Real.log (1000000 / 1220251) := by
    rw [show ((1220251 / 1000000) : ℝ) = ((1000000 / 1220251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49756641 / 200000000) ≤ -Real.log (779749 / 1000000) ∧
    -Real.log (779749 / 1000000) ≤ (124391603 / 500000000) := by
  have h := checkLog_sound (w := (220251 / 1779749)) (n := 12)
    (lo := (49756641 / 200000000)) (hi := (124391603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 779749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 779749) = 1/(779749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-124391603 / 500000000) (-49756641 / 200000000) (Real.log (779749 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (99661439 / 500000000) ≤ -Real.log (31250 / 38143) ∧
    -Real.log (31250 / 38143) ≤ (199322879 / 1000000000) := by
  have h := checkLog_sound (w := (6893 / 69393)) (n := 12)
    (lo := (99661439 / 500000000)) (hi := (199322879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38143 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38143 / 31250) = 1/(31250 / 38143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (99661439 / 500000000) (199322879 / 1000000000) (Real.log (38143 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (38143 / 31250) = -Real.log (31250 / 38143) := by
    rw [show ((38143 / 31250) : ℝ) = ((31250 / 38143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (249200093 / 1000000000) ≤ -Real.log (24357 / 31250) ∧
    -Real.log (24357 / 31250) ≤ (124600047 / 500000000) := by
  have h := checkLog_sound (w := (6893 / 55607)) (n := 12)
    (lo := (249200093 / 1000000000)) (hi := (124600047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24357) = 1/(24357 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-124600047 / 500000000) (-249200093 / 1000000000) (Real.log (24357 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (313409873 / 500000000) ≤ -Real.log (500000000000 / 935824392933) ∧
    -Real.log (500000000000 / 935824392933) ≤ (626819747 / 1000000000) := by
  have h := checkLog_sound (w := (435824392933 / 1435824392933)) (n := 12)
    (lo := (313409873 / 500000000)) (hi := (626819747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935824392933 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935824392933 / 500000000000) = 1/(500000000000 / 935824392933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (313409873 / 500000000) (626819747 / 1000000000) (Real.log (935824392933 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (935824392933 / 500000000000) = -Real.log (500000000000 / 935824392933) := by
    rw [show ((935824392933 / 500000000000) : ℝ) = ((500000000000 / 935824392933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (78469793 / 125000000) ≤ -Real.log (250000000000 / 468351584253) ∧
    -Real.log (250000000000 / 468351584253) ≤ (125551669 / 200000000) := by
  have h := checkLog_sound (w := (218351584253 / 718351584253)) (n := 12)
    (lo := (78469793 / 125000000)) (hi := (125551669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((468351584253 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(468351584253 / 250000000000) = 1/(250000000000 / 468351584253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (78469793 / 125000000) (125551669 / 200000000) (Real.log (468351584253 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (468351584253 / 250000000000) = -Real.log (250000000000 / 468351584253) := by
    rw [show ((468351584253 / 250000000000) : ℝ) = ((250000000000 / 468351584253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (447839781 / 1000000000) ≤ -Real.log (25000000000 / 39123198619) ∧
    -Real.log (25000000000 / 39123198619) ≤ (223919891 / 500000000) := by
  have h := checkLog_sound (w := (14123198619 / 64123198619)) (n := 12)
    (lo := (447839781 / 1000000000)) (hi := (223919891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39123198619 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39123198619 / 25000000000) = 1/(25000000000 / 39123198619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (447839781 / 1000000000) (223919891 / 500000000) (Real.log (39123198619 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (39123198619 / 25000000000) = -Real.log (25000000000 / 39123198619) := by
    rw [show ((39123198619 / 25000000000) : ℝ) = ((25000000000 / 39123198619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (112130743 / 250000000) ≤ -Real.log (250000000000 / 391499363633) ∧
    -Real.log (250000000000 / 391499363633) ≤ (448522973 / 1000000000) := by
  have h := checkLog_sound (w := (141499363633 / 641499363633)) (n := 12)
    (lo := (112130743 / 250000000)) (hi := (448522973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391499363633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391499363633 / 250000000000) = 1/(250000000000 / 391499363633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (112130743 / 250000000) (448522973 / 1000000000) (Real.log (391499363633 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (391499363633 / 250000000000) = -Real.log (250000000000 / 391499363633) := by
    rw [show ((391499363633 / 250000000000) : ℝ) = ((250000000000 / 391499363633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0429

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0430Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0430
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

theorem reflection_log_1_neg : (24125807 / 125000000) ≤ -Real.log (512 / 621) ∧
    -Real.log (512 / 621) ≤ (193006457 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1133)) (n := 12)
    (lo := (24125807 / 125000000)) (hi := (193006457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621 / 512) = 1/(512 / 621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24125807 / 125000000) (193006457 / 1000000000) (Real.log (621 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (621 / 512) = -Real.log (512 / 621) := by
    rw [show ((621 / 512) : ℝ) = ((512 / 621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (239388063 / 1000000000) ≤ -Real.log (403 / 512) ∧
    -Real.log (403 / 512) ≤ (7480877 / 31250000) := by
  have h := checkLog_sound (w := (109 / 915)) (n := 12)
    (lo := (239388063 / 1000000000)) (hi := (7480877 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 403) = 1/(403 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7480877 / 31250000) (-239388063 / 1000000000) (Real.log (403 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (192764881 / 1000000000) ≤ -Real.log (10240 / 12417) ∧
    -Real.log (10240 / 12417) ≤ (96382441 / 500000000) := by
  have h := checkLog_sound (w := (2177 / 22657)) (n := 12)
    (lo := (192764881 / 1000000000)) (hi := (96382441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12417 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12417 / 10240) = 1/(10240 / 12417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (192764881 / 1000000000) (96382441 / 500000000) (Real.log (12417 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12417 / 10240) = -Real.log (10240 / 12417) := by
    rw [show ((12417 / 10240) : ℝ) = ((10240 / 12417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (239015923 / 1000000000) ≤ -Real.log (8063 / 10240) ∧
    -Real.log (8063 / 10240) ≤ (59753981 / 250000000) := by
  have h := checkLog_sound (w := (2177 / 18303)) (n := 12)
    (lo := (239015923 / 1000000000)) (hi := (59753981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8063) = 1/(8063 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59753981 / 250000000) (-239015923 / 1000000000) (Real.log (8063 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (354719909 / 1000000000) ≤ -Real.log (256 / 365) ∧
    -Real.log (256 / 365) ≤ (35471991 / 100000000) := by
  have h := checkLog_sound (w := (109 / 621)) (n := 12)
    (lo := (354719909 / 1000000000)) (hi := (35471991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365 / 256) = 1/(256 / 365) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (354719909 / 1000000000) (35471991 / 100000000) (Real.log (365 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (365 / 256) = -Real.log (256 / 365) := by
    rw [show ((365 / 256) : ℝ) = ((256 / 365) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (554744857 / 1000000000) ≤ -Real.log (147 / 256) ∧
    -Real.log (147 / 256) ≤ (277372429 / 500000000) := by
  have h := checkLog_sound (w := (109 / 403)) (n := 12)
    (lo := (554744857 / 1000000000)) (hi := (277372429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 147) = 1/(147 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-277372429 / 500000000) (-554744857 / 1000000000) (Real.log (147 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (70861773 / 200000000) ≤ -Real.log (5120 / 7297) ∧
    -Real.log (5120 / 7297) ≤ (177154433 / 500000000) := by
  have h := checkLog_sound (w := (2177 / 12417)) (n := 12)
    (lo := (70861773 / 200000000)) (hi := (177154433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7297 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7297 / 5120) = 1/(5120 / 7297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (70861773 / 200000000) (177154433 / 500000000) (Real.log (7297 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7297 / 5120) = -Real.log (5120 / 7297) := by
    rw [show ((7297 / 5120) : ℝ) = ((5120 / 7297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (553724969 / 1000000000) ≤ -Real.log (2943 / 5120) ∧
    -Real.log (2943 / 5120) ≤ (55372497 / 100000000) := by
  have h := checkLog_sound (w := (2177 / 8063)) (n := 12)
    (lo := (553724969 / 1000000000)) (hi := (55372497 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2943) = 1/(2943 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-55372497 / 100000000) (-553724969 / 1000000000) (Real.log (2943 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (132377241 / 500000000) ≤ -Real.log (1000000 / 1303111) ∧
    -Real.log (1000000 / 1303111) ≤ (264754483 / 1000000000) := by
  have h := checkLog_sound (w := (303111 / 2303111)) (n := 12)
    (lo := (132377241 / 500000000)) (hi := (264754483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303111 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303111 / 1000000) = 1/(1000000 / 1303111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (132377241 / 500000000) (264754483 / 1000000000) (Real.log (1303111 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1303111 / 1000000) = -Real.log (1000000 / 1303111) := by
    rw [show ((1303111 / 1000000) : ℝ) = ((1000000 / 1303111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (180564567 / 500000000) ≤ -Real.log (696889 / 1000000) ∧
    -Real.log (696889 / 1000000) ≤ (72225827 / 200000000) := by
  have h := checkLog_sound (w := (303111 / 1696889)) (n := 12)
    (lo := (180564567 / 500000000)) (hi := (72225827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 696889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 696889) = 1/(696889 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-72225827 / 200000000) (-180564567 / 500000000) (Real.log (696889 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (265081339 / 1000000000) ≤ -Real.log (1000000 / 1303537) ∧
    -Real.log (1000000 / 1303537) ≤ (13254067 / 50000000) := by
  have h := checkLog_sound (w := (303537 / 2303537)) (n := 12)
    (lo := (265081339 / 1000000000)) (hi := (13254067 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303537 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303537 / 1000000) = 1/(1000000 / 1303537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (265081339 / 1000000000) (13254067 / 50000000) (Real.log (1303537 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1303537 / 1000000) = -Real.log (1000000 / 1303537) := by
    rw [show ((1303537 / 1000000) : ℝ) = ((1000000 / 1303537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (361740609 / 1000000000) ≤ -Real.log (696463 / 1000000) ∧
    -Real.log (696463 / 1000000) ≤ (36174061 / 100000000) := by
  have h := checkLog_sound (w := (303537 / 1696463)) (n := 12)
    (lo := (361740609 / 1000000000)) (hi := (36174061 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 696463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 696463) = 1/(696463 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36174061 / 100000000) (-361740609 / 1000000000) (Real.log (696463 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (198790201 / 1000000000) ≤ -Real.log (500000 / 609963) ∧
    -Real.log (500000 / 609963) ≤ (99395101 / 500000000) := by
  have h := checkLog_sound (w := (109963 / 1109963)) (n := 12)
    (lo := (198790201 / 1000000000)) (hi := (99395101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609963 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609963 / 500000) = 1/(500000 / 609963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (198790201 / 1000000000) (99395101 / 500000000) (Real.log (609963 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (609963 / 500000) = -Real.log (500000 / 609963) := by
    rw [show ((609963 / 500000) : ℝ) = ((500000 / 609963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (62091623 / 250000000) ≤ -Real.log (390037 / 500000) ∧
    -Real.log (390037 / 500000) ≤ (248366493 / 1000000000) := by
  have h := checkLog_sound (w := (109963 / 890037)) (n := 12)
    (lo := (62091623 / 250000000)) (hi := (248366493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 390037) = 1/(390037 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-248366493 / 1000000000) (-62091623 / 250000000) (Real.log (390037 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (99528697 / 500000000) ≤ -Real.log (250000 / 305063) ∧
    -Real.log (250000 / 305063) ≤ (39811479 / 200000000) := by
  have h := checkLog_sound (w := (55063 / 555063)) (n := 12)
    (lo := (99528697 / 500000000)) (hi := (39811479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305063 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305063 / 250000) = 1/(250000 / 305063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (99528697 / 500000000) (39811479 / 200000000) (Real.log (305063 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (305063 / 250000) = -Real.log (250000 / 305063) := by
    rw [show ((305063 / 250000) : ℝ) = ((250000 / 305063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (31098061 / 125000000) ≤ -Real.log (194937 / 250000) ∧
    -Real.log (194937 / 250000) ≤ (248784489 / 1000000000) := by
  have h := checkLog_sound (w := (55063 / 444937)) (n := 12)
    (lo := (31098061 / 125000000)) (hi := (248784489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194937) = 1/(194937 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-248784489 / 1000000000) (-31098061 / 125000000) (Real.log (194937 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (625883617 / 1000000000) ≤ -Real.log (100000000000 / 186989750161) ∧
    -Real.log (100000000000 / 186989750161) ≤ (312941809 / 500000000) := by
  have h := checkLog_sound (w := (86989750161 / 286989750161)) (n := 12)
    (lo := (625883617 / 1000000000)) (hi := (312941809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186989750161 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186989750161 / 100000000000) = 1/(100000000000 / 186989750161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (625883617 / 1000000000) (312941809 / 500000000) (Real.log (186989750161 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (186989750161 / 100000000000) = -Real.log (100000000000 / 186989750161) := by
    rw [show ((186989750161 / 100000000000) : ℝ) = ((100000000000 / 186989750161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (626821949 / 1000000000) ≤ -Real.log (500000000000 / 935826454529) ∧
    -Real.log (500000000000 / 935826454529) ≤ (12536439 / 20000000) := by
  have h := checkLog_sound (w := (435826454529 / 1435826454529)) (n := 12)
    (lo := (626821949 / 1000000000)) (hi := (12536439 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935826454529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935826454529 / 500000000000) = 1/(500000000000 / 935826454529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (626821949 / 1000000000) (12536439 / 20000000) (Real.log (935826454529 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (935826454529 / 500000000000) = -Real.log (500000000000 / 935826454529) := by
    rw [show ((935826454529 / 500000000000) : ℝ) = ((500000000000 / 935826454529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (447156693 / 1000000000) ≤ -Real.log (500000000000 / 781929663083) ∧
    -Real.log (500000000000 / 781929663083) ≤ (223578347 / 500000000) := by
  have h := checkLog_sound (w := (281929663083 / 1281929663083)) (n := 12)
    (lo := (447156693 / 1000000000)) (hi := (223578347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781929663083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781929663083 / 500000000000) = 1/(500000000000 / 781929663083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (447156693 / 1000000000) (223578347 / 500000000) (Real.log (781929663083 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (781929663083 / 500000000000) = -Real.log (500000000000 / 781929663083) := by
    rw [show ((781929663083 / 500000000000) : ℝ) = ((500000000000 / 781929663083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (447841883 / 1000000000) ≤ -Real.log (500000000000 / 782465617097) ∧
    -Real.log (500000000000 / 782465617097) ≤ (111960471 / 250000000) := by
  have h := checkLog_sound (w := (282465617097 / 1282465617097)) (n := 12)
    (lo := (447841883 / 1000000000)) (hi := (111960471 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782465617097 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782465617097 / 500000000000) = 1/(500000000000 / 782465617097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (447841883 / 1000000000) (111960471 / 250000000) (Real.log (782465617097 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (782465617097 / 500000000000) = -Real.log (500000000000 / 782465617097) := by
    rw [show ((782465617097 / 500000000000) : ℝ) = ((500000000000 / 782465617097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0430

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0431Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0431
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

theorem reflection_log_1_neg : (192764881 / 1000000000) ≤ -Real.log (10240 / 12417) ∧
    -Real.log (10240 / 12417) ≤ (96382441 / 500000000) := by
  have h := checkLog_sound (w := (2177 / 22657)) (n := 12)
    (lo := (192764881 / 1000000000)) (hi := (96382441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12417 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12417 / 10240) = 1/(10240 / 12417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (192764881 / 1000000000) (96382441 / 500000000) (Real.log (12417 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12417 / 10240) = -Real.log (10240 / 12417) := by
    rw [show ((12417 / 10240) : ℝ) = ((10240 / 12417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (239015923 / 1000000000) ≤ -Real.log (8063 / 10240) ∧
    -Real.log (8063 / 10240) ≤ (59753981 / 250000000) := by
  have h := checkLog_sound (w := (2177 / 18303)) (n := 12)
    (lo := (239015923 / 1000000000)) (hi := (59753981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8063) = 1/(8063 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59753981 / 250000000) (-239015923 / 1000000000) (Real.log (8063 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12032703 / 62500000) ≤ -Real.log (5120 / 6207) ∧
    -Real.log (5120 / 6207) ≤ (192523249 / 1000000000) := by
  have h := checkLog_sound (w := (1087 / 11327)) (n := 12)
    (lo := (12032703 / 62500000)) (hi := (192523249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6207 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6207 / 5120) = 1/(5120 / 6207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12032703 / 62500000) (192523249 / 1000000000) (Real.log (6207 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6207 / 5120) = -Real.log (5120 / 6207) := by
    rw [show ((6207 / 5120) : ℝ) = ((5120 / 6207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (238643923 / 1000000000) ≤ -Real.log (4033 / 5120) ∧
    -Real.log (4033 / 5120) ≤ (59660981 / 250000000) := by
  have h := checkLog_sound (w := (1087 / 9153)) (n := 12)
    (lo := (238643923 / 1000000000)) (hi := (59660981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4033) = 1/(4033 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59660981 / 250000000) (-238643923 / 1000000000) (Real.log (4033 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (70861773 / 200000000) ≤ -Real.log (5120 / 7297) ∧
    -Real.log (5120 / 7297) ≤ (177154433 / 500000000) := by
  have h := checkLog_sound (w := (2177 / 12417)) (n := 12)
    (lo := (70861773 / 200000000)) (hi := (177154433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7297 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7297 / 5120) = 1/(5120 / 7297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (70861773 / 200000000) (177154433 / 500000000) (Real.log (7297 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7297 / 5120) = -Real.log (5120 / 7297) := by
    rw [show ((7297 / 5120) : ℝ) = ((5120 / 7297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (553724969 / 1000000000) ≤ -Real.log (2943 / 5120) ∧
    -Real.log (2943 / 5120) ≤ (55372497 / 100000000) := by
  have h := checkLog_sound (w := (2177 / 8063)) (n := 12)
    (lo := (553724969 / 1000000000)) (hi := (55372497 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2943) = 1/(2943 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-55372497 / 100000000) (-553724969 / 1000000000) (Real.log (2943 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (353897653 / 1000000000) ≤ -Real.log (2560 / 3647) ∧
    -Real.log (2560 / 3647) ≤ (176948827 / 500000000) := by
  have h := checkLog_sound (w := (1087 / 6207)) (n := 12)
    (lo := (353897653 / 1000000000)) (hi := (176948827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3647 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3647 / 2560) = 1/(2560 / 3647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (353897653 / 1000000000) (176948827 / 500000000) (Real.log (3647 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3647 / 2560) = -Real.log (2560 / 3647) := by
    rw [show ((3647 / 2560) : ℝ) = ((2560 / 3647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (552706121 / 1000000000) ≤ -Real.log (1473 / 2560) ∧
    -Real.log (1473 / 2560) ≤ (276353061 / 500000000) := by
  have h := checkLog_sound (w := (1087 / 4033)) (n := 12)
    (lo := (552706121 / 1000000000)) (hi := (276353061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1473) = 1/(1473 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-276353061 / 500000000) (-552706121 / 1000000000) (Real.log (1473 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (132214143 / 500000000) ≤ -Real.log (500000 / 651343) ∧
    -Real.log (500000 / 651343) ≤ (264428287 / 1000000000) := by
  have h := checkLog_sound (w := (151343 / 1151343)) (n := 12)
    (lo := (132214143 / 500000000)) (hi := (264428287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651343 / 500000) = 1/(500000 / 651343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (132214143 / 500000000) (264428287 / 1000000000) (Real.log (651343 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (651343 / 500000) = -Real.log (500000 / 651343) := by
    rw [show ((651343 / 500000) : ℝ) = ((500000 / 651343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (360519467 / 1000000000) ≤ -Real.log (348657 / 500000) ∧
    -Real.log (348657 / 500000) ≤ (90129867 / 250000000) := by
  have h := checkLog_sound (w := (151343 / 848657)) (n := 12)
    (lo := (360519467 / 1000000000)) (hi := (90129867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 348657) = 1/(348657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-90129867 / 250000000) (-360519467 / 1000000000) (Real.log (348657 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (264755249 / 1000000000) ≤ -Real.log (125000 / 162889) ∧
    -Real.log (125000 / 162889) ≤ (1059021 / 4000000) := by
  have h := checkLog_sound (w := (37889 / 287889)) (n := 12)
    (lo := (264755249 / 1000000000)) (hi := (1059021 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162889 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162889 / 125000) = 1/(125000 / 162889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (264755249 / 1000000000) (1059021 / 4000000) (Real.log (162889 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (162889 / 125000) = -Real.log (125000 / 162889) := by
    rw [show ((162889 / 125000) : ℝ) = ((125000 / 162889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (361130569 / 1000000000) ≤ -Real.log (87111 / 125000) ∧
    -Real.log (87111 / 125000) ≤ (36113057 / 100000000) := by
  have h := checkLog_sound (w := (37889 / 212111)) (n := 12)
    (lo := (361130569 / 1000000000)) (hi := (36113057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 87111) = 1/(87111 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36113057 / 100000000) (-361130569 / 1000000000) (Real.log (87111 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6203893 / 31250000) ≤ -Real.log (500000 / 609801) ∧
    -Real.log (500000 / 609801) ≤ (198524577 / 1000000000) := by
  have h := checkLog_sound (w := (109801 / 1109801)) (n := 12)
    (lo := (6203893 / 31250000)) (hi := (198524577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609801 / 500000) = 1/(500000 / 609801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6203893 / 31250000) (198524577 / 1000000000) (Real.log (609801 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (609801 / 500000) = -Real.log (500000 / 609801) := by
    rw [show ((609801 / 500000) : ℝ) = ((500000 / 609801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (247951233 / 1000000000) ≤ -Real.log (390199 / 500000) ∧
    -Real.log (390199 / 500000) ≤ (123975617 / 500000000) := by
  have h := checkLog_sound (w := (109801 / 890199)) (n := 12)
    (lo := (247951233 / 1000000000)) (hi := (123975617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 390199) = 1/(390199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-123975617 / 500000000) (-247951233 / 1000000000) (Real.log (390199 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (9939551 / 50000000) ≤ -Real.log (1000000 / 1219927) ∧
    -Real.log (1000000 / 1219927) ≤ (198791021 / 1000000000) := by
  have h := checkLog_sound (w := (219927 / 2219927)) (n := 12)
    (lo := (9939551 / 50000000)) (hi := (198791021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219927 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219927 / 1000000) = 1/(1000000 / 1219927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (9939551 / 50000000) (198791021 / 1000000000) (Real.log (1219927 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1219927 / 1000000) = -Real.log (1000000 / 1219927) := by
    rw [show ((1219927 / 1000000) : ℝ) = ((1000000 / 1219927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (248367773 / 1000000000) ≤ -Real.log (780073 / 1000000) ∧
    -Real.log (780073 / 1000000) ≤ (124183887 / 500000000) := by
  have h := checkLog_sound (w := (219927 / 1780073)) (n := 12)
    (lo := (248367773 / 1000000000)) (hi := (124183887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780073) = 1/(780073 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-124183887 / 500000000) (-248367773 / 1000000000) (Real.log (780073 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (312473877 / 500000000) ≤ -Real.log (125000000000 / 233518544013) ∧
    -Real.log (125000000000 / 233518544013) ≤ (124989551 / 200000000) := by
  have h := checkLog_sound (w := (108518544013 / 358518544013)) (n := 12)
    (lo := (312473877 / 500000000)) (hi := (124989551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233518544013 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233518544013 / 125000000000) = 1/(125000000000 / 233518544013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (312473877 / 500000000) (124989551 / 200000000) (Real.log (233518544013 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (233518544013 / 125000000000) = -Real.log (125000000000 / 233518544013) := by
    rw [show ((233518544013 / 125000000000) : ℝ) = ((125000000000 / 233518544013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (625885819 / 1000000000) ≤ -Real.log (500000000000 / 934950809887) ∧
    -Real.log (500000000000 / 934950809887) ≤ (31294291 / 50000000) := by
  have h := checkLog_sound (w := (434950809887 / 1434950809887)) (n := 12)
    (lo := (625885819 / 1000000000)) (hi := (31294291 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((934950809887 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(934950809887 / 500000000000) = 1/(500000000000 / 934950809887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (625885819 / 1000000000) (31294291 / 50000000) (Real.log (934950809887 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (934950809887 / 500000000000) = -Real.log (500000000000 / 934950809887) := by
    rw [show ((934950809887 / 500000000000) : ℝ) = ((500000000000 / 934950809887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (446475809 / 1000000000) ≤ -Real.log (500000000000 / 781397440793) ∧
    -Real.log (500000000000 / 781397440793) ≤ (44647581 / 100000000) := by
  have h := checkLog_sound (w := (281397440793 / 1281397440793)) (n := 12)
    (lo := (446475809 / 1000000000)) (hi := (44647581 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781397440793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781397440793 / 500000000000) = 1/(500000000000 / 781397440793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (446475809 / 1000000000) (44647581 / 100000000) (Real.log (781397440793 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (781397440793 / 500000000000) = -Real.log (500000000000 / 781397440793) := by
    rw [show ((781397440793 / 500000000000) : ℝ) = ((500000000000 / 781397440793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (223579397 / 500000000) ≤ -Real.log (50000000000 / 78193130643) ∧
    -Real.log (50000000000 / 78193130643) ≤ (89431759 / 200000000) := by
  have h := checkLog_sound (w := (28193130643 / 128193130643)) (n := 12)
    (lo := (223579397 / 500000000)) (hi := (89431759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78193130643 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78193130643 / 50000000000) = 1/(50000000000 / 78193130643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (223579397 / 500000000) (89431759 / 200000000) (Real.log (78193130643 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (78193130643 / 50000000000) = -Real.log (50000000000 / 78193130643) := by
    rw [show ((78193130643 / 50000000000) : ℝ) = ((50000000000 / 78193130643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0431

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0432Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0432
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

theorem reflection_log_1_neg : (12032703 / 62500000) ≤ -Real.log (5120 / 6207) ∧
    -Real.log (5120 / 6207) ≤ (192523249 / 1000000000) := by
  have h := checkLog_sound (w := (1087 / 11327)) (n := 12)
    (lo := (12032703 / 62500000)) (hi := (192523249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6207 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6207 / 5120) = 1/(5120 / 6207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12032703 / 62500000) (192523249 / 1000000000) (Real.log (6207 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6207 / 5120) = -Real.log (5120 / 6207) := by
    rw [show ((6207 / 5120) : ℝ) = ((5120 / 6207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (238643923 / 1000000000) ≤ -Real.log (4033 / 5120) ∧
    -Real.log (4033 / 5120) ≤ (59660981 / 250000000) := by
  have h := checkLog_sound (w := (1087 / 9153)) (n := 12)
    (lo := (238643923 / 1000000000)) (hi := (59660981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4033) = 1/(4033 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59660981 / 250000000) (-238643923 / 1000000000) (Real.log (4033 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (48070389 / 250000000) ≤ -Real.log (10240 / 12411) ∧
    -Real.log (10240 / 12411) ≤ (192281557 / 1000000000) := by
  have h := checkLog_sound (w := (2171 / 22651)) (n := 12)
    (lo := (48070389 / 250000000)) (hi := (192281557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12411 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12411 / 10240) = 1/(10240 / 12411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (48070389 / 250000000) (192281557 / 1000000000) (Real.log (12411 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12411 / 10240) = -Real.log (10240 / 12411) := by
    rw [show ((12411 / 10240) : ℝ) = ((10240 / 12411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (11913603 / 50000000) ≤ -Real.log (8069 / 10240) ∧
    -Real.log (8069 / 10240) ≤ (238272061 / 1000000000) := by
  have h := checkLog_sound (w := (2171 / 18309)) (n := 12)
    (lo := (11913603 / 50000000)) (hi := (238272061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8069) = 1/(8069 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-238272061 / 1000000000) (-11913603 / 50000000) (Real.log (8069 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (353897653 / 1000000000) ≤ -Real.log (2560 / 3647) ∧
    -Real.log (2560 / 3647) ≤ (176948827 / 500000000) := by
  have h := checkLog_sound (w := (1087 / 6207)) (n := 12)
    (lo := (353897653 / 1000000000)) (hi := (176948827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3647 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3647 / 2560) = 1/(2560 / 3647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (353897653 / 1000000000) (176948827 / 500000000) (Real.log (3647 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3647 / 2560) = -Real.log (2560 / 3647) := by
    rw [show ((3647 / 2560) : ℝ) = ((2560 / 3647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (552706121 / 1000000000) ≤ -Real.log (1473 / 2560) ∧
    -Real.log (1473 / 2560) ≤ (276353061 / 500000000) := by
  have h := checkLog_sound (w := (1087 / 4033)) (n := 12)
    (lo := (552706121 / 1000000000)) (hi := (276353061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1473) = 1/(1473 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-276353061 / 500000000) (-552706121 / 1000000000) (Real.log (1473 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (353486271 / 1000000000) ≤ -Real.log (5120 / 7291) ∧
    -Real.log (5120 / 7291) ≤ (5523223 / 15625000) := by
  have h := checkLog_sound (w := (2171 / 12411)) (n := 12)
    (lo := (353486271 / 1000000000)) (hi := (5523223 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7291 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7291 / 5120) = 1/(5120 / 7291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (353486271 / 1000000000) (5523223 / 15625000) (Real.log (7291 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7291 / 5120) = -Real.log (5120 / 7291) := by
    rw [show ((7291 / 5120) : ℝ) = ((5120 / 7291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (551688309 / 1000000000) ≤ -Real.log (2949 / 5120) ∧
    -Real.log (2949 / 5120) ≤ (55168831 / 100000000) := by
  have h := checkLog_sound (w := (2171 / 8069)) (n := 12)
    (lo := (551688309 / 1000000000)) (hi := (55168831 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2949) = 1/(2949 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-55168831 / 100000000) (-551688309 / 1000000000) (Real.log (2949 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8253187 / 31250000) ≤ -Real.log (1000000 / 1302261) ∧
    -Real.log (1000000 / 1302261) ≤ (52820397 / 200000000) := by
  have h := checkLog_sound (w := (302261 / 2302261)) (n := 12)
    (lo := (8253187 / 31250000)) (hi := (52820397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1302261 / 1000000) = 1/(1000000 / 1302261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8253187 / 31250000) (52820397 / 200000000) (Real.log (1302261 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1302261 / 1000000) = -Real.log (1000000 / 1302261) := by
    rw [show ((1302261 / 1000000) : ℝ) = ((1000000 / 1302261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (359910171 / 1000000000) ≤ -Real.log (697739 / 1000000) ∧
    -Real.log (697739 / 1000000) ≤ (89977543 / 250000000) := by
  have h := checkLog_sound (w := (302261 / 1697739)) (n := 12)
    (lo := (359910171 / 1000000000)) (hi := (89977543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 697739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 697739) = 1/(697739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-89977543 / 250000000) (-359910171 / 1000000000) (Real.log (697739 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (132214527 / 500000000) ≤ -Real.log (1000000 / 1302687) ∧
    -Real.log (1000000 / 1302687) ≤ (52885811 / 200000000) := by
  have h := checkLog_sound (w := (302687 / 2302687)) (n := 12)
    (lo := (132214527 / 500000000)) (hi := (52885811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1302687 / 1000000) = 1/(1000000 / 1302687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (132214527 / 500000000) (52885811 / 200000000) (Real.log (1302687 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1302687 / 1000000) = -Real.log (1000000 / 1302687) := by
    rw [show ((1302687 / 1000000) : ℝ) = ((1000000 / 1302687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (360520901 / 1000000000) ≤ -Real.log (697313 / 1000000) ∧
    -Real.log (697313 / 1000000) ≤ (180260451 / 500000000) := by
  have h := checkLog_sound (w := (302687 / 1697313)) (n := 12)
    (lo := (360520901 / 1000000000)) (hi := (180260451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 697313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 697313) = 1/(697313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-180260451 / 500000000) (-360520901 / 1000000000) (Real.log (697313 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9912903 / 50000000) ≤ -Real.log (1000000 / 1219277) ∧
    -Real.log (1000000 / 1219277) ≤ (198258061 / 1000000000) := by
  have h := checkLog_sound (w := (219277 / 2219277)) (n := 12)
    (lo := (9912903 / 50000000)) (hi := (198258061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219277 / 1000000) = 1/(1000000 / 1219277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9912903 / 50000000) (198258061 / 1000000000) (Real.log (1219277 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1219277 / 1000000) = -Real.log (1000000 / 1219277) := by
    rw [show ((1219277 / 1000000) : ℝ) = ((1000000 / 1219277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49506973 / 200000000) ≤ -Real.log (780723 / 1000000) ∧
    -Real.log (780723 / 1000000) ≤ (123767433 / 500000000) := by
  have h := checkLog_sound (w := (219277 / 1780723)) (n := 12)
    (lo := (49506973 / 200000000)) (hi := (123767433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780723) = 1/(780723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-123767433 / 500000000) (-49506973 / 200000000) (Real.log (780723 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (39705079 / 200000000) ≤ -Real.log (1000000 / 1219603) ∧
    -Real.log (1000000 / 1219603) ≤ (49631349 / 250000000) := by
  have h := checkLog_sound (w := (219603 / 2219603)) (n := 12)
    (lo := (39705079 / 200000000)) (hi := (49631349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219603 / 1000000) = 1/(1000000 / 1219603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (39705079 / 200000000) (49631349 / 250000000) (Real.log (1219603 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1219603 / 1000000) = -Real.log (1000000 / 1219603) := by
    rw [show ((1219603 / 1000000) : ℝ) = ((1000000 / 1219603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (123976257 / 500000000) ≤ -Real.log (780397 / 1000000) ∧
    -Real.log (780397 / 1000000) ≤ (49590503 / 200000000) := by
  have h := checkLog_sound (w := (219603 / 1780397)) (n := 12)
    (lo := (123976257 / 500000000)) (hi := (49590503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780397) = 1/(780397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-49590503 / 200000000) (-123976257 / 500000000) (Real.log (780397 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (156003039 / 250000000) ≤ -Real.log (125000000000 / 233300166681) ∧
    -Real.log (125000000000 / 233300166681) ≤ (624012157 / 1000000000) := by
  have h := checkLog_sound (w := (108300166681 / 358300166681)) (n := 12)
    (lo := (156003039 / 250000000)) (hi := (624012157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233300166681 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233300166681 / 125000000000) = 1/(125000000000 / 233300166681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (156003039 / 250000000) (624012157 / 1000000000) (Real.log (233300166681 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (233300166681 / 125000000000) = -Real.log (125000000000 / 233300166681) := by
    rw [show ((233300166681 / 125000000000) : ℝ) = ((125000000000 / 233300166681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (124989991 / 200000000) ≤ -Real.log (4000000000 / 7472609861) ∧
    -Real.log (4000000000 / 7472609861) ≤ (156237489 / 250000000) := by
  have h := checkLog_sound (w := (3472609861 / 11472609861)) (n := 12)
    (lo := (124989991 / 200000000)) (hi := (156237489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7472609861 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7472609861 / 4000000000) = 1/(4000000000 / 7472609861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (124989991 / 200000000) (156237489 / 250000000) (Real.log (7472609861 / 4000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7472609861 / 4000000000) = -Real.log (4000000000 / 7472609861) := by
    rw [show ((7472609861 / 4000000000) : ℝ) = ((4000000000 / 7472609861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17831717 / 40000000) ≤ -Real.log (500000000000 / 780864019633) ∧
    -Real.log (500000000000 / 780864019633) ≤ (222896463 / 500000000) := by
  have h := checkLog_sound (w := (280864019633 / 1280864019633)) (n := 12)
    (lo := (17831717 / 40000000)) (hi := (222896463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780864019633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(780864019633 / 500000000000) = 1/(500000000000 / 780864019633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (17831717 / 40000000) (222896463 / 500000000) (Real.log (780864019633 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (780864019633 / 500000000000) = -Real.log (500000000000 / 780864019633) := by
    rw [show ((780864019633 / 500000000000) : ℝ) = ((500000000000 / 780864019633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (44647791 / 100000000) ≤ -Real.log (20000000000 / 31255963311) ∧
    -Real.log (20000000000 / 31255963311) ≤ (446477911 / 1000000000) := by
  have h := checkLog_sound (w := (11255963311 / 51255963311)) (n := 12)
    (lo := (44647791 / 100000000)) (hi := (446477911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31255963311 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31255963311 / 20000000000) = 1/(20000000000 / 31255963311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (44647791 / 100000000) (446477911 / 1000000000) (Real.log (31255963311 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (31255963311 / 20000000000) = -Real.log (20000000000 / 31255963311) := by
    rw [show ((31255963311 / 20000000000) : ℝ) = ((20000000000 / 31255963311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0432

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0433Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0433
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

theorem reflection_log_1_neg : (48070389 / 250000000) ≤ -Real.log (10240 / 12411) ∧
    -Real.log (10240 / 12411) ≤ (192281557 / 1000000000) := by
  have h := checkLog_sound (w := (2171 / 22651)) (n := 12)
    (lo := (48070389 / 250000000)) (hi := (192281557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12411 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12411 / 10240) = 1/(10240 / 12411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (48070389 / 250000000) (192281557 / 1000000000) (Real.log (12411 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12411 / 10240) = -Real.log (10240 / 12411) := by
    rw [show ((12411 / 10240) : ℝ) = ((10240 / 12411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (11913603 / 50000000) ≤ -Real.log (8069 / 10240) ∧
    -Real.log (8069 / 10240) ≤ (238272061 / 1000000000) := by
  have h := checkLog_sound (w := (2171 / 18309)) (n := 12)
    (lo := (11913603 / 50000000)) (hi := (238272061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8069) = 1/(8069 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-238272061 / 1000000000) (-11913603 / 50000000) (Real.log (8069 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (96019903 / 500000000) ≤ -Real.log (1280 / 1551) ∧
    -Real.log (1280 / 1551) ≤ (192039807 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2831)) (n := 12)
    (lo := (96019903 / 500000000)) (hi := (192039807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1551 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1551 / 1280) = 1/(1280 / 1551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (96019903 / 500000000) (192039807 / 1000000000) (Real.log (1551 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1551 / 1280) = -Real.log (1280 / 1551) := by
    rw [show ((1551 / 1280) : ℝ) = ((1280 / 1551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (14868771 / 62500000) ≤ -Real.log (1009 / 1280) ∧
    -Real.log (1009 / 1280) ≤ (237900337 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2289)) (n := 12)
    (lo := (14868771 / 62500000)) (hi := (237900337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1009) = 1/(1009 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-237900337 / 1000000000) (-14868771 / 62500000) (Real.log (1009 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (353486271 / 1000000000) ≤ -Real.log (5120 / 7291) ∧
    -Real.log (5120 / 7291) ≤ (5523223 / 15625000) := by
  have h := checkLog_sound (w := (2171 / 12411)) (n := 12)
    (lo := (353486271 / 1000000000)) (hi := (5523223 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7291 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7291 / 5120) = 1/(5120 / 7291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (353486271 / 1000000000) (5523223 / 15625000) (Real.log (7291 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7291 / 5120) = -Real.log (5120 / 7291) := by
    rw [show ((7291 / 5120) : ℝ) = ((5120 / 7291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (551688309 / 1000000000) ≤ -Real.log (2949 / 5120) ∧
    -Real.log (2949 / 5120) ≤ (55168831 / 100000000) := by
  have h := checkLog_sound (w := (2171 / 8069)) (n := 12)
    (lo := (551688309 / 1000000000)) (hi := (55168831 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2949) = 1/(2949 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-55168831 / 100000000) (-551688309 / 1000000000) (Real.log (2949 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2206717 / 6250000) ≤ -Real.log (640 / 911) ∧
    -Real.log (640 / 911) ≤ (353074721 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1551)) (n := 12)
    (lo := (2206717 / 6250000)) (hi := (353074721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911 / 640) = 1/(640 / 911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2206717 / 6250000) (353074721 / 1000000000) (Real.log (911 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (911 / 640) = -Real.log (640 / 911) := by
    rw [show ((911 / 640) : ℝ) = ((640 / 911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (137667883 / 250000000) ≤ -Real.log (369 / 640) ∧
    -Real.log (369 / 640) ≤ (550671533 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1009)) (n := 12)
    (lo := (137667883 / 250000000)) (hi := (550671533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 369) = 1/(369 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-550671533 / 1000000000) (-137667883 / 250000000) (Real.log (369 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10551023 / 40000000) ≤ -Real.log (250000 / 325459) ∧
    -Real.log (250000 / 325459) ≤ (32971947 / 125000000) := by
  have h := checkLog_sound (w := (75459 / 575459)) (n := 12)
    (lo := (10551023 / 40000000)) (hi := (32971947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325459 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325459 / 250000) = 1/(250000 / 325459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10551023 / 40000000) (32971947 / 125000000) (Real.log (325459 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (325459 / 250000) = -Real.log (250000 / 325459) := by
    rw [show ((325459 / 250000) : ℝ) = ((250000 / 325459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (179650623 / 500000000) ≤ -Real.log (174541 / 250000) ∧
    -Real.log (174541 / 250000) ≤ (359301247 / 1000000000) := by
  have h := checkLog_sound (w := (75459 / 424541)) (n := 12)
    (lo := (179650623 / 500000000)) (hi := (359301247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 174541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 174541) = 1/(174541 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-359301247 / 1000000000) (-179650623 / 500000000) (Real.log (174541 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (8253211 / 31250000) ≤ -Real.log (500000 / 651131) ∧
    -Real.log (500000 / 651131) ≤ (264102753 / 1000000000) := by
  have h := checkLog_sound (w := (151131 / 1151131)) (n := 12)
    (lo := (8253211 / 31250000)) (hi := (264102753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651131 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651131 / 500000) = 1/(500000 / 651131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (8253211 / 31250000) (264102753 / 1000000000) (Real.log (651131 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (651131 / 500000) = -Real.log (500000 / 651131) := by
    rw [show ((651131 / 500000) : ℝ) = ((500000 / 651131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (89977901 / 250000000) ≤ -Real.log (348869 / 500000) ∧
    -Real.log (348869 / 500000) ≤ (71982321 / 200000000) := by
  have h := checkLog_sound (w := (151131 / 848869)) (n := 12)
    (lo := (89977901 / 250000000)) (hi := (71982321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 348869) = 1/(348869 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-71982321 / 200000000) (-89977901 / 250000000) (Real.log (348869 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (197992293 / 1000000000) ≤ -Real.log (1000000 / 1218953) ∧
    -Real.log (1000000 / 1218953) ≤ (98996147 / 500000000) := by
  have h := checkLog_sound (w := (218953 / 2218953)) (n := 12)
    (lo := (197992293 / 1000000000)) (hi := (98996147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218953 / 1000000) = 1/(1000000 / 1218953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (197992293 / 1000000000) (98996147 / 500000000) (Real.log (1218953 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1218953 / 1000000) = -Real.log (1000000 / 1218953) := by
    rw [show ((1218953 / 1000000) : ℝ) = ((1000000 / 1218953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (247119951 / 1000000000) ≤ -Real.log (781047 / 1000000) ∧
    -Real.log (781047 / 1000000) ≤ (15444997 / 62500000) := by
  have h := checkLog_sound (w := (218953 / 1781047)) (n := 12)
    (lo := (247119951 / 1000000000)) (hi := (15444997 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781047) = 1/(781047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-15444997 / 62500000) (-247119951 / 1000000000) (Real.log (781047 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (619559 / 3125000) ≤ -Real.log (500000 / 609639) ∧
    -Real.log (500000 / 609639) ≤ (198258881 / 1000000000) := by
  have h := checkLog_sound (w := (109639 / 1109639)) (n := 12)
    (lo := (619559 / 3125000)) (hi := (198258881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609639 / 500000) = 1/(500000 / 609639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (619559 / 3125000) (198258881 / 1000000000) (Real.log (609639 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (609639 / 500000) = -Real.log (500000 / 609639) := by
    rw [show ((609639 / 500000) : ℝ) = ((500000 / 609639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (123768073 / 500000000) ≤ -Real.log (390361 / 500000) ∧
    -Real.log (390361 / 500000) ≤ (247536147 / 1000000000) := by
  have h := checkLog_sound (w := (109639 / 890361)) (n := 12)
    (lo := (123768073 / 500000000)) (hi := (247536147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 390361) = 1/(390361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-247536147 / 1000000000) (-123768073 / 500000000) (Real.log (390361 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (311538411 / 500000000) ≤ -Real.log (125000000000 / 233082055219) ∧
    -Real.log (125000000000 / 233082055219) ≤ (623076823 / 1000000000) := by
  have h := checkLog_sound (w := (108082055219 / 358082055219)) (n := 12)
    (lo := (311538411 / 500000000)) (hi := (623076823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233082055219 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233082055219 / 125000000000) = 1/(125000000000 / 233082055219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (311538411 / 500000000) (623076823 / 1000000000) (Real.log (233082055219 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (233082055219 / 125000000000) = -Real.log (125000000000 / 233082055219) := by
    rw [show ((233082055219 / 125000000000) : ℝ) = ((125000000000 / 233082055219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (624014357 / 1000000000) ≤ -Real.log (500000000000 / 933202720793) ∧
    -Real.log (500000000000 / 933202720793) ≤ (312007179 / 500000000) := by
  have h := checkLog_sound (w := (433202720793 / 1433202720793)) (n := 12)
    (lo := (624014357 / 1000000000)) (hi := (312007179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933202720793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933202720793 / 500000000000) = 1/(500000000000 / 933202720793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (624014357 / 1000000000) (312007179 / 500000000) (Real.log (933202720793 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (933202720793 / 500000000000) = -Real.log (500000000000 / 933202720793) := by
    rw [show ((933202720793 / 500000000000) : ℝ) = ((500000000000 / 933202720793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (89022449 / 200000000) ≤ -Real.log (500000000000 / 780332681643) ∧
    -Real.log (500000000000 / 780332681643) ≤ (222556123 / 500000000) := by
  have h := checkLog_sound (w := (280332681643 / 1280332681643)) (n := 12)
    (lo := (89022449 / 200000000)) (hi := (222556123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780332681643 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(780332681643 / 500000000000) = 1/(500000000000 / 780332681643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (89022449 / 200000000) (222556123 / 500000000) (Real.log (780332681643 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (780332681643 / 500000000000) = -Real.log (500000000000 / 780332681643) := by
    rw [show ((780332681643 / 500000000000) : ℝ) = ((500000000000 / 780332681643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (222897513 / 500000000) ≤ -Real.log (62500000000 / 97608207531) ∧
    -Real.log (62500000000 / 97608207531) ≤ (445795027 / 1000000000) := by
  have h := checkLog_sound (w := (35108207531 / 160108207531)) (n := 12)
    (lo := (222897513 / 500000000)) (hi := (445795027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97608207531 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97608207531 / 62500000000) = 1/(62500000000 / 97608207531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (222897513 / 500000000) (445795027 / 1000000000) (Real.log (97608207531 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (97608207531 / 62500000000) = -Real.log (62500000000 / 97608207531) := by
    rw [show ((97608207531 / 62500000000) : ℝ) = ((62500000000 / 97608207531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0433

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0434Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0434
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

theorem reflection_log_1_neg : (96019903 / 500000000) ≤ -Real.log (1280 / 1551) ∧
    -Real.log (1280 / 1551) ≤ (192039807 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2831)) (n := 12)
    (lo := (96019903 / 500000000)) (hi := (192039807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1551 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1551 / 1280) = 1/(1280 / 1551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (96019903 / 500000000) (192039807 / 1000000000) (Real.log (1551 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1551 / 1280) = -Real.log (1280 / 1551) := by
    rw [show ((1551 / 1280) : ℝ) = ((1280 / 1551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (14868771 / 62500000) ≤ -Real.log (1009 / 1280) ∧
    -Real.log (1009 / 1280) ≤ (237900337 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2289)) (n := 12)
    (lo := (14868771 / 62500000)) (hi := (237900337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1009) = 1/(1009 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-237900337 / 1000000000) (-14868771 / 62500000) (Real.log (1009 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (191797997 / 1000000000) ≤ -Real.log (2048 / 2481) ∧
    -Real.log (2048 / 2481) ≤ (95898999 / 500000000) := by
  have h := checkLog_sound (w := (433 / 4529)) (n := 12)
    (lo := (191797997 / 1000000000)) (hi := (95898999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2481 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2481 / 2048) = 1/(2048 / 2481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (191797997 / 1000000000) (95898999 / 500000000) (Real.log (2481 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2481 / 2048) = -Real.log (2048 / 2481) := by
    rw [show ((2481 / 2048) : ℝ) = ((2048 / 2481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (190023 / 800000) ≤ -Real.log (1615 / 2048) ∧
    -Real.log (1615 / 2048) ≤ (237528751 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 3663)) (n := 12)
    (lo := (190023 / 800000)) (hi := (237528751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1615) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1615) = 1/(1615 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-237528751 / 1000000000) (-190023 / 800000) (Real.log (1615 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2206717 / 6250000) ≤ -Real.log (640 / 911) ∧
    -Real.log (640 / 911) ≤ (353074721 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1551)) (n := 12)
    (lo := (2206717 / 6250000)) (hi := (353074721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911 / 640) = 1/(640 / 911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2206717 / 6250000) (353074721 / 1000000000) (Real.log (911 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (911 / 640) = -Real.log (640 / 911) := by
    rw [show ((911 / 640) : ℝ) = ((640 / 911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (137667883 / 250000000) ≤ -Real.log (369 / 640) ∧
    -Real.log (369 / 640) ≤ (550671533 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1009)) (n := 12)
    (lo := (137667883 / 250000000)) (hi := (550671533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 369) = 1/(369 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-550671533 / 1000000000) (-137667883 / 250000000) (Real.log (369 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (352663 / 1000000) ≤ -Real.log (1024 / 1457) ∧
    -Real.log (1024 / 1457) ≤ (352663001 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2481)) (n := 12)
    (lo := (352663 / 1000000)) (hi := (352663001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1457 / 1024) = 1/(1024 / 1457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (352663 / 1000000) (352663001 / 1000000000) (Real.log (1457 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1457 / 1024) = -Real.log (1024 / 1457) := by
    rw [show ((1457 / 1024) : ℝ) = ((1024 / 1457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (137413947 / 250000000) ≤ -Real.log (591 / 1024) ∧
    -Real.log (591 / 1024) ≤ (549655789 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 1615)) (n := 12)
    (lo := (137413947 / 250000000)) (hi := (549655789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 591) = 1/(591 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-549655789 / 1000000000) (-137413947 / 250000000) (Real.log (591 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (13172453 / 50000000) ≤ -Real.log (1000000 / 1301411) ∧
    -Real.log (1000000 / 1301411) ≤ (263449061 / 1000000000) := by
  have h := checkLog_sound (w := (301411 / 2301411)) (n := 12)
    (lo := (13172453 / 50000000)) (hi := (263449061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301411 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301411 / 1000000) = 1/(1000000 / 1301411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (13172453 / 50000000) (263449061 / 1000000000) (Real.log (1301411 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1301411 / 1000000) = -Real.log (1000000 / 1301411) := by
    rw [show ((1301411 / 1000000) : ℝ) = ((1000000 / 1301411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89673173 / 250000000) ≤ -Real.log (698589 / 1000000) ∧
    -Real.log (698589 / 1000000) ≤ (358692693 / 1000000000) := by
  have h := checkLog_sound (w := (301411 / 1698589)) (n := 12)
    (lo := (89673173 / 250000000)) (hi := (358692693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 698589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 698589) = 1/(698589 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-358692693 / 1000000000) (-89673173 / 250000000) (Real.log (698589 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (263776343 / 1000000000) ≤ -Real.log (1000000 / 1301837) ∧
    -Real.log (1000000 / 1301837) ≤ (32972043 / 125000000) := by
  have h := checkLog_sound (w := (301837 / 2301837)) (n := 12)
    (lo := (263776343 / 1000000000)) (hi := (32972043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301837 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301837 / 1000000) = 1/(1000000 / 1301837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (263776343 / 1000000000) (32972043 / 125000000) (Real.log (1301837 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1301837 / 1000000) = -Real.log (1000000 / 1301837) := by
    rw [show ((1301837 / 1000000) : ℝ) = ((1000000 / 1301837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (359302679 / 1000000000) ≤ -Real.log (698163 / 1000000) ∧
    -Real.log (698163 / 1000000) ≤ (8982567 / 25000000) := by
  have h := checkLog_sound (w := (301837 / 1698163)) (n := 12)
    (lo := (359302679 / 1000000000)) (hi := (8982567 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 698163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 698163) = 1/(698163 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8982567 / 25000000) (-359302679 / 1000000000) (Real.log (698163 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (24715807 / 125000000) ≤ -Real.log (1000000 / 1218629) ∧
    -Real.log (1000000 / 1218629) ≤ (197726457 / 1000000000) := by
  have h := checkLog_sound (w := (218629 / 2218629)) (n := 12)
    (lo := (24715807 / 125000000)) (hi := (197726457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218629 / 1000000) = 1/(1000000 / 1218629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (24715807 / 125000000) (197726457 / 1000000000) (Real.log (1218629 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1218629 / 1000000) = -Real.log (1000000 / 1218629) := by
    rw [show ((1218629 / 1000000) : ℝ) = ((1000000 / 1218629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (246705209 / 1000000000) ≤ -Real.log (781371 / 1000000) ∧
    -Real.log (781371 / 1000000) ≤ (24670521 / 100000000) := by
  have h := checkLog_sound (w := (218629 / 1781371)) (n := 12)
    (lo := (246705209 / 1000000000)) (hi := (24670521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781371) = 1/(781371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-24670521 / 100000000) (-246705209 / 1000000000) (Real.log (781371 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (197993113 / 1000000000) ≤ -Real.log (500000 / 609477) ∧
    -Real.log (500000 / 609477) ≤ (98996557 / 500000000) := by
  have h := checkLog_sound (w := (109477 / 1109477)) (n := 12)
    (lo := (197993113 / 1000000000)) (hi := (98996557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609477 / 500000) = 1/(500000 / 609477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (197993113 / 1000000000) (98996557 / 500000000) (Real.log (609477 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (609477 / 500000) = -Real.log (500000 / 609477) := by
    rw [show ((609477 / 500000) : ℝ) = ((500000 / 609477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (15445077 / 62500000) ≤ -Real.log (390523 / 500000) ∧
    -Real.log (390523 / 500000) ≤ (247121233 / 1000000000) := by
  have h := checkLog_sound (w := (109477 / 890523)) (n := 12)
    (lo := (15445077 / 62500000)) (hi := (247121233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 390523) = 1/(390523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-247121233 / 1000000000) (-15445077 / 62500000) (Real.log (390523 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (77767719 / 125000000) ≤ -Real.log (250000000000 / 465728418283) ∧
    -Real.log (250000000000 / 465728418283) ≤ (622141753 / 1000000000) := by
  have h := checkLog_sound (w := (215728418283 / 715728418283)) (n := 12)
    (lo := (77767719 / 125000000)) (hi := (622141753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((465728418283 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(465728418283 / 250000000000) = 1/(250000000000 / 465728418283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (77767719 / 125000000) (622141753 / 1000000000) (Real.log (465728418283 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (465728418283 / 250000000000) = -Real.log (250000000000 / 465728418283) := by
    rw [show ((465728418283 / 250000000000) : ℝ) = ((250000000000 / 465728418283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (623079023 / 1000000000) ≤ -Real.log (125000000000 / 233082568111) ∧
    -Real.log (125000000000 / 233082568111) ≤ (38942439 / 62500000) := by
  have h := checkLog_sound (w := (108082568111 / 358082568111)) (n := 12)
    (lo := (623079023 / 1000000000)) (hi := (38942439 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233082568111 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233082568111 / 125000000000) = 1/(125000000000 / 233082568111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (623079023 / 1000000000) (38942439 / 62500000) (Real.log (233082568111 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (233082568111 / 125000000000) = -Real.log (125000000000 / 233082568111) := by
    rw [show ((233082568111 / 125000000000) : ℝ) = ((125000000000 / 233082568111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (222215833 / 500000000) ≤ -Real.log (500000000000 / 779801784299) ∧
    -Real.log (500000000000 / 779801784299) ≤ (444431667 / 1000000000) := by
  have h := checkLog_sound (w := (279801784299 / 1279801784299)) (n := 12)
    (lo := (222215833 / 500000000)) (hi := (444431667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779801784299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779801784299 / 500000000000) = 1/(500000000000 / 779801784299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (222215833 / 500000000) (444431667 / 1000000000) (Real.log (779801784299 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (779801784299 / 500000000000) = -Real.log (500000000000 / 779801784299) := by
    rw [show ((779801784299 / 500000000000) : ℝ) = ((500000000000 / 779801784299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (89022869 / 200000000) ≤ -Real.log (250000000000 / 390167160449) ∧
    -Real.log (250000000000 / 390167160449) ≤ (222557173 / 500000000) := by
  have h := checkLog_sound (w := (140167160449 / 640167160449)) (n := 12)
    (lo := (89022869 / 200000000)) (hi := (222557173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390167160449 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390167160449 / 250000000000) = 1/(250000000000 / 390167160449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (89022869 / 200000000) (222557173 / 500000000) (Real.log (390167160449 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (390167160449 / 250000000000) = -Real.log (250000000000 / 390167160449) := by
    rw [show ((390167160449 / 250000000000) : ℝ) = ((250000000000 / 390167160449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0434

end


