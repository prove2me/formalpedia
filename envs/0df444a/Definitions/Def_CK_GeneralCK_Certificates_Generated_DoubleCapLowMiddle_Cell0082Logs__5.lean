-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0082Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0082Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:55:17.154722+00:00
-- url     : https://prove2.me/theorems/981efb94-bf9e-445f-b9b2-1675c69c6565
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0082Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0083Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0082Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0083Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0084Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0085Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0086Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0082Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0083Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0084Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0085Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0086Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0082Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0083Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0084Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0085Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0086Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0082Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0083Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0084Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0085Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0086Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0082Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0082
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

theorem reflection_log_1_neg : (337408063 / 500000000) ≤ -Real.log (2560 / 5027) ∧
    -Real.log (2560 / 5027) ≤ (674816127 / 1000000000) := by
  have h := checkLog_sound (w := (2467 / 7587)) (n := 12)
    (lo := (337408063 / 500000000)) (hi := (674816127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5027 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5027 / 2560) = 1/(2560 / 5027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (337408063 / 500000000) (674816127 / 1000000000) (Real.log (5027 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5027 / 2560) = -Real.log (2560 / 5027) := by
    rw [show ((5027 / 2560) : ℝ) = ((2560 / 5027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1657581521 / 500000000) ≤ -Real.log (93 / 2560) ∧
    -Real.log (93 / 2560) ≤ (3315163047 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 93) = 1/(93 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3315163047 / 1000000000) (-1657581521 / 500000000) (Real.log (93 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (84328391 / 125000000) ≤ -Real.log (51200 / 100521) ∧
    -Real.log (51200 / 100521) ≤ (674627129 / 1000000000) := by
  have h := checkLog_sound (w := (49321 / 151721)) (n := 12)
    (lo := (84328391 / 125000000)) (hi := (674627129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100521 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100521 / 51200) = 1/(51200 / 100521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (84328391 / 125000000) (674627129 / 1000000000) (Real.log (100521 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100521 / 51200) = -Real.log (51200 / 100521) := by
    rw [show ((100521 / 51200) : ℝ) = ((51200 / 100521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3304999809 / 1000000000) ≤ -Real.log (1879 / 51200) ∧
    -Real.log (1879 / 51200) ≤ (1652499907 / 500000000) := by
  have h := checkLog_sound (w := (1321 / 5079)) (n := 12)
    (lo := (532411089 / 1000000000)) (hi := (53241109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1879) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1879) = 1/(1879 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1652499907 / 500000000) (-3304999809 / 1000000000) (Real.log (1879 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (656142759 / 1000000000) ≤ -Real.log (1280 / 2467) ∧
    -Real.log (1280 / 2467) ≤ (16403569 / 25000000) := by
  have h := checkLog_sound (w := (1187 / 3747)) (n := 12)
    (lo := (656142759 / 1000000000)) (hi := (16403569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2467 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2467 / 1280) = 1/(1280 / 2467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (656142759 / 1000000000) (16403569 / 25000000) (Real.log (2467 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2467 / 1280) = -Real.log (1280 / 2467) := by
    rw [show ((2467 / 1280) : ℝ) = ((1280 / 2467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1311007931 / 500000000) ≤ -Real.log (93 / 1280) ∧
    -Real.log (93 / 1280) ≤ (1311007933 / 500000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 93) = 1/(93 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1311007933 / 500000000) (-1311007931 / 500000000) (Real.log (93 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (327878801 / 500000000) ≤ -Real.log (25600 / 49321) ∧
    -Real.log (25600 / 49321) ≤ (655757603 / 1000000000) := by
  have h := checkLog_sound (w := (23721 / 74921)) (n := 12)
    (lo := (327878801 / 500000000)) (hi := (655757603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49321 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49321 / 25600) = 1/(25600 / 49321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (327878801 / 500000000) (655757603 / 1000000000) (Real.log (49321 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49321 / 25600) = -Real.log (25600 / 49321) := by
    rw [show ((49321 / 25600) : ℝ) = ((25600 / 49321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2611852629 / 1000000000) ≤ -Real.log (1879 / 25600) ∧
    -Real.log (1879 / 25600) ≤ (2611852633 / 1000000000) := by
  have h := checkLog_sound (w := (1321 / 5079)) (n := 12)
    (lo := (532411089 / 1000000000)) (hi := (53241109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1879) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1879) = 1/(1879 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2611852633 / 1000000000) (-2611852629 / 1000000000) (Real.log (1879 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (677845707 / 1000000000) ≤ -Real.log (100000 / 196963) ∧
    -Real.log (100000 / 196963) ≤ (169461427 / 250000000) := by
  have h := checkLog_sound (w := (96963 / 296963)) (n := 12)
    (lo := (677845707 / 1000000000)) (hi := (169461427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196963 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196963 / 100000) = 1/(100000 / 196963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (677845707 / 1000000000) (169461427 / 250000000) (Real.log (196963 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (196963 / 100000) = -Real.log (100000 / 196963) := by
    rw [show ((196963 / 100000) : ℝ) = ((100000 / 196963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3494299997 / 1000000000) ≤ -Real.log (3037 / 100000) ∧
    -Real.log (3037 / 100000) ≤ (3494300003 / 1000000000) := by
  have h := checkLog_sound (w := (44 / 3081)) (n := 12)
    (lo := (28564097 / 1000000000)) (hi := (14282049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3037) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 3037) = 1/(3037 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3494300003 / 1000000000) (-3494299997 / 1000000000) (Real.log (3037 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169498487 / 250000000) ≤ -Real.log (500000 / 984961) ∧
    -Real.log (500000 / 984961) ≤ (677993949 / 1000000000) := by
  have h := checkLog_sound (w := (484961 / 1484961)) (n := 12)
    (lo := (169498487 / 250000000)) (hi := (677993949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((984961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(984961 / 500000) = 1/(500000 / 984961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169498487 / 250000000) (677993949 / 1000000000) (Real.log (984961 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (984961 / 500000) = -Real.log (500000 / 984961) := by
    rw [show ((984961 / 500000) : ℝ) = ((500000 / 984961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (875990317 / 250000000) ≤ -Real.log (15039 / 500000) ∧
    -Real.log (15039 / 500000) ≤ (1751980637 / 500000000) := by
  have h := checkLog_sound (w := (293 / 15332)) (n := 12)
    (lo := (4778171 / 125000000)) (hi := (38225369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15039) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 15039) = 1/(15039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1751980637 / 500000000) (-875990317 / 250000000) (Real.log (15039 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (135544973 / 200000000) ≤ -Real.log (62500 / 123087) ∧
    -Real.log (62500 / 123087) ≤ (338862433 / 500000000) := by
  have h := checkLog_sound (w := (60587 / 185587)) (n := 12)
    (lo := (135544973 / 200000000)) (hi := (338862433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123087 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123087 / 62500) = 1/(62500 / 123087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (135544973 / 200000000) (338862433 / 500000000) (Real.log (123087 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (123087 / 62500) = -Real.log (62500 / 123087) := by
    rw [show ((123087 / 62500) : ℝ) = ((62500 / 123087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3486493863 / 1000000000) ≤ -Real.log (1913 / 62500) ∧
    -Real.log (1913 / 62500) ≤ (3486493869 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 30929)) (n := 12)
    (lo := (20757963 / 1000000000)) (hi := (5189491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15304) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 15304) = 1/(1913 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3486493869 / 1000000000) (-3486493863 / 1000000000) (Real.log (1913 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (338937831 / 500000000) ≤ -Real.log (1000000 / 1969689) ∧
    -Real.log (1000000 / 1969689) ≤ (677875663 / 1000000000) := by
  have h := checkLog_sound (w := (969689 / 2969689)) (n := 12)
    (lo := (338937831 / 500000000)) (hi := (677875663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969689 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969689 / 1000000) = 1/(1000000 / 1969689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (338937831 / 500000000) (677875663 / 1000000000) (Real.log (1969689 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1969689 / 1000000) = -Real.log (1000000 / 1969689) := by
    rw [show ((1969689 / 1000000) : ℝ) = ((1000000 / 1969689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3496244593 / 1000000000) ≤ -Real.log (30311 / 1000000) ∧
    -Real.log (30311 / 1000000) ≤ (3496244599 / 1000000000) := by
  have h := checkLog_sound (w := (939 / 61561)) (n := 12)
    (lo := (30508693 / 1000000000)) (hi := (15254347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30311) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30311) = 1/(30311 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3496244599 / 1000000000) (-3496244593 / 1000000000) (Real.log (30311 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (521518213 / 125000000) ≤ -Real.log (31250000000 / 2026701926243) ∧
    -Real.log (31250000000 / 2026701926243) ≤ (4172145711 / 1000000000) := by
  have h := checkLog_sound (w := (26701926243 / 4026701926243)) (n := 12)
    (lo := (414457 / 31250000)) (hi := (106101 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2026701926243 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2026701926243 / 2000000000000) = 1/(31250000000 / 2026701926243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (521518213 / 125000000) (4172145711 / 1000000000) (Real.log (2026701926243 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2026701926243 / 31250000000) = -Real.log (31250000000 / 2026701926243) := by
    rw [show ((2026701926243 / 31250000000) : ℝ) = ((31250000000 / 2026701926243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (261372201 / 62500000) ≤ -Real.log (500000000000 / 32746891415653) ∧
    -Real.log (500000000000 / 32746891415653) ≤ (4181955223 / 1000000000) := by
  have h := checkLog_sound (w := (746891415653 / 64746891415653)) (n := 12)
    (lo := (2884017 / 125000000)) (hi := (23072137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32746891415653 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32746891415653 / 32000000000000) = 1/(500000000000 / 32746891415653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (261372201 / 62500000) (4181955223 / 1000000000) (Real.log (32746891415653 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (32746891415653 / 500000000000) = -Real.log (500000000000 / 32746891415653) := by
    rw [show ((32746891415653 / 500000000000) : ℝ) = ((500000000000 / 32746891415653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (520527341 / 125000000) ≤ -Real.log (25000000000 / 1608559853633) ∧
    -Real.log (25000000000 / 1608559853633) ≤ (832843747 / 200000000) := by
  have h := checkLog_sound (w := (8559853633 / 3208559853633)) (n := 12)
    (lo := (166739 / 31250000)) (hi := (5335649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1608559853633 / 1600000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1608559853633 / 1600000000000) = 1/(25000000000 / 1608559853633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (520527341 / 125000000) (832843747 / 200000000) (Real.log (1608559853633 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1608559853633 / 25000000000) = -Real.log (25000000000 / 1608559853633) := by
    rw [show ((1608559853633 / 25000000000) : ℝ) = ((25000000000 / 1608559853633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2087060127 / 500000000) ≤ -Real.log (500000000000 / 32491323281977) ∧
    -Real.log (500000000000 / 32491323281977) ≤ (4174120261 / 1000000000) := by
  have h := checkLog_sound (w := (491323281977 / 64491323281977)) (n := 12)
    (lo := (7618587 / 500000000)) (hi := (609487 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32491323281977 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32491323281977 / 32000000000000) = 1/(500000000000 / 32491323281977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2087060127 / 500000000) (4174120261 / 1000000000) (Real.log (32491323281977 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (32491323281977 / 500000000000) = -Real.log (500000000000 / 32491323281977) := by
    rw [show ((32491323281977 / 500000000000) : ℝ) = ((500000000000 / 32491323281977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0082

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0083Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0083
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

theorem reflection_log_1_neg : (84328391 / 125000000) ≤ -Real.log (51200 / 100521) ∧
    -Real.log (51200 / 100521) ≤ (674627129 / 1000000000) := by
  have h := checkLog_sound (w := (49321 / 151721)) (n := 12)
    (lo := (84328391 / 125000000)) (hi := (674627129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100521 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100521 / 51200) = 1/(51200 / 100521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (84328391 / 125000000) (674627129 / 1000000000) (Real.log (100521 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100521 / 51200) = -Real.log (51200 / 100521) := by
    rw [show ((100521 / 51200) : ℝ) = ((51200 / 100521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3304999809 / 1000000000) ≤ -Real.log (1879 / 51200) ∧
    -Real.log (1879 / 51200) ≤ (1652499907 / 500000000) := by
  have h := checkLog_sound (w := (1321 / 5079)) (n := 12)
    (lo := (532411089 / 1000000000)) (hi := (53241109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1879) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1879) = 1/(1879 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1652499907 / 500000000) (-3304999809 / 1000000000) (Real.log (1879 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (134887619 / 200000000) ≤ -Real.log (25600 / 50251) ∧
    -Real.log (25600 / 50251) ≤ (42152381 / 62500000) := by
  have h := checkLog_sound (w := (24651 / 75851)) (n := 12)
    (lo := (134887619 / 200000000)) (hi := (42152381 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50251 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50251 / 25600) = 1/(25600 / 50251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (134887619 / 200000000) (42152381 / 62500000) (Real.log (50251 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50251 / 25600) = -Real.log (25600 / 50251) := by
    rw [show ((50251 / 25600) : ℝ) = ((25600 / 50251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3294938829 / 1000000000) ≤ -Real.log (949 / 25600) ∧
    -Real.log (949 / 25600) ≤ (1647469417 / 500000000) := by
  have h := checkLog_sound (w := (651 / 2549)) (n := 12)
    (lo := (522350109 / 1000000000)) (hi := (52235011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 949) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 949) = 1/(949 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1647469417 / 500000000) (-3294938829 / 1000000000) (Real.log (949 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (327878801 / 500000000) ≤ -Real.log (25600 / 49321) ∧
    -Real.log (25600 / 49321) ≤ (655757603 / 1000000000) := by
  have h := checkLog_sound (w := (23721 / 74921)) (n := 12)
    (lo := (327878801 / 500000000)) (hi := (655757603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49321 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49321 / 25600) = 1/(25600 / 49321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (327878801 / 500000000) (655757603 / 1000000000) (Real.log (49321 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49321 / 25600) = -Real.log (25600 / 49321) := by
    rw [show ((49321 / 25600) : ℝ) = ((25600 / 49321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2611852629 / 1000000000) ≤ -Real.log (1879 / 25600) ∧
    -Real.log (1879 / 25600) ≤ (2611852633 / 1000000000) := by
  have h := checkLog_sound (w := (1321 / 5079)) (n := 12)
    (lo := (532411089 / 1000000000)) (hi := (53241109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1879) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1879) = 1/(1879 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2611852633 / 1000000000) (-2611852629 / 1000000000) (Real.log (1879 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (81921537 / 125000000) ≤ -Real.log (12800 / 24651) ∧
    -Real.log (12800 / 24651) ≤ (655372297 / 1000000000) := by
  have h := checkLog_sound (w := (11851 / 37451)) (n := 12)
    (lo := (81921537 / 125000000)) (hi := (655372297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24651 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24651 / 12800) = 1/(12800 / 24651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (81921537 / 125000000) (655372297 / 1000000000) (Real.log (24651 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24651 / 12800) = -Real.log (12800 / 24651) := by
    rw [show ((24651 / 12800) : ℝ) = ((12800 / 24651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2601791649 / 1000000000) ≤ -Real.log (949 / 12800) ∧
    -Real.log (949 / 12800) ≤ (2601791653 / 1000000000) := by
  have h := checkLog_sound (w := (651 / 2549)) (n := 12)
    (lo := (522350109 / 1000000000)) (hi := (52235011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 949) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 949) = 1/(949 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2601791653 / 1000000000) (-2601791649 / 1000000000) (Real.log (949 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (677698461 / 1000000000) ≤ -Real.log (50000 / 98467) ∧
    -Real.log (50000 / 98467) ≤ (338849231 / 500000000) := by
  have h := checkLog_sound (w := (48467 / 148467)) (n := 12)
    (lo := (677698461 / 1000000000)) (hi := (338849231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98467 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98467 / 50000) = 1/(50000 / 98467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (677698461 / 1000000000) (338849231 / 500000000) (Real.log (98467 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (98467 / 50000) = -Real.log (50000 / 98467) := by
    rw [show ((98467 / 50000) : ℝ) = ((50000 / 98467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1742398201 / 500000000) ≤ -Real.log (1533 / 50000) ∧
    -Real.log (1533 / 50000) ≤ (435599551 / 125000000) := by
  have h := checkLog_sound (w := (59 / 6191)) (n := 12)
    (lo := (9530251 / 500000000)) (hi := (19060503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3066) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 3066) = 1/(1533 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-435599551 / 125000000) (-1742398201 / 500000000) (Real.log (1533 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135569243 / 200000000) ≤ -Real.log (1000000 / 1969631) ∧
    -Real.log (1000000 / 1969631) ≤ (84730777 / 125000000) := by
  have h := checkLog_sound (w := (969631 / 2969631)) (n := 12)
    (lo := (135569243 / 200000000)) (hi := (84730777 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969631 / 1000000) = 1/(1000000 / 1969631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135569243 / 200000000) (84730777 / 125000000) (Real.log (1969631 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1969631 / 1000000) = -Real.log (1000000 / 1969631) := by
    rw [show ((1969631 / 1000000) : ℝ) = ((1000000 / 1969631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (873583231 / 250000000) ≤ -Real.log (30369 / 1000000) ∧
    -Real.log (30369 / 1000000) ≤ (349433293 / 100000000) := by
  have h := checkLog_sound (w := (881 / 61619)) (n := 12)
    (lo := (893657 / 31250000)) (hi := (1143881 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30369) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30369) = 1/(30369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-349433293 / 100000000) (-873583231 / 250000000) (Real.log (30369 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (338787277 / 500000000) ≤ -Real.log (125000 / 246137) ∧
    -Real.log (125000 / 246137) ≤ (135514911 / 200000000) := by
  have h := checkLog_sound (w := (121137 / 371137)) (n := 12)
    (lo := (338787277 / 500000000)) (hi := (135514911 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246137 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246137 / 125000) = 1/(125000 / 246137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (338787277 / 500000000) (135514911 / 200000000) (Real.log (246137 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (246137 / 125000) = -Real.log (125000 / 246137) := by
    rw [show ((246137 / 125000) : ℝ) = ((125000 / 246137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69537393 / 20000000) ≤ -Real.log (3863 / 125000) ∧
    -Real.log (3863 / 125000) ≤ (434608707 / 125000000) := by
  have h := checkLog_sound (w := (173 / 31077)) (n := 12)
    (lo := (8907 / 800000)) (hi := (11133751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15452) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 15452) = 1/(3863 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-434608707 / 125000000) (-69537393 / 20000000) (Real.log (3863 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (677725373 / 1000000000) ≤ -Real.log (1000000 / 1969393) ∧
    -Real.log (1000000 / 1969393) ≤ (338862687 / 500000000) := by
  have h := checkLog_sound (w := (969393 / 2969393)) (n := 12)
    (lo := (677725373 / 1000000000)) (hi := (338862687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969393 / 1000000) = 1/(1000000 / 1969393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (677725373 / 1000000000) (338862687 / 500000000) (Real.log (1969393 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1969393 / 1000000) = -Real.log (1000000 / 1969393) := by
    rw [show ((1969393 / 1000000) : ℝ) = ((1000000 / 1969393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (697305307 / 200000000) ≤ -Real.log (30607 / 1000000) ∧
    -Real.log (30607 / 1000000) ≤ (3486526541 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 61857)) (n := 12)
    (lo := (4158127 / 200000000)) (hi := (5197659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30607) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30607) = 1/(30607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3486526541 / 1000000000) (-697305307 / 200000000) (Real.log (30607 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4162494863 / 1000000000) ≤ -Real.log (500000000000 / 32115786040443) ∧
    -Real.log (500000000000 / 32115786040443) ≤ (416249487 / 100000000) := by
  have h := checkLog_sound (w := (115786040443 / 64115786040443)) (n := 12)
    (lo := (3611783 / 1000000000)) (hi := (451473 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32115786040443 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32115786040443 / 32000000000000) = 1/(500000000000 / 32115786040443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4162494863 / 1000000000) (416249487 / 100000000) (Real.log (32115786040443 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (32115786040443 / 500000000000) = -Real.log (500000000000 / 32115786040443) := by
    rw [show ((32115786040443 / 500000000000) : ℝ) = ((500000000000 / 32115786040443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4172179139 / 1000000000) ≤ -Real.log (500000000000 / 32428315058119) ∧
    -Real.log (500000000000 / 32428315058119) ≤ (2086089573 / 500000000) := by
  have h := checkLog_sound (w := (428315058119 / 64428315058119)) (n := 12)
    (lo := (13296059 / 1000000000)) (hi := (664803 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32428315058119 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32428315058119 / 32000000000000) = 1/(500000000000 / 32428315058119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4172179139 / 1000000000) (2086089573 / 500000000) (Real.log (32428315058119 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (32428315058119 / 500000000000) = -Real.log (500000000000 / 32428315058119) := by
    rw [show ((32428315058119 / 500000000000) : ℝ) = ((500000000000 / 32428315058119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (830888841 / 200000000) ≤ -Real.log (500000000000 / 31858270774009) ∧
    -Real.log (500000000000 / 31858270774009) ≤ (4154444211 / 1000000000) := by
  have h := checkLog_sound (w := (15858270774009 / 47858270774009)) (n := 12)
    (lo := (137741661 / 200000000)) (hi := (344354153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31858270774009 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31858270774009 / 16000000000000) = 1/(500000000000 / 31858270774009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (830888841 / 200000000) (4154444211 / 1000000000) (Real.log (31858270774009 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (31858270774009 / 500000000000) = -Real.log (500000000000 / 31858270774009) := by
    rw [show ((31858270774009 / 500000000000) : ℝ) = ((500000000000 / 31858270774009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1041062977 / 250000000) ≤ -Real.log (250000000000 / 16086132257327) ∧
    -Real.log (250000000000 / 16086132257327) ≤ (832850383 / 200000000) := by
  have h := checkLog_sound (w := (86132257327 / 32086132257327)) (n := 12)
    (lo := (1342207 / 250000000)) (hi := (5368829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16086132257327 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(16086132257327 / 16000000000000) = 1/(250000000000 / 16086132257327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1041062977 / 250000000) (832850383 / 200000000) (Real.log (16086132257327 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16086132257327 / 250000000000) = -Real.log (250000000000 / 16086132257327) := by
    rw [show ((16086132257327 / 250000000000) : ℝ) = ((250000000000 / 16086132257327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0083

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0084Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0084
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

theorem reflection_log_1_neg : (134887619 / 200000000) ≤ -Real.log (25600 / 50251) ∧
    -Real.log (25600 / 50251) ≤ (42152381 / 62500000) := by
  have h := checkLog_sound (w := (24651 / 75851)) (n := 12)
    (lo := (134887619 / 200000000)) (hi := (42152381 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50251 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50251 / 25600) = 1/(25600 / 50251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (134887619 / 200000000) (42152381 / 62500000) (Real.log (50251 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50251 / 25600) = -Real.log (25600 / 50251) := by
    rw [show ((50251 / 25600) : ℝ) = ((25600 / 50251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3294938829 / 1000000000) ≤ -Real.log (949 / 25600) ∧
    -Real.log (949 / 25600) ≤ (1647469417 / 500000000) := by
  have h := checkLog_sound (w := (651 / 2549)) (n := 12)
    (lo := (522350109 / 1000000000)) (hi := (52235011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 949) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 949) = 1/(949 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1647469417 / 500000000) (-3294938829 / 1000000000) (Real.log (949 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (337124513 / 500000000) ≤ -Real.log (51200 / 100483) ∧
    -Real.log (51200 / 100483) ≤ (674249027 / 1000000000) := by
  have h := checkLog_sound (w := (49283 / 151683)) (n := 12)
    (lo := (337124513 / 500000000)) (hi := (674249027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100483 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100483 / 51200) = 1/(51200 / 100483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (337124513 / 500000000) (674249027 / 1000000000) (Real.log (100483 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100483 / 51200) = -Real.log (51200 / 100483) := by
    rw [show ((100483 / 51200) : ℝ) = ((51200 / 100483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (656995613 / 200000000) ≤ -Real.log (1917 / 51200) ∧
    -Real.log (1917 / 51200) ≤ (328497807 / 100000000) := by
  have h := checkLog_sound (w := (1283 / 5117)) (n := 12)
    (lo := (102477869 / 200000000)) (hi := (256194673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1917) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1917) = 1/(1917 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-328497807 / 100000000) (-656995613 / 200000000) (Real.log (1917 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (81921537 / 125000000) ≤ -Real.log (12800 / 24651) ∧
    -Real.log (12800 / 24651) ≤ (655372297 / 1000000000) := by
  have h := checkLog_sound (w := (11851 / 37451)) (n := 12)
    (lo := (81921537 / 125000000)) (hi := (655372297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24651 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24651 / 12800) = 1/(12800 / 24651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (81921537 / 125000000) (655372297 / 1000000000) (Real.log (24651 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24651 / 12800) = -Real.log (12800 / 24651) := by
    rw [show ((24651 / 12800) : ℝ) = ((12800 / 24651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2601791649 / 1000000000) ≤ -Real.log (949 / 12800) ∧
    -Real.log (949 / 12800) ≤ (2601791653 / 1000000000) := by
  have h := checkLog_sound (w := (651 / 2549)) (n := 12)
    (lo := (522350109 / 1000000000)) (hi := (52235011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 949) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 949) = 1/(949 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2601791653 / 1000000000) (-2601791649 / 1000000000) (Real.log (949 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (327493421 / 500000000) ≤ -Real.log (25600 / 49283) ∧
    -Real.log (25600 / 49283) ≤ (654986843 / 1000000000) := by
  have h := checkLog_sound (w := (23683 / 74883)) (n := 12)
    (lo := (327493421 / 500000000)) (hi := (654986843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49283 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49283 / 25600) = 1/(25600 / 49283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (327493421 / 500000000) (654986843 / 1000000000) (Real.log (49283 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49283 / 25600) = -Real.log (25600 / 49283) := by
    rw [show ((49283 / 25600) : ℝ) = ((25600 / 49283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (518366177 / 200000000) ≤ -Real.log (1917 / 25600) ∧
    -Real.log (1917 / 25600) ≤ (2591830889 / 1000000000) := by
  have h := checkLog_sound (w := (1283 / 5117)) (n := 12)
    (lo := (102477869 / 200000000)) (hi := (256194673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1917) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1917) = 1/(1917 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2591830889 / 1000000000) (-518366177 / 200000000) (Real.log (1917 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135510137 / 200000000) ≤ -Real.log (1000000 / 1969049) ∧
    -Real.log (1000000 / 1969049) ≤ (338775343 / 500000000) := by
  have h := checkLog_sound (w := (969049 / 2969049)) (n := 12)
    (lo := (135510137 / 200000000)) (hi := (338775343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969049 / 1000000) = 1/(1000000 / 1969049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135510137 / 200000000) (338775343 / 500000000) (Real.log (1969049 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1969049 / 1000000) = -Real.log (1000000 / 1969049) := by
    rw [show ((1969049 / 1000000) : ℝ) = ((1000000 / 1969049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3475349967 / 1000000000) ≤ -Real.log (30951 / 1000000) ∧
    -Real.log (30951 / 1000000) ≤ (3475349973 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 62201)) (n := 12)
    (lo := (9614067 / 1000000000)) (hi := (2403517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30951) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30951) = 1/(30951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3475349973 / 1000000000) (-3475349967 / 1000000000) (Real.log (30951 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (677698969 / 1000000000) ≤ -Real.log (1000000 / 1969341) ∧
    -Real.log (1000000 / 1969341) ≤ (67769897 / 100000000) := by
  have h := checkLog_sound (w := (969341 / 2969341)) (n := 12)
    (lo := (677698969 / 1000000000)) (hi := (67769897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969341 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969341 / 1000000) = 1/(1000000 / 1969341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (677698969 / 1000000000) (67769897 / 100000000) (Real.log (1969341 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1969341 / 1000000) = -Real.log (1000000 / 1969341) := by
    rw [show ((1969341 / 1000000) : ℝ) = ((1000000 / 1969341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3484829019 / 1000000000) ≤ -Real.log (30659 / 1000000) ∧
    -Real.log (30659 / 1000000) ≤ (139393161 / 40000000) := by
  have h := checkLog_sound (w := (591 / 61909)) (n := 12)
    (lo := (19093119 / 1000000000)) (hi := (29833 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30659) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30659) = 1/(30659 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-139393161 / 40000000) (-3484829019 / 1000000000) (Real.log (30659 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (33871211 / 50000000) ≤ -Real.log (1250 / 2461) ∧
    -Real.log (1250 / 2461) ≤ (677424221 / 1000000000) := by
  have h := checkLog_sound (w := (1211 / 3711)) (n := 12)
    (lo := (33871211 / 50000000)) (hi := (677424221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2461 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2461 / 1250) = 1/(1250 / 2461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (33871211 / 50000000) (677424221 / 1000000000) (Real.log (2461 / 1250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (2461 / 1250) = -Real.log (1250 / 2461) := by
    rw [show ((2461 / 1250) : ℝ) = ((1250 / 2461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3467337181 / 1000000000) ≤ -Real.log (39 / 1250) ∧
    -Real.log (39 / 1250) ≤ (3467337187 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 1249)) (n := 12)
    (lo := (1601281 / 1000000000)) (hi := (800641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 624) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(625 / 624) = 1/(39 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3467337187 / 1000000000) (-3467337181 / 1000000000) (Real.log (39 / 1250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (338787531 / 500000000) ≤ -Real.log (1000000 / 1969097) ∧
    -Real.log (1000000 / 1969097) ≤ (677575063 / 1000000000) := by
  have h := checkLog_sound (w := (969097 / 2969097)) (n := 12)
    (lo := (338787531 / 500000000)) (hi := (677575063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969097 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969097 / 1000000) = 1/(1000000 / 1969097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (338787531 / 500000000) (677575063 / 1000000000) (Real.log (1969097 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1969097 / 1000000) = -Real.log (1000000 / 1969097) := by
    rw [show ((1969097 / 1000000) : ℝ) = ((1000000 / 1969097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3476902009 / 1000000000) ≤ -Real.log (30903 / 1000000) ∧
    -Real.log (30903 / 1000000) ≤ (695380403 / 200000000) := by
  have h := checkLog_sound (w := (347 / 62153)) (n := 12)
    (lo := (11166109 / 1000000000)) (hi := (1116611 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30903) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30903) = 1/(30903 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-695380403 / 200000000) (-3476902009 / 1000000000) (Real.log (30903 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1038225163 / 250000000) ≤ -Real.log (500000000000 / 31809133792123) ∧
    -Real.log (500000000000 / 31809133792123) ≤ (2076450329 / 500000000) := by
  have h := checkLog_sound (w := (15809133792123 / 47809133792123)) (n := 12)
    (lo := (42947797 / 62500000)) (hi := (687164753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31809133792123 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31809133792123 / 16000000000000) = 1/(500000000000 / 31809133792123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1038225163 / 250000000) (2076450329 / 500000000) (Real.log (31809133792123 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (31809133792123 / 500000000000) = -Real.log (500000000000 / 31809133792123) := by
    rw [show ((31809133792123 / 500000000000) : ℝ) = ((500000000000 / 31809133792123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4162527987 / 1000000000) ≤ -Real.log (500000000000 / 32116849864641) ∧
    -Real.log (500000000000 / 32116849864641) ≤ (2081263997 / 500000000) := by
  have h := checkLog_sound (w := (116849864641 / 64116849864641)) (n := 12)
    (lo := (3644907 / 1000000000)) (hi := (911227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32116849864641 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32116849864641 / 32000000000000) = 1/(500000000000 / 32116849864641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4162527987 / 1000000000) (2081263997 / 500000000) (Real.log (32116849864641 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (32116849864641 / 500000000000) = -Real.log (500000000000 / 32116849864641) := by
    rw [show ((32116849864641 / 500000000000) : ℝ) = ((500000000000 / 32116849864641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4144761401 / 1000000000) ≤ -Real.log (250000000000 / 15775641025641) ∧
    -Real.log (250000000000 / 15775641025641) ≤ (4144761407 / 1000000000) := by
  have h := checkLog_sound (w := (7775641025641 / 23775641025641)) (n := 12)
    (lo := (679025501 / 1000000000)) (hi := (339512751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15775641025641 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15775641025641 / 8000000000000) = 1/(250000000000 / 15775641025641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4144761401 / 1000000000) (4144761407 / 1000000000) (Real.log (15775641025641 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (15775641025641 / 250000000000) = -Real.log (250000000000 / 15775641025641) := by
    rw [show ((15775641025641 / 250000000000) : ℝ) = ((250000000000 / 15775641025641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4154477071 / 1000000000) ≤ -Real.log (25000000000 / 1592965893279) ∧
    -Real.log (25000000000 / 1592965893279) ≤ (4154477077 / 1000000000) := by
  have h := checkLog_sound (w := (792965893279 / 2392965893279)) (n := 12)
    (lo := (688741171 / 1000000000)) (hi := (172185293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1592965893279 / 800000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1592965893279 / 800000000000) = 1/(25000000000 / 1592965893279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4154477071 / 1000000000) (4154477077 / 1000000000) (Real.log (1592965893279 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1592965893279 / 25000000000) = -Real.log (25000000000 / 1592965893279) := by
    rw [show ((1592965893279 / 25000000000) : ℝ) = ((25000000000 / 1592965893279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0084

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0085Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0085
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

theorem reflection_log_1_neg : (337124513 / 500000000) ≤ -Real.log (51200 / 100483) ∧
    -Real.log (51200 / 100483) ≤ (674249027 / 1000000000) := by
  have h := checkLog_sound (w := (49283 / 151683)) (n := 12)
    (lo := (337124513 / 500000000)) (hi := (674249027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100483 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100483 / 51200) = 1/(51200 / 100483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (337124513 / 500000000) (674249027 / 1000000000) (Real.log (100483 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100483 / 51200) = -Real.log (51200 / 100483) := by
    rw [show ((100483 / 51200) : ℝ) = ((51200 / 100483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (656995613 / 200000000) ≤ -Real.log (1917 / 51200) ∧
    -Real.log (1917 / 51200) ≤ (328497807 / 100000000) := by
  have h := checkLog_sound (w := (1283 / 5117)) (n := 12)
    (lo := (102477869 / 200000000)) (hi := (256194673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1917) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1917) = 1/(1917 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-328497807 / 100000000) (-656995613 / 200000000) (Real.log (1917 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (337029961 / 500000000) ≤ -Real.log (3200 / 6279) ∧
    -Real.log (3200 / 6279) ≤ (674059923 / 1000000000) := by
  have h := checkLog_sound (w := (3079 / 9479)) (n := 12)
    (lo := (337029961 / 500000000)) (hi := (674059923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6279 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6279 / 3200) = 1/(3200 / 6279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (337029961 / 500000000) (674059923 / 1000000000) (Real.log (6279 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6279 / 3200) = -Real.log (3200 / 6279) := by
    rw [show ((6279 / 3200) : ℝ) = ((3200 / 6279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (163755777 / 50000000) ≤ -Real.log (121 / 3200) ∧
    -Real.log (121 / 3200) ≤ (655023109 / 200000000) := by
  have h := checkLog_sound (w := (79 / 321)) (n := 12)
    (lo := (25126341 / 50000000)) (hi := (502526821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 121) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 121) = 1/(121 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-655023109 / 200000000) (-163755777 / 50000000) (Real.log (121 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (327493421 / 500000000) ≤ -Real.log (25600 / 49283) ∧
    -Real.log (25600 / 49283) ≤ (654986843 / 1000000000) := by
  have h := checkLog_sound (w := (23683 / 74883)) (n := 12)
    (lo := (327493421 / 500000000)) (hi := (654986843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49283 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49283 / 25600) = 1/(25600 / 49283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (327493421 / 500000000) (654986843 / 1000000000) (Real.log (49283 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49283 / 25600) = -Real.log (25600 / 49283) := by
    rw [show ((49283 / 25600) : ℝ) = ((25600 / 49283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (518366177 / 200000000) ≤ -Real.log (1917 / 25600) ∧
    -Real.log (1917 / 25600) ≤ (2591830889 / 1000000000) := by
  have h := checkLog_sound (w := (1283 / 5117)) (n := 12)
    (lo := (102477869 / 200000000)) (hi := (256194673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1917) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1917) = 1/(1917 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2591830889 / 1000000000) (-518366177 / 200000000) (Real.log (1917 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (654601239 / 1000000000) ≤ -Real.log (1600 / 3079) ∧
    -Real.log (1600 / 3079) ≤ (16365031 / 25000000) := by
  have h := checkLog_sound (w := (1479 / 4679)) (n := 12)
    (lo := (654601239 / 1000000000)) (hi := (16365031 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3079 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3079 / 1600) = 1/(1600 / 3079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (654601239 / 1000000000) (16365031 / 25000000) (Real.log (3079 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3079 / 1600) = -Real.log (1600 / 3079) := by
    rw [show ((3079 / 1600) : ℝ) = ((1600 / 3079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (64549209 / 25000000) ≤ -Real.log (121 / 1600) ∧
    -Real.log (121 / 1600) ≤ (645492091 / 250000000) := by
  have h := checkLog_sound (w := (79 / 321)) (n := 12)
    (lo := (25126341 / 50000000)) (hi := (502526821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 121) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 121) = 1/(121 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-645492091 / 250000000) (-64549209 / 25000000) (Real.log (121 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135480679 / 200000000) ≤ -Real.log (1000000 / 1968759) ∧
    -Real.log (1000000 / 1968759) ≤ (169350849 / 250000000) := by
  have h := checkLog_sound (w := (968759 / 2968759)) (n := 12)
    (lo := (135480679 / 200000000)) (hi := (169350849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1968759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1968759 / 1000000) = 1/(1000000 / 1968759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135480679 / 200000000) (169350849 / 250000000) (Real.log (1968759 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1968759 / 1000000) = -Real.log (1000000 / 1968759) := by
    rw [show ((1968759 / 1000000) : ℝ) = ((1000000 / 1968759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3466023941 / 1000000000) ≤ -Real.log (31241 / 1000000) ∧
    -Real.log (31241 / 1000000) ≤ (3466023947 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 62491)) (n := 12)
    (lo := (288041 / 1000000000)) (hi := (144021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31241) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 31241) = 1/(31241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3466023947 / 1000000000) (-3466023941 / 1000000000) (Real.log (31241 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84693899 / 125000000) ≤ -Real.log (20000 / 39381) ∧
    -Real.log (20000 / 39381) ≤ (677551193 / 1000000000) := by
  have h := checkLog_sound (w := (19381 / 59381)) (n := 12)
    (lo := (84693899 / 125000000)) (hi := (677551193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39381 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39381 / 20000) = 1/(20000 / 39381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84693899 / 125000000) (677551193 / 1000000000) (Real.log (39381 / 20000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (39381 / 20000) = -Real.log (20000 / 39381) := by
    rw [show ((39381 / 20000) : ℝ) = ((20000 / 39381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3475382277 / 1000000000) ≤ -Real.log (619 / 20000) ∧
    -Real.log (619 / 20000) ≤ (3475382283 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 622)) (n := 12)
    (lo := (9646377 / 1000000000)) (hi := (4823189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 619) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(625 / 619) = 1/(619 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3475382283 / 1000000000) (-3475382277 / 1000000000) (Real.log (619 / 20000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (677273863 / 1000000000) ≤ -Real.log (125000 / 246063) ∧
    -Real.log (125000 / 246063) ≤ (84659233 / 125000000) := by
  have h := checkLog_sound (w := (121063 / 371063)) (n := 12)
    (lo := (677273863 / 1000000000)) (hi := (84659233 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246063 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246063 / 125000) = 1/(125000 / 246063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (677273863 / 1000000000) (84659233 / 125000000) (Real.log (246063 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (246063 / 125000) = -Real.log (125000 / 246063) := by
    rw [show ((246063 / 125000) : ℝ) = ((125000 / 246063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3457894723 / 1000000000) ≤ -Real.log (3937 / 125000) ∧
    -Real.log (3937 / 125000) ≤ (432236841 / 125000000) := by
  have h := checkLog_sound (w := (7751 / 23499)) (n := 12)
    (lo := (685306003 / 1000000000)) (hi := (171326501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 7874) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 7874) = 1/(3937 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-432236841 / 125000000) (-3457894723 / 1000000000) (Real.log (3937 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (84678091 / 125000000) ≤ -Real.log (1000000 / 1968801) ∧
    -Real.log (1000000 / 1968801) ≤ (677424729 / 1000000000) := by
  have h := checkLog_sound (w := (968801 / 2968801)) (n := 12)
    (lo := (84678091 / 125000000)) (hi := (677424729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1968801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1968801 / 1000000) = 1/(1000000 / 1968801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (84678091 / 125000000) (677424729 / 1000000000) (Real.log (1968801 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1968801 / 1000000) = -Real.log (1000000 / 1968801) := by
    rw [show ((1968801 / 1000000) : ℝ) = ((1000000 / 1968801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3467369233 / 1000000000) ≤ -Real.log (31199 / 1000000) ∧
    -Real.log (31199 / 1000000) ≤ (3467369239 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 62449)) (n := 12)
    (lo := (1633333 / 1000000000)) (hi := (816667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31199) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 31199) = 1/(31199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3467369239 / 1000000000) (-3467369233 / 1000000000) (Real.log (31199 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (517928417 / 125000000) ≤ -Real.log (125000000000 / 7877304663743) ∧
    -Real.log (125000000000 / 7877304663743) ≤ (2071713671 / 500000000) := by
  have h := checkLog_sound (w := (3877304663743 / 11877304663743)) (n := 12)
    (lo := (169422859 / 250000000)) (hi := (677691437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7877304663743 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7877304663743 / 4000000000000) = 1/(125000000000 / 7877304663743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (517928417 / 125000000) (2071713671 / 500000000) (Real.log (7877304663743 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7877304663743 / 125000000000) = -Real.log (125000000000 / 7877304663743) := by
    rw [show ((7877304663743 / 125000000000) : ℝ) = ((125000000000 / 7877304663743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4152933469 / 1000000000) ≤ -Real.log (250000000000 / 15905088852989) ∧
    -Real.log (250000000000 / 15905088852989) ≤ (166117339 / 40000000) := by
  have h := checkLog_sound (w := (7905088852989 / 23905088852989)) (n := 12)
    (lo := (687197569 / 1000000000)) (hi := (68719757 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15905088852989 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15905088852989 / 8000000000000) = 1/(250000000000 / 15905088852989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4152933469 / 1000000000) (166117339 / 40000000) (Real.log (15905088852989 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (15905088852989 / 250000000000) = -Real.log (250000000000 / 15905088852989) := by
    rw [show ((15905088852989 / 250000000000) : ℝ) = ((250000000000 / 15905088852989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (827033717 / 200000000) ≤ -Real.log (500000000000 / 31250063500127) ∧
    -Real.log (500000000000 / 31250063500127) ≤ (4135168591 / 1000000000) := by
  have h := checkLog_sound (w := (15250063500127 / 47250063500127)) (n := 12)
    (lo := (133886537 / 200000000)) (hi := (334716343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250063500127 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250063500127 / 16000000000000) = 1/(500000000000 / 31250063500127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (827033717 / 200000000) (4135168591 / 1000000000) (Real.log (31250063500127 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (31250063500127 / 500000000000) = -Real.log (500000000000 / 31250063500127) := by
    rw [show ((31250063500127 / 500000000000) : ℝ) = ((500000000000 / 31250063500127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4144793961 / 1000000000) ≤ -Real.log (500000000000 / 31552309368891) ∧
    -Real.log (500000000000 / 31552309368891) ≤ (4144793967 / 1000000000) := by
  have h := checkLog_sound (w := (15552309368891 / 47552309368891)) (n := 12)
    (lo := (679058061 / 1000000000)) (hi := (339529031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31552309368891 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31552309368891 / 16000000000000) = 1/(500000000000 / 31552309368891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4144793961 / 1000000000) (4144793967 / 1000000000) (Real.log (31552309368891 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (31552309368891 / 500000000000) = -Real.log (500000000000 / 31552309368891) := by
    rw [show ((31552309368891 / 500000000000) : ℝ) = ((500000000000 / 31552309368891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0085

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0086Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0086
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

theorem reflection_log_1_neg : (337029961 / 500000000) ≤ -Real.log (3200 / 6279) ∧
    -Real.log (3200 / 6279) ≤ (674059923 / 1000000000) := by
  have h := checkLog_sound (w := (3079 / 9479)) (n := 12)
    (lo := (337029961 / 500000000)) (hi := (674059923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6279 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6279 / 3200) = 1/(3200 / 6279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (337029961 / 500000000) (674059923 / 1000000000) (Real.log (6279 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6279 / 3200) = -Real.log (3200 / 6279) := by
    rw [show ((6279 / 3200) : ℝ) = ((3200 / 6279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (163755777 / 50000000) ≤ -Real.log (121 / 3200) ∧
    -Real.log (121 / 3200) ≤ (655023109 / 200000000) := by
  have h := checkLog_sound (w := (79 / 321)) (n := 12)
    (lo := (25126341 / 50000000)) (hi := (502526821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 121) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 121) = 1/(121 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-655023109 / 200000000) (-163755777 / 50000000) (Real.log (121 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (673870781 / 1000000000) ≤ -Real.log (10240 / 20089) ∧
    -Real.log (10240 / 20089) ≤ (336935391 / 500000000) := by
  have h := checkLog_sound (w := (9849 / 30329)) (n := 12)
    (lo := (673870781 / 1000000000)) (hi := (336935391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20089 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20089 / 10240) = 1/(10240 / 20089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (673870781 / 1000000000) (336935391 / 500000000) (Real.log (20089 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20089 / 10240) = -Real.log (10240 / 20089) := by
    rw [show ((20089 / 10240) : ℝ) = ((10240 / 20089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (408168667 / 125000000) ≤ -Real.log (391 / 10240) ∧
    -Real.log (391 / 10240) ≤ (3265349341 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 1031)) (n := 12)
    (lo := (61595077 / 125000000)) (hi := (492760617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 391) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 391) = 1/(391 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3265349341 / 1000000000) (-408168667 / 125000000) (Real.log (391 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (654601239 / 1000000000) ≤ -Real.log (1600 / 3079) ∧
    -Real.log (1600 / 3079) ≤ (16365031 / 25000000) := by
  have h := checkLog_sound (w := (1479 / 4679)) (n := 12)
    (lo := (654601239 / 1000000000)) (hi := (16365031 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3079 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3079 / 1600) = 1/(1600 / 3079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (654601239 / 1000000000) (16365031 / 25000000) (Real.log (3079 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3079 / 1600) = -Real.log (1600 / 3079) := by
    rw [show ((3079 / 1600) : ℝ) = ((1600 / 3079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (64549209 / 25000000) ≤ -Real.log (121 / 1600) ∧
    -Real.log (121 / 1600) ≤ (645492091 / 250000000) := by
  have h := checkLog_sound (w := (79 / 321)) (n := 12)
    (lo := (25126341 / 50000000)) (hi := (502526821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 121) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 121) = 1/(121 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-645492091 / 250000000) (-64549209 / 25000000) (Real.log (121 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10222117 / 15625000) ≤ -Real.log (5120 / 9849) ∧
    -Real.log (5120 / 9849) ≤ (654215489 / 1000000000) := by
  have h := checkLog_sound (w := (4729 / 14969)) (n := 12)
    (lo := (10222117 / 15625000)) (hi := (654215489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9849 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9849 / 5120) = 1/(5120 / 9849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10222117 / 15625000) (654215489 / 1000000000) (Real.log (9849 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9849 / 5120) = -Real.log (5120 / 9849) := by
    rw [show ((9849 / 5120) : ℝ) = ((5120 / 9849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (643050539 / 250000000) ≤ -Real.log (391 / 5120) ∧
    -Real.log (391 / 5120) ≤ (32152527 / 12500000) := by
  have h := checkLog_sound (w := (249 / 1031)) (n := 12)
    (lo := (61595077 / 125000000)) (hi := (492760617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 391) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 391) = 1/(391 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-32152527 / 12500000) (-643050539 / 250000000) (Real.log (391 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (677256591 / 1000000000) ≤ -Real.log (100000 / 196847) ∧
    -Real.log (100000 / 196847) ≤ (42328537 / 62500000) := by
  have h := checkLog_sound (w := (96847 / 296847)) (n := 12)
    (lo := (677256591 / 1000000000)) (hi := (42328537 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196847 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196847 / 100000) = 1/(100000 / 196847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (677256591 / 1000000000) (42328537 / 62500000) (Real.log (196847 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (196847 / 100000) = -Real.log (100000 / 196847) := by
    rw [show ((196847 / 100000) : ℝ) = ((100000 / 196847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3456815803 / 1000000000) ≤ -Real.log (3153 / 100000) ∧
    -Real.log (3153 / 100000) ≤ (54012747 / 15625000) := by
  have h := checkLog_sound (w := (3097 / 9403)) (n := 12)
    (lo := (684227083 / 1000000000)) (hi := (171056771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3153) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 3153) = 1/(3153 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-54012747 / 15625000) (-3456815803 / 1000000000) (Real.log (3153 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (338701951 / 500000000) ≤ -Real.log (25000 / 49219) ∧
    -Real.log (25000 / 49219) ≤ (677403903 / 1000000000) := by
  have h := checkLog_sound (w := (24219 / 74219)) (n := 12)
    (lo := (338701951 / 500000000)) (hi := (677403903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49219 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49219 / 25000) = 1/(25000 / 49219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (338701951 / 500000000) (677403903 / 1000000000) (Real.log (49219 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (49219 / 25000) = -Real.log (25000 / 49219) := by
    rw [show ((49219 / 25000) : ℝ) = ((25000 / 49219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3466055951 / 1000000000) ≤ -Real.log (781 / 25000) ∧
    -Real.log (781 / 25000) ≤ (3466055957 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 6249)) (n := 12)
    (lo := (320051 / 1000000000)) (hi := (80013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3124) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 3124) = 1/(781 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3466055957 / 1000000000) (-3466055951 / 1000000000) (Real.log (781 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (84640499 / 125000000) ≤ -Real.log (1000000 / 1968209) ∧
    -Real.log (1000000 / 1968209) ≤ (677123993 / 1000000000) := by
  have h := checkLog_sound (w := (968209 / 2968209)) (n := 12)
    (lo := (84640499 / 125000000)) (hi := (677123993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1968209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1968209 / 1000000) = 1/(1000000 / 1968209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (84640499 / 125000000) (677123993 / 1000000000) (Real.log (1968209 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1968209 / 1000000) = -Real.log (1000000 / 1968209) := by
    rw [show ((1968209 / 1000000) : ℝ) = ((1000000 / 1968209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (689714409 / 200000000) ≤ -Real.log (31791 / 1000000) ∧
    -Real.log (31791 / 1000000) ≤ (68971441 / 20000000) := by
  have h := checkLog_sound (w := (30709 / 94291)) (n := 12)
    (lo := (27039333 / 40000000)) (hi := (337991663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31791) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 31791) = 1/(31791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-68971441 / 20000000) (-689714409 / 200000000) (Real.log (31791 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (677274371 / 1000000000) ≤ -Real.log (200000 / 393701) ∧
    -Real.log (200000 / 393701) ≤ (169318593 / 250000000) := by
  have h := checkLog_sound (w := (193701 / 593701)) (n := 12)
    (lo := (677274371 / 1000000000)) (hi := (169318593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393701 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393701 / 200000) = 1/(200000 / 393701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (677274371 / 1000000000) (169318593 / 250000000) (Real.log (393701 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (393701 / 200000) = -Real.log (200000 / 393701) := by
    rw [show ((393701 / 200000) : ℝ) = ((200000 / 393701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3457926473 / 1000000000) ≤ -Real.log (6299 / 200000) ∧
    -Real.log (6299 / 200000) ≤ (1728963239 / 500000000) := by
  have h := checkLog_sound (w := (6201 / 18799)) (n := 12)
    (lo := (685337753 / 1000000000)) (hi := (342668877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6299) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 6299) = 1/(6299 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1728963239 / 500000000) (-3457926473 / 1000000000) (Real.log (6299 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4134072393 / 1000000000) ≤ -Real.log (62500000000 / 3901978274659) ∧
    -Real.log (62500000000 / 3901978274659) ≤ (4134072399 / 1000000000) := by
  have h := checkLog_sound (w := (1901978274659 / 5901978274659)) (n := 12)
    (lo := (668336493 / 1000000000)) (hi := (334168247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3901978274659 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3901978274659 / 2000000000000) = 1/(62500000000 / 3901978274659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4134072393 / 1000000000) (4134072399 / 1000000000) (Real.log (3901978274659 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3901978274659 / 62500000000) = -Real.log (62500000000 / 3901978274659) := by
    rw [show ((3901978274659 / 62500000000) : ℝ) = ((62500000000 / 3901978274659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2071729927 / 500000000) ≤ -Real.log (500000000000 / 31510243277849) ∧
    -Real.log (500000000000 / 31510243277849) ≤ (207172993 / 50000000) := by
  have h := checkLog_sound (w := (15510243277849 / 47510243277849)) (n := 12)
    (lo := (338861977 / 500000000)) (hi := (135544791 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31510243277849 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31510243277849 / 16000000000000) = 1/(500000000000 / 31510243277849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2071729927 / 500000000) (207172993 / 50000000) (Real.log (31510243277849 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (31510243277849 / 500000000000) = -Real.log (500000000000 / 31510243277849) := by
    rw [show ((31510243277849 / 500000000000) : ℝ) = ((500000000000 / 31510243277849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4125696037 / 1000000000) ≤ -Real.log (250000000000 / 15477721682237) ∧
    -Real.log (250000000000 / 15477721682237) ≤ (4125696043 / 1000000000) := by
  have h := checkLog_sound (w := (7477721682237 / 23477721682237)) (n := 12)
    (lo := (659960137 / 1000000000)) (hi := (329980069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15477721682237 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15477721682237 / 8000000000000) = 1/(250000000000 / 15477721682237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4125696037 / 1000000000) (4125696043 / 1000000000) (Real.log (15477721682237 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (15477721682237 / 250000000000) = -Real.log (250000000000 / 15477721682237) := by
    rw [show ((15477721682237 / 250000000000) : ℝ) = ((250000000000 / 15477721682237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1033800211 / 250000000) ≤ -Real.log (500000000000 / 31251071598667) ∧
    -Real.log (500000000000 / 31251071598667) ≤ (82704017 / 20000000) := by
  have h := checkLog_sound (w := (15251071598667 / 47251071598667)) (n := 12)
    (lo := (41841559 / 62500000)) (hi := (133892989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31251071598667 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31251071598667 / 16000000000000) = 1/(500000000000 / 31251071598667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1033800211 / 250000000) (82704017 / 20000000) (Real.log (31251071598667 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (31251071598667 / 500000000000) = -Real.log (500000000000 / 31251071598667) := by
    rw [show ((31251071598667 / 500000000000) : ℝ) = ((500000000000 / 31251071598667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0086

end


