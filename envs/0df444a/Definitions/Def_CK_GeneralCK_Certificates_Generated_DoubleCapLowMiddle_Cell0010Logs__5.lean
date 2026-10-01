-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0010Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0010Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:44:18.901685+00:00
-- url     : https://prove2.me/theorems/ede5ffdd-267d-4518-ad39-f1ba66f1dc71
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0010Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0011Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0010Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0011Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0012Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0013Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0014Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0010Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0011Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0012Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0013Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0014Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0010Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0011Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0012Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0013Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0014Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0010Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0011Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0012Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0013Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0014Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0010Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0010
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

theorem reflection_log_1_neg : (341314091 / 500000000) ≤ -Real.log (102400 / 202657) ∧
    -Real.log (102400 / 202657) ≤ (682628183 / 1000000000) := by
  have h := checkLog_sound (w := (100257 / 305057)) (n := 12)
    (lo := (341314091 / 500000000)) (hi := (682628183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202657 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202657 / 102400) = 1/(102400 / 202657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (341314091 / 500000000) (682628183 / 1000000000) (Real.log (202657 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202657 / 102400) = -Real.log (102400 / 202657) := by
    rw [show ((202657 / 102400) : ℝ) = ((102400 / 202657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3866679993 / 1000000000) ≤ -Real.log (2143 / 102400) ∧
    -Real.log (2143 / 102400) ≤ (3866679999 / 1000000000) := by
  have h := checkLog_sound (w := (1057 / 5343)) (n := 12)
    (lo := (400944093 / 1000000000)) (hi := (200472047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2143) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2143) = 1/(2143 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3866679999 / 1000000000) (-3866679993 / 1000000000) (Real.log (2143 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682581303 / 1000000000) ≤ -Real.log (1000000000000 / 1978979492187) ∧
    -Real.log (1000000000000 / 1978979492187) ≤ (85322663 / 125000000) := by
  have h := checkLog_sound (w := (978979492187 / 2978979492187)) (n := 12)
    (lo := (682581303 / 1000000000)) (hi := (85322663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978979492187 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978979492187 / 1000000000000) = 1/(1000000000000 / 1978979492187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682581303 / 1000000000) (85322663 / 125000000) (Real.log (1978979492187 / 1000000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1978979492187 / 1000000000000) = -Real.log (1000000000000 / 1978979492187) := by
    rw [show ((1978979492187 / 1000000000000) : ℝ) = ((1000000000000 / 1978979492187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (241391047 / 62500000) ≤ -Real.log (21020507813 / 1000000000000) ∧
    -Real.log (21020507813 / 1000000000000) ≤ (1931128379 / 500000000) := by
  have h := checkLog_sound (w := (10229492187 / 52270507813)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 21020507813) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 21020507813) = 1/(21020507813 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1931128379 / 500000000) (-241391047 / 62500000) (Real.log (21020507813 / 1000000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (671997357 / 1000000000) ≤ -Real.log (51200 / 100257) ∧
    -Real.log (51200 / 100257) ≤ (335998679 / 500000000) := by
  have h := checkLog_sound (w := (49057 / 151457)) (n := 12)
    (lo := (671997357 / 1000000000)) (hi := (335998679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100257 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100257 / 51200) = 1/(51200 / 100257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (671997357 / 1000000000) (335998679 / 500000000) (Real.log (100257 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100257 / 51200) = -Real.log (51200 / 100257) := by
    rw [show ((100257 / 51200) : ℝ) = ((51200 / 100257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3173532813 / 1000000000) ≤ -Real.log (2143 / 51200) ∧
    -Real.log (2143 / 51200) ≤ (1586766409 / 500000000) := by
  have h := checkLog_sound (w := (1057 / 5343)) (n := 12)
    (lo := (400944093 / 1000000000)) (hi := (200472047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2143) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2143) = 1/(2143 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1586766409 / 500000000) (-3173532813 / 1000000000) (Real.log (2143 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (167975649 / 250000000) ≤ -Real.log (20480 / 40099) ∧
    -Real.log (20480 / 40099) ≤ (671902597 / 1000000000) := by
  have h := checkLog_sound (w := (19619 / 60579)) (n := 12)
    (lo := (167975649 / 250000000)) (hi := (671902597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40099 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40099 / 20480) = 1/(20480 / 40099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (167975649 / 250000000) (671902597 / 1000000000) (Real.log (40099 / 20480)) := by
  have h := reflection_log_7_neg
  have he : Real.log (40099 / 20480) = -Real.log (20480 / 40099) := by
    rw [show ((40099 / 20480) : ℝ) = ((20480 / 40099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (792277393 / 250000000) ≤ -Real.log (861 / 20480) ∧
    -Real.log (861 / 20480) ≤ (3169109577 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2141)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 861) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1280 / 861) = 1/(861 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3169109577 / 1000000000) (-792277393 / 250000000) (Real.log (861 / 20480)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684183627 / 1000000000) ≤ -Real.log (1000000 / 1982153) ∧
    -Real.log (1000000 / 1982153) ≤ (171045907 / 250000000) := by
  have h := checkLog_sound (w := (982153 / 2982153)) (n := 12)
    (lo := (684183627 / 1000000000)) (hi := (171045907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982153 / 1000000) = 1/(1000000 / 1982153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684183627 / 1000000000) (171045907 / 250000000) (Real.log (1982153 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1982153 / 1000000) = -Real.log (1000000 / 1982153) := by
    rw [show ((1982153 / 1000000) : ℝ) = ((1000000 / 1982153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4025919849 / 1000000000) ≤ -Real.log (17847 / 1000000) ∧
    -Real.log (17847 / 1000000) ≤ (805183971 / 200000000) := by
  have h := checkLog_sound (w := (13403 / 49097)) (n := 12)
    (lo := (560183949 / 1000000000)) (hi := (11203679 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17847) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17847) = 1/(17847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-805183971 / 200000000) (-4025919849 / 1000000000) (Real.log (17847 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684222473 / 1000000000) ≤ -Real.log (100000 / 198223) ∧
    -Real.log (100000 / 198223) ≤ (342111237 / 500000000) := by
  have h := checkLog_sound (w := (98223 / 298223)) (n := 12)
    (lo := (684222473 / 1000000000)) (hi := (342111237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198223 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198223 / 100000) = 1/(100000 / 198223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684222473 / 1000000000) (342111237 / 500000000) (Real.log (198223 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (198223 / 100000) = -Real.log (100000 / 198223) := by
    rw [show ((198223 / 100000) : ℝ) = ((100000 / 198223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2015121817 / 500000000) ≤ -Real.log (1777 / 100000) ∧
    -Real.log (1777 / 100000) ≤ (100756091 / 25000000) := by
  have h := checkLog_sound (w := (674 / 2451)) (n := 12)
    (lo := (282253867 / 500000000)) (hi := (112901547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1777) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1777) = 1/(1777 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-100756091 / 25000000) (-2015121817 / 500000000) (Real.log (1777 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (17103733 / 25000000) ≤ -Real.log (200000 / 396417) ∧
    -Real.log (200000 / 396417) ≤ (684149321 / 1000000000) := by
  have h := checkLog_sound (w := (196417 / 596417)) (n := 12)
    (lo := (17103733 / 25000000)) (hi := (684149321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396417 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396417 / 200000) = 1/(200000 / 396417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (17103733 / 25000000) (684149321 / 1000000000) (Real.log (396417 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (396417 / 200000) = -Real.log (200000 / 396417) := by
    rw [show ((396417 / 200000) : ℝ) = ((200000 / 396417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (160884677 / 40000000) ≤ -Real.log (3583 / 200000) ∧
    -Real.log (3583 / 200000) ≤ (4022116931 / 1000000000) := by
  have h := checkLog_sound (w := (2667 / 9833)) (n := 12)
    (lo := (22255241 / 40000000)) (hi := (278190513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3583) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3583) = 1/(3583 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4022116931 / 1000000000) (-160884677 / 40000000) (Real.log (3583 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (85523521 / 125000000) ≤ -Real.log (500000 / 991081) ∧
    -Real.log (500000 / 991081) ≤ (684188169 / 1000000000) := by
  have h := checkLog_sound (w := (491081 / 1491081)) (n := 12)
    (lo := (85523521 / 125000000)) (hi := (684188169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991081 / 500000) = 1/(500000 / 991081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (85523521 / 125000000) (684188169 / 1000000000) (Real.log (991081 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (991081 / 500000) = -Real.log (500000 / 991081) := by
    rw [show ((991081 / 500000) : ℝ) = ((500000 / 991081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2013212131 / 500000000) ≤ -Real.log (8919 / 500000) ∧
    -Real.log (8919 / 500000) ≤ (1006606067 / 250000000) := by
  have h := checkLog_sound (w := (3353 / 12272)) (n := 12)
    (lo := (280344181 / 500000000)) (hi := (560688363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8919) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8919) = 1/(8919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1006606067 / 250000000) (-2013212131 / 500000000) (Real.log (8919 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1177525869 / 250000000) ≤ -Real.log (500000000000 / 55531826077211) ∧
    -Real.log (500000000000 / 55531826077211) ≤ (4710103483 / 1000000000) := by
  have h := checkLog_sound (w := (23531826077211 / 87531826077211)) (n := 12)
    (lo := (137805099 / 250000000)) (hi := (551220397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55531826077211 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55531826077211 / 32000000000000) = 1/(500000000000 / 55531826077211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1177525869 / 250000000) (4710103483 / 1000000000) (Real.log (55531826077211 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (55531826077211 / 500000000000) = -Real.log (500000000000 / 55531826077211) := by
    rw [show ((55531826077211 / 500000000000) : ℝ) = ((500000000000 / 55531826077211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4714466107 / 1000000000) ≤ -Real.log (100000000000 / 11154924029263) ∧
    -Real.log (100000000000 / 11154924029263) ≤ (2357233057 / 500000000) := by
  have h := checkLog_sound (w := (4754924029263 / 17554924029263)) (n := 12)
    (lo := (555583027 / 1000000000)) (hi := (138895757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11154924029263 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11154924029263 / 6400000000000) = 1/(100000000000 / 11154924029263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4714466107 / 1000000000) (2357233057 / 500000000) (Real.log (11154924029263 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11154924029263 / 100000000000) = -Real.log (100000000000 / 11154924029263) := by
    rw [show ((11154924029263 / 100000000000) : ℝ) = ((100000000000 / 11154924029263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (941253249 / 200000000) ≤ -Real.log (250000000000 / 27659572983533) ∧
    -Real.log (250000000000 / 27659572983533) ≤ (1176566563 / 250000000) := by
  have h := checkLog_sound (w := (11659572983533 / 43659572983533)) (n := 12)
    (lo := (109476633 / 200000000)) (hi := (273691583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27659572983533 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(27659572983533 / 16000000000000) = 1/(250000000000 / 27659572983533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (941253249 / 200000000) (1176566563 / 250000000) (Real.log (27659572983533 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (27659572983533 / 250000000000) = -Real.log (250000000000 / 27659572983533) := by
    rw [show ((27659572983533 / 250000000000) : ℝ) = ((250000000000 / 27659572983533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (471061243 / 100000000) ≤ -Real.log (250000000000 / 27780048211683) ∧
    -Real.log (250000000000 / 27780048211683) ≤ (4710612437 / 1000000000) := by
  have h := checkLog_sound (w := (11780048211683 / 43780048211683)) (n := 12)
    (lo := (11034587 / 20000000)) (hi := (551729351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27780048211683 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(27780048211683 / 16000000000000) = 1/(250000000000 / 27780048211683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (471061243 / 100000000) (4710612437 / 1000000000) (Real.log (27780048211683 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (27780048211683 / 250000000000) = -Real.log (250000000000 / 27780048211683) := by
    rw [show ((27780048211683 / 250000000000) : ℝ) = ((250000000000 / 27780048211683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0010

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0011Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0011
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

theorem reflection_log_1_neg : (682581303 / 1000000000) ≤ -Real.log (250000000000 / 494744873047) ∧
    -Real.log (250000000000 / 494744873047) ≤ (85322663 / 125000000) := by
  have h := checkLog_sound (w := (244744873047 / 744744873047)) (n := 12)
    (lo := (682581303 / 1000000000)) (hi := (85322663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494744873047 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494744873047 / 250000000000) = 1/(250000000000 / 494744873047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682581303 / 1000000000) (85322663 / 125000000) (Real.log (494744873047 / 250000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (494744873047 / 250000000000) = -Real.log (250000000000 / 494744873047) := by
    rw [show ((494744873047 / 250000000000) : ℝ) = ((250000000000 / 494744873047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (241391047 / 62500000) ≤ -Real.log (5255126953 / 250000000000) ∧
    -Real.log (5255126953 / 250000000000) ≤ (1931128379 / 500000000) := by
  have h := checkLog_sound (w := (2557373047 / 13067626953)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7812500000 / 5255126953) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7812500000 / 5255126953) = 1/(5255126953 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1931128379 / 500000000) (-241391047 / 62500000) (Real.log (5255126953 / 250000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682534423 / 1000000000) ≤ -Real.log (51200 / 101319) ∧
    -Real.log (51200 / 101319) ≤ (85316803 / 125000000) := by
  have h := checkLog_sound (w := (50119 / 152519)) (n := 12)
    (lo := (682534423 / 1000000000)) (hi := (85316803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101319 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101319 / 51200) = 1/(51200 / 101319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682534423 / 1000000000) (85316803 / 125000000) (Real.log (101319 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101319 / 51200) = -Real.log (51200 / 101319) := by
    rw [show ((101319 / 51200) : ℝ) = ((51200 / 101319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (385785299 / 100000000) ≤ -Real.log (1081 / 51200) ∧
    -Real.log (1081 / 51200) ≤ (964463249 / 250000000) := by
  have h := checkLog_sound (w := (519 / 2681)) (n := 12)
    (lo := (39211709 / 100000000)) (hi := (392117091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1081) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1081) = 1/(1081 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-964463249 / 250000000) (-385785299 / 100000000) (Real.log (1081 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167975649 / 250000000) ≤ -Real.log (20480 / 40099) ∧
    -Real.log (20480 / 40099) ≤ (671902597 / 1000000000) := by
  have h := checkLog_sound (w := (19619 / 60579)) (n := 12)
    (lo := (167975649 / 250000000)) (hi := (671902597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40099 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40099 / 20480) = 1/(20480 / 40099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167975649 / 250000000) (671902597 / 1000000000) (Real.log (40099 / 20480)) := by
  have h := reflection_log_5_neg
  have he : Real.log (40099 / 20480) = -Real.log (20480 / 40099) := by
    rw [show ((40099 / 20480) : ℝ) = ((20480 / 40099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (792277393 / 250000000) ≤ -Real.log (861 / 20480) ∧
    -Real.log (861 / 20480) ≤ (3169109577 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2141)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 861) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1280 / 861) = 1/(861 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3169109577 / 1000000000) (-792277393 / 250000000) (Real.log (861 / 20480)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (335903913 / 500000000) ≤ -Real.log (25600 / 50119) ∧
    -Real.log (25600 / 50119) ≤ (671807827 / 1000000000) := by
  have h := checkLog_sound (w := (24519 / 75719)) (n := 12)
    (lo := (335903913 / 500000000)) (hi := (671807827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50119 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50119 / 25600) = 1/(25600 / 50119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (335903913 / 500000000) (671807827 / 1000000000) (Real.log (50119 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (50119 / 25600) = -Real.log (25600 / 50119) := by
    rw [show ((50119 / 25600) : ℝ) = ((25600 / 50119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (316470581 / 100000000) ≤ -Real.log (1081 / 25600) ∧
    -Real.log (1081 / 25600) ≤ (632941163 / 200000000) := by
  have h := checkLog_sound (w := (519 / 2681)) (n := 12)
    (lo := (39211709 / 100000000)) (hi := (392117091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1081) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1081) = 1/(1081 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-632941163 / 200000000) (-316470581 / 100000000) (Real.log (1081 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684145789 / 1000000000) ≤ -Real.log (500000 / 991039) ∧
    -Real.log (500000 / 991039) ≤ (68414579 / 100000000) := by
  have h := checkLog_sound (w := (491039 / 1491039)) (n := 12)
    (lo := (684145789 / 1000000000)) (hi := (68414579 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991039 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991039 / 500000) = 1/(500000 / 991039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684145789 / 1000000000) (68414579 / 100000000) (Real.log (991039 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (991039 / 500000) = -Real.log (500000 / 991039) := by
    rw [show ((991039 / 500000) : ℝ) = ((500000 / 991039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4021726267 / 1000000000) ≤ -Real.log (8961 / 500000) ∧
    -Real.log (8961 / 500000) ≤ (4021726273 / 1000000000) := by
  have h := checkLog_sound (w := (3332 / 12293)) (n := 12)
    (lo := (555990367 / 1000000000)) (hi := (17374699 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8961) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8961) = 1/(8961 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4021726273 / 1000000000) (-4021726267 / 1000000000) (Real.log (8961 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (171046033 / 250000000) ≤ -Real.log (500000 / 991077) ∧
    -Real.log (500000 / 991077) ≤ (684184133 / 1000000000) := by
  have h := checkLog_sound (w := (491077 / 1491077)) (n := 12)
    (lo := (171046033 / 250000000)) (hi := (684184133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991077 / 500000) = 1/(500000 / 991077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (171046033 / 250000000) (684184133 / 1000000000) (Real.log (991077 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (991077 / 500000) = -Real.log (500000 / 991077) := by
    rw [show ((991077 / 500000) : ℝ) = ((500000 / 991077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2012987941 / 500000000) ≤ -Real.log (8923 / 500000) ∧
    -Real.log (8923 / 500000) ≤ (251623493 / 62500000) := by
  have h := checkLog_sound (w := (3351 / 12274)) (n := 12)
    (lo := (280119991 / 500000000)) (hi := (560239983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8923) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8923) = 1/(8923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-251623493 / 62500000) (-2012987941 / 500000000) (Real.log (8923 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (85513809 / 125000000) ≤ -Real.log (125000 / 247751) ∧
    -Real.log (125000 / 247751) ≤ (684110473 / 1000000000) := by
  have h := checkLog_sound (w := (122751 / 372751)) (n := 12)
    (lo := (85513809 / 125000000)) (hi := (684110473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247751 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247751 / 125000) = 1/(125000 / 247751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (85513809 / 125000000) (684110473 / 1000000000) (Real.log (247751 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247751 / 125000) = -Real.log (125000 / 247751) := by
    rw [show ((247751 / 125000) : ℝ) = ((125000 / 247751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4017828061 / 1000000000) ≤ -Real.log (2249 / 125000) ∧
    -Real.log (2249 / 125000) ≤ (4017828067 / 1000000000) := by
  have h := checkLog_sound (w := (6629 / 24621)) (n := 12)
    (lo := (552092161 / 1000000000)) (hi := (276046081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8996) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8996) = 1/(2249 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4017828067 / 1000000000) (-4017828061 / 1000000000) (Real.log (2249 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (27365993 / 40000000) ≤ -Real.log (500000 / 991043) ∧
    -Real.log (500000 / 991043) ≤ (342074913 / 500000000) := by
  have h := checkLog_sound (w := (491043 / 1491043)) (n := 12)
    (lo := (27365993 / 40000000)) (hi := (342074913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991043 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991043 / 500000) = 1/(500000 / 991043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (27365993 / 40000000) (342074913 / 500000000) (Real.log (991043 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (991043 / 500000) = -Real.log (500000 / 991043) := by
    rw [show ((991043 / 500000) : ℝ) = ((500000 / 991043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2011086373 / 500000000) ≤ -Real.log (8957 / 500000) ∧
    -Real.log (8957 / 500000) ≤ (251385797 / 62500000) := by
  have h := checkLog_sound (w := (3334 / 12291)) (n := 12)
    (lo := (278218423 / 500000000)) (hi := (556436847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8957) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8957) = 1/(8957 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-251385797 / 62500000) (-2011086373 / 500000000) (Real.log (8957 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (588234007 / 125000000) ≤ -Real.log (500000000000 / 55297344046423) ∧
    -Real.log (500000000000 / 55297344046423) ≤ (4705872063 / 1000000000) := by
  have h := checkLog_sound (w := (23297344046423 / 87297344046423)) (n := 12)
    (lo := (34186811 / 62500000)) (hi := (546988977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55297344046423 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55297344046423 / 32000000000000) = 1/(500000000000 / 55297344046423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (588234007 / 125000000) (4705872063 / 1000000000) (Real.log (55297344046423 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (55297344046423 / 500000000000) = -Real.log (500000000000 / 55297344046423) := by
    rw [show ((55297344046423 / 500000000000) : ℝ) = ((500000000000 / 55297344046423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2355080007 / 500000000) ≤ -Real.log (500000000000 / 55534965818671) ∧
    -Real.log (500000000000 / 55534965818671) ≤ (4710160021 / 1000000000) := by
  have h := checkLog_sound (w := (23534965818671 / 87534965818671)) (n := 12)
    (lo := (275638467 / 500000000)) (hi := (110255387 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55534965818671 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55534965818671 / 32000000000000) = 1/(500000000000 / 55534965818671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2355080007 / 500000000) (4710160021 / 1000000000) (Real.log (55534965818671 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (55534965818671 / 500000000000) = -Real.log (500000000000 / 55534965818671) := by
    rw [show ((55534965818671 / 500000000000) : ℝ) = ((500000000000 / 55534965818671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4701938533 / 1000000000) ≤ -Real.log (125000000000 / 13770064473099) ∧
    -Real.log (125000000000 / 13770064473099) ≤ (235096927 / 50000000) := by
  have h := checkLog_sound (w := (5770064473099 / 21770064473099)) (n := 12)
    (lo := (543055453 / 1000000000)) (hi := (271527727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13770064473099 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(13770064473099 / 8000000000000) = 1/(125000000000 / 13770064473099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4701938533 / 1000000000) (235096927 / 50000000) (Real.log (13770064473099 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13770064473099 / 125000000000) = -Real.log (125000000000 / 13770064473099) := by
    rw [show ((13770064473099 / 125000000000) : ℝ) = ((125000000000 / 13770064473099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4706322571 / 1000000000) ≤ -Real.log (500000000000 / 55322261918053) ∧
    -Real.log (500000000000 / 55322261918053) ≤ (2353161289 / 500000000) := by
  have h := checkLog_sound (w := (23322261918053 / 87322261918053)) (n := 12)
    (lo := (547439491 / 1000000000)) (hi := (136859873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55322261918053 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55322261918053 / 32000000000000) = 1/(500000000000 / 55322261918053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4706322571 / 1000000000) (2353161289 / 500000000) (Real.log (55322261918053 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (55322261918053 / 500000000000) = -Real.log (500000000000 / 55322261918053) := by
    rw [show ((55322261918053 / 500000000000) : ℝ) = ((500000000000 / 55322261918053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0011

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0012Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0012
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

theorem reflection_log_1_neg : (682534423 / 1000000000) ≤ -Real.log (51200 / 101319) ∧
    -Real.log (51200 / 101319) ≤ (85316803 / 125000000) := by
  have h := checkLog_sound (w := (50119 / 152519)) (n := 12)
    (lo := (682534423 / 1000000000)) (hi := (85316803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101319 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101319 / 51200) = 1/(51200 / 101319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682534423 / 1000000000) (85316803 / 125000000) (Real.log (101319 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101319 / 51200) = -Real.log (51200 / 101319) := by
    rw [show ((101319 / 51200) : ℝ) = ((51200 / 101319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (385785299 / 100000000) ≤ -Real.log (1081 / 51200) ∧
    -Real.log (1081 / 51200) ≤ (964463249 / 250000000) := by
  have h := checkLog_sound (w := (519 / 2681)) (n := 12)
    (lo := (39211709 / 100000000)) (hi := (392117091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1081) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1081) = 1/(1081 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-964463249 / 250000000) (-385785299 / 100000000) (Real.log (1081 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (34124377 / 50000000) ≤ -Real.log (31250000000 / 61837310791) ∧
    -Real.log (31250000000 / 61837310791) ≤ (682487541 / 1000000000) := by
  have h := checkLog_sound (w := (30587310791 / 93087310791)) (n := 12)
    (lo := (34124377 / 50000000)) (hi := (682487541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61837310791 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61837310791 / 31250000000) = 1/(31250000000 / 61837310791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (34124377 / 50000000) (682487541 / 1000000000) (Real.log (61837310791 / 31250000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (61837310791 / 31250000000) = -Real.log (31250000000 / 61837310791) := by
    rw [show ((61837310791 / 31250000000) : ℝ) = ((31250000000 / 61837310791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (481683567 / 125000000) ≤ -Real.log (662689209 / 31250000000) ∧
    -Real.log (662689209 / 31250000000) ≤ (1926734271 / 500000000) := by
  have h := checkLog_sound (w := (313873291 / 1639251709)) (n := 12)
    (lo := (96933159 / 250000000)) (hi := (387732637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 662689209) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(976562500 / 662689209) = 1/(662689209 / 31250000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1926734271 / 500000000) (-481683567 / 125000000) (Real.log (662689209 / 31250000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (335903913 / 500000000) ≤ -Real.log (25600 / 50119) ∧
    -Real.log (25600 / 50119) ≤ (671807827 / 1000000000) := by
  have h := checkLog_sound (w := (24519 / 75719)) (n := 12)
    (lo := (335903913 / 500000000)) (hi := (671807827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50119 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50119 / 25600) = 1/(25600 / 50119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (335903913 / 500000000) (671807827 / 1000000000) (Real.log (50119 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (50119 / 25600) = -Real.log (25600 / 50119) := by
    rw [show ((50119 / 25600) : ℝ) = ((25600 / 50119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (316470581 / 100000000) ≤ -Real.log (1081 / 25600) ∧
    -Real.log (1081 / 25600) ≤ (632941163 / 200000000) := by
  have h := checkLog_sound (w := (519 / 2681)) (n := 12)
    (lo := (39211709 / 100000000)) (hi := (392117091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1081) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1081) = 1/(1081 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-632941163 / 200000000) (-316470581 / 100000000) (Real.log (1081 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (671713047 / 1000000000) ≤ -Real.log (102400 / 200457) ∧
    -Real.log (102400 / 200457) ≤ (83964131 / 125000000) := by
  have h := checkLog_sound (w := (98057 / 302857)) (n := 12)
    (lo := (671713047 / 1000000000)) (hi := (83964131 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200457 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200457 / 102400) = 1/(102400 / 200457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (671713047 / 1000000000) (83964131 / 125000000) (Real.log (200457 / 102400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (200457 / 102400) = -Real.log (102400 / 200457) := by
    rw [show ((200457 / 102400) : ℝ) = ((102400 / 200457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (790080339 / 250000000) ≤ -Real.log (4343 / 102400) ∧
    -Real.log (4343 / 102400) ≤ (3160321361 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 10743)) (n := 12)
    (lo := (96933159 / 250000000)) (hi := (387732637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4343) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4343) = 1/(4343 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3160321361 / 1000000000) (-790080339 / 250000000) (Real.log (4343 / 102400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (171026861 / 250000000) ≤ -Real.log (500000 / 991001) ∧
    -Real.log (500000 / 991001) ≤ (136821489 / 200000000) := by
  have h := checkLog_sound (w := (491001 / 1491001)) (n := 12)
    (lo := (171026861 / 250000000)) (hi := (136821489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991001 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991001 / 500000) = 1/(500000 / 991001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (171026861 / 250000000) (136821489 / 200000000) (Real.log (991001 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (991001 / 500000) = -Real.log (500000 / 991001) := by
    rw [show ((991001 / 500000) : ℝ) = ((500000 / 991001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (803498927 / 200000000) ≤ -Real.log (8999 / 500000) ∧
    -Real.log (8999 / 500000) ≤ (4017494641 / 1000000000) := by
  have h := checkLog_sound (w := (3313 / 12312)) (n := 12)
    (lo := (110351747 / 200000000)) (hi := (34484921 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8999) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8999) = 1/(8999 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4017494641 / 1000000000) (-803498927 / 200000000) (Real.log (8999 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684146293 / 1000000000) ≤ -Real.log (1000000 / 1982079) ∧
    -Real.log (1000000 / 1982079) ≤ (342073147 / 500000000) := by
  have h := checkLog_sound (w := (982079 / 2982079)) (n := 12)
    (lo := (684146293 / 1000000000)) (hi := (342073147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982079 / 1000000) = 1/(1000000 / 1982079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684146293 / 1000000000) (342073147 / 500000000) (Real.log (1982079 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982079 / 1000000) = -Real.log (1000000 / 1982079) := by
    rw [show ((1982079 / 1000000) : ℝ) = ((1000000 / 1982079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2010891033 / 500000000) ≤ -Real.log (17921 / 1000000) ∧
    -Real.log (17921 / 1000000) ≤ (502722759 / 125000000) := by
  have h := checkLog_sound (w := (13329 / 49171)) (n := 12)
    (lo := (278023083 / 500000000)) (hi := (556046167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17921) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17921) = 1/(17921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-502722759 / 125000000) (-2010891033 / 500000000) (Real.log (17921 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (342036063 / 500000000) ≤ -Real.log (250000 / 495483) ∧
    -Real.log (250000 / 495483) ≤ (684072127 / 1000000000) := by
  have h := checkLog_sound (w := (245483 / 745483)) (n := 12)
    (lo := (342036063 / 500000000)) (hi := (684072127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495483 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495483 / 250000) = 1/(250000 / 495483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (342036063 / 500000000) (684072127 / 1000000000) (Real.log (495483 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (495483 / 250000) = -Real.log (250000 / 495483) := by
    rw [show ((495483 / 250000) : ℝ) = ((250000 / 495483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2006806429 / 500000000) ≤ -Real.log (4517 / 250000) ∧
    -Real.log (4517 / 250000) ≤ (62712701 / 15625000) := by
  have h := checkLog_sound (w := (6591 / 24659)) (n := 12)
    (lo := (273938479 / 500000000)) (hi := (547876959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9034) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9034) = 1/(4517 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62712701 / 15625000) (-2006806429 / 500000000) (Real.log (4517 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (5344617 / 7812500) ≤ -Real.log (1000000 / 1982009) ∧
    -Real.log (1000000 / 1982009) ≤ (684110977 / 1000000000) := by
  have h := checkLog_sound (w := (982009 / 2982009)) (n := 12)
    (lo := (5344617 / 7812500)) (hi := (684110977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982009 / 1000000) = 1/(1000000 / 1982009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (5344617 / 7812500) (684110977 / 1000000000) (Real.log (1982009 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1982009 / 1000000) = -Real.log (1000000 / 1982009) := by
    rw [show ((1982009 / 1000000) : ℝ) = ((1000000 / 1982009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4017883643 / 1000000000) ≤ -Real.log (17991 / 1000000) ∧
    -Real.log (17991 / 1000000) ≤ (4017883649 / 1000000000) := by
  have h := checkLog_sound (w := (13259 / 49241)) (n := 12)
    (lo := (552147743 / 1000000000)) (hi := (17254617 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17991) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17991) = 1/(17991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4017883649 / 1000000000) (-4017883643 / 1000000000) (Real.log (17991 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4701602079 / 1000000000) ≤ -Real.log (500000000000 / 55061729081009) ∧
    -Real.log (500000000000 / 55061729081009) ≤ (2350801043 / 500000000) := by
  have h := checkLog_sound (w := (23061729081009 / 87061729081009)) (n := 12)
    (lo := (542718999 / 1000000000)) (hi := (542719 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55061729081009 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55061729081009 / 32000000000000) = 1/(500000000000 / 55061729081009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4701602079 / 1000000000) (2350801043 / 500000000) (Real.log (55061729081009 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (55061729081009 / 500000000000) = -Real.log (500000000000 / 55061729081009) := by
    rw [show ((55061729081009 / 500000000000) : ℝ) = ((500000000000 / 55061729081009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4705928359 / 1000000000) ≤ -Real.log (500000000000 / 55300457563753) ∧
    -Real.log (500000000000 / 55300457563753) ≤ (2352964183 / 500000000) := by
  have h := checkLog_sound (w := (23300457563753 / 87300457563753)) (n := 12)
    (lo := (547045279 / 1000000000)) (hi := (3419033 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55300457563753 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55300457563753 / 32000000000000) = 1/(500000000000 / 55300457563753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4705928359 / 1000000000) (2352964183 / 500000000) (Real.log (55300457563753 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (55300457563753 / 500000000000) = -Real.log (500000000000 / 55300457563753) := by
    rw [show ((55300457563753 / 500000000000) : ℝ) = ((500000000000 / 55300457563753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (587210623 / 125000000) ≤ -Real.log (125000000000 / 13711617223821) ∧
    -Real.log (125000000000 / 13711617223821) ≤ (4697684991 / 1000000000) := by
  have h := checkLog_sound (w := (5711617223821 / 21711617223821)) (n := 12)
    (lo := (33675119 / 62500000)) (hi := (107760381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13711617223821 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(13711617223821 / 8000000000000) = 1/(125000000000 / 13711617223821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (587210623 / 125000000) (4697684991 / 1000000000) (Real.log (13711617223821 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13711617223821 / 125000000000) = -Real.log (125000000000 / 13711617223821) := by
    rw [show ((13711617223821 / 125000000000) : ℝ) = ((125000000000 / 13711617223821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4701994619 / 1000000000) ≤ -Real.log (500000000000 / 55083347229171) ∧
    -Real.log (500000000000 / 55083347229171) ≤ (2350997313 / 500000000) := by
  have h := checkLog_sound (w := (23083347229171 / 87083347229171)) (n := 12)
    (lo := (543111539 / 1000000000)) (hi := (27155577 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55083347229171 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55083347229171 / 32000000000000) = 1/(500000000000 / 55083347229171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4701994619 / 1000000000) (2350997313 / 500000000) (Real.log (55083347229171 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (55083347229171 / 500000000000) = -Real.log (500000000000 / 55083347229171) := by
    rw [show ((55083347229171 / 500000000000) : ℝ) = ((500000000000 / 55083347229171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0012

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0013Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0013
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

theorem reflection_log_1_neg : (34124377 / 50000000) ≤ -Real.log (1000000000000 / 1978793945313) ∧
    -Real.log (1000000000000 / 1978793945313) ≤ (682487541 / 1000000000) := by
  have h := checkLog_sound (w := (978793945313 / 2978793945313)) (n := 12)
    (lo := (34124377 / 50000000)) (hi := (682487541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978793945313 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978793945313 / 1000000000000) = 1/(1000000000000 / 1978793945313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (34124377 / 50000000) (682487541 / 1000000000) (Real.log (1978793945313 / 1000000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1978793945313 / 1000000000000) = -Real.log (1000000000000 / 1978793945313) := by
    rw [show ((1978793945313 / 1000000000000) : ℝ) = ((1000000000000 / 1978793945313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (481683567 / 125000000) ≤ -Real.log (21206054687 / 1000000000000) ∧
    -Real.log (21206054687 / 1000000000000) ≤ (1926734271 / 500000000) := by
  have h := checkLog_sound (w := (10043945313 / 52456054687)) (n := 12)
    (lo := (96933159 / 250000000)) (hi := (387732637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 21206054687) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 21206054687) = 1/(21206054687 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1926734271 / 500000000) (-481683567 / 125000000) (Real.log (21206054687 / 1000000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (136488131 / 200000000) ≤ -Real.log (102400 / 202619) ∧
    -Real.log (102400 / 202619) ≤ (42652541 / 62500000) := by
  have h := checkLog_sound (w := (100219 / 305019)) (n := 12)
    (lo := (136488131 / 200000000)) (hi := (42652541 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202619 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202619 / 102400) = 1/(102400 / 202619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (136488131 / 200000000) (42652541 / 62500000) (Real.log (202619 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202619 / 102400) = -Real.log (102400 / 202619) := by
    rw [show ((202619 / 102400) : ℝ) = ((102400 / 202619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1924551611 / 500000000) ≤ -Real.log (2181 / 102400) ∧
    -Real.log (2181 / 102400) ≤ (962275807 / 250000000) := by
  have h := checkLog_sound (w := (1019 / 5381)) (n := 12)
    (lo := (191683661 / 500000000)) (hi := (383367323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2181) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2181) = 1/(2181 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-962275807 / 250000000) (-1924551611 / 500000000) (Real.log (2181 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (671713047 / 1000000000) ≤ -Real.log (102400 / 200457) ∧
    -Real.log (102400 / 200457) ≤ (83964131 / 125000000) := by
  have h := checkLog_sound (w := (98057 / 302857)) (n := 12)
    (lo := (671713047 / 1000000000)) (hi := (83964131 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200457 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200457 / 102400) = 1/(102400 / 200457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (671713047 / 1000000000) (83964131 / 125000000) (Real.log (200457 / 102400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (200457 / 102400) = -Real.log (102400 / 200457) := by
    rw [show ((200457 / 102400) : ℝ) = ((102400 / 200457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (790080339 / 250000000) ≤ -Real.log (4343 / 102400) ∧
    -Real.log (4343 / 102400) ≤ (3160321361 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 10743)) (n := 12)
    (lo := (96933159 / 250000000)) (hi := (387732637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4343) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4343) = 1/(4343 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3160321361 / 1000000000) (-790080339 / 250000000) (Real.log (4343 / 102400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (671618259 / 1000000000) ≤ -Real.log (51200 / 100219) ∧
    -Real.log (51200 / 100219) ≤ (33580913 / 50000000) := by
  have h := checkLog_sound (w := (49019 / 151419)) (n := 12)
    (lo := (671618259 / 1000000000)) (hi := (33580913 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100219 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100219 / 51200) = 1/(51200 / 100219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (671618259 / 1000000000) (33580913 / 50000000) (Real.log (100219 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100219 / 51200) = -Real.log (51200 / 100219) := by
    rw [show ((100219 / 51200) : ℝ) = ((51200 / 100219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1577978021 / 500000000) ≤ -Real.log (2181 / 51200) ∧
    -Real.log (2181 / 51200) ≤ (3155956047 / 1000000000) := by
  have h := checkLog_sound (w := (1019 / 5381)) (n := 12)
    (lo := (191683661 / 500000000)) (hi := (383367323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2181) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2181) = 1/(2181 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3155956047 / 1000000000) (-1577978021 / 500000000) (Real.log (2181 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684069099 / 1000000000) ≤ -Real.log (500000 / 990963) ∧
    -Real.log (500000 / 990963) ≤ (6840691 / 10000000) := by
  have h := checkLog_sound (w := (490963 / 1490963)) (n := 12)
    (lo := (684069099 / 1000000000)) (hi := (6840691 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990963 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990963 / 500000) = 1/(500000 / 990963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684069099 / 1000000000) (6840691 / 10000000) (Real.log (990963 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (990963 / 500000) = -Real.log (500000 / 990963) := by
    rw [show ((990963 / 500000) : ℝ) = ((500000 / 990963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2006640417 / 500000000) ≤ -Real.log (9037 / 500000) ∧
    -Real.log (9037 / 500000) ≤ (100332021 / 25000000) := by
  have h := checkLog_sound (w := (3294 / 12331)) (n := 12)
    (lo := (273772467 / 500000000)) (hi := (109508987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9037) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9037) = 1/(9037 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-100332021 / 25000000) (-2006640417 / 500000000) (Real.log (9037 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684107949 / 1000000000) ≤ -Real.log (1000000 / 1982003) ∧
    -Real.log (1000000 / 1982003) ≤ (13682159 / 20000000) := by
  have h := checkLog_sound (w := (982003 / 2982003)) (n := 12)
    (lo := (684107949 / 1000000000)) (hi := (13682159 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982003 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982003 / 1000000) = 1/(1000000 / 1982003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684107949 / 1000000000) (13682159 / 20000000) (Real.log (1982003 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982003 / 1000000) = -Real.log (1000000 / 1982003) := by
    rw [show ((1982003 / 1000000) : ℝ) = ((1000000 / 1982003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2008775099 / 500000000) ≤ -Real.log (17997 / 1000000) ∧
    -Real.log (17997 / 1000000) ≤ (1004387551 / 250000000) := by
  have h := checkLog_sound (w := (13253 / 49247)) (n := 12)
    (lo := (275907149 / 500000000)) (hi := (551814299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17997) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17997) = 1/(17997 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1004387551 / 250000000) (-2008775099 / 500000000) (Real.log (17997 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684033779 / 1000000000) ≤ -Real.log (31250 / 61933) ∧
    -Real.log (31250 / 61933) ≤ (34201689 / 50000000) := by
  have h := checkLog_sound (w := (30683 / 93183)) (n := 12)
    (lo := (684033779 / 1000000000)) (hi := (34201689 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61933 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61933 / 31250) = 1/(31250 / 61933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684033779 / 1000000000) (34201689 / 50000000) (Real.log (61933 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61933 / 31250) = -Real.log (31250 / 61933) := by
    rw [show ((61933 / 31250) : ℝ) = ((31250 / 61933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1002353837 / 250000000) ≤ -Real.log (567 / 31250) ∧
    -Real.log (567 / 31250) ≤ (2004707677 / 500000000) := by
  have h := checkLog_sound (w := (6553 / 24697)) (n := 12)
    (lo := (67959931 / 125000000)) (hi := (543679449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9072) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9072) = 1/(567 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2004707677 / 500000000) (-1002353837 / 250000000) (Real.log (567 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684072631 / 1000000000) ≤ -Real.log (1000000 / 1981933) ∧
    -Real.log (1000000 / 1981933) ≤ (85509079 / 125000000) := by
  have h := checkLog_sound (w := (981933 / 2981933)) (n := 12)
    (lo := (684072631 / 1000000000)) (hi := (85509079 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981933 / 1000000) = 1/(1000000 / 1981933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684072631 / 1000000000) (85509079 / 125000000) (Real.log (1981933 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1981933 / 1000000) = -Real.log (1000000 / 1981933) := by
    rw [show ((1981933 / 1000000) : ℝ) = ((1000000 / 1981933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2006834103 / 500000000) ≤ -Real.log (18067 / 1000000) ∧
    -Real.log (18067 / 1000000) ≤ (1003417053 / 250000000) := by
  have h := checkLog_sound (w := (13183 / 49317)) (n := 12)
    (lo := (273966153 / 500000000)) (hi := (547932307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18067) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18067) = 1/(18067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1003417053 / 250000000) (-2006834103 / 500000000) (Real.log (18067 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4697349933 / 1000000000) ≤ -Real.log (500000000000 / 54828095606949) ∧
    -Real.log (500000000000 / 54828095606949) ≤ (234867497 / 50000000) := by
  have h := checkLog_sound (w := (22828095606949 / 86828095606949)) (n := 12)
    (lo := (538466853 / 1000000000)) (hi := (269233427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54828095606949 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(54828095606949 / 32000000000000) = 1/(500000000000 / 54828095606949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4697349933 / 1000000000) (234867497 / 50000000) (Real.log (54828095606949 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (54828095606949 / 500000000000) = -Real.log (500000000000 / 54828095606949) := by
    rw [show ((54828095606949 / 500000000000) : ℝ) = ((500000000000 / 54828095606949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4701658147 / 1000000000) ≤ -Real.log (250000000000 / 27532408179141) ∧
    -Real.log (250000000000 / 27532408179141) ≤ (2350829077 / 500000000) := by
  have h := checkLog_sound (w := (11532408179141 / 43532408179141)) (n := 12)
    (lo := (542775067 / 1000000000)) (hi := (135693767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27532408179141 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(27532408179141 / 16000000000000) = 1/(250000000000 / 27532408179141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4701658147 / 1000000000) (2350829077 / 500000000) (Real.log (27532408179141 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (27532408179141 / 250000000000) = -Real.log (250000000000 / 27532408179141) := by
    rw [show ((27532408179141 / 250000000000) : ℝ) = ((250000000000 / 27532408179141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4693449127 / 1000000000) ≤ -Real.log (500000000000 / 54614638447971) ∧
    -Real.log (500000000000 / 54614638447971) ≤ (2346724567 / 500000000) := by
  have h := checkLog_sound (w := (22614638447971 / 86614638447971)) (n := 12)
    (lo := (534566047 / 1000000000)) (hi := (16705189 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54614638447971 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(54614638447971 / 32000000000000) = 1/(500000000000 / 54614638447971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4693449127 / 1000000000) (2346724567 / 500000000) (Real.log (54614638447971 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (54614638447971 / 500000000000) = -Real.log (500000000000 / 54614638447971) := by
    rw [show ((54614638447971 / 500000000000) : ℝ) = ((500000000000 / 54614638447971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1174435209 / 250000000) ≤ -Real.log (500000000000 / 54849532296453) ∧
    -Real.log (500000000000 / 54849532296453) ≤ (4697740843 / 1000000000) := by
  have h := checkLog_sound (w := (22849532296453 / 86849532296453)) (n := 12)
    (lo := (134714439 / 250000000)) (hi := (538857757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54849532296453 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(54849532296453 / 32000000000000) = 1/(500000000000 / 54849532296453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1174435209 / 250000000) (4697740843 / 1000000000) (Real.log (54849532296453 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (54849532296453 / 500000000000) = -Real.log (500000000000 / 54849532296453) := by
    rw [show ((54849532296453 / 500000000000) : ℝ) = ((500000000000 / 54849532296453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0013

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0014Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0014
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

theorem reflection_log_1_neg : (136488131 / 200000000) ≤ -Real.log (102400 / 202619) ∧
    -Real.log (102400 / 202619) ≤ (42652541 / 62500000) := by
  have h := checkLog_sound (w := (100219 / 305019)) (n := 12)
    (lo := (136488131 / 200000000)) (hi := (42652541 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202619 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202619 / 102400) = 1/(102400 / 202619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (136488131 / 200000000) (42652541 / 62500000) (Real.log (202619 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202619 / 102400) = -Real.log (102400 / 202619) := by
    rw [show ((202619 / 102400) : ℝ) = ((102400 / 202619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1924551611 / 500000000) ≤ -Real.log (2181 / 102400) ∧
    -Real.log (2181 / 102400) ≤ (962275807 / 250000000) := by
  have h := checkLog_sound (w := (1019 / 5381)) (n := 12)
    (lo := (191683661 / 500000000)) (hi := (383367323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2181) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2181) = 1/(2181 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-962275807 / 250000000) (-1924551611 / 500000000) (Real.log (2181 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682346879 / 1000000000) ≤ -Real.log (512 / 1013) ∧
    -Real.log (512 / 1013) ≤ (1066167 / 1562500) := by
  have h := checkLog_sound (w := (501 / 1525)) (n := 12)
    (lo := (682346879 / 1000000000)) (hi := (1066167 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1013 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1013 / 512) = 1/(512 / 1013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682346879 / 1000000000) (1066167 / 1562500) (Real.log (1013 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1013 / 512) = -Real.log (512 / 1013) := by
    rw [show ((1013 / 512) : ℝ) = ((512 / 1013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3840429349 / 1000000000) ≤ -Real.log (11 / 512) ∧
    -Real.log (11 / 512) ≤ (768085871 / 200000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16 / 11) = 1/(11 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-768085871 / 200000000) (-3840429349 / 1000000000) (Real.log (11 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (671618259 / 1000000000) ≤ -Real.log (51200 / 100219) ∧
    -Real.log (51200 / 100219) ≤ (33580913 / 50000000) := by
  have h := checkLog_sound (w := (49019 / 151419)) (n := 12)
    (lo := (671618259 / 1000000000)) (hi := (33580913 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100219 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100219 / 51200) = 1/(51200 / 100219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (671618259 / 1000000000) (33580913 / 50000000) (Real.log (100219 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100219 / 51200) = -Real.log (51200 / 100219) := by
    rw [show ((100219 / 51200) : ℝ) = ((51200 / 100219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1577978021 / 500000000) ≤ -Real.log (2181 / 51200) ∧
    -Real.log (2181 / 51200) ≤ (3155956047 / 1000000000) := by
  have h := checkLog_sound (w := (1019 / 5381)) (n := 12)
    (lo := (191683661 / 500000000)) (hi := (383367323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2181) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2181) = 1/(2181 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3155956047 / 1000000000) (-1577978021 / 500000000) (Real.log (2181 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41964291 / 62500000) ≤ -Real.log (256 / 501) ∧
    -Real.log (256 / 501) ≤ (671428657 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 757)) (n := 12)
    (lo := (41964291 / 62500000)) (hi := (671428657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((501 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(501 / 256) = 1/(256 / 501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41964291 / 62500000) (671428657 / 1000000000) (Real.log (501 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (501 / 256) = -Real.log (256 / 501) := by
    rw [show ((501 / 256) : ℝ) = ((256 / 501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3147282169 / 1000000000) ≤ -Real.log (11 / 256) ∧
    -Real.log (11 / 256) ≤ (1573641087 / 500000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 11) = 1/(11 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1573641087 / 500000000) (-3147282169 / 1000000000) (Real.log (11 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (683992907 / 1000000000) ≤ -Real.log (40000 / 79271) ∧
    -Real.log (40000 / 79271) ≤ (170998227 / 250000000) := by
  have h := checkLog_sound (w := (39271 / 119271)) (n := 12)
    (lo := (683992907 / 1000000000)) (hi := (170998227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79271 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79271 / 40000) = 1/(40000 / 79271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (683992907 / 1000000000) (170998227 / 250000000) (Real.log (79271 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (79271 / 40000) = -Real.log (40000 / 79271) := by
    rw [show ((79271 / 40000) : ℝ) = ((40000 / 79271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2002480499 / 500000000) ≤ -Real.log (729 / 40000) ∧
    -Real.log (729 / 40000) ≤ (1001240251 / 250000000) := by
  have h := checkLog_sound (w := (521 / 1979)) (n := 12)
    (lo := (269612549 / 500000000)) (hi := (539225099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 729) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1250 / 729) = 1/(729 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1001240251 / 250000000) (-2002480499 / 500000000) (Real.log (729 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684069603 / 1000000000) ≤ -Real.log (1000000 / 1981927) ∧
    -Real.log (1000000 / 1981927) ≤ (171017401 / 250000000) := by
  have h := checkLog_sound (w := (981927 / 2981927)) (n := 12)
    (lo := (684069603 / 1000000000)) (hi := (171017401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981927 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981927 / 1000000) = 1/(1000000 / 1981927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684069603 / 1000000000) (171017401 / 250000000) (Real.log (1981927 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1981927 / 1000000) = -Real.log (1000000 / 1981927) := by
    rw [show ((1981927 / 1000000) : ℝ) = ((1000000 / 1981927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1003334041 / 250000000) ≤ -Real.log (18073 / 1000000) ∧
    -Real.log (18073 / 1000000) ≤ (401333617 / 100000000) := by
  have h := checkLog_sound (w := (13177 / 49323)) (n := 12)
    (lo := (68450033 / 125000000)) (hi := (109520053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18073) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18073) = 1/(18073 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-401333617 / 100000000) (-1003334041 / 250000000) (Real.log (18073 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21373643 / 31250000) ≤ -Real.log (1000000 / 1981703) ∧
    -Real.log (1000000 / 1981703) ≤ (683956577 / 1000000000) := by
  have h := checkLog_sound (w := (981703 / 2981703)) (n := 12)
    (lo := (21373643 / 31250000)) (hi := (683956577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981703 / 1000000) = 1/(1000000 / 1981703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21373643 / 31250000) (683956577 / 1000000000) (Real.log (1981703 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1981703 / 1000000) = -Real.log (1000000 / 1981703) := by
    rw [show ((1981703 / 1000000) : ℝ) = ((1000000 / 1981703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1000254541 / 250000000) ≤ -Real.log (18297 / 1000000) ∧
    -Real.log (18297 / 1000000) ≤ (400101817 / 100000000) := by
  have h := checkLog_sound (w := (12953 / 49547)) (n := 12)
    (lo := (66910283 / 125000000)) (hi := (107056453 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18297) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18297) = 1/(18297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-400101817 / 100000000) (-1000254541 / 250000000) (Real.log (18297 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684034283 / 1000000000) ≤ -Real.log (1000000 / 1981857) ∧
    -Real.log (1000000 / 1981857) ≤ (171008571 / 250000000) := by
  have h := checkLog_sound (w := (981857 / 2981857)) (n := 12)
    (lo := (684034283 / 1000000000)) (hi := (171008571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981857 / 1000000) = 1/(1000000 / 1981857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684034283 / 1000000000) (171008571 / 250000000) (Real.log (1981857 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1981857 / 1000000) = -Real.log (1000000 / 1981857) := by
    rw [show ((1981857 / 1000000) : ℝ) = ((1000000 / 1981857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (7830997 / 1953125) ≤ -Real.log (18143 / 1000000) ∧
    -Real.log (18143 / 1000000) ≤ (400947047 / 100000000) := by
  have h := checkLog_sound (w := (13107 / 49393)) (n := 12)
    (lo := (135933641 / 250000000)) (hi := (108746913 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18143) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18143) = 1/(18143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-400947047 / 100000000) (-7830997 / 1953125) (Real.log (18143 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (937790781 / 200000000) ≤ -Real.log (250000000000 / 27184842249657) ∧
    -Real.log (250000000000 / 27184842249657) ≤ (586119239 / 125000000) := by
  have h := checkLog_sound (w := (11184842249657 / 43184842249657)) (n := 12)
    (lo := (21202833 / 40000000)) (hi := (265035413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27184842249657 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(27184842249657 / 16000000000000) = 1/(250000000000 / 27184842249657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (937790781 / 200000000) (586119239 / 125000000) (Real.log (27184842249657 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (27184842249657 / 250000000000) = -Real.log (250000000000 / 27184842249657) := by
    rw [show ((27184842249657 / 250000000000) : ℝ) = ((250000000000 / 27184842249657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4697405767 / 1000000000) ≤ -Real.log (500000000000 / 54831156974493) ∧
    -Real.log (500000000000 / 54831156974493) ≤ (2348702887 / 500000000) := by
  have h := checkLog_sound (w := (22831156974493 / 86831156974493)) (n := 12)
    (lo := (538522687 / 1000000000)) (hi := (8414417 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54831156974493 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(54831156974493 / 32000000000000) = 1/(500000000000 / 54831156974493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4697405767 / 1000000000) (2348702887 / 500000000) (Real.log (54831156974493 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (54831156974493 / 500000000000) = -Real.log (500000000000 / 54831156974493) := by
    rw [show ((54831156974493 / 500000000000) : ℝ) = ((500000000000 / 54831156974493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4684974739 / 1000000000) ≤ -Real.log (500000000000 / 54153768377329) ∧
    -Real.log (500000000000 / 54153768377329) ≤ (2342487373 / 500000000) := by
  have h := checkLog_sound (w := (22153768377329 / 86153768377329)) (n := 12)
    (lo := (526091659 / 1000000000)) (hi := (26304583 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54153768377329 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(54153768377329 / 32000000000000) = 1/(500000000000 / 54153768377329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4684974739 / 1000000000) (2342487373 / 500000000) (Real.log (54153768377329 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (54153768377329 / 500000000000) = -Real.log (500000000000 / 54153768377329) := by
    rw [show ((54153768377329 / 500000000000) : ℝ) = ((500000000000 / 54153768377329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1173376187 / 250000000) ≤ -Real.log (50000000000 / 5461767623877) ∧
    -Real.log (50000000000 / 5461767623877) ≤ (938700951 / 200000000) := by
  have h := checkLog_sound (w := (2261767623877 / 8661767623877)) (n := 12)
    (lo := (133655417 / 250000000)) (hi := (534621669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5461767623877 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5461767623877 / 3200000000000) = 1/(50000000000 / 5461767623877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1173376187 / 250000000) (938700951 / 200000000) (Real.log (5461767623877 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5461767623877 / 50000000000) = -Real.log (50000000000 / 5461767623877) := by
    rw [show ((5461767623877 / 50000000000) : ℝ) = ((50000000000 / 5461767623877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0014

end


