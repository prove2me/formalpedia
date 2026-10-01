-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0045Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0045Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:00:35.196882+00:00
-- url     : https://prove2.me/theorems/65214ab5-667a-43e5-8984-6cd32a8db4c6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0045Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0046Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0045Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0046Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0047Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0048Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0049Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0050Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0045Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0046Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0047Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0048Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0049Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0050Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0045Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0046Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0047Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0048Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0049Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0050Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0045Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0046Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0047Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0048Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0049Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0050Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0045Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0045
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

theorem reflection_log_1_neg : (42470593 / 62500000) ≤ -Real.log (10240 / 20203) ∧
    -Real.log (10240 / 20203) ≤ (679529489 / 1000000000) := by
  have h := checkLog_sound (w := (9963 / 30443)) (n := 12)
    (lo := (42470593 / 62500000)) (hi := (679529489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20203 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20203 / 10240) = 1/(10240 / 20203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42470593 / 62500000) (679529489 / 1000000000) (Real.log (20203 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20203 / 10240) = -Real.log (10240 / 20203) := by
    rw [show ((20203 / 10240) : ℝ) = ((10240 / 20203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3610039389 / 1000000000) ≤ -Real.log (277 / 10240) ∧
    -Real.log (277 / 10240) ≤ (722007879 / 200000000) := by
  have h := checkLog_sound (w := (43 / 597)) (n := 12)
    (lo := (144303489 / 1000000000)) (hi := (14430349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 277) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(320 / 277) = 1/(277 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-722007879 / 200000000) (-3610039389 / 1000000000) (Real.log (277 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (339717719 / 500000000) ≤ -Real.log (102400 / 202011) ∧
    -Real.log (102400 / 202011) ≤ (679435439 / 1000000000) := by
  have h := checkLog_sound (w := (99611 / 304411)) (n := 12)
    (lo := (339717719 / 500000000)) (hi := (679435439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202011 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202011 / 102400) = 1/(102400 / 202011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (339717719 / 500000000) (679435439 / 1000000000) (Real.log (202011 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202011 / 102400) = -Real.log (102400 / 202011) := by
    rw [show ((202011 / 102400) : ℝ) = ((102400 / 202011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3603203601 / 1000000000) ≤ -Real.log (2789 / 102400) ∧
    -Real.log (2789 / 102400) ≤ (3603203607 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 5989)) (n := 12)
    (lo := (137467701 / 1000000000)) (hi := (68733851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2789) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2789) = 1/(2789 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3603203607 / 1000000000) (-3603203601 / 1000000000) (Real.log (2789 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41607737 / 62500000) ≤ -Real.log (5120 / 9963) ∧
    -Real.log (5120 / 9963) ≤ (665723793 / 1000000000) := by
  have h := checkLog_sound (w := (4843 / 15083)) (n := 12)
    (lo := (41607737 / 62500000)) (hi := (665723793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9963 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9963 / 5120) = 1/(5120 / 9963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41607737 / 62500000) (665723793 / 1000000000) (Real.log (9963 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9963 / 5120) = -Real.log (5120 / 9963) := by
    rw [show ((9963 / 5120) : ℝ) = ((5120 / 9963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2916892209 / 1000000000) ≤ -Real.log (277 / 5120) ∧
    -Real.log (277 / 5120) ≤ (1458446107 / 500000000) := by
  have h := checkLog_sound (w := (43 / 597)) (n := 12)
    (lo := (144303489 / 1000000000)) (hi := (14430349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 277) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 277) = 1/(277 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1458446107 / 500000000) (-2916892209 / 1000000000) (Real.log (277 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (166383267 / 250000000) ≤ -Real.log (51200 / 99611) ∧
    -Real.log (51200 / 99611) ≤ (665533069 / 1000000000) := by
  have h := checkLog_sound (w := (48411 / 150811)) (n := 12)
    (lo := (166383267 / 250000000)) (hi := (665533069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99611 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99611 / 51200) = 1/(51200 / 99611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (166383267 / 250000000) (665533069 / 1000000000) (Real.log (99611 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99611 / 51200) = -Real.log (51200 / 99611) := by
    rw [show ((99611 / 51200) : ℝ) = ((51200 / 99611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2910056421 / 1000000000) ≤ -Real.log (2789 / 51200) ∧
    -Real.log (2789 / 51200) ≤ (1455028213 / 500000000) := by
  have h := checkLog_sound (w := (411 / 5989)) (n := 12)
    (lo := (137467701 / 1000000000)) (hi := (68733851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2789) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2789) = 1/(2789 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1455028213 / 500000000) (-2910056421 / 1000000000) (Real.log (2789 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340822643 / 500000000) ≤ -Real.log (125000 / 247141) ∧
    -Real.log (125000 / 247141) ≤ (681645287 / 1000000000) := by
  have h := checkLog_sound (w := (122141 / 372141)) (n := 12)
    (lo := (340822643 / 500000000)) (hi := (681645287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247141 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247141 / 125000) = 1/(125000 / 247141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340822643 / 500000000) (681645287 / 1000000000) (Real.log (247141 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (247141 / 125000) = -Real.log (125000 / 247141) := by
    rw [show ((247141 / 125000) : ℝ) = ((125000 / 247141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3777841821 / 1000000000) ≤ -Real.log (2859 / 125000) ∧
    -Real.log (2859 / 125000) ≤ (3777841827 / 1000000000) := by
  have h := checkLog_sound (w := (4189 / 27061)) (n := 12)
    (lo := (312105921 / 1000000000)) (hi := (156052961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11436) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11436) = 1/(2859 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3777841827 / 1000000000) (-3777841821 / 1000000000) (Real.log (2859 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (681721151 / 1000000000) ≤ -Real.log (500000 / 988639) ∧
    -Real.log (500000 / 988639) ≤ (10651893 / 15625000) := by
  have h := checkLog_sound (w := (488639 / 1488639)) (n := 12)
    (lo := (681721151 / 1000000000)) (hi := (10651893 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988639 / 500000) = 1/(500000 / 988639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (681721151 / 1000000000) (10651893 / 15625000) (Real.log (988639 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (988639 / 500000) = -Real.log (500000 / 988639) := by
    rw [show ((988639 / 500000) : ℝ) = ((500000 / 988639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1892210829 / 500000000) ≤ -Real.log (11361 / 500000) ∧
    -Real.log (11361 / 500000) ≤ (118263177 / 31250000) := by
  have h := checkLog_sound (w := (2132 / 13493)) (n := 12)
    (lo := (159342879 / 500000000)) (hi := (318685759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11361) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11361) = 1/(11361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-118263177 / 31250000) (-1892210829 / 500000000) (Real.log (11361 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681583073 / 1000000000) ≤ -Real.log (200000 / 395401) ∧
    -Real.log (200000 / 395401) ≤ (340791537 / 500000000) := by
  have h := checkLog_sound (w := (195401 / 595401)) (n := 12)
    (lo := (681583073 / 1000000000)) (hi := (340791537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395401 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395401 / 200000) = 1/(200000 / 395401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681583073 / 1000000000) (340791537 / 500000000) (Real.log (395401 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (395401 / 200000) = -Real.log (200000 / 395401) := by
    rw [show ((395401 / 200000) : ℝ) = ((200000 / 395401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (150899139 / 40000000) ≤ -Real.log (4599 / 200000) ∧
    -Real.log (4599 / 200000) ≤ (3772478481 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 10849)) (n := 12)
    (lo := (12269703 / 40000000)) (hi := (19171411 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4599) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4599) = 1/(4599 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3772478481 / 1000000000) (-150899139 / 40000000) (Real.log (4599 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (340829977 / 500000000) ≤ -Real.log (1000000 / 1977157) ∧
    -Real.log (1000000 / 1977157) ≤ (136331991 / 200000000) := by
  have h := checkLog_sound (w := (977157 / 2977157)) (n := 12)
    (lo := (340829977 / 500000000)) (hi := (136331991 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977157 / 1000000) = 1/(1000000 / 1977157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (340829977 / 500000000) (136331991 / 200000000) (Real.log (1977157 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1977157 / 1000000) = -Real.log (1000000 / 1977157) := by
    rw [show ((1977157 / 1000000) : ℝ) = ((1000000 / 1977157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3779110551 / 1000000000) ≤ -Real.log (22843 / 1000000) ∧
    -Real.log (22843 / 1000000) ≤ (3779110557 / 1000000000) := by
  have h := checkLog_sound (w := (8407 / 54093)) (n := 12)
    (lo := (313374651 / 1000000000)) (hi := (78343663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22843) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22843) = 1/(22843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3779110557 / 1000000000) (-3779110551 / 1000000000) (Real.log (22843 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4459487107 / 1000000000) ≤ -Real.log (500000000000 / 43221580972367) ∧
    -Real.log (500000000000 / 43221580972367) ≤ (2229743557 / 500000000) := by
  have h := checkLog_sound (w := (11221580972367 / 75221580972367)) (n := 12)
    (lo := (300604027 / 1000000000)) (hi := (75151007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43221580972367 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(43221580972367 / 32000000000000) = 1/(500000000000 / 43221580972367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4459487107 / 1000000000) (2229743557 / 500000000) (Real.log (43221580972367 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (43221580972367 / 500000000000) = -Real.log (500000000000 / 43221580972367) := by
    rw [show ((43221580972367 / 500000000000) : ℝ) = ((500000000000 / 43221580972367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (558267851 / 125000000) ≤ -Real.log (250000000000 / 21755105184403) ∧
    -Real.log (250000000000 / 21755105184403) ≤ (893228563 / 200000000) := by
  have h := checkLog_sound (w := (5755105184403 / 37755105184403)) (n := 12)
    (lo := (19203733 / 62500000)) (hi := (307259729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21755105184403 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21755105184403 / 16000000000000) = 1/(250000000000 / 21755105184403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (558267851 / 125000000) (893228563 / 200000000) (Real.log (21755105184403 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21755105184403 / 250000000000) = -Real.log (250000000000 / 21755105184403) := by
    rw [show ((21755105184403 / 250000000000) : ℝ) = ((250000000000 / 21755105184403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4454061547 / 1000000000) ≤ -Real.log (500000000000 / 42987714720591) ∧
    -Real.log (500000000000 / 42987714720591) ≤ (2227030777 / 500000000) := by
  have h := checkLog_sound (w := (10987714720591 / 74987714720591)) (n := 12)
    (lo := (295178467 / 1000000000)) (hi := (73794617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42987714720591 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(42987714720591 / 32000000000000) = 1/(500000000000 / 42987714720591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4454061547 / 1000000000) (2227030777 / 500000000) (Real.log (42987714720591 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (42987714720591 / 500000000000) = -Real.log (500000000000 / 42987714720591) := by
    rw [show ((42987714720591 / 500000000000) : ℝ) = ((500000000000 / 42987714720591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (892154101 / 200000000) ≤ -Real.log (500000000000 / 43277087072627) ∧
    -Real.log (500000000000 / 43277087072627) ≤ (278798157 / 62500000) := by
  have h := checkLog_sound (w := (11277087072627 / 75277087072627)) (n := 12)
    (lo := (12075497 / 40000000)) (hi := (150943713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43277087072627 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(43277087072627 / 32000000000000) = 1/(500000000000 / 43277087072627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (892154101 / 200000000) (278798157 / 62500000) (Real.log (43277087072627 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (43277087072627 / 500000000000) = -Real.log (500000000000 / 43277087072627) := by
    rw [show ((43277087072627 / 500000000000) : ℝ) = ((500000000000 / 43277087072627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0045

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0046Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0046
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

theorem reflection_log_1_neg : (339717719 / 500000000) ≤ -Real.log (102400 / 202011) ∧
    -Real.log (102400 / 202011) ≤ (679435439 / 1000000000) := by
  have h := checkLog_sound (w := (99611 / 304411)) (n := 12)
    (lo := (339717719 / 500000000)) (hi := (679435439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202011 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202011 / 102400) = 1/(102400 / 202011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (339717719 / 500000000) (679435439 / 1000000000) (Real.log (202011 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202011 / 102400) = -Real.log (102400 / 202011) := by
    rw [show ((202011 / 102400) : ℝ) = ((102400 / 202011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3603203601 / 1000000000) ≤ -Real.log (2789 / 102400) ∧
    -Real.log (2789 / 102400) ≤ (3603203607 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 5989)) (n := 12)
    (lo := (137467701 / 1000000000)) (hi := (68733851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2789) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2789) = 1/(2789 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3603203607 / 1000000000) (-3603203601 / 1000000000) (Real.log (2789 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33967069 / 50000000) ≤ -Real.log (12800 / 25249) ∧
    -Real.log (12800 / 25249) ≤ (679341381 / 1000000000) := by
  have h := checkLog_sound (w := (12449 / 38049)) (n := 12)
    (lo := (33967069 / 50000000)) (hi := (679341381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25249 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25249 / 12800) = 1/(12800 / 25249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33967069 / 50000000) (679341381 / 1000000000) (Real.log (25249 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25249 / 12800) = -Real.log (12800 / 25249) := by
    rw [show ((25249 / 12800) : ℝ) = ((12800 / 25249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3596414223 / 1000000000) ≤ -Real.log (351 / 12800) ∧
    -Real.log (351 / 12800) ≤ (3596414229 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 751)) (n := 12)
    (lo := (130678323 / 1000000000)) (hi := (32669581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 351) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 351) = 1/(351 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3596414229 / 1000000000) (-3596414223 / 1000000000) (Real.log (351 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (166383267 / 250000000) ≤ -Real.log (51200 / 99611) ∧
    -Real.log (51200 / 99611) ≤ (665533069 / 1000000000) := by
  have h := checkLog_sound (w := (48411 / 150811)) (n := 12)
    (lo := (166383267 / 250000000)) (hi := (665533069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99611 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99611 / 51200) = 1/(51200 / 99611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (166383267 / 250000000) (665533069 / 1000000000) (Real.log (99611 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99611 / 51200) = -Real.log (51200 / 99611) := by
    rw [show ((99611 / 51200) : ℝ) = ((51200 / 99611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2910056421 / 1000000000) ≤ -Real.log (2789 / 51200) ∧
    -Real.log (2789 / 51200) ≤ (1455028213 / 500000000) := by
  have h := checkLog_sound (w := (411 / 5989)) (n := 12)
    (lo := (137467701 / 1000000000)) (hi := (68733851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2789) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2789) = 1/(2789 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1455028213 / 500000000) (-2910056421 / 1000000000) (Real.log (2789 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (166335577 / 250000000) ≤ -Real.log (6400 / 12449) ∧
    -Real.log (6400 / 12449) ≤ (665342309 / 1000000000) := by
  have h := checkLog_sound (w := (6049 / 18849)) (n := 12)
    (lo := (166335577 / 250000000)) (hi := (665342309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12449 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12449 / 6400) = 1/(6400 / 12449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (166335577 / 250000000) (665342309 / 1000000000) (Real.log (12449 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12449 / 6400) = -Real.log (6400 / 12449) := by
    rw [show ((12449 / 6400) : ℝ) = ((6400 / 12449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2903267043 / 1000000000) ≤ -Real.log (351 / 6400) ∧
    -Real.log (351 / 6400) ≤ (362908381 / 125000000) := by
  have h := checkLog_sound (w := (49 / 751)) (n := 12)
    (lo := (130678323 / 1000000000)) (hi := (32669581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 351) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 351) = 1/(351 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-362908381 / 125000000) (-2903267043 / 1000000000) (Real.log (351 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (681569921 / 1000000000) ≤ -Real.log (1000000 / 1976979) ∧
    -Real.log (1000000 / 1976979) ≤ (340784961 / 500000000) := by
  have h := checkLog_sound (w := (976979 / 2976979)) (n := 12)
    (lo := (681569921 / 1000000000)) (hi := (340784961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976979 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976979 / 1000000) = 1/(1000000 / 1976979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (681569921 / 1000000000) (340784961 / 500000000) (Real.log (1976979 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1976979 / 1000000) = -Real.log (1000000 / 1976979) := by
    rw [show ((1976979 / 1000000) : ℝ) = ((1000000 / 1976979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3771348433 / 1000000000) ≤ -Real.log (23021 / 1000000) ∧
    -Real.log (23021 / 1000000) ≤ (3771348439 / 1000000000) := by
  have h := checkLog_sound (w := (8229 / 54271)) (n := 12)
    (lo := (305612533 / 1000000000)) (hi := (152806267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23021) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23021) = 1/(23021 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3771348439 / 1000000000) (-3771348433 / 1000000000) (Real.log (23021 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (21301431 / 31250000) ≤ -Real.log (1000000 / 1977129) ∧
    -Real.log (1000000 / 1977129) ≤ (681645793 / 1000000000) := by
  have h := checkLog_sound (w := (977129 / 2977129)) (n := 12)
    (lo := (21301431 / 31250000)) (hi := (681645793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977129 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977129 / 1000000) = 1/(1000000 / 1977129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (21301431 / 31250000) (681645793 / 1000000000) (Real.log (1977129 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1977129 / 1000000) = -Real.log (1000000 / 1977129) := by
    rw [show ((1977129 / 1000000) : ℝ) = ((1000000 / 1977129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3777885543 / 1000000000) ≤ -Real.log (22871 / 1000000) ∧
    -Real.log (22871 / 1000000) ≤ (3777885549 / 1000000000) := by
  have h := checkLog_sound (w := (8379 / 54121)) (n := 12)
    (lo := (312149643 / 1000000000)) (hi := (78037411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22871) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22871) = 1/(22871 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3777885549 / 1000000000) (-3777885543 / 1000000000) (Real.log (22871 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (340753599 / 500000000) ≤ -Real.log (200000 / 395371) ∧
    -Real.log (200000 / 395371) ≤ (681507199 / 1000000000) := by
  have h := checkLog_sound (w := (195371 / 595371)) (n := 12)
    (lo := (340753599 / 500000000)) (hi := (681507199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395371 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395371 / 200000) = 1/(200000 / 395371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (340753599 / 500000000) (681507199 / 1000000000) (Real.log (395371 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (395371 / 200000) = -Real.log (200000 / 395371) := by
    rw [show ((395371 / 200000) : ℝ) = ((200000 / 395371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3765976501 / 1000000000) ≤ -Real.log (4629 / 200000) ∧
    -Real.log (4629 / 200000) ≤ (3765976507 / 1000000000) := by
  have h := checkLog_sound (w := (1621 / 10879)) (n := 12)
    (lo := (300240601 / 1000000000)) (hi := (150120301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4629) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4629) = 1/(4629 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3765976507 / 1000000000) (-3765976501 / 1000000000) (Real.log (4629 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681583579 / 1000000000) ≤ -Real.log (500000 / 988503) ∧
    -Real.log (500000 / 988503) ≤ (34079179 / 50000000) := by
  have h := checkLog_sound (w := (488503 / 1488503)) (n := 12)
    (lo := (681583579 / 1000000000)) (hi := (34079179 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988503 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988503 / 500000) = 1/(500000 / 988503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681583579 / 1000000000) (34079179 / 50000000) (Real.log (988503 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (988503 / 500000) = -Real.log (500000 / 988503) := by
    rw [show ((988503 / 500000) : ℝ) = ((500000 / 988503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3772521963 / 1000000000) ≤ -Real.log (11497 / 500000) ∧
    -Real.log (11497 / 500000) ≤ (3772521969 / 1000000000) := by
  have h := checkLog_sound (w := (2064 / 13561)) (n := 12)
    (lo := (306786063 / 1000000000)) (hi := (19174129 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11497) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11497) = 1/(11497 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3772521969 / 1000000000) (-3772521963 / 1000000000) (Real.log (11497 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2226459177 / 500000000) ≤ -Real.log (10000000000 / 858771990791) ∧
    -Real.log (10000000000 / 858771990791) ≤ (4452918361 / 1000000000) := by
  have h := checkLog_sound (w := (218771990791 / 1498771990791)) (n := 12)
    (lo := (147017637 / 500000000)) (hi := (11761411 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858771990791 / 640000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(858771990791 / 640000000000) = 1/(10000000000 / 858771990791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2226459177 / 500000000) (4452918361 / 1000000000) (Real.log (858771990791 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (858771990791 / 10000000000) = -Real.log (10000000000 / 858771990791) := by
    rw [show ((858771990791 / 10000000000) : ℝ) = ((10000000000 / 858771990791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (891906267 / 200000000) ≤ -Real.log (31250000000 / 2701468289537) ∧
    -Real.log (31250000000 / 2701468289537) ≤ (2229765671 / 500000000) := by
  have h := checkLog_sound (w := (701468289537 / 4701468289537)) (n := 12)
    (lo := (60129651 / 200000000)) (hi := (4697629 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2701468289537 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2701468289537 / 2000000000000) = 1/(31250000000 / 2701468289537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (891906267 / 200000000) (2229765671 / 500000000) (Real.log (2701468289537 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2701468289537 / 31250000000) = -Real.log (31250000000 / 2701468289537) := by
    rw [show ((2701468289537 / 31250000000) : ℝ) = ((31250000000 / 2701468289537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4447483699 / 1000000000) ≤ -Real.log (100000000000 / 8541175199827) ∧
    -Real.log (100000000000 / 8541175199827) ≤ (2223741853 / 500000000) := by
  have h := checkLog_sound (w := (2141175199827 / 14941175199827)) (n := 12)
    (lo := (288600619 / 1000000000)) (hi := (14430031 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8541175199827 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8541175199827 / 6400000000000) = 1/(100000000000 / 8541175199827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4447483699 / 1000000000) (2223741853 / 500000000) (Real.log (8541175199827 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8541175199827 / 100000000000) = -Real.log (100000000000 / 8541175199827) := by
    rw [show ((8541175199827 / 100000000000) : ℝ) = ((100000000000 / 8541175199827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2227052771 / 500000000) ≤ -Real.log (50000000000 / 4298960598417) ∧
    -Real.log (50000000000 / 4298960598417) ≤ (4454105549 / 1000000000) := by
  have h := checkLog_sound (w := (1098960598417 / 7498960598417)) (n := 12)
    (lo := (147611231 / 500000000)) (hi := (295222463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4298960598417 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4298960598417 / 3200000000000) = 1/(50000000000 / 4298960598417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2227052771 / 500000000) (4454105549 / 1000000000) (Real.log (4298960598417 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4298960598417 / 50000000000) = -Real.log (50000000000 / 4298960598417) := by
    rw [show ((4298960598417 / 50000000000) : ℝ) = ((50000000000 / 4298960598417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0046

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0047Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0047
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

theorem reflection_log_1_neg : (33967069 / 50000000) ≤ -Real.log (12800 / 25249) ∧
    -Real.log (12800 / 25249) ≤ (679341381 / 1000000000) := by
  have h := checkLog_sound (w := (12449 / 38049)) (n := 12)
    (lo := (33967069 / 50000000)) (hi := (679341381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25249 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25249 / 12800) = 1/(12800 / 25249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33967069 / 50000000) (679341381 / 1000000000) (Real.log (25249 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25249 / 12800) = -Real.log (12800 / 25249) := by
    rw [show ((25249 / 12800) : ℝ) = ((12800 / 25249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3596414223 / 1000000000) ≤ -Real.log (351 / 12800) ∧
    -Real.log (351 / 12800) ≤ (3596414229 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 751)) (n := 12)
    (lo := (130678323 / 1000000000)) (hi := (32669581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 351) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 351) = 1/(351 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3596414229 / 1000000000) (-3596414223 / 1000000000) (Real.log (351 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42452957 / 62500000) ≤ -Real.log (102400 / 201973) ∧
    -Real.log (102400 / 201973) ≤ (679247313 / 1000000000) := by
  have h := checkLog_sound (w := (99573 / 304373)) (n := 12)
    (lo := (42452957 / 62500000)) (hi := (679247313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201973 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201973 / 102400) = 1/(102400 / 201973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42452957 / 62500000) (679247313 / 1000000000) (Real.log (201973 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201973 / 102400) = -Real.log (102400 / 201973) := by
    rw [show ((201973 / 102400) : ℝ) = ((102400 / 201973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3589670631 / 1000000000) ≤ -Real.log (2827 / 102400) ∧
    -Real.log (2827 / 102400) ≤ (3589670637 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 6027)) (n := 12)
    (lo := (123934731 / 1000000000)) (hi := (30983683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2827) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2827) = 1/(2827 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3589670637 / 1000000000) (-3589670631 / 1000000000) (Real.log (2827 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (166335577 / 250000000) ≤ -Real.log (6400 / 12449) ∧
    -Real.log (6400 / 12449) ≤ (665342309 / 1000000000) := by
  have h := checkLog_sound (w := (6049 / 18849)) (n := 12)
    (lo := (166335577 / 250000000)) (hi := (665342309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12449 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12449 / 6400) = 1/(6400 / 12449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (166335577 / 250000000) (665342309 / 1000000000) (Real.log (12449 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12449 / 6400) = -Real.log (6400 / 12449) := by
    rw [show ((12449 / 6400) : ℝ) = ((6400 / 12449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2903267043 / 1000000000) ≤ -Real.log (351 / 6400) ∧
    -Real.log (351 / 6400) ≤ (362908381 / 125000000) := by
  have h := checkLog_sound (w := (49 / 751)) (n := 12)
    (lo := (130678323 / 1000000000)) (hi := (32669581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 351) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 351) = 1/(351 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-362908381 / 125000000) (-2903267043 / 1000000000) (Real.log (351 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (665151511 / 1000000000) ≤ -Real.log (51200 / 99573) ∧
    -Real.log (51200 / 99573) ≤ (83143939 / 125000000) := by
  have h := checkLog_sound (w := (48373 / 150773)) (n := 12)
    (lo := (665151511 / 1000000000)) (hi := (83143939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99573 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99573 / 51200) = 1/(51200 / 99573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (665151511 / 1000000000) (83143939 / 125000000) (Real.log (99573 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99573 / 51200) = -Real.log (51200 / 99573) := by
    rw [show ((99573 / 51200) : ℝ) = ((51200 / 99573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2896523451 / 1000000000) ≤ -Real.log (2827 / 51200) ∧
    -Real.log (2827 / 51200) ≤ (45258179 / 15625000) := by
  have h := checkLog_sound (w := (373 / 6027)) (n := 12)
    (lo := (123934731 / 1000000000)) (hi := (30983683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2827) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2827) = 1/(2827 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-45258179 / 15625000) (-2896523451 / 1000000000) (Real.log (2827 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (681494551 / 1000000000) ≤ -Real.log (100000 / 197683) ∧
    -Real.log (100000 / 197683) ≤ (85186819 / 125000000) := by
  have h := checkLog_sound (w := (97683 / 297683)) (n := 12)
    (lo := (681494551 / 1000000000)) (hi := (85186819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197683 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197683 / 100000) = 1/(100000 / 197683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (681494551 / 1000000000) (85186819 / 125000000) (Real.log (197683 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (197683 / 100000) = -Real.log (100000 / 197683) := by
    rw [show ((197683 / 100000) : ℝ) = ((100000 / 197683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3764896937 / 1000000000) ≤ -Real.log (2317 / 100000) ∧
    -Real.log (2317 / 100000) ≤ (3764896943 / 1000000000) := by
  have h := checkLog_sound (w := (404 / 2721)) (n := 12)
    (lo := (299161037 / 1000000000)) (hi := (149580519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2317) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2317) = 1/(2317 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3764896943 / 1000000000) (-3764896937 / 1000000000) (Real.log (2317 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (681570427 / 1000000000) ≤ -Real.log (50000 / 98849) ∧
    -Real.log (50000 / 98849) ≤ (170392607 / 250000000) := by
  have h := checkLog_sound (w := (48849 / 148849)) (n := 12)
    (lo := (681570427 / 1000000000)) (hi := (170392607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98849 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98849 / 50000) = 1/(50000 / 98849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (681570427 / 1000000000) (170392607 / 250000000) (Real.log (98849 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (98849 / 50000) = -Real.log (50000 / 98849) := by
    rw [show ((98849 / 50000) : ℝ) = ((50000 / 98849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (29463999 / 7812500) ≤ -Real.log (1151 / 50000) ∧
    -Real.log (1151 / 50000) ≤ (1885695939 / 500000000) := by
  have h := checkLog_sound (w := (823 / 5427)) (n := 12)
    (lo := (76413993 / 250000000)) (hi := (305655973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2302) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2302) = 1/(1151 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1885695939 / 500000000) (-29463999 / 7812500) (Real.log (1151 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681430811 / 1000000000) ≤ -Real.log (15625 / 30886) ∧
    -Real.log (15625 / 30886) ≤ (170357703 / 250000000) := by
  have h := checkLog_sound (w := (15261 / 46511)) (n := 12)
    (lo := (681430811 / 1000000000)) (hi := (170357703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30886 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30886 / 15625) = 1/(15625 / 30886) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681430811 / 1000000000) (170357703 / 250000000) (Real.log (30886 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (30886 / 15625) = -Real.log (15625 / 30886) := by
    rw [show ((30886 / 15625) : ℝ) = ((15625 / 30886) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (939868401 / 250000000) ≤ -Real.log (364 / 15625) ∧
    -Real.log (364 / 15625) ≤ (375947361 / 100000000) := by
  have h := checkLog_sound (w := (3977 / 27273)) (n := 12)
    (lo := (36717213 / 125000000)) (hi := (58747541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11648) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11648) = 1/(364 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-375947361 / 100000000) (-939868401 / 250000000) (Real.log (364 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681507703 / 1000000000) ≤ -Real.log (125000 / 247107) ∧
    -Real.log (125000 / 247107) ≤ (85188463 / 125000000) := by
  have h := checkLog_sound (w := (122107 / 372107)) (n := 12)
    (lo := (681507703 / 1000000000)) (hi := (85188463 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247107 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247107 / 125000) = 1/(125000 / 247107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681507703 / 1000000000) (85188463 / 125000000) (Real.log (247107 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (247107 / 125000) = -Real.log (125000 / 247107) := by
    rw [show ((247107 / 125000) : ℝ) = ((125000 / 247107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (941504927 / 250000000) ≤ -Real.log (2893 / 125000) ∧
    -Real.log (2893 / 125000) ≤ (1883009857 / 500000000) := by
  have h := checkLog_sound (w := (4053 / 27197)) (n := 12)
    (lo := (9383869 / 31250000)) (hi := (300283809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11572) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11572) = 1/(2893 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1883009857 / 500000000) (-941504927 / 250000000) (Real.log (2893 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (69474867 / 15625000) ≤ -Real.log (15625000000 / 1333101801899) ∧
    -Real.log (15625000000 / 1333101801899) ≤ (889278299 / 200000000) := by
  have h := checkLog_sound (w := (333101801899 / 2333101801899)) (n := 12)
    (lo := (35938551 / 125000000)) (hi := (287508409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333101801899 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1333101801899 / 1000000000000) = 1/(15625000000 / 1333101801899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (69474867 / 15625000) (889278299 / 200000000) (Real.log (1333101801899 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1333101801899 / 15625000000) = -Real.log (15625000000 / 1333101801899) := by
    rw [show ((1333101801899 / 15625000000) : ℝ) = ((15625000000 / 1333101801899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (44529623 / 10000000) ≤ -Real.log (10000000000 / 858809730669) ∧
    -Real.log (10000000000 / 858809730669) ≤ (4452962307 / 1000000000) := by
  have h := checkLog_sound (w := (218809730669 / 1498809730669)) (n := 12)
    (lo := (14703961 / 50000000)) (hi := (294079221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858809730669 / 640000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(858809730669 / 640000000000) = 1/(10000000000 / 858809730669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (44529623 / 10000000) (4452962307 / 1000000000) (Real.log (858809730669 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (858809730669 / 10000000000) = -Real.log (10000000000 / 858809730669) := by
    rw [show ((858809730669 / 10000000000) : ℝ) = ((10000000000 / 858809730669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2220452207 / 500000000) ≤ -Real.log (31250000000 / 2651614010989) ∧
    -Real.log (31250000000 / 2651614010989) ≤ (4440904421 / 1000000000) := by
  have h := checkLog_sound (w := (651614010989 / 4651614010989)) (n := 12)
    (lo := (141010667 / 500000000)) (hi := (56404267 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2651614010989 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2651614010989 / 2000000000000) = 1/(31250000000 / 2651614010989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2220452207 / 500000000) (4440904421 / 1000000000) (Real.log (2651614010989 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2651614010989 / 31250000000) = -Real.log (31250000000 / 2651614010989) := by
    rw [show ((2651614010989 / 31250000000) : ℝ) = ((31250000000 / 2651614010989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4447527411 / 1000000000) ≤ -Real.log (100000000000 / 8541548565503) ∧
    -Real.log (100000000000 / 8541548565503) ≤ (2223763709 / 500000000) := by
  have h := checkLog_sound (w := (2141548565503 / 14941548565503)) (n := 12)
    (lo := (288644331 / 1000000000)) (hi := (72161083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8541548565503 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8541548565503 / 6400000000000) = 1/(100000000000 / 8541548565503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4447527411 / 1000000000) (2223763709 / 500000000) (Real.log (8541548565503 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8541548565503 / 100000000000) = -Real.log (100000000000 / 8541548565503) := by
    rw [show ((8541548565503 / 100000000000) : ℝ) = ((100000000000 / 8541548565503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0047

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0048Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0048
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

theorem reflection_log_1_neg : (42452957 / 62500000) ≤ -Real.log (102400 / 201973) ∧
    -Real.log (102400 / 201973) ≤ (679247313 / 1000000000) := by
  have h := checkLog_sound (w := (99573 / 304373)) (n := 12)
    (lo := (42452957 / 62500000)) (hi := (679247313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201973 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201973 / 102400) = 1/(102400 / 201973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42452957 / 62500000) (679247313 / 1000000000) (Real.log (201973 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201973 / 102400) = -Real.log (102400 / 201973) := by
    rw [show ((201973 / 102400) : ℝ) = ((102400 / 201973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3589670631 / 1000000000) ≤ -Real.log (2827 / 102400) ∧
    -Real.log (2827 / 102400) ≤ (3589670637 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 6027)) (n := 12)
    (lo := (123934731 / 1000000000)) (hi := (30983683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2827) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2827) = 1/(2827 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3589670637 / 1000000000) (-3589670631 / 1000000000) (Real.log (2827 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (169788309 / 250000000) ≤ -Real.log (51200 / 100977) ∧
    -Real.log (51200 / 100977) ≤ (679153237 / 1000000000) := by
  have h := checkLog_sound (w := (49777 / 152177)) (n := 12)
    (lo := (169788309 / 250000000)) (hi := (679153237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100977 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100977 / 51200) = 1/(51200 / 100977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (169788309 / 250000000) (679153237 / 1000000000) (Real.log (100977 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100977 / 51200) = -Real.log (51200 / 100977) := by
    rw [show ((100977 / 51200) : ℝ) = ((51200 / 100977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (358297221 / 100000000) ≤ -Real.log (1423 / 51200) ∧
    -Real.log (1423 / 51200) ≤ (447871527 / 125000000) := by
  have h := checkLog_sound (w := (177 / 3023)) (n := 12)
    (lo := (11723631 / 100000000)) (hi := (117236311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1423) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1423) = 1/(1423 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-447871527 / 125000000) (-358297221 / 100000000) (Real.log (1423 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (665151511 / 1000000000) ≤ -Real.log (51200 / 99573) ∧
    -Real.log (51200 / 99573) ≤ (83143939 / 125000000) := by
  have h := checkLog_sound (w := (48373 / 150773)) (n := 12)
    (lo := (665151511 / 1000000000)) (hi := (83143939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99573 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99573 / 51200) = 1/(51200 / 99573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (665151511 / 1000000000) (83143939 / 125000000) (Real.log (99573 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99573 / 51200) = -Real.log (51200 / 99573) := by
    rw [show ((99573 / 51200) : ℝ) = ((51200 / 99573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2896523451 / 1000000000) ≤ -Real.log (2827 / 51200) ∧
    -Real.log (2827 / 51200) ≤ (45258179 / 15625000) := by
  have h := checkLog_sound (w := (373 / 6027)) (n := 12)
    (lo := (123934731 / 1000000000)) (hi := (30983683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2827) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2827) = 1/(2827 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-45258179 / 15625000) (-2896523451 / 1000000000) (Real.log (2827 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (332480339 / 500000000) ≤ -Real.log (25600 / 49777) ∧
    -Real.log (25600 / 49777) ≤ (664960679 / 1000000000) := by
  have h := checkLog_sound (w := (24177 / 75377)) (n := 12)
    (lo := (332480339 / 500000000)) (hi := (664960679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49777 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49777 / 25600) = 1/(25600 / 49777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (332480339 / 500000000) (664960679 / 1000000000) (Real.log (49777 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49777 / 25600) = -Real.log (25600 / 49777) := by
    rw [show ((49777 / 25600) : ℝ) = ((25600 / 49777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (288982503 / 100000000) ≤ -Real.log (1423 / 25600) ∧
    -Real.log (1423 / 25600) ≤ (577965007 / 200000000) := by
  have h := checkLog_sound (w := (177 / 3023)) (n := 12)
    (lo := (11723631 / 100000000)) (hi := (117236311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1423) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1423) = 1/(1423 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-577965007 / 200000000) (-288982503 / 100000000) (Real.log (1423 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (681419681 / 1000000000) ≤ -Real.log (500000 / 988341) ∧
    -Real.log (500000 / 988341) ≤ (340709841 / 500000000) := by
  have h := checkLog_sound (w := (488341 / 1488341)) (n := 12)
    (lo := (681419681 / 1000000000)) (hi := (340709841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988341 / 500000) = 1/(500000 / 988341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (681419681 / 1000000000) (340709841 / 500000000) (Real.log (988341 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (988341 / 500000) = -Real.log (500000 / 988341) := by
    rw [show ((988341 / 500000) : ℝ) = ((500000 / 988341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3758529681 / 1000000000) ≤ -Real.log (11659 / 500000) ∧
    -Real.log (11659 / 500000) ≤ (3758529687 / 1000000000) := by
  have h := checkLog_sound (w := (1983 / 13642)) (n := 12)
    (lo := (292793781 / 1000000000)) (hi := (146396891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11659) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11659) = 1/(11659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3758529687 / 1000000000) (-3758529681 / 1000000000) (Real.log (11659 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (681495057 / 1000000000) ≤ -Real.log (1000000 / 1976831) ∧
    -Real.log (1000000 / 1976831) ≤ (340747529 / 500000000) := by
  have h := checkLog_sound (w := (976831 / 2976831)) (n := 12)
    (lo := (681495057 / 1000000000)) (hi := (340747529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976831 / 1000000) = 1/(1000000 / 1976831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (681495057 / 1000000000) (340747529 / 500000000) (Real.log (1976831 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1976831 / 1000000) = -Real.log (1000000 / 1976831) := by
    rw [show ((1976831 / 1000000) : ℝ) = ((1000000 / 1976831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3764940097 / 1000000000) ≤ -Real.log (23169 / 1000000) ∧
    -Real.log (23169 / 1000000) ≤ (3764940103 / 1000000000) := by
  have h := checkLog_sound (w := (8081 / 54419)) (n := 12)
    (lo := (299204197 / 1000000000)) (hi := (149602099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23169) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23169) = 1/(23169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3764940103 / 1000000000) (-3764940097 / 1000000000) (Real.log (23169 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (170338731 / 250000000) ≤ -Real.log (500000 / 988277) ∧
    -Real.log (500000 / 988277) ≤ (27254197 / 40000000) := by
  have h := checkLog_sound (w := (488277 / 1488277)) (n := 12)
    (lo := (170338731 / 250000000)) (hi := (27254197 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988277 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988277 / 500000) = 1/(500000 / 988277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (170338731 / 250000000) (27254197 / 40000000) (Real.log (988277 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (988277 / 500000) = -Real.log (500000 / 988277) := by
    rw [show ((988277 / 500000) : ℝ) = ((500000 / 988277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3753055371 / 1000000000) ≤ -Real.log (11723 / 500000) ∧
    -Real.log (11723 / 500000) ≤ (3753055377 / 1000000000) := by
  have h := checkLog_sound (w := (1951 / 13674)) (n := 12)
    (lo := (287319471 / 1000000000)) (hi := (17957467 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11723) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11723) = 1/(11723 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3753055377 / 1000000000) (-3753055371 / 1000000000) (Real.log (11723 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681431317 / 1000000000) ≤ -Real.log (200000 / 395341) ∧
    -Real.log (200000 / 395341) ≤ (340715659 / 500000000) := by
  have h := checkLog_sound (w := (195341 / 595341)) (n := 12)
    (lo := (681431317 / 1000000000)) (hi := (340715659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395341 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395341 / 200000) = 1/(200000 / 395341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681431317 / 1000000000) (340715659 / 500000000) (Real.log (395341 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (395341 / 200000) = -Real.log (200000 / 395341) := by
    rw [show ((395341 / 200000) : ℝ) = ((200000 / 395341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (375951653 / 100000000) ≤ -Real.log (4659 / 200000) ∧
    -Real.log (4659 / 200000) ≤ (469939567 / 125000000) := by
  have h := checkLog_sound (w := (1591 / 10909)) (n := 12)
    (lo := (29378063 / 100000000)) (hi := (293780631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4659) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4659) = 1/(4659 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-469939567 / 125000000) (-375951653 / 100000000) (Real.log (4659 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2219974681 / 500000000) ≤ -Real.log (500000000000 / 42385324641907) ∧
    -Real.log (500000000000 / 42385324641907) ≤ (4439949369 / 1000000000) := by
  have h := checkLog_sound (w := (10385324641907 / 74385324641907)) (n := 12)
    (lo := (140533141 / 500000000)) (hi := (281066283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42385324641907 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(42385324641907 / 32000000000000) = 1/(500000000000 / 42385324641907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2219974681 / 500000000) (4439949369 / 1000000000) (Real.log (42385324641907 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (42385324641907 / 500000000000) = -Real.log (500000000000 / 42385324641907) := by
    rw [show ((42385324641907 / 500000000000) : ℝ) = ((500000000000 / 42385324641907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2223217577 / 500000000) ≤ -Real.log (15625000000 / 1333160014459) ∧
    -Real.log (15625000000 / 1333160014459) ≤ (4446435161 / 1000000000) := by
  have h := checkLog_sound (w := (333160014459 / 2333160014459)) (n := 12)
    (lo := (143776037 / 500000000)) (hi := (11502083 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333160014459 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1333160014459 / 1000000000000) = 1/(15625000000 / 1333160014459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2223217577 / 500000000) (4446435161 / 1000000000) (Real.log (1333160014459 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1333160014459 / 15625000000) = -Real.log (15625000000 / 1333160014459) := by
    rw [show ((1333160014459 / 15625000000) : ℝ) = ((15625000000 / 1333160014459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (886882059 / 200000000) ≤ -Real.log (500000000000 / 42151198498677) ∧
    -Real.log (500000000000 / 42151198498677) ≤ (2217205151 / 500000000) := by
  have h := checkLog_sound (w := (10151198498677 / 74151198498677)) (n := 12)
    (lo := (55105443 / 200000000)) (hi := (17220451 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42151198498677 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(42151198498677 / 32000000000000) = 1/(500000000000 / 42151198498677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (886882059 / 200000000) (2217205151 / 500000000) (Real.log (42151198498677 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (42151198498677 / 500000000000) = -Real.log (500000000000 / 42151198498677) := by
    rw [show ((42151198498677 / 500000000000) : ℝ) = ((500000000000 / 42151198498677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4440947847 / 1000000000) ≤ -Real.log (250000000000 / 21213833440653) ∧
    -Real.log (250000000000 / 21213833440653) ≤ (2220473927 / 500000000) := by
  have h := checkLog_sound (w := (5213833440653 / 37213833440653)) (n := 12)
    (lo := (282064767 / 1000000000)) (hi := (2203631 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21213833440653 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21213833440653 / 16000000000000) = 1/(250000000000 / 21213833440653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4440947847 / 1000000000) (2220473927 / 500000000) (Real.log (21213833440653 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21213833440653 / 250000000000) = -Real.log (250000000000 / 21213833440653) := by
    rw [show ((21213833440653 / 250000000000) : ℝ) = ((250000000000 / 21213833440653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0048

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0049Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0049
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

theorem reflection_log_1_neg : (169788309 / 250000000) ≤ -Real.log (51200 / 100977) ∧
    -Real.log (51200 / 100977) ≤ (679153237 / 1000000000) := by
  have h := checkLog_sound (w := (49777 / 152177)) (n := 12)
    (lo := (169788309 / 250000000)) (hi := (679153237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100977 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100977 / 51200) = 1/(51200 / 100977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (169788309 / 250000000) (679153237 / 1000000000) (Real.log (100977 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100977 / 51200) = -Real.log (51200 / 100977) := by
    rw [show ((100977 / 51200) : ℝ) = ((51200 / 100977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (358297221 / 100000000) ≤ -Real.log (1423 / 51200) ∧
    -Real.log (1423 / 51200) ≤ (447871527 / 125000000) := by
  have h := checkLog_sound (w := (177 / 3023)) (n := 12)
    (lo := (11723631 / 100000000)) (hi := (117236311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1423) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1423) = 1/(1423 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-447871527 / 125000000) (-358297221 / 100000000) (Real.log (1423 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13581183 / 20000000) ≤ -Real.log (20480 / 40387) ∧
    -Real.log (20480 / 40387) ≤ (679059151 / 1000000000) := by
  have h := checkLog_sound (w := (19907 / 60867)) (n := 12)
    (lo := (13581183 / 20000000)) (hi := (679059151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40387 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40387 / 20480) = 1/(20480 / 40387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13581183 / 20000000) (679059151 / 1000000000) (Real.log (40387 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (40387 / 20480) = -Real.log (20480 / 40387) := by
    rw [show ((40387 / 20480) : ℝ) = ((20480 / 40387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3576318359 / 1000000000) ≤ -Real.log (573 / 20480) ∧
    -Real.log (573 / 20480) ≤ (715263673 / 200000000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 573) = 1/(573 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-715263673 / 200000000) (-3576318359 / 1000000000) (Real.log (573 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (332480339 / 500000000) ≤ -Real.log (25600 / 49777) ∧
    -Real.log (25600 / 49777) ≤ (664960679 / 1000000000) := by
  have h := checkLog_sound (w := (24177 / 75377)) (n := 12)
    (lo := (332480339 / 500000000)) (hi := (664960679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49777 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49777 / 25600) = 1/(25600 / 49777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (332480339 / 500000000) (664960679 / 1000000000) (Real.log (49777 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49777 / 25600) = -Real.log (25600 / 49777) := by
    rw [show ((49777 / 25600) : ℝ) = ((25600 / 49777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (288982503 / 100000000) ≤ -Real.log (1423 / 25600) ∧
    -Real.log (1423 / 25600) ≤ (577965007 / 200000000) := by
  have h := checkLog_sound (w := (177 / 3023)) (n := 12)
    (lo := (11723631 / 100000000)) (hi := (117236311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1423) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1423) = 1/(1423 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-577965007 / 200000000) (-288982503 / 100000000) (Real.log (1423 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (664769809 / 1000000000) ≤ -Real.log (10240 / 19907) ∧
    -Real.log (10240 / 19907) ≤ (66476981 / 100000000) := by
  have h := checkLog_sound (w := (9667 / 30147)) (n := 12)
    (lo := (664769809 / 1000000000)) (hi := (66476981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19907 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19907 / 10240) = 1/(10240 / 19907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (664769809 / 1000000000) (66476981 / 100000000) (Real.log (19907 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (19907 / 10240) = -Real.log (10240 / 19907) := by
    rw [show ((19907 / 10240) : ℝ) = ((10240 / 19907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2883171179 / 1000000000) ≤ -Real.log (573 / 10240) ∧
    -Real.log (573 / 10240) ≤ (180198199 / 62500000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 573) = 1/(573 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-180198199 / 62500000) (-2883171179 / 1000000000) (Real.log (573 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (681344299 / 1000000000) ≤ -Real.log (1000000 / 1976533) ∧
    -Real.log (1000000 / 1976533) ≤ (6813443 / 10000000) := by
  have h := checkLog_sound (w := (976533 / 2976533)) (n := 12)
    (lo := (681344299 / 1000000000)) (hi := (6813443 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976533 / 1000000) = 1/(1000000 / 1976533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (681344299 / 1000000000) (6813443 / 10000000) (Real.log (1976533 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1976533 / 1000000) = -Real.log (1000000 / 1976533) := by
    rw [show ((1976533 / 1000000) : ℝ) = ((1000000 / 1976533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3752160097 / 1000000000) ≤ -Real.log (23467 / 1000000) ∧
    -Real.log (23467 / 1000000) ≤ (3752160103 / 1000000000) := by
  have h := checkLog_sound (w := (7783 / 54717)) (n := 12)
    (lo := (286424197 / 1000000000)) (hi := (143212099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23467) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23467) = 1/(23467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3752160103 / 1000000000) (-3752160097 / 1000000000) (Real.log (23467 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (681420187 / 1000000000) ≤ -Real.log (1000000 / 1976683) ∧
    -Real.log (1000000 / 1976683) ≤ (170355047 / 250000000) := by
  have h := checkLog_sound (w := (976683 / 2976683)) (n := 12)
    (lo := (681420187 / 1000000000)) (hi := (170355047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976683 / 1000000) = 1/(1000000 / 1976683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (681420187 / 1000000000) (170355047 / 250000000) (Real.log (1976683 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1976683 / 1000000) = -Real.log (1000000 / 1976683) := by
    rw [show ((1976683 / 1000000) : ℝ) = ((1000000 / 1976683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3758572567 / 1000000000) ≤ -Real.log (23317 / 1000000) ∧
    -Real.log (23317 / 1000000) ≤ (3758572573 / 1000000000) := by
  have h := checkLog_sound (w := (7933 / 54567)) (n := 12)
    (lo := (292836667 / 1000000000)) (hi := (73209167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23317) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23317) = 1/(23317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3758572573 / 1000000000) (-3758572567 / 1000000000) (Real.log (23317 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (27251141 / 40000000) ≤ -Real.log (1000000 / 1976403) ∧
    -Real.log (1000000 / 1976403) ≤ (340639263 / 500000000) := by
  have h := checkLog_sound (w := (976403 / 2976403)) (n := 12)
    (lo := (27251141 / 40000000)) (hi := (340639263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976403 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976403 / 1000000) = 1/(1000000 / 1976403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (27251141 / 40000000) (340639263 / 500000000) (Real.log (1976403 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1976403 / 1000000) = -Real.log (1000000 / 1976403) := by
    rw [show ((1976403 / 1000000) : ℝ) = ((1000000 / 1976403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (374663569 / 100000000) ≤ -Real.log (23597 / 1000000) ∧
    -Real.log (23597 / 1000000) ≤ (234164731 / 62500000) := by
  have h := checkLog_sound (w := (7653 / 54847)) (n := 12)
    (lo := (28089979 / 100000000)) (hi := (280899791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23597) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23597) = 1/(23597 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-234164731 / 62500000) (-374663569 / 100000000) (Real.log (23597 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (68135543 / 100000000) ≤ -Real.log (200000 / 395311) ∧
    -Real.log (200000 / 395311) ≤ (681355431 / 1000000000) := by
  have h := checkLog_sound (w := (195311 / 595311)) (n := 12)
    (lo := (68135543 / 100000000)) (hi := (681355431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395311 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395311 / 200000) = 1/(200000 / 395311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (68135543 / 100000000) (681355431 / 1000000000) (Real.log (395311 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (395311 / 200000) = -Real.log (200000 / 395311) := by
    rw [show ((395311 / 200000) : ℝ) = ((200000 / 395311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3753098023 / 1000000000) ≤ -Real.log (4689 / 200000) ∧
    -Real.log (4689 / 200000) ≤ (3753098029 / 1000000000) := by
  have h := checkLog_sound (w := (1561 / 10939)) (n := 12)
    (lo := (287362123 / 1000000000)) (hi := (71840531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4689) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4689) = 1/(4689 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3753098029 / 1000000000) (-3753098023 / 1000000000) (Real.log (4689 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1108376099 / 250000000) ≤ -Real.log (500000000000 / 42113031064899) ∧
    -Real.log (500000000000 / 42113031064899) ≤ (4433504403 / 1000000000) := by
  have h := checkLog_sound (w := (10113031064899 / 74113031064899)) (n := 12)
    (lo := (68655329 / 250000000)) (hi := (274621317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42113031064899 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(42113031064899 / 32000000000000) = 1/(500000000000 / 42113031064899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1108376099 / 250000000) (4433504403 / 1000000000) (Real.log (42113031064899 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (42113031064899 / 500000000000) = -Real.log (500000000000 / 42113031064899) := by
    rw [show ((42113031064899 / 500000000000) : ℝ) = ((500000000000 / 42113031064899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2219996377 / 500000000) ≤ -Real.log (250000000000 / 21193581935927) ∧
    -Real.log (250000000000 / 21193581935927) ≤ (4439992761 / 1000000000) := by
  have h := checkLog_sound (w := (5193581935927 / 37193581935927)) (n := 12)
    (lo := (140554837 / 500000000)) (hi := (11244387 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21193581935927 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21193581935927 / 16000000000000) = 1/(250000000000 / 21193581935927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2219996377 / 500000000) (4439992761 / 1000000000) (Real.log (21193581935927 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21193581935927 / 250000000000) = -Real.log (250000000000 / 21193581935927) := by
    rw [show ((21193581935927 / 250000000000) : ℝ) = ((250000000000 / 21193581935927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (553489277 / 125000000) ≤ -Real.log (31250000000 / 2617391776497) ∧
    -Real.log (31250000000 / 2617391776497) ≤ (4427914223 / 1000000000) := by
  have h := checkLog_sound (w := (617391776497 / 4617391776497)) (n := 12)
    (lo := (8407223 / 31250000)) (hi := (269031137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2617391776497 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2617391776497 / 2000000000000) = 1/(31250000000 / 2617391776497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (553489277 / 125000000) (4427914223 / 1000000000) (Real.log (2617391776497 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2617391776497 / 31250000000) = -Real.log (31250000000 / 2617391776497) := by
    rw [show ((2617391776497 / 31250000000) : ℝ) = ((31250000000 / 2617391776497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4434453453 / 1000000000) ≤ -Real.log (500000000000 / 42153017701003) ∧
    -Real.log (500000000000 / 42153017701003) ≤ (221722673 / 50000000) := by
  have h := checkLog_sound (w := (10153017701003 / 74153017701003)) (n := 12)
    (lo := (275570373 / 1000000000)) (hi := (137785187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42153017701003 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(42153017701003 / 32000000000000) = 1/(500000000000 / 42153017701003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4434453453 / 1000000000) (221722673 / 50000000) (Real.log (42153017701003 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (42153017701003 / 500000000000) = -Real.log (500000000000 / 42153017701003) := by
    rw [show ((42153017701003 / 500000000000) : ℝ) = ((500000000000 / 42153017701003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0049

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0050Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0050
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

theorem reflection_log_1_neg : (13581183 / 20000000) ≤ -Real.log (20480 / 40387) ∧
    -Real.log (20480 / 40387) ≤ (679059151 / 1000000000) := by
  have h := checkLog_sound (w := (19907 / 60867)) (n := 12)
    (lo := (13581183 / 20000000)) (hi := (679059151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40387 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40387 / 20480) = 1/(20480 / 40387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13581183 / 20000000) (679059151 / 1000000000) (Real.log (40387 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (40387 / 20480) = -Real.log (20480 / 40387) := by
    rw [show ((40387 / 20480) : ℝ) = ((20480 / 40387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3576318359 / 1000000000) ≤ -Real.log (573 / 20480) ∧
    -Real.log (573 / 20480) ≤ (715263673 / 200000000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 573) = 1/(573 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-715263673 / 200000000) (-3576318359 / 1000000000) (Real.log (573 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10608829 / 15625000) ≤ -Real.log (25600 / 50479) ∧
    -Real.log (25600 / 50479) ≤ (678965057 / 1000000000) := by
  have h := checkLog_sound (w := (24879 / 76079)) (n := 12)
    (lo := (10608829 / 15625000)) (hi := (678965057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50479 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50479 / 25600) = 1/(25600 / 50479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10608829 / 15625000) (678965057 / 1000000000) (Real.log (50479 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50479 / 25600) = -Real.log (25600 / 50479) := by
    rw [show ((50479 / 25600) : ℝ) = ((25600 / 50479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (356970849 / 100000000) ≤ -Real.log (721 / 25600) ∧
    -Real.log (721 / 25600) ≤ (223106781 / 62500000) := by
  have h := checkLog_sound (w := (79 / 1521)) (n := 12)
    (lo := (10397259 / 100000000)) (hi := (103972591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 721) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 721) = 1/(721 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-223106781 / 62500000) (-356970849 / 100000000) (Real.log (721 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (664769809 / 1000000000) ≤ -Real.log (10240 / 19907) ∧
    -Real.log (10240 / 19907) ≤ (66476981 / 100000000) := by
  have h := checkLog_sound (w := (9667 / 30147)) (n := 12)
    (lo := (664769809 / 1000000000)) (hi := (66476981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19907 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19907 / 10240) = 1/(10240 / 19907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (664769809 / 1000000000) (66476981 / 100000000) (Real.log (19907 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19907 / 10240) = -Real.log (10240 / 19907) := by
    rw [show ((19907 / 10240) : ℝ) = ((10240 / 19907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2883171179 / 1000000000) ≤ -Real.log (573 / 10240) ∧
    -Real.log (573 / 10240) ≤ (180198199 / 62500000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 573) = 1/(573 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-180198199 / 62500000) (-2883171179 / 1000000000) (Real.log (573 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (664578903 / 1000000000) ≤ -Real.log (12800 / 24879) ∧
    -Real.log (12800 / 24879) ≤ (83072363 / 125000000) := by
  have h := checkLog_sound (w := (12079 / 37679)) (n := 12)
    (lo := (664578903 / 1000000000)) (hi := (83072363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24879 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24879 / 12800) = 1/(12800 / 24879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (664578903 / 1000000000) (83072363 / 125000000) (Real.log (24879 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24879 / 12800) = -Real.log (12800 / 24879) := by
    rw [show ((24879 / 12800) : ℝ) = ((12800 / 24879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (287656131 / 100000000) ≤ -Real.log (721 / 12800) ∧
    -Real.log (721 / 12800) ≤ (575312263 / 200000000) := by
  have h := checkLog_sound (w := (79 / 1521)) (n := 12)
    (lo := (10397259 / 100000000)) (hi := (103972591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 721) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 721) = 1/(721 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-575312263 / 200000000) (-287656131 / 100000000) (Real.log (721 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340634709 / 500000000) ≤ -Real.log (200000 / 395277) ∧
    -Real.log (200000 / 395277) ≤ (681269419 / 1000000000) := by
  have h := checkLog_sound (w := (195277 / 595277)) (n := 12)
    (lo := (340634709 / 500000000)) (hi := (681269419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395277 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395277 / 200000) = 1/(200000 / 395277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340634709 / 500000000) (681269419 / 1000000000) (Real.log (395277 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (395277 / 200000) = -Real.log (200000 / 395277) := by
    rw [show ((395277 / 200000) : ℝ) = ((200000 / 395277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (936468293 / 250000000) ≤ -Real.log (4723 / 200000) ∧
    -Real.log (4723 / 200000) ≤ (1872936589 / 500000000) := by
  have h := checkLog_sound (w := (1527 / 10973)) (n := 12)
    (lo := (35017159 / 125000000)) (hi := (280137273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4723) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4723) = 1/(4723 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1872936589 / 500000000) (-936468293 / 250000000) (Real.log (4723 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136268961 / 200000000) ≤ -Real.log (500000 / 988267) ∧
    -Real.log (500000 / 988267) ≤ (340672403 / 500000000) := by
  have h := checkLog_sound (w := (488267 / 1488267)) (n := 12)
    (lo := (136268961 / 200000000)) (hi := (340672403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988267 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988267 / 500000) = 1/(500000 / 988267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136268961 / 200000000) (340672403 / 500000000) (Real.log (988267 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (988267 / 500000) = -Real.log (500000 / 988267) := by
    rw [show ((988267 / 500000) : ℝ) = ((500000 / 988267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3752202711 / 1000000000) ≤ -Real.log (11733 / 500000) ∧
    -Real.log (11733 / 500000) ≤ (3752202717 / 1000000000) := by
  have h := checkLog_sound (w := (1946 / 13679)) (n := 12)
    (lo := (286466811 / 1000000000)) (hi := (71616703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11733) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11733) = 1/(11733 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3752202717 / 1000000000) (-3752202711 / 1000000000) (Real.log (11733 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681202627 / 1000000000) ≤ -Real.log (1000000 / 1976253) ∧
    -Real.log (1000000 / 1976253) ≤ (170300657 / 250000000) := by
  have h := checkLog_sound (w := (976253 / 2976253)) (n := 12)
    (lo := (681202627 / 1000000000)) (hi := (170300657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976253 / 1000000) = 1/(1000000 / 1976253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681202627 / 1000000000) (170300657 / 250000000) (Real.log (1976253 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1976253 / 1000000) = -Real.log (1000000 / 1976253) := by
    rw [show ((1976253 / 1000000) : ℝ) = ((1000000 / 1976253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3740299069 / 1000000000) ≤ -Real.log (23747 / 1000000) ∧
    -Real.log (23747 / 1000000) ≤ (149611963 / 40000000) := by
  have h := checkLog_sound (w := (7503 / 54997)) (n := 12)
    (lo := (274563169 / 1000000000)) (hi := (27456317 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23747) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23747) = 1/(23747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-149611963 / 40000000) (-3740299069 / 1000000000) (Real.log (23747 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681279031 / 1000000000) ≤ -Real.log (250000 / 494101) ∧
    -Real.log (250000 / 494101) ≤ (85159879 / 125000000) := by
  have h := checkLog_sound (w := (244101 / 744101)) (n := 12)
    (lo := (681279031 / 1000000000)) (hi := (85159879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494101 / 250000) = 1/(250000 / 494101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681279031 / 1000000000) (85159879 / 125000000) (Real.log (494101 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (494101 / 250000) = -Real.log (250000 / 494101) := by
    rw [show ((494101 / 250000) : ℝ) = ((250000 / 494101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (374667807 / 100000000) ≤ -Real.log (5899 / 250000) ∧
    -Real.log (5899 / 250000) ≤ (936669519 / 250000000) := by
  have h := checkLog_sound (w := (3827 / 27423)) (n := 12)
    (lo := (28094217 / 100000000)) (hi := (280942171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11798) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11798) = 1/(5899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-936669519 / 250000000) (-374667807 / 100000000) (Real.log (5899 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (442714259 / 100000000) ≤ -Real.log (250000000000 / 20922983273343) ∧
    -Real.log (250000000000 / 20922983273343) ≤ (4427142597 / 1000000000) := by
  have h := checkLog_sound (w := (4922983273343 / 36922983273343)) (n := 12)
    (lo := (26825951 / 100000000)) (hi := (268259511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20922983273343 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20922983273343 / 16000000000000) = 1/(250000000000 / 20922983273343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (442714259 / 100000000) (4427142597 / 1000000000) (Real.log (20922983273343 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (20922983273343 / 250000000000) = -Real.log (250000000000 / 20922983273343) := by
    rw [show ((20922983273343 / 250000000000) : ℝ) = ((250000000000 / 20922983273343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1108386879 / 250000000) ≤ -Real.log (5000000000 / 421148470127) ∧
    -Real.log (5000000000 / 421148470127) ≤ (4433547523 / 1000000000) := by
  have h := checkLog_sound (w := (101148470127 / 741148470127)) (n := 12)
    (lo := (68666109 / 250000000)) (hi := (274664437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421148470127 / 320000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(421148470127 / 320000000000) = 1/(5000000000 / 421148470127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1108386879 / 250000000) (4433547523 / 1000000000) (Real.log (421148470127 / 5000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (421148470127 / 5000000000) = -Real.log (5000000000 / 421148470127) := by
    rw [show ((421148470127 / 5000000000) : ℝ) = ((5000000000 / 421148470127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17271491 / 3906250) ≤ -Real.log (250000000000 / 20805291194677) ∧
    -Real.log (250000000000 / 20805291194677) ≤ (4421501703 / 1000000000) := by
  have h := checkLog_sound (w := (4805291194677 / 36805291194677)) (n := 12)
    (lo := (32827327 / 125000000)) (hi := (262618617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20805291194677 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20805291194677 / 16000000000000) = 1/(250000000000 / 20805291194677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (17271491 / 3906250) (4421501703 / 1000000000) (Real.log (20805291194677 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (20805291194677 / 250000000000) = -Real.log (250000000000 / 20805291194677) := by
    rw [show ((20805291194677 / 250000000000) : ℝ) = ((250000000000 / 20805291194677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4427957101 / 1000000000) ≤ -Real.log (250000000000 / 20940032208849) ∧
    -Real.log (250000000000 / 20940032208849) ≤ (1106989277 / 250000000) := by
  have h := checkLog_sound (w := (4940032208849 / 36940032208849)) (n := 12)
    (lo := (269074021 / 1000000000)) (hi := (134537011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20940032208849 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20940032208849 / 16000000000000) = 1/(250000000000 / 20940032208849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4427957101 / 1000000000) (1106989277 / 250000000) (Real.log (20940032208849 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20940032208849 / 250000000000) = -Real.log (250000000000 / 20940032208849) := by
    rw [show ((20940032208849 / 250000000000) : ℝ) = ((250000000000 / 20940032208849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0050

end


