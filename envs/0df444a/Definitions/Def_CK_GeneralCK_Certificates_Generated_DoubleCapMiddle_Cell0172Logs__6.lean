-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0172Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0172Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:29:50.064763+00:00
-- url     : https://prove2.me/theorems/24eb600d-6b2a-47a3-ad4f-955f708a27a7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0172Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0173Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0172Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0173Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0174Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0175Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0176Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0177Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0172Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0173Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0174Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0175Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0176Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0177Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0172Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0173Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0174Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0175Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0176Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0177Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0172Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0173Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0174Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0175Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0176Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0177Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0172Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0172
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

theorem reflection_log_1_neg : (55632853 / 200000000) ≤ -Real.log (2560 / 3381) ∧
    -Real.log (2560 / 3381) ≤ (139082133 / 500000000) := by
  have h := checkLog_sound (w := (821 / 5941)) (n := 12)
    (lo := (55632853 / 200000000)) (hi := (139082133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3381 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3381 / 2560) = 1/(2560 / 3381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (55632853 / 200000000) (139082133 / 500000000) (Real.log (3381 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3381 / 2560) = -Real.log (2560 / 3381) := by
    rw [show ((3381 / 2560) : ℝ) = ((2560 / 3381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (386697023 / 1000000000) ≤ -Real.log (1739 / 2560) ∧
    -Real.log (1739 / 2560) ≤ (6042141 / 15625000) := by
  have h := checkLog_sound (w := (821 / 4299)) (n := 12)
    (lo := (386697023 / 1000000000)) (hi := (6042141 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1739) = 1/(1739 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6042141 / 15625000) (-386697023 / 1000000000) (Real.log (1739 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (277720511 / 1000000000) ≤ -Real.log (5120 / 6759) ∧
    -Real.log (5120 / 6759) ≤ (4339383 / 15625000) := by
  have h := checkLog_sound (w := (1639 / 11879)) (n := 12)
    (lo := (277720511 / 1000000000)) (hi := (4339383 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6759 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6759 / 5120) = 1/(5120 / 6759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (277720511 / 1000000000) (4339383 / 15625000) (Real.log (6759 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6759 / 5120) = -Real.log (5120 / 6759) := by
    rw [show ((6759 / 5120) : ℝ) = ((5120 / 6759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (38583483 / 100000000) ≤ -Real.log (3481 / 5120) ∧
    -Real.log (3481 / 5120) ≤ (385834831 / 1000000000) := by
  have h := checkLog_sound (w := (1639 / 8601)) (n := 12)
    (lo := (38583483 / 100000000)) (hi := (385834831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3481) = 1/(3481 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-385834831 / 1000000000) (-38583483 / 100000000) (Real.log (3481 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (495553343 / 1000000000) ≤ -Real.log (1280 / 2101) ∧
    -Real.log (1280 / 2101) ≤ (7743021 / 15625000) := by
  have h := checkLog_sound (w := (821 / 3381)) (n := 12)
    (lo := (495553343 / 1000000000)) (hi := (7743021 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2101 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2101 / 1280) = 1/(1280 / 2101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (495553343 / 1000000000) (7743021 / 15625000) (Real.log (2101 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2101 / 1280) = -Real.log (1280 / 2101) := by
    rw [show ((2101 / 1280) : ℝ) = ((1280 / 2101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (512782573 / 500000000) ≤ -Real.log (459 / 1280) ∧
    -Real.log (459 / 1280) ≤ (256391287 / 250000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 459) = 1/(459 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-256391287 / 250000000) (-512782573 / 500000000) (Real.log (459 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (494839143 / 1000000000) ≤ -Real.log (2560 / 4199) ∧
    -Real.log (2560 / 4199) ≤ (61854893 / 125000000) := by
  have h := checkLog_sound (w := (1639 / 6759)) (n := 12)
    (lo := (494839143 / 1000000000)) (hi := (61854893 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4199 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4199 / 2560) = 1/(2560 / 4199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (494839143 / 1000000000) (61854893 / 125000000) (Real.log (4199 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4199 / 2560) = -Real.log (2560 / 4199) := by
    rw [show ((4199 / 2560) : ℝ) = ((2560 / 4199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (408921 / 400000) ≤ -Real.log (921 / 2560) ∧
    -Real.log (921 / 2560) ≤ (511151251 / 500000000) := by
  have h := checkLog_sound (w := (359 / 2201)) (n := 12)
    (lo := (8228883 / 25000000)) (hi := (329155321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 921) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 921) = 1/(921 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-511151251 / 500000000) (-408921 / 400000) (Real.log (921 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (189957397 / 500000000) ≤ -Real.log (12500 / 18277) ∧
    -Real.log (12500 / 18277) ≤ (75982959 / 200000000) := by
  have h := checkLog_sound (w := (5777 / 30777)) (n := 12)
    (lo := (189957397 / 500000000)) (hi := (75982959 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18277 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18277 / 12500) = 1/(12500 / 18277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (189957397 / 500000000) (75982959 / 200000000) (Real.log (18277 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (18277 / 12500) = -Real.log (12500 / 18277) := by
    rw [show ((18277 / 12500) : ℝ) = ((12500 / 18277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (7752427 / 12500000) ≤ -Real.log (6723 / 12500) ∧
    -Real.log (6723 / 12500) ≤ (620194161 / 1000000000) := by
  have h := checkLog_sound (w := (5777 / 19223)) (n := 12)
    (lo := (7752427 / 12500000)) (hi := (620194161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 6723) = 1/(6723 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-620194161 / 1000000000) (-7752427 / 12500000) (Real.log (6723 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (380523297 / 1000000000) ≤ -Real.log (20000 / 29261) ∧
    -Real.log (20000 / 29261) ≤ (190261649 / 500000000) := by
  have h := checkLog_sound (w := (9261 / 49261)) (n := 12)
    (lo := (380523297 / 1000000000)) (hi := (190261649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29261 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29261 / 20000) = 1/(20000 / 29261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (380523297 / 1000000000) (190261649 / 500000000) (Real.log (29261 / 20000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (29261 / 20000) = -Real.log (20000 / 29261) := by
    rw [show ((29261 / 20000) : ℝ) = ((20000 / 29261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (310925149 / 500000000) ≤ -Real.log (10739 / 20000) ∧
    -Real.log (10739 / 20000) ≤ (621850299 / 1000000000) := by
  have h := checkLog_sound (w := (9261 / 30739)) (n := 12)
    (lo := (310925149 / 500000000)) (hi := (621850299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 10739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 10739) = 1/(10739 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-621850299 / 1000000000) (-310925149 / 500000000) (Real.log (10739 / 20000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (298084033 / 1000000000) ≤ -Real.log (40000 / 53891) ∧
    -Real.log (40000 / 53891) ≤ (149042017 / 500000000) := by
  have h := checkLog_sound (w := (13891 / 93891)) (n := 12)
    (lo := (298084033 / 1000000000)) (hi := (149042017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53891 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53891 / 40000) = 1/(40000 / 53891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (298084033 / 1000000000) (149042017 / 500000000) (Real.log (53891 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (53891 / 40000) = -Real.log (40000 / 53891) := by
    rw [show ((53891 / 40000) : ℝ) = ((40000 / 53891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (426599371 / 1000000000) ≤ -Real.log (26109 / 40000) ∧
    -Real.log (26109 / 40000) ≤ (106649843 / 250000000) := by
  have h := checkLog_sound (w := (13891 / 66109)) (n := 12)
    (lo := (426599371 / 1000000000)) (hi := (106649843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26109) = 1/(26109 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-106649843 / 250000000) (-426599371 / 1000000000) (Real.log (26109 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (298642041 / 1000000000) ≤ -Real.log (1000000 / 1348027) ∧
    -Real.log (1000000 / 1348027) ≤ (149321021 / 500000000) := by
  have h := checkLog_sound (w := (348027 / 2348027)) (n := 12)
    (lo := (298642041 / 1000000000)) (hi := (149321021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1348027 / 1000000) = 1/(1000000 / 1348027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (298642041 / 1000000000) (149321021 / 500000000) (Real.log (1348027 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1348027 / 1000000) = -Real.log (1000000 / 1348027) := by
    rw [show ((1348027 / 1000000) : ℝ) = ((1000000 / 1348027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (6683627 / 15625000) ≤ -Real.log (651973 / 1000000) ∧
    -Real.log (651973 / 1000000) ≤ (427752129 / 1000000000) := by
  have h := checkLog_sound (w := (348027 / 1651973)) (n := 12)
    (lo := (6683627 / 15625000)) (hi := (427752129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 651973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 651973) = 1/(651973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-427752129 / 1000000000) (-6683627 / 15625000) (Real.log (651973 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (500054477 / 500000000) ≤ -Real.log (500000000000 / 1359289007883) ∧
    -Real.log (500000000000 / 1359289007883) ≤ (250027239 / 250000000) := by
  have h := checkLog_sound (w := (359289007883 / 2359289007883)) (n := 12)
    (lo := (153480887 / 500000000)) (hi := (12278471 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359289007883 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1359289007883 / 1000000000000) = 1/(500000000000 / 1359289007883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (500054477 / 500000000) (250027239 / 250000000) (Real.log (1359289007883 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1359289007883 / 500000000000) = -Real.log (500000000000 / 1359289007883) := by
    rw [show ((1359289007883 / 500000000000) : ℝ) = ((500000000000 / 1359289007883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (200474719 / 200000000) ≤ -Real.log (250000000000 / 681185399013) ∧
    -Real.log (250000000000 / 681185399013) ≤ (1002373597 / 1000000000) := by
  have h := checkLog_sound (w := (181185399013 / 1181185399013)) (n := 12)
    (lo := (61845283 / 200000000)) (hi := (19326651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681185399013 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(681185399013 / 500000000000) = 1/(250000000000 / 681185399013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (200474719 / 200000000) (1002373597 / 1000000000) (Real.log (681185399013 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (681185399013 / 250000000000) = -Real.log (250000000000 / 681185399013) := by
    rw [show ((681185399013 / 250000000000) : ℝ) = ((250000000000 / 681185399013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (144936681 / 200000000) ≤ -Real.log (25000000000 / 51601938029) ∧
    -Real.log (25000000000 / 51601938029) ≤ (724683407 / 1000000000) := by
  have h := checkLog_sound (w := (1601938029 / 101601938029)) (n := 12)
    (lo := (1261449 / 40000000)) (hi := (15768113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51601938029 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51601938029 / 50000000000) = 1/(25000000000 / 51601938029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (144936681 / 200000000) (724683407 / 1000000000) (Real.log (51601938029 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (51601938029 / 25000000000) = -Real.log (25000000000 / 51601938029) := by
    rw [show ((51601938029 / 25000000000) : ℝ) = ((25000000000 / 51601938029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (72639417 / 100000000) ≤ -Real.log (500000000000 / 1033805847789) ∧
    -Real.log (500000000000 / 1033805847789) ≤ (181598543 / 250000000) := by
  have h := checkLog_sound (w := (33805847789 / 2033805847789)) (n := 12)
    (lo := (3324699 / 100000000)) (hi := (33246991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1033805847789 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1033805847789 / 1000000000000) = 1/(500000000000 / 1033805847789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (72639417 / 100000000) (181598543 / 250000000) (Real.log (1033805847789 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1033805847789 / 500000000000) = -Real.log (500000000000 / 1033805847789) := by
    rw [show ((1033805847789 / 500000000000) : ℝ) = ((500000000000 / 1033805847789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0172

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0173Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0173
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

theorem reflection_log_1_neg : (277720511 / 1000000000) ≤ -Real.log (5120 / 6759) ∧
    -Real.log (5120 / 6759) ≤ (4339383 / 15625000) := by
  have h := checkLog_sound (w := (1639 / 11879)) (n := 12)
    (lo := (277720511 / 1000000000)) (hi := (4339383 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6759 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6759 / 5120) = 1/(5120 / 6759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (277720511 / 1000000000) (4339383 / 15625000) (Real.log (6759 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6759 / 5120) = -Real.log (5120 / 6759) := by
    rw [show ((6759 / 5120) : ℝ) = ((5120 / 6759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (38583483 / 100000000) ≤ -Real.log (3481 / 5120) ∧
    -Real.log (3481 / 5120) ≤ (385834831 / 1000000000) := by
  have h := checkLog_sound (w := (1639 / 8601)) (n := 12)
    (lo := (38583483 / 100000000)) (hi := (385834831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3481) = 1/(3481 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-385834831 / 1000000000) (-38583483 / 100000000) (Real.log (3481 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (277276559 / 1000000000) ≤ -Real.log (1280 / 1689) ∧
    -Real.log (1280 / 1689) ≤ (3465957 / 12500000) := by
  have h := checkLog_sound (w := (409 / 2969)) (n := 12)
    (lo := (277276559 / 1000000000)) (hi := (3465957 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1689 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1689 / 1280) = 1/(1280 / 1689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (277276559 / 1000000000) (3465957 / 12500000) (Real.log (1689 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1689 / 1280) = -Real.log (1280 / 1689) := by
    rw [show ((1689 / 1280) : ℝ) = ((1280 / 1689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19248669 / 50000000) ≤ -Real.log (871 / 1280) ∧
    -Real.log (871 / 1280) ≤ (384973381 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2151)) (n := 12)
    (lo := (19248669 / 50000000)) (hi := (384973381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 871) = 1/(871 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-384973381 / 1000000000) (-19248669 / 50000000) (Real.log (871 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (494839143 / 1000000000) ≤ -Real.log (2560 / 4199) ∧
    -Real.log (2560 / 4199) ≤ (61854893 / 125000000) := by
  have h := checkLog_sound (w := (1639 / 6759)) (n := 12)
    (lo := (494839143 / 1000000000)) (hi := (61854893 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4199 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4199 / 2560) = 1/(2560 / 4199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (494839143 / 1000000000) (61854893 / 125000000) (Real.log (4199 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4199 / 2560) = -Real.log (2560 / 4199) := by
    rw [show ((4199 / 2560) : ℝ) = ((2560 / 4199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (408921 / 400000) ≤ -Real.log (921 / 2560) ∧
    -Real.log (921 / 2560) ≤ (511151251 / 500000000) := by
  have h := checkLog_sound (w := (359 / 2201)) (n := 12)
    (lo := (8228883 / 25000000)) (hi := (329155321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 921) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 921) = 1/(921 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-511151251 / 500000000) (-408921 / 400000) (Real.log (921 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (30882777 / 62500000) ≤ -Real.log (640 / 1049) ∧
    -Real.log (640 / 1049) ≤ (494124433 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 1689)) (n := 12)
    (lo := (30882777 / 62500000)) (hi := (494124433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1049 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1049 / 640) = 1/(640 / 1049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (30882777 / 62500000) (494124433 / 1000000000) (Real.log (1049 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1049 / 640) = -Real.log (640 / 1049) := by
    rw [show ((1049 / 640) : ℝ) = ((640 / 1049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (203810093 / 200000000) ≤ -Real.log (231 / 640) ∧
    -Real.log (231 / 640) ≤ (1019050467 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 231) = 1/(231 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1019050467 / 1000000000) (-203810093 / 200000000) (Real.log (231 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (94826651 / 250000000) ≤ -Real.log (1000000 / 1461271) ∧
    -Real.log (1000000 / 1461271) ≤ (75861321 / 200000000) := by
  have h := checkLog_sound (w := (461271 / 2461271)) (n := 12)
    (lo := (94826651 / 250000000)) (hi := (75861321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1461271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1461271 / 1000000) = 1/(1000000 / 1461271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (94826651 / 250000000) (75861321 / 200000000) (Real.log (1461271 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1461271 / 1000000) = -Real.log (1000000 / 1461271) := by
    rw [show ((1461271 / 1000000) : ℝ) = ((1000000 / 1461271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (618542617 / 1000000000) ≤ -Real.log (538729 / 1000000) ∧
    -Real.log (538729 / 1000000) ≤ (309271309 / 500000000) := by
  have h := checkLog_sound (w := (461271 / 1538729)) (n := 12)
    (lo := (618542617 / 1000000000)) (hi := (309271309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 538729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 538729) = 1/(538729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-309271309 / 500000000) (-618542617 / 1000000000) (Real.log (538729 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (189957739 / 500000000) ≤ -Real.log (1000000 / 1462161) ∧
    -Real.log (1000000 / 1462161) ≤ (379915479 / 1000000000) := by
  have h := checkLog_sound (w := (462161 / 2462161)) (n := 12)
    (lo := (189957739 / 500000000)) (hi := (379915479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1462161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1462161 / 1000000) = 1/(1000000 / 1462161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (189957739 / 500000000) (379915479 / 1000000000) (Real.log (1462161 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1462161 / 1000000) = -Real.log (1000000 / 1462161) := by
    rw [show ((1462161 / 1000000) : ℝ) = ((1000000 / 1462161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (31009801 / 50000000) ≤ -Real.log (537839 / 1000000) ∧
    -Real.log (537839 / 1000000) ≤ (620196021 / 1000000000) := by
  have h := checkLog_sound (w := (462161 / 1537839)) (n := 12)
    (lo := (31009801 / 50000000)) (hi := (620196021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 537839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 537839) = 1/(537839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-620196021 / 1000000000) (-31009801 / 50000000) (Real.log (537839 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (297526457 / 1000000000) ≤ -Real.log (250000 / 336631) ∧
    -Real.log (250000 / 336631) ≤ (148763229 / 500000000) := by
  have h := checkLog_sound (w := (86631 / 586631)) (n := 12)
    (lo := (297526457 / 1000000000)) (hi := (148763229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336631 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336631 / 250000) = 1/(250000 / 336631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (297526457 / 1000000000) (148763229 / 500000000) (Real.log (336631 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (336631 / 250000) = -Real.log (250000 / 336631) := by
    rw [show ((336631 / 250000) : ℝ) = ((250000 / 336631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (425449471 / 1000000000) ≤ -Real.log (163369 / 250000) ∧
    -Real.log (163369 / 250000) ≤ (830956 / 1953125) := by
  have h := checkLog_sound (w := (86631 / 413369)) (n := 12)
    (lo := (425449471 / 1000000000)) (hi := (830956 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163369) = 1/(163369 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-830956 / 1953125) (-425449471 / 1000000000) (Real.log (163369 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (37260597 / 125000000) ≤ -Real.log (250000 / 336819) ∧
    -Real.log (250000 / 336819) ≤ (298084777 / 1000000000) := by
  have h := checkLog_sound (w := (86819 / 586819)) (n := 12)
    (lo := (37260597 / 125000000)) (hi := (298084777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336819 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336819 / 250000) = 1/(250000 / 336819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (37260597 / 125000000) (298084777 / 1000000000) (Real.log (336819 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (336819 / 250000) = -Real.log (250000 / 336819) := by
    rw [show ((336819 / 250000) : ℝ) = ((250000 / 336819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (426600903 / 1000000000) ≤ -Real.log (163181 / 250000) ∧
    -Real.log (163181 / 250000) ≤ (53325113 / 125000000) := by
  have h := checkLog_sound (w := (86819 / 413181)) (n := 12)
    (lo := (426600903 / 1000000000)) (hi := (53325113 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163181) = 1/(163181 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-53325113 / 125000000) (-426600903 / 1000000000) (Real.log (163181 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (997849221 / 1000000000) ≤ -Real.log (500000000000 / 1356220845731) ∧
    -Real.log (500000000000 / 1356220845731) ≤ (997849223 / 1000000000) := by
  have h := checkLog_sound (w := (356220845731 / 2356220845731)) (n := 12)
    (lo := (304702041 / 1000000000)) (hi := (152351021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356220845731 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1356220845731 / 1000000000000) = 1/(500000000000 / 1356220845731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (997849221 / 1000000000) (997849223 / 1000000000) (Real.log (1356220845731 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1356220845731 / 500000000000) = -Real.log (500000000000 / 1356220845731) := by
    rw [show ((1356220845731 / 500000000000) : ℝ) = ((500000000000 / 1356220845731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1000111497 / 1000000000) ≤ -Real.log (250000000000 / 679646232423) ∧
    -Real.log (250000000000 / 679646232423) ≤ (1000111499 / 1000000000) := by
  have h := checkLog_sound (w := (179646232423 / 1179646232423)) (n := 12)
    (lo := (306964317 / 1000000000)) (hi := (153482159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679646232423 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(679646232423 / 500000000000) = 1/(250000000000 / 679646232423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1000111497 / 1000000000) (1000111499 / 1000000000) (Real.log (679646232423 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (679646232423 / 250000000000) = -Real.log (250000000000 / 679646232423) := by
    rw [show ((679646232423 / 250000000000) : ℝ) = ((250000000000 / 679646232423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (90371991 / 125000000) ≤ -Real.log (500000000000 / 1030278082133) ∧
    -Real.log (500000000000 / 1030278082133) ≤ (72297593 / 100000000) := by
  have h := checkLog_sound (w := (30278082133 / 2030278082133)) (n := 12)
    (lo := (7457187 / 250000000)) (hi := (29828749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1030278082133 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1030278082133 / 1000000000000) = 1/(500000000000 / 1030278082133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (90371991 / 125000000) (72297593 / 100000000) (Real.log (1030278082133 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1030278082133 / 500000000000) = -Real.log (500000000000 / 1030278082133) := by
    rw [show ((1030278082133 / 500000000000) : ℝ) = ((500000000000 / 1030278082133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (724685679 / 1000000000) ≤ -Real.log (31250000000 / 64502569233) ∧
    -Real.log (31250000000 / 64502569233) ≤ (724685681 / 1000000000) := by
  have h := checkLog_sound (w := (2002569233 / 127002569233)) (n := 12)
    (lo := (31538499 / 1000000000)) (hi := (63077 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64502569233 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64502569233 / 62500000000) = 1/(31250000000 / 64502569233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (724685679 / 1000000000) (724685681 / 1000000000) (Real.log (64502569233 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (64502569233 / 31250000000) = -Real.log (31250000000 / 64502569233) := by
    rw [show ((64502569233 / 31250000000) : ℝ) = ((31250000000 / 64502569233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0173

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0174Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0174
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

theorem reflection_log_1_neg : (277276559 / 1000000000) ≤ -Real.log (1280 / 1689) ∧
    -Real.log (1280 / 1689) ≤ (3465957 / 12500000) := by
  have h := checkLog_sound (w := (409 / 2969)) (n := 12)
    (lo := (277276559 / 1000000000)) (hi := (3465957 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1689 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1689 / 1280) = 1/(1280 / 1689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (277276559 / 1000000000) (3465957 / 12500000) (Real.log (1689 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1689 / 1280) = -Real.log (1280 / 1689) := by
    rw [show ((1689 / 1280) : ℝ) = ((1280 / 1689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19248669 / 50000000) ≤ -Real.log (871 / 1280) ∧
    -Real.log (871 / 1280) ≤ (384973381 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2151)) (n := 12)
    (lo := (19248669 / 50000000)) (hi := (384973381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 871) = 1/(871 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-384973381 / 1000000000) (-19248669 / 50000000) (Real.log (871 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (276832411 / 1000000000) ≤ -Real.log (5120 / 6753) ∧
    -Real.log (5120 / 6753) ≤ (69208103 / 250000000) := by
  have h := checkLog_sound (w := (1633 / 11873)) (n := 12)
    (lo := (276832411 / 1000000000)) (hi := (69208103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6753 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6753 / 5120) = 1/(5120 / 6753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (276832411 / 1000000000) (69208103 / 250000000) (Real.log (6753 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6753 / 5120) = -Real.log (5120 / 6753) := by
    rw [show ((6753 / 5120) : ℝ) = ((5120 / 6753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (384112671 / 1000000000) ≤ -Real.log (3487 / 5120) ∧
    -Real.log (3487 / 5120) ≤ (12003521 / 31250000) := by
  have h := checkLog_sound (w := (1633 / 8607)) (n := 12)
    (lo := (384112671 / 1000000000)) (hi := (12003521 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3487) = 1/(3487 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12003521 / 31250000) (-384112671 / 1000000000) (Real.log (3487 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (30882777 / 62500000) ≤ -Real.log (640 / 1049) ∧
    -Real.log (640 / 1049) ≤ (494124433 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 1689)) (n := 12)
    (lo := (30882777 / 62500000)) (hi := (494124433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1049 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1049 / 640) = 1/(640 / 1049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (30882777 / 62500000) (494124433 / 1000000000) (Real.log (1049 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1049 / 640) = -Real.log (640 / 1049) := by
    rw [show ((1049 / 640) : ℝ) = ((640 / 1049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (203810093 / 200000000) ≤ -Real.log (231 / 640) ∧
    -Real.log (231 / 640) ≤ (1019050467 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 231) = 1/(231 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1019050467 / 1000000000) (-203810093 / 200000000) (Real.log (231 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (493409209 / 1000000000) ≤ -Real.log (2560 / 4193) ∧
    -Real.log (2560 / 4193) ≤ (49340921 / 100000000) := by
  have h := checkLog_sound (w := (1633 / 6753)) (n := 12)
    (lo := (493409209 / 1000000000)) (hi := (49340921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4193 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4193 / 2560) = 1/(2560 / 4193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (493409209 / 1000000000) (49340921 / 100000000) (Real.log (4193 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4193 / 2560) = -Real.log (2560 / 4193) := by
    rw [show ((4193 / 2560) : ℝ) = ((2560 / 4193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1015808971 / 1000000000) ≤ -Real.log (927 / 2560) ∧
    -Real.log (927 / 2560) ≤ (1015808973 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 2207)) (n := 12)
    (lo := (322661791 / 1000000000)) (hi := (10083181 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 927) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 927) = 1/(927 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1015808973 / 1000000000) (-1015808971 / 1000000000) (Real.log (927 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (37869873 / 100000000) ≤ -Real.log (1000000 / 1460383) ∧
    -Real.log (1000000 / 1460383) ≤ (378698731 / 1000000000) := by
  have h := checkLog_sound (w := (460383 / 2460383)) (n := 12)
    (lo := (37869873 / 100000000)) (hi := (378698731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1460383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1460383 / 1000000) = 1/(1000000 / 1460383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (37869873 / 100000000) (378698731 / 1000000000) (Real.log (1460383 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1460383 / 1000000) = -Real.log (1000000 / 1460383) := by
    rw [show ((1460383 / 1000000) : ℝ) = ((1000000 / 1460383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (12337913 / 20000000) ≤ -Real.log (539617 / 1000000) ∧
    -Real.log (539617 / 1000000) ≤ (616895651 / 1000000000) := by
  have h := checkLog_sound (w := (460383 / 1539617)) (n := 12)
    (lo := (12337913 / 20000000)) (hi := (616895651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 539617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 539617) = 1/(539617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-616895651 / 1000000000) (-12337913 / 20000000) (Real.log (539617 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (379307289 / 1000000000) ≤ -Real.log (125000 / 182659) ∧
    -Real.log (125000 / 182659) ≤ (37930729 / 100000000) := by
  have h := checkLog_sound (w := (57659 / 307659)) (n := 12)
    (lo := (379307289 / 1000000000)) (hi := (37930729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182659 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182659 / 125000) = 1/(125000 / 182659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (379307289 / 1000000000) (37930729 / 100000000) (Real.log (182659 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (182659 / 125000) = -Real.log (125000 / 182659) := by
    rw [show ((182659 / 125000) : ℝ) = ((125000 / 182659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (618544473 / 1000000000) ≤ -Real.log (67341 / 125000) ∧
    -Real.log (67341 / 125000) ≤ (309272237 / 500000000) := by
  have h := checkLog_sound (w := (57659 / 192341)) (n := 12)
    (lo := (618544473 / 1000000000)) (hi := (309272237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 67341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 67341) = 1/(67341 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-309272237 / 500000000) (-618544473 / 1000000000) (Real.log (67341 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9280291 / 31250000) ≤ -Real.log (500000 / 672887) ∧
    -Real.log (500000 / 672887) ≤ (296969313 / 1000000000) := by
  have h := checkLog_sound (w := (172887 / 1172887)) (n := 12)
    (lo := (9280291 / 31250000)) (hi := (296969313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672887 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(672887 / 500000) = 1/(500000 / 672887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9280291 / 31250000) (296969313 / 1000000000) (Real.log (672887 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (672887 / 500000) = -Real.log (500000 / 672887) := by
    rw [show ((672887 / 500000) : ℝ) = ((500000 / 672887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (424302421 / 1000000000) ≤ -Real.log (327113 / 500000) ∧
    -Real.log (327113 / 500000) ≤ (212151211 / 500000000) := by
  have h := checkLog_sound (w := (172887 / 827113)) (n := 12)
    (lo := (424302421 / 1000000000)) (hi := (212151211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 327113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 327113) = 1/(327113 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-212151211 / 500000000) (-424302421 / 1000000000) (Real.log (327113 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (297527199 / 1000000000) ≤ -Real.log (40000 / 53861) ∧
    -Real.log (40000 / 53861) ≤ (371909 / 1250000) := by
  have h := checkLog_sound (w := (13861 / 93861)) (n := 12)
    (lo := (297527199 / 1000000000)) (hi := (371909 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53861 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53861 / 40000) = 1/(40000 / 53861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (297527199 / 1000000000) (371909 / 1250000) (Real.log (53861 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (53861 / 40000) = -Real.log (40000 / 53861) := by
    rw [show ((53861 / 40000) : ℝ) = ((40000 / 53861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (212725501 / 500000000) ≤ -Real.log (26139 / 40000) ∧
    -Real.log (26139 / 40000) ≤ (425451003 / 1000000000) := by
  have h := checkLog_sound (w := (13861 / 66139)) (n := 12)
    (lo := (212725501 / 500000000)) (hi := (425451003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26139) = 1/(26139 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-425451003 / 1000000000) (-212725501 / 500000000) (Real.log (26139 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (995594379 / 1000000000) ≤ -Real.log (500000000000 / 1353166227157) ∧
    -Real.log (500000000000 / 1353166227157) ≤ (995594381 / 1000000000) := by
  have h := checkLog_sound (w := (353166227157 / 2353166227157)) (n := 12)
    (lo := (302447199 / 1000000000)) (hi := (378059 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353166227157 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1353166227157 / 1000000000000) = 1/(500000000000 / 1353166227157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (995594379 / 1000000000) (995594381 / 1000000000) (Real.log (1353166227157 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1353166227157 / 500000000000) = -Real.log (500000000000 / 1353166227157) := by
    rw [show ((1353166227157 / 500000000000) : ℝ) = ((500000000000 / 1353166227157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (498925881 / 500000000) ≤ -Real.log (250000000000 / 678112145647) ∧
    -Real.log (250000000000 / 678112145647) ≤ (249462941 / 250000000) := by
  have h := checkLog_sound (w := (178112145647 / 1178112145647)) (n := 12)
    (lo := (152352291 / 500000000)) (hi := (304704583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678112145647 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(678112145647 / 500000000000) = 1/(250000000000 / 678112145647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (498925881 / 500000000) (249462941 / 250000000) (Real.log (678112145647 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (678112145647 / 250000000000) = -Real.log (250000000000 / 678112145647) := by
    rw [show ((678112145647 / 250000000000) : ℝ) = ((250000000000 / 678112145647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (721271733 / 1000000000) ≤ -Real.log (500000000000 / 1028523782301) ∧
    -Real.log (500000000000 / 1028523782301) ≤ (144254347 / 200000000) := by
  have h := checkLog_sound (w := (28523782301 / 2028523782301)) (n := 12)
    (lo := (28124553 / 1000000000)) (hi := (14062277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1028523782301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1028523782301 / 1000000000000) = 1/(500000000000 / 1028523782301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (721271733 / 1000000000) (144254347 / 200000000) (Real.log (1028523782301 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1028523782301 / 500000000000) = -Real.log (500000000000 / 1028523782301) := by
    rw [show ((1028523782301 / 500000000000) : ℝ) = ((500000000000 / 1028523782301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (722978201 / 1000000000) ≤ -Real.log (31250000000 / 64392526493) ∧
    -Real.log (31250000000 / 64392526493) ≤ (722978203 / 1000000000) := by
  have h := checkLog_sound (w := (1892526493 / 126892526493)) (n := 12)
    (lo := (29831021 / 1000000000)) (hi := (14915511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64392526493 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64392526493 / 62500000000) = 1/(31250000000 / 64392526493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (722978201 / 1000000000) (722978203 / 1000000000) (Real.log (64392526493 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (64392526493 / 31250000000) = -Real.log (31250000000 / 64392526493) := by
    rw [show ((64392526493 / 31250000000) : ℝ) = ((31250000000 / 64392526493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0174

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0175Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0175
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

theorem reflection_log_1_neg : (276832411 / 1000000000) ≤ -Real.log (5120 / 6753) ∧
    -Real.log (5120 / 6753) ≤ (69208103 / 250000000) := by
  have h := checkLog_sound (w := (1633 / 11873)) (n := 12)
    (lo := (276832411 / 1000000000)) (hi := (69208103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6753 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6753 / 5120) = 1/(5120 / 6753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (276832411 / 1000000000) (69208103 / 250000000) (Real.log (6753 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6753 / 5120) = -Real.log (5120 / 6753) := by
    rw [show ((6753 / 5120) : ℝ) = ((5120 / 6753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (384112671 / 1000000000) ≤ -Real.log (3487 / 5120) ∧
    -Real.log (3487 / 5120) ≤ (12003521 / 31250000) := by
  have h := checkLog_sound (w := (1633 / 8607)) (n := 12)
    (lo := (384112671 / 1000000000)) (hi := (12003521 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3487) = 1/(3487 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12003521 / 31250000) (-384112671 / 1000000000) (Real.log (3487 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (55277613 / 200000000) ≤ -Real.log (512 / 675) ∧
    -Real.log (512 / 675) ≤ (138194033 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1187)) (n := 12)
    (lo := (55277613 / 200000000)) (hi := (138194033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675 / 512) = 1/(512 / 675) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (55277613 / 200000000) (138194033 / 500000000) (Real.log (675 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (675 / 512) = -Real.log (512 / 675) := by
    rw [show ((675 / 512) : ℝ) = ((512 / 675) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (191626351 / 500000000) ≤ -Real.log (349 / 512) ∧
    -Real.log (349 / 512) ≤ (383252703 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 861)) (n := 12)
    (lo := (191626351 / 500000000)) (hi := (383252703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 349) = 1/(349 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-383252703 / 1000000000) (-191626351 / 500000000) (Real.log (349 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (493409209 / 1000000000) ≤ -Real.log (2560 / 4193) ∧
    -Real.log (2560 / 4193) ≤ (49340921 / 100000000) := by
  have h := checkLog_sound (w := (1633 / 6753)) (n := 12)
    (lo := (493409209 / 1000000000)) (hi := (49340921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4193 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4193 / 2560) = 1/(2560 / 4193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (493409209 / 1000000000) (49340921 / 100000000) (Real.log (4193 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4193 / 2560) = -Real.log (2560 / 4193) := by
    rw [show ((4193 / 2560) : ℝ) = ((2560 / 4193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1015808971 / 1000000000) ≤ -Real.log (927 / 2560) ∧
    -Real.log (927 / 2560) ≤ (1015808973 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 2207)) (n := 12)
    (lo := (322661791 / 1000000000)) (hi := (10083181 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 927) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 927) = 1/(927 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1015808973 / 1000000000) (-1015808971 / 1000000000) (Real.log (927 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (19707739 / 40000000) ≤ -Real.log (256 / 419) ∧
    -Real.log (256 / 419) ≤ (123173369 / 250000000) := by
  have h := checkLog_sound (w := (163 / 675)) (n := 12)
    (lo := (19707739 / 40000000)) (hi := (123173369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419 / 256) = 1/(256 / 419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (19707739 / 40000000) (123173369 / 250000000) (Real.log (419 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (419 / 256) = -Real.log (256 / 419) := by
    rw [show ((419 / 256) : ℝ) = ((256 / 419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (20251559 / 20000000) ≤ -Real.log (93 / 256) ∧
    -Real.log (93 / 256) ≤ (31643061 / 31250000) := by
  have h := checkLog_sound (w := (35 / 221)) (n := 12)
    (lo := (31943077 / 100000000)) (hi := (319430771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 93) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 93) = 1/(93 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-31643061 / 31250000) (-20251559 / 20000000) (Real.log (93 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75618097 / 200000000) ≤ -Real.log (200000 / 291899) ∧
    -Real.log (200000 / 291899) ≤ (189045243 / 500000000) := by
  have h := checkLog_sound (w := (91899 / 491899)) (n := 12)
    (lo := (75618097 / 200000000)) (hi := (189045243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291899 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291899 / 200000) = 1/(200000 / 291899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75618097 / 200000000) (189045243 / 500000000) (Real.log (291899 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (291899 / 200000) = -Real.log (200000 / 291899) := by
    rw [show ((291899 / 200000) : ℝ) = ((200000 / 291899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (615251391 / 1000000000) ≤ -Real.log (108101 / 200000) ∧
    -Real.log (108101 / 200000) ≤ (9613303 / 15625000) := by
  have h := checkLog_sound (w := (91899 / 308101)) (n := 12)
    (lo := (615251391 / 1000000000)) (hi := (9613303 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 108101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 108101) = 1/(108101 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9613303 / 15625000) (-615251391 / 1000000000) (Real.log (108101 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (189349707 / 500000000) ≤ -Real.log (31250 / 45637) ∧
    -Real.log (31250 / 45637) ≤ (75739883 / 200000000) := by
  have h := checkLog_sound (w := (14387 / 76887)) (n := 12)
    (lo := (189349707 / 500000000)) (hi := (75739883 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45637 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45637 / 31250) = 1/(31250 / 45637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (189349707 / 500000000) (75739883 / 200000000) (Real.log (45637 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (45637 / 31250) = -Real.log (31250 / 45637) := by
    rw [show ((45637 / 31250) : ℝ) = ((31250 / 45637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (616897503 / 1000000000) ≤ -Real.log (16863 / 31250) ∧
    -Real.log (16863 / 31250) ≤ (19278047 / 31250000) := by
  have h := checkLog_sound (w := (14387 / 48113)) (n := 12)
    (lo := (616897503 / 1000000000)) (hi := (19278047 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 16863) = 1/(16863 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-19278047 / 31250000) (-616897503 / 1000000000) (Real.log (16863 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1482063 / 5000000) ≤ -Real.log (40000 / 53801) ∧
    -Real.log (40000 / 53801) ≤ (296412601 / 1000000000) := by
  have h := checkLog_sound (w := (13801 / 93801)) (n := 12)
    (lo := (1482063 / 5000000)) (hi := (296412601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53801 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53801 / 40000) = 1/(40000 / 53801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1482063 / 5000000) (296412601 / 1000000000) (Real.log (53801 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (53801 / 40000) = -Real.log (40000 / 53801) := by
    rw [show ((53801 / 40000) : ℝ) = ((40000 / 53801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (105789553 / 250000000) ≤ -Real.log (26199 / 40000) ∧
    -Real.log (26199 / 40000) ≤ (423158213 / 1000000000) := by
  have h := checkLog_sound (w := (13801 / 66199)) (n := 12)
    (lo := (105789553 / 250000000)) (hi := (423158213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26199) = 1/(26199 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-423158213 / 1000000000) (-105789553 / 250000000) (Real.log (26199 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (59394011 / 200000000) ≤ -Real.log (40000 / 53831) ∧
    -Real.log (40000 / 53831) ≤ (37121257 / 125000000) := by
  have h := checkLog_sound (w := (13831 / 93831)) (n := 12)
    (lo := (59394011 / 200000000)) (hi := (37121257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53831 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53831 / 40000) = 1/(40000 / 53831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (59394011 / 200000000) (37121257 / 125000000) (Real.log (53831 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (53831 / 40000) = -Real.log (40000 / 53831) := by
    rw [show ((53831 / 40000) : ℝ) = ((40000 / 53831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (424303949 / 1000000000) ≤ -Real.log (26169 / 40000) ∧
    -Real.log (26169 / 40000) ≤ (8486079 / 20000000) := by
  have h := checkLog_sound (w := (13831 / 66169)) (n := 12)
    (lo := (424303949 / 1000000000)) (hi := (8486079 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26169) = 1/(26169 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-8486079 / 20000000) (-424303949 / 1000000000) (Real.log (26169 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (248335469 / 250000000) ≤ -Real.log (250000000000 / 675060822749) ∧
    -Real.log (250000000000 / 675060822749) ≤ (496670939 / 500000000) := by
  have h := checkLog_sound (w := (175060822749 / 1175060822749)) (n := 12)
    (lo := (37524337 / 125000000)) (hi := (300194697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675060822749 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(675060822749 / 500000000000) = 1/(250000000000 / 675060822749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (248335469 / 250000000) (496670939 / 500000000) (Real.log (675060822749 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (675060822749 / 250000000000) = -Real.log (250000000000 / 675060822749) := by
    rw [show ((675060822749 / 250000000000) : ℝ) = ((250000000000 / 675060822749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (995596917 / 1000000000) ≤ -Real.log (500000000000 / 1353169661389) ∧
    -Real.log (500000000000 / 1353169661389) ≤ (995596919 / 1000000000) := by
  have h := checkLog_sound (w := (353169661389 / 2353169661389)) (n := 12)
    (lo := (302449737 / 1000000000)) (hi := (151224869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353169661389 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1353169661389 / 1000000000000) = 1/(500000000000 / 1353169661389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (995596917 / 1000000000) (995596919 / 1000000000) (Real.log (1353169661389 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1353169661389 / 500000000000) = -Real.log (500000000000 / 1353169661389) := by
    rw [show ((1353169661389 / 500000000000) : ℝ) = ((500000000000 / 1353169661389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (719570811 / 1000000000) ≤ -Real.log (250000000000 / 513387915569) ∧
    -Real.log (250000000000 / 513387915569) ≤ (719570813 / 1000000000) := by
  have h := checkLog_sound (w := (13387915569 / 1013387915569)) (n := 12)
    (lo := (26423631 / 1000000000)) (hi := (1651477 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((513387915569 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(513387915569 / 500000000000) = 1/(250000000000 / 513387915569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (719570811 / 1000000000) (719570813 / 1000000000) (Real.log (513387915569 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (513387915569 / 250000000000) = -Real.log (250000000000 / 513387915569) := by
    rw [show ((513387915569 / 250000000000) : ℝ) = ((250000000000 / 513387915569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (180318501 / 250000000) ≤ -Real.log (500000000000 / 1028526118691) ∧
    -Real.log (500000000000 / 1028526118691) ≤ (360637003 / 500000000) := by
  have h := checkLog_sound (w := (28526118691 / 2028526118691)) (n := 12)
    (lo := (3515853 / 125000000)) (hi := (1125073 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1028526118691 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1028526118691 / 1000000000000) = 1/(500000000000 / 1028526118691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (180318501 / 250000000) (360637003 / 500000000) (Real.log (1028526118691 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1028526118691 / 500000000000) = -Real.log (500000000000 / 1028526118691) := by
    rw [show ((1028526118691 / 500000000000) : ℝ) = ((500000000000 / 1028526118691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0175

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0176Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0176
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

theorem reflection_log_1_neg : (55277613 / 200000000) ≤ -Real.log (512 / 675) ∧
    -Real.log (512 / 675) ≤ (138194033 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1187)) (n := 12)
    (lo := (55277613 / 200000000)) (hi := (138194033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675 / 512) = 1/(512 / 675) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (55277613 / 200000000) (138194033 / 500000000) (Real.log (675 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (675 / 512) = -Real.log (512 / 675) := by
    rw [show ((675 / 512) : ℝ) = ((512 / 675) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (191626351 / 500000000) ≤ -Real.log (349 / 512) ∧
    -Real.log (349 / 512) ≤ (383252703 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 861)) (n := 12)
    (lo := (191626351 / 500000000)) (hi := (383252703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 349) = 1/(349 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-383252703 / 1000000000) (-191626351 / 500000000) (Real.log (349 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (137971761 / 500000000) ≤ -Real.log (5120 / 6747) ∧
    -Real.log (5120 / 6747) ≤ (275943523 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 11867)) (n := 12)
    (lo := (137971761 / 500000000)) (hi := (275943523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6747 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6747 / 5120) = 1/(5120 / 6747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (137971761 / 500000000) (275943523 / 1000000000) (Real.log (6747 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6747 / 5120) = -Real.log (5120 / 6747) := by
    rw [show ((6747 / 5120) : ℝ) = ((5120 / 6747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (382393473 / 1000000000) ≤ -Real.log (3493 / 5120) ∧
    -Real.log (3493 / 5120) ≤ (191196737 / 500000000) := by
  have h := checkLog_sound (w := (1627 / 8613)) (n := 12)
    (lo := (382393473 / 1000000000)) (hi := (191196737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3493) = 1/(3493 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-191196737 / 500000000) (-382393473 / 1000000000) (Real.log (3493 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19707739 / 40000000) ≤ -Real.log (256 / 419) ∧
    -Real.log (256 / 419) ≤ (123173369 / 250000000) := by
  have h := checkLog_sound (w := (163 / 675)) (n := 12)
    (lo := (19707739 / 40000000)) (hi := (123173369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419 / 256) = 1/(256 / 419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19707739 / 40000000) (123173369 / 250000000) (Real.log (419 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (419 / 256) = -Real.log (256 / 419) := by
    rw [show ((419 / 256) : ℝ) = ((256 / 419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (20251559 / 20000000) ≤ -Real.log (93 / 256) ∧
    -Real.log (93 / 256) ≤ (31643061 / 31250000) := by
  have h := checkLog_sound (w := (35 / 221)) (n := 12)
    (lo := (31943077 / 100000000)) (hi := (319430771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 93) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 93) = 1/(93 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-31643061 / 31250000) (-20251559 / 20000000) (Real.log (93 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122994307 / 250000000) ≤ -Real.log (2560 / 4187) ∧
    -Real.log (2560 / 4187) ≤ (491977229 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 6747)) (n := 12)
    (lo := (122994307 / 250000000)) (hi := (491977229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4187 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4187 / 2560) = 1/(2560 / 4187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122994307 / 250000000) (491977229 / 1000000000) (Real.log (4187 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4187 / 2560) = -Real.log (2560 / 4187) := by
    rw [show ((4187 / 2560) : ℝ) = ((2560 / 4187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (126169667 / 125000000) ≤ -Real.log (933 / 2560) ∧
    -Real.log (933 / 2560) ≤ (504678669 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2213)) (n := 12)
    (lo := (79052539 / 250000000)) (hi := (316210157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 933) = 1/(933 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-504678669 / 500000000) (-126169667 / 125000000) (Real.log (933 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (37748187 / 100000000) ≤ -Real.log (1000000 / 1458607) ∧
    -Real.log (1000000 / 1458607) ≤ (377481871 / 1000000000) := by
  have h := checkLog_sound (w := (458607 / 2458607)) (n := 12)
    (lo := (37748187 / 100000000)) (hi := (377481871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1458607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1458607 / 1000000) = 1/(1000000 / 1458607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (37748187 / 100000000) (377481871 / 1000000000) (Real.log (1458607 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1458607 / 1000000) = -Real.log (1000000 / 1458607) := by
    rw [show ((1458607 / 1000000) : ℝ) = ((1000000 / 1458607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (613609831 / 1000000000) ≤ -Real.log (541393 / 1000000) ∧
    -Real.log (541393 / 1000000) ≤ (76701229 / 125000000) := by
  have h := checkLog_sound (w := (458607 / 1541393)) (n := 12)
    (lo := (613609831 / 1000000000)) (hi := (76701229 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 541393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 541393) = 1/(541393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-76701229 / 125000000) (-613609831 / 1000000000) (Real.log (541393 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37809117 / 100000000) ≤ -Real.log (125000 / 182437) ∧
    -Real.log (125000 / 182437) ≤ (378091171 / 1000000000) := by
  have h := checkLog_sound (w := (57437 / 307437)) (n := 12)
    (lo := (37809117 / 100000000)) (hi := (378091171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182437 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182437 / 125000) = 1/(125000 / 182437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37809117 / 100000000) (378091171 / 1000000000) (Real.log (182437 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (182437 / 125000) = -Real.log (125000 / 182437) := by
    rw [show ((182437 / 125000) : ℝ) = ((125000 / 182437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (615253241 / 1000000000) ≤ -Real.log (67563 / 125000) ∧
    -Real.log (67563 / 125000) ≤ (307626621 / 500000000) := by
  have h := checkLog_sound (w := (57437 / 192563)) (n := 12)
    (lo := (615253241 / 1000000000)) (hi := (307626621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 67563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 67563) = 1/(67563 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-307626621 / 500000000) (-615253241 / 1000000000) (Real.log (67563 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (147927789 / 500000000) ≤ -Real.log (250000 / 336069) ∧
    -Real.log (250000 / 336069) ≤ (295855579 / 1000000000) := by
  have h := checkLog_sound (w := (86069 / 586069)) (n := 12)
    (lo := (147927789 / 500000000)) (hi := (295855579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336069 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336069 / 250000) = 1/(250000 / 336069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (147927789 / 500000000) (295855579 / 1000000000) (Real.log (336069 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (336069 / 250000) = -Real.log (250000 / 336069) := by
    rw [show ((336069 / 250000) : ℝ) = ((250000 / 336069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (42201531 / 100000000) ≤ -Real.log (163931 / 250000) ∧
    -Real.log (163931 / 250000) ≤ (422015311 / 1000000000) := by
  have h := checkLog_sound (w := (86069 / 413931)) (n := 12)
    (lo := (42201531 / 100000000)) (hi := (422015311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163931) = 1/(163931 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-422015311 / 1000000000) (-42201531 / 100000000) (Real.log (163931 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (296413343 / 1000000000) ≤ -Real.log (500000 / 672513) ∧
    -Real.log (500000 / 672513) ≤ (9262917 / 31250000) := by
  have h := checkLog_sound (w := (172513 / 1172513)) (n := 12)
    (lo := (296413343 / 1000000000)) (hi := (9262917 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672513 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(672513 / 500000) = 1/(500000 / 672513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (296413343 / 1000000000) (9262917 / 31250000) (Real.log (672513 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (672513 / 500000) = -Real.log (500000 / 672513) := by
    rw [show ((672513 / 500000) : ℝ) = ((500000 / 672513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (211579869 / 500000000) ≤ -Real.log (327487 / 500000) ∧
    -Real.log (327487 / 500000) ≤ (423159739 / 1000000000) := by
  have h := checkLog_sound (w := (172513 / 827487)) (n := 12)
    (lo := (211579869 / 500000000)) (hi := (423159739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 327487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 327487) = 1/(327487 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-423159739 / 1000000000) (-211579869 / 500000000) (Real.log (327487 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (991091701 / 1000000000) ≤ -Real.log (100000000000 / 269417410273) ∧
    -Real.log (100000000000 / 269417410273) ≤ (991091703 / 1000000000) := by
  have h := checkLog_sound (w := (69417410273 / 469417410273)) (n := 12)
    (lo := (297944521 / 1000000000)) (hi := (148972261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269417410273 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269417410273 / 200000000000) = 1/(100000000000 / 269417410273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (991091701 / 1000000000) (991091703 / 1000000000) (Real.log (269417410273 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (269417410273 / 100000000000) = -Real.log (100000000000 / 269417410273) := by
    rw [show ((269417410273 / 100000000000) : ℝ) = ((100000000000 / 269417410273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (993344411 / 1000000000) ≤ -Real.log (100000000000 / 270025013691) ∧
    -Real.log (100000000000 / 270025013691) ≤ (993344413 / 1000000000) := by
  have h := checkLog_sound (w := (70025013691 / 470025013691)) (n := 12)
    (lo := (300197231 / 1000000000)) (hi := (18762327 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270025013691 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(270025013691 / 200000000000) = 1/(100000000000 / 270025013691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (993344411 / 1000000000) (993344413 / 1000000000) (Real.log (270025013691 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (270025013691 / 100000000000) = -Real.log (100000000000 / 270025013691) := by
    rw [show ((270025013691 / 100000000000) : ℝ) = ((100000000000 / 270025013691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (717870887 / 1000000000) ≤ -Real.log (250000000000 / 512515936583) ∧
    -Real.log (250000000000 / 512515936583) ≤ (717870889 / 1000000000) := by
  have h := checkLog_sound (w := (12515936583 / 1012515936583)) (n := 12)
    (lo := (24723707 / 1000000000)) (hi := (6180927 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512515936583 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512515936583 / 500000000000) = 1/(250000000000 / 512515936583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (717870887 / 1000000000) (717870889 / 1000000000) (Real.log (512515936583 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (512515936583 / 250000000000) = -Real.log (250000000000 / 512515936583) := by
    rw [show ((512515936583 / 250000000000) : ℝ) = ((250000000000 / 512515936583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (719573081 / 1000000000) ≤ -Real.log (500000000000 / 1026778162187) ∧
    -Real.log (500000000000 / 1026778162187) ≤ (719573083 / 1000000000) := by
  have h := checkLog_sound (w := (26778162187 / 2026778162187)) (n := 12)
    (lo := (26425901 / 1000000000)) (hi := (13212951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1026778162187 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1026778162187 / 1000000000000) = 1/(500000000000 / 1026778162187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (719573081 / 1000000000) (719573083 / 1000000000) (Real.log (1026778162187 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1026778162187 / 500000000000) = -Real.log (500000000000 / 1026778162187) := by
    rw [show ((1026778162187 / 500000000000) : ℝ) = ((500000000000 / 1026778162187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0176

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0177Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0177
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

theorem reflection_log_1_neg : (137971761 / 500000000) ≤ -Real.log (5120 / 6747) ∧
    -Real.log (5120 / 6747) ≤ (275943523 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 11867)) (n := 12)
    (lo := (137971761 / 500000000)) (hi := (275943523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6747 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6747 / 5120) = 1/(5120 / 6747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (137971761 / 500000000) (275943523 / 1000000000) (Real.log (6747 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6747 / 5120) = -Real.log (5120 / 6747) := by
    rw [show ((6747 / 5120) : ℝ) = ((5120 / 6747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (382393473 / 1000000000) ≤ -Real.log (3493 / 5120) ∧
    -Real.log (3493 / 5120) ≤ (191196737 / 500000000) := by
  have h := checkLog_sound (w := (1627 / 8613)) (n := 12)
    (lo := (382393473 / 1000000000)) (hi := (191196737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3493) = 1/(3493 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-191196737 / 500000000) (-382393473 / 1000000000) (Real.log (3493 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (275498781 / 1000000000) ≤ -Real.log (640 / 843) ∧
    -Real.log (640 / 843) ≤ (137749391 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1483)) (n := 12)
    (lo := (275498781 / 1000000000)) (hi := (137749391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843 / 640) = 1/(640 / 843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (275498781 / 1000000000) (137749391 / 500000000) (Real.log (843 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (843 / 640) = -Real.log (640 / 843) := by
    rw [show ((843 / 640) : ℝ) = ((640 / 843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (381534981 / 1000000000) ≤ -Real.log (437 / 640) ∧
    -Real.log (437 / 640) ≤ (190767491 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1077)) (n := 12)
    (lo := (381534981 / 1000000000)) (hi := (190767491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 437) = 1/(437 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-190767491 / 500000000) (-381534981 / 1000000000) (Real.log (437 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (122994307 / 250000000) ≤ -Real.log (2560 / 4187) ∧
    -Real.log (2560 / 4187) ≤ (491977229 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 6747)) (n := 12)
    (lo := (122994307 / 250000000)) (hi := (491977229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4187 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4187 / 2560) = 1/(2560 / 4187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (122994307 / 250000000) (491977229 / 1000000000) (Real.log (4187 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4187 / 2560) = -Real.log (2560 / 4187) := by
    rw [show ((4187 / 2560) : ℝ) = ((2560 / 4187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (126169667 / 125000000) ≤ -Real.log (933 / 2560) ∧
    -Real.log (933 / 2560) ≤ (504678669 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2213)) (n := 12)
    (lo := (79052539 / 250000000)) (hi := (316210157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 933) = 1/(933 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-504678669 / 500000000) (-126169667 / 125000000) (Real.log (933 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122815117 / 250000000) ≤ -Real.log (320 / 523) ∧
    -Real.log (320 / 523) ≤ (491260469 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 843)) (n := 12)
    (lo := (122815117 / 250000000)) (hi := (491260469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((523 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(523 / 320) = 1/(320 / 523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122815117 / 250000000) (491260469 / 1000000000) (Real.log (523 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (523 / 320) = -Real.log (320 / 523) := by
    rw [show ((523 / 320) : ℝ) = ((320 / 523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50307353 / 50000000) ≤ -Real.log (117 / 320) ∧
    -Real.log (117 / 320) ≤ (503073531 / 500000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 117) = 1/(117 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-503073531 / 500000000) (-50307353 / 50000000) (Real.log (117 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (376873571 / 1000000000) ≤ -Real.log (25000 / 36443) ∧
    -Real.log (25000 / 36443) ≤ (94218393 / 250000000) := by
  have h := checkLog_sound (w := (11443 / 61443)) (n := 12)
    (lo := (376873571 / 1000000000)) (hi := (94218393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36443 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36443 / 25000) = 1/(25000 / 36443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (376873571 / 1000000000) (94218393 / 250000000) (Real.log (36443 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (36443 / 25000) = -Real.log (25000 / 36443) := by
    rw [show ((36443 / 25000) : ℝ) = ((25000 / 36443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (122394561 / 200000000) ≤ -Real.log (13557 / 25000) ∧
    -Real.log (13557 / 25000) ≤ (305986403 / 500000000) := by
  have h := checkLog_sound (w := (11443 / 38557)) (n := 12)
    (lo := (122394561 / 200000000)) (hi := (305986403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 13557) = 1/(13557 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-305986403 / 500000000) (-122394561 / 200000000) (Real.log (13557 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (94370639 / 250000000) ≤ -Real.log (62500 / 91163) ∧
    -Real.log (62500 / 91163) ≤ (377482557 / 1000000000) := by
  have h := checkLog_sound (w := (28663 / 153663)) (n := 12)
    (lo := (94370639 / 250000000)) (hi := (377482557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91163 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91163 / 62500) = 1/(62500 / 91163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (94370639 / 250000000) (377482557 / 1000000000) (Real.log (91163 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (91163 / 62500) = -Real.log (62500 / 91163) := by
    rw [show ((91163 / 62500) : ℝ) = ((62500 / 91163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (306805839 / 500000000) ≤ -Real.log (33837 / 62500) ∧
    -Real.log (33837 / 62500) ≤ (613611679 / 1000000000) := by
  have h := checkLog_sound (w := (28663 / 96337)) (n := 12)
    (lo := (306805839 / 500000000)) (hi := (613611679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 33837) = 1/(33837 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-613611679 / 1000000000) (-306805839 / 500000000) (Real.log (33837 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (147649867 / 500000000) ≤ -Real.log (1000000 / 1343529) ∧
    -Real.log (1000000 / 1343529) ≤ (59059947 / 200000000) := by
  have h := checkLog_sound (w := (343529 / 2343529)) (n := 12)
    (lo := (147649867 / 500000000)) (hi := (59059947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1343529 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1343529 / 1000000) = 1/(1000000 / 1343529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (147649867 / 500000000) (59059947 / 200000000) (Real.log (1343529 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1343529 / 1000000) = -Real.log (1000000 / 1343529) := by
    rw [show ((1343529 / 1000000) : ℝ) = ((1000000 / 1343529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (420876759 / 1000000000) ≤ -Real.log (656471 / 1000000) ∧
    -Real.log (656471 / 1000000) ≤ (10521919 / 25000000) := by
  have h := checkLog_sound (w := (343529 / 1656471)) (n := 12)
    (lo := (420876759 / 1000000000)) (hi := (10521919 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 656471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 656471) = 1/(656471 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10521919 / 25000000) (-420876759 / 1000000000) (Real.log (656471 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (59171413 / 200000000) ≤ -Real.log (500000 / 672139) ∧
    -Real.log (500000 / 672139) ≤ (147928533 / 500000000) := by
  have h := checkLog_sound (w := (172139 / 1172139)) (n := 12)
    (lo := (59171413 / 200000000)) (hi := (147928533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672139 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(672139 / 500000) = 1/(500000 / 672139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (59171413 / 200000000) (147928533 / 500000000) (Real.log (672139 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (672139 / 500000) = -Real.log (500000 / 672139) := by
    rw [show ((672139 / 500000) : ℝ) = ((500000 / 672139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (10550459 / 25000000) ≤ -Real.log (327861 / 500000) ∧
    -Real.log (327861 / 500000) ≤ (422018361 / 1000000000) := by
  have h := checkLog_sound (w := (172139 / 827861)) (n := 12)
    (lo := (10550459 / 25000000)) (hi := (422018361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 327861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 327861) = 1/(327861 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-422018361 / 1000000000) (-10550459 / 25000000) (Real.log (327861 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (123605797 / 125000000) ≤ -Real.log (500000000000 / 1344065796267) ∧
    -Real.log (500000000000 / 1344065796267) ≤ (494423189 / 500000000) := by
  have h := checkLog_sound (w := (344065796267 / 2344065796267)) (n := 12)
    (lo := (73924799 / 250000000)) (hi := (295699197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1344065796267 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1344065796267 / 1000000000000) = 1/(500000000000 / 1344065796267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (123605797 / 125000000) (494423189 / 500000000) (Real.log (1344065796267 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1344065796267 / 500000000000) = -Real.log (500000000000 / 1344065796267) := by
    rw [show ((1344065796267 / 500000000000) : ℝ) = ((500000000000 / 1344065796267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (495547117 / 500000000) ≤ -Real.log (500000000000 / 1347090463103) ∧
    -Real.log (500000000000 / 1347090463103) ≤ (247773559 / 250000000) := by
  have h := checkLog_sound (w := (347090463103 / 2347090463103)) (n := 12)
    (lo := (148973527 / 500000000)) (hi := (59589411 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347090463103 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1347090463103 / 1000000000000) = 1/(500000000000 / 1347090463103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (495547117 / 500000000) (247773559 / 250000000) (Real.log (1347090463103 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1347090463103 / 500000000000) = -Real.log (500000000000 / 1347090463103) := by
    rw [show ((1347090463103 / 500000000000) : ℝ) = ((500000000000 / 1347090463103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (716176493 / 1000000000) ≤ -Real.log (250000000000 / 511648267783) ∧
    -Real.log (250000000000 / 511648267783) ≤ (143235299 / 200000000) := by
  have h := checkLog_sound (w := (11648267783 / 1011648267783)) (n := 12)
    (lo := (23029313 / 1000000000)) (hi := (11514657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511648267783 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(511648267783 / 500000000000) = 1/(250000000000 / 511648267783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (716176493 / 1000000000) (143235299 / 200000000) (Real.log (511648267783 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (511648267783 / 250000000000) = -Real.log (250000000000 / 511648267783) := by
    rw [show ((511648267783 / 250000000000) : ℝ) = ((250000000000 / 511648267783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (28715017 / 40000000) ≤ -Real.log (4000000000 / 8200292197) ∧
    -Real.log (4000000000 / 8200292197) ≤ (717875427 / 1000000000) := by
  have h := checkLog_sound (w := (200292197 / 16200292197)) (n := 12)
    (lo := (4945649 / 200000000)) (hi := (12364123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8200292197 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8200292197 / 8000000000) = 1/(4000000000 / 8200292197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (28715017 / 40000000) (717875427 / 1000000000) (Real.log (8200292197 / 4000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8200292197 / 4000000000) = -Real.log (4000000000 / 8200292197) := by
    rw [show ((8200292197 / 4000000000) : ℝ) = ((4000000000 / 8200292197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0177

end


