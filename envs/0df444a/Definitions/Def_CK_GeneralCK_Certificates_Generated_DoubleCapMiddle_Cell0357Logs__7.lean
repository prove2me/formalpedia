-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0357Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0357Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:35:30.378889+00:00
-- url     : https://prove2.me/theorems/e2f24674-14bd-4524-a443-42442b7b18d5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0357Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0358Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0357Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0358Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0359Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0360Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0361Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0362Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0363Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0357Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0358Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0359Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0360Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0361Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0362Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0363Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0357Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0358Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0359Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0360Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0361Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0362Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0363Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0357Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0358Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0359Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0360Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0361Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0362Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0363Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0357Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0357
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

theorem reflection_log_1_neg : (52621413 / 250000000) ≤ -Real.log (10240 / 12639) ∧
    -Real.log (10240 / 12639) ≤ (210485653 / 1000000000) := by
  have h := checkLog_sound (w := (2399 / 22879)) (n := 12)
    (lo := (52621413 / 250000000)) (hi := (210485653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12639 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12639 / 10240) = 1/(10240 / 12639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (52621413 / 250000000) (210485653 / 1000000000) (Real.log (12639 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12639 / 10240) = -Real.log (10240 / 12639) := by
    rw [show ((12639 / 10240) : ℝ) = ((10240 / 12639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (133467621 / 500000000) ≤ -Real.log (7841 / 10240) ∧
    -Real.log (7841 / 10240) ≤ (266935243 / 1000000000) := by
  have h := checkLog_sound (w := (2399 / 18081)) (n := 12)
    (lo := (133467621 / 500000000)) (hi := (266935243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7841) = 1/(7841 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-266935243 / 1000000000) (-133467621 / 500000000) (Real.log (7841 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (210248263 / 1000000000) ≤ -Real.log (2560 / 3159) ∧
    -Real.log (2560 / 3159) ≤ (26281033 / 125000000) := by
  have h := checkLog_sound (w := (599 / 5719)) (n := 12)
    (lo := (210248263 / 1000000000)) (hi := (26281033 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3159 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3159 / 2560) = 1/(2560 / 3159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (210248263 / 1000000000) (26281033 / 125000000) (Real.log (3159 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3159 / 2560) = -Real.log (2560 / 3159) := by
    rw [show ((3159 / 2560) : ℝ) = ((2560 / 3159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (266552711 / 1000000000) ≤ -Real.log (1961 / 2560) ∧
    -Real.log (1961 / 2560) ≤ (33319089 / 125000000) := by
  have h := checkLog_sound (w := (599 / 4521)) (n := 12)
    (lo := (266552711 / 1000000000)) (hi := (33319089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1961) = 1/(1961 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33319089 / 125000000) (-266552711 / 1000000000) (Real.log (1961 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (384278711 / 1000000000) ≤ -Real.log (5120 / 7519) ∧
    -Real.log (5120 / 7519) ≤ (48034839 / 125000000) := by
  have h := checkLog_sound (w := (2399 / 12639)) (n := 12)
    (lo := (384278711 / 1000000000)) (hi := (48034839 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7519 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7519 / 5120) = 1/(5120 / 7519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (384278711 / 1000000000) (48034839 / 125000000) (Real.log (7519 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7519 / 5120) = -Real.log (5120 / 7519) := by
    rw [show ((7519 / 5120) : ℝ) = ((5120 / 7519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (632154979 / 1000000000) ≤ -Real.log (2721 / 5120) ∧
    -Real.log (2721 / 5120) ≤ (31607749 / 50000000) := by
  have h := checkLog_sound (w := (2399 / 7841)) (n := 12)
    (lo := (632154979 / 1000000000)) (hi := (31607749 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2721) = 1/(2721 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-31607749 / 50000000) (-632154979 / 1000000000) (Real.log (2721 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (191939821 / 500000000) ≤ -Real.log (1280 / 1879) ∧
    -Real.log (1280 / 1879) ≤ (383879643 / 1000000000) := by
  have h := checkLog_sound (w := (599 / 3159)) (n := 12)
    (lo := (191939821 / 500000000)) (hi := (383879643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1879 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1879 / 1280) = 1/(1280 / 1879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (191939821 / 500000000) (383879643 / 1000000000) (Real.log (1879 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1879 / 1280) = -Real.log (1280 / 1879) := by
    rw [show ((1879 / 1280) : ℝ) = ((1280 / 1879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12621061 / 20000000) ≤ -Real.log (681 / 1280) ∧
    -Real.log (681 / 1280) ≤ (631053051 / 1000000000) := by
  have h := checkLog_sound (w := (599 / 1961)) (n := 12)
    (lo := (12621061 / 20000000)) (hi := (631053051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 681) = 1/(681 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-631053051 / 1000000000) (-12621061 / 20000000) (Real.log (681 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9011167 / 31250000) ≤ -Real.log (500000 / 667117) ∧
    -Real.log (500000 / 667117) ≤ (57671469 / 200000000) := by
  have h := checkLog_sound (w := (167117 / 1167117)) (n := 12)
    (lo := (9011167 / 31250000)) (hi := (57671469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667117 / 500000) = 1/(500000 / 667117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9011167 / 31250000) (57671469 / 200000000) (Real.log (667117 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (667117 / 500000) = -Real.log (500000 / 667117) := by
    rw [show ((667117 / 500000) : ℝ) = ((500000 / 667117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (406817021 / 1000000000) ≤ -Real.log (332883 / 500000) ∧
    -Real.log (332883 / 500000) ≤ (203408511 / 500000000) := by
  have h := checkLog_sound (w := (167117 / 832883)) (n := 12)
    (lo := (406817021 / 1000000000)) (hi := (203408511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 332883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 332883) = 1/(332883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-203408511 / 500000000) (-406817021 / 1000000000) (Real.log (332883 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (11547153 / 40000000) ≤ -Real.log (1000000 / 1334663) ∧
    -Real.log (1000000 / 1334663) ≤ (144339413 / 500000000) := by
  have h := checkLog_sound (w := (334663 / 2334663)) (n := 12)
    (lo := (11547153 / 40000000)) (hi := (144339413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1334663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1334663 / 1000000) = 1/(1000000 / 1334663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (11547153 / 40000000) (144339413 / 500000000) (Real.log (1334663 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1334663 / 1000000) = -Real.log (1000000 / 1334663) := by
    rw [show ((1334663 / 1000000) : ℝ) = ((1000000 / 1334663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (407461599 / 1000000000) ≤ -Real.log (665337 / 1000000) ∧
    -Real.log (665337 / 1000000) ≤ (509327 / 1250000) := by
  have h := checkLog_sound (w := (334663 / 1665337)) (n := 12)
    (lo := (407461599 / 1000000000)) (hi := (509327 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 665337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 665337) = 1/(665337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-509327 / 1250000) (-407461599 / 1000000000) (Real.log (665337 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (109117361 / 500000000) ≤ -Real.log (1000000 / 1243879) ∧
    -Real.log (1000000 / 1243879) ≤ (218234723 / 1000000000) := by
  have h := checkLog_sound (w := (243879 / 2243879)) (n := 12)
    (lo := (109117361 / 500000000)) (hi := (218234723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243879 / 1000000) = 1/(1000000 / 1243879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (109117361 / 500000000) (218234723 / 1000000000) (Real.log (1243879 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1243879 / 1000000) = -Real.log (1000000 / 1243879) := by
    rw [show ((1243879 / 1000000) : ℝ) = ((1000000 / 1243879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (139776931 / 500000000) ≤ -Real.log (756121 / 1000000) ∧
    -Real.log (756121 / 1000000) ≤ (279553863 / 1000000000) := by
  have h := checkLog_sound (w := (243879 / 1756121)) (n := 12)
    (lo := (139776931 / 500000000)) (hi := (279553863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 756121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 756121) = 1/(756121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-279553863 / 1000000000) (-139776931 / 500000000) (Real.log (756121 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (218502397 / 1000000000) ≤ -Real.log (250000 / 311053) ∧
    -Real.log (250000 / 311053) ≤ (109251199 / 500000000) := by
  have h := checkLog_sound (w := (61053 / 561053)) (n := 12)
    (lo := (218502397 / 1000000000)) (hi := (109251199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311053 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311053 / 250000) = 1/(250000 / 311053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (218502397 / 1000000000) (109251199 / 500000000) (Real.log (311053 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (311053 / 250000) = -Real.log (250000 / 311053) := by
    rw [show ((311053 / 250000) : ℝ) = ((250000 / 311053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55998873 / 200000000) ≤ -Real.log (188947 / 250000) ∧
    -Real.log (188947 / 250000) ≤ (139997183 / 500000000) := by
  have h := checkLog_sound (w := (61053 / 438947)) (n := 12)
    (lo := (55998873 / 200000000)) (hi := (139997183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188947) = 1/(188947 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-139997183 / 500000000) (-55998873 / 200000000) (Real.log (188947 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (139034873 / 200000000) ≤ -Real.log (100000000000 / 200405848301) ∧
    -Real.log (100000000000 / 200405848301) ≤ (695174367 / 1000000000) := by
  have h := checkLog_sound (w := (405848301 / 400405848301)) (n := 12)
    (lo := (405437 / 200000000)) (hi := (1013593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200405848301 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200405848301 / 200000000000) = 1/(100000000000 / 200405848301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (139034873 / 200000000) (695174367 / 1000000000) (Real.log (200405848301 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (200405848301 / 100000000000) = -Real.log (100000000000 / 200405848301) := by
    rw [show ((200405848301 / 100000000000) : ℝ) = ((100000000000 / 200405848301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (87017553 / 125000000) ≤ -Real.log (500000000000 / 1002997728971) ∧
    -Real.log (500000000000 / 1002997728971) ≤ (348070213 / 500000000) := by
  have h := checkLog_sound (w := (2997728971 / 2002997728971)) (n := 12)
    (lo := (748311 / 250000000)) (hi := (598649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1002997728971 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1002997728971 / 1000000000000) = 1/(500000000000 / 1002997728971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (87017553 / 125000000) (348070213 / 500000000) (Real.log (1002997728971 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1002997728971 / 500000000000) = -Real.log (500000000000 / 1002997728971) := by
    rw [show ((1002997728971 / 500000000000) : ℝ) = ((500000000000 / 1002997728971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (99557717 / 200000000) ≤ -Real.log (15625000000 / 25704363951) ∧
    -Real.log (15625000000 / 25704363951) ≤ (248894293 / 500000000) := by
  have h := checkLog_sound (w := (10079363951 / 41329363951)) (n := 12)
    (lo := (99557717 / 200000000)) (hi := (248894293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25704363951 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25704363951 / 15625000000) = 1/(15625000000 / 25704363951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (99557717 / 200000000) (248894293 / 500000000) (Real.log (25704363951 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (25704363951 / 15625000000) = -Real.log (15625000000 / 25704363951) := by
    rw [show ((25704363951 / 15625000000) : ℝ) = ((15625000000 / 25704363951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (498496763 / 1000000000) ≤ -Real.log (62500000000 / 102890294633) ∧
    -Real.log (62500000000 / 102890294633) ≤ (124624191 / 250000000) := by
  have h := checkLog_sound (w := (40390294633 / 165390294633)) (n := 12)
    (lo := (498496763 / 1000000000)) (hi := (124624191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102890294633 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102890294633 / 62500000000) = 1/(62500000000 / 102890294633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (498496763 / 1000000000) (124624191 / 250000000) (Real.log (102890294633 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (102890294633 / 62500000000) = -Real.log (62500000000 / 102890294633) := by
    rw [show ((102890294633 / 62500000000) : ℝ) = ((62500000000 / 102890294633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0357

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0358Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0358
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

theorem reflection_log_1_neg : (210248263 / 1000000000) ≤ -Real.log (2560 / 3159) ∧
    -Real.log (2560 / 3159) ≤ (26281033 / 125000000) := by
  have h := checkLog_sound (w := (599 / 5719)) (n := 12)
    (lo := (210248263 / 1000000000)) (hi := (26281033 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3159 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3159 / 2560) = 1/(2560 / 3159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (210248263 / 1000000000) (26281033 / 125000000) (Real.log (3159 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3159 / 2560) = -Real.log (2560 / 3159) := by
    rw [show ((3159 / 2560) : ℝ) = ((2560 / 3159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (266552711 / 1000000000) ≤ -Real.log (1961 / 2560) ∧
    -Real.log (1961 / 2560) ≤ (33319089 / 125000000) := by
  have h := checkLog_sound (w := (599 / 4521)) (n := 12)
    (lo := (266552711 / 1000000000)) (hi := (33319089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1961) = 1/(1961 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33319089 / 125000000) (-266552711 / 1000000000) (Real.log (1961 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (105005409 / 500000000) ≤ -Real.log (10240 / 12633) ∧
    -Real.log (10240 / 12633) ≤ (210010819 / 1000000000) := by
  have h := checkLog_sound (w := (2393 / 22873)) (n := 12)
    (lo := (105005409 / 500000000)) (hi := (210010819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12633 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12633 / 10240) = 1/(10240 / 12633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (105005409 / 500000000) (210010819 / 1000000000) (Real.log (12633 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12633 / 10240) = -Real.log (10240 / 12633) := by
    rw [show ((12633 / 10240) : ℝ) = ((10240 / 12633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (133085163 / 500000000) ≤ -Real.log (7847 / 10240) ∧
    -Real.log (7847 / 10240) ≤ (266170327 / 1000000000) := by
  have h := checkLog_sound (w := (2393 / 18087)) (n := 12)
    (lo := (133085163 / 500000000)) (hi := (266170327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7847) = 1/(7847 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-266170327 / 1000000000) (-133085163 / 500000000) (Real.log (7847 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (191939821 / 500000000) ≤ -Real.log (1280 / 1879) ∧
    -Real.log (1280 / 1879) ≤ (383879643 / 1000000000) := by
  have h := checkLog_sound (w := (599 / 3159)) (n := 12)
    (lo := (191939821 / 500000000)) (hi := (383879643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1879 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1879 / 1280) = 1/(1280 / 1879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (191939821 / 500000000) (383879643 / 1000000000) (Real.log (1879 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1879 / 1280) = -Real.log (1280 / 1879) := by
    rw [show ((1879 / 1280) : ℝ) = ((1280 / 1879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12621061 / 20000000) ≤ -Real.log (681 / 1280) ∧
    -Real.log (681 / 1280) ≤ (631053051 / 1000000000) := by
  have h := checkLog_sound (w := (599 / 1961)) (n := 12)
    (lo := (12621061 / 20000000)) (hi := (631053051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 681) = 1/(681 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-631053051 / 1000000000) (-12621061 / 20000000) (Real.log (681 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (191740207 / 500000000) ≤ -Real.log (5120 / 7513) ∧
    -Real.log (5120 / 7513) ≤ (76696083 / 200000000) := by
  have h := checkLog_sound (w := (2393 / 12633)) (n := 12)
    (lo := (191740207 / 500000000)) (hi := (76696083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7513 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7513 / 5120) = 1/(5120 / 7513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (191740207 / 500000000) (76696083 / 200000000) (Real.log (7513 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7513 / 5120) = -Real.log (5120 / 7513) := by
    rw [show ((7513 / 5120) : ℝ) = ((5120 / 7513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (125990467 / 200000000) ≤ -Real.log (2727 / 5120) ∧
    -Real.log (2727 / 5120) ≤ (39372021 / 62500000) := by
  have h := checkLog_sound (w := (2393 / 7847)) (n := 12)
    (lo := (125990467 / 200000000)) (hi := (39372021 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2727) = 1/(2727 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-39372021 / 62500000) (-125990467 / 200000000) (Real.log (2727 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (288036509 / 1000000000) ≤ -Real.log (500000 / 666903) ∧
    -Real.log (500000 / 666903) ≤ (28803651 / 100000000) := by
  have h := checkLog_sound (w := (166903 / 1166903)) (n := 12)
    (lo := (288036509 / 1000000000)) (hi := (28803651 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666903 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666903 / 500000) = 1/(500000 / 666903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (288036509 / 1000000000) (28803651 / 100000000) (Real.log (666903 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (666903 / 500000) = -Real.log (500000 / 666903) := by
    rw [show ((666903 / 500000) : ℝ) = ((500000 / 666903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (406174359 / 1000000000) ≤ -Real.log (333097 / 500000) ∧
    -Real.log (333097 / 500000) ≤ (10154359 / 25000000) := by
  have h := checkLog_sound (w := (166903 / 833097)) (n := 12)
    (lo := (406174359 / 1000000000)) (hi := (10154359 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 333097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 333097) = 1/(333097 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-10154359 / 25000000) (-406174359 / 1000000000) (Real.log (333097 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (288358093 / 1000000000) ≤ -Real.log (200000 / 266847) ∧
    -Real.log (200000 / 266847) ≤ (144179047 / 500000000) := by
  have h := checkLog_sound (w := (66847 / 466847)) (n := 12)
    (lo := (288358093 / 1000000000)) (hi := (144179047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266847 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(266847 / 200000) = 1/(200000 / 266847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (288358093 / 1000000000) (144179047 / 500000000) (Real.log (266847 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (266847 / 200000) = -Real.log (200000 / 266847) := by
    rw [show ((266847 / 200000) : ℝ) = ((200000 / 266847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (406818523 / 1000000000) ≤ -Real.log (133153 / 200000) ∧
    -Real.log (133153 / 200000) ≤ (101704631 / 250000000) := by
  have h := checkLog_sound (w := (66847 / 333153)) (n := 12)
    (lo := (406818523 / 1000000000)) (hi := (101704631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 133153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 133153) = 1/(133153 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-101704631 / 250000000) (-406818523 / 1000000000) (Real.log (133153 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10898389 / 50000000) ≤ -Real.log (1000000 / 1243547) ∧
    -Real.log (1000000 / 1243547) ≤ (217967781 / 1000000000) := by
  have h := checkLog_sound (w := (243547 / 2243547)) (n := 12)
    (lo := (10898389 / 50000000)) (hi := (217967781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243547 / 1000000) = 1/(1000000 / 1243547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10898389 / 50000000) (217967781 / 1000000000) (Real.log (1243547 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1243547 / 1000000) = -Real.log (1000000 / 1243547) := by
    rw [show ((1243547 / 1000000) : ℝ) = ((1000000 / 1243547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2232919 / 8000000) ≤ -Real.log (756453 / 1000000) ∧
    -Real.log (756453 / 1000000) ≤ (69778719 / 250000000) := by
  have h := checkLog_sound (w := (243547 / 1756453)) (n := 12)
    (lo := (2232919 / 8000000)) (hi := (69778719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 756453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 756453) = 1/(756453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-69778719 / 250000000) (-2232919 / 8000000) (Real.log (756453 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (109117763 / 500000000) ≤ -Real.log (25000 / 31097) ∧
    -Real.log (25000 / 31097) ≤ (218235527 / 1000000000) := by
  have h := checkLog_sound (w := (6097 / 56097)) (n := 12)
    (lo := (109117763 / 500000000)) (hi := (218235527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31097 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31097 / 25000) = 1/(25000 / 31097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (109117763 / 500000000) (218235527 / 1000000000) (Real.log (31097 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (31097 / 25000) = -Real.log (25000 / 31097) := by
    rw [show ((31097 / 25000) : ℝ) = ((25000 / 31097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55911037 / 200000000) ≤ -Real.log (18903 / 25000) ∧
    -Real.log (18903 / 25000) ≤ (139777593 / 500000000) := by
  have h := checkLog_sound (w := (6097 / 43903)) (n := 12)
    (lo := (55911037 / 200000000)) (hi := (139777593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 18903) = 1/(18903 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-139777593 / 500000000) (-55911037 / 200000000) (Real.log (18903 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (173552717 / 250000000) ≤ -Real.log (125000000000 / 250266063639) ∧
    -Real.log (125000000000 / 250266063639) ≤ (69421087 / 100000000) := by
  have h := checkLog_sound (w := (266063639 / 500266063639)) (n := 12)
    (lo := (132961 / 125000000)) (hi := (1063689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250266063639 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250266063639 / 250000000000) = 1/(125000000000 / 250266063639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (173552717 / 250000000) (69421087 / 100000000) (Real.log (250266063639 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (250266063639 / 125000000000) = -Real.log (125000000000 / 250266063639) := by
    rw [show ((250266063639 / 125000000000) : ℝ) = ((125000000000 / 250266063639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (86897077 / 125000000) ≤ -Real.log (500000000000 / 1002031497601) ∧
    -Real.log (500000000000 / 1002031497601) ≤ (347588309 / 500000000) := by
  have h := checkLog_sound (w := (2031497601 / 2002031497601)) (n := 12)
    (lo := (507359 / 250000000)) (hi := (2029437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1002031497601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1002031497601 / 1000000000000) = 1/(500000000000 / 1002031497601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (86897077 / 125000000) (347588309 / 500000000) (Real.log (1002031497601 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1002031497601 / 500000000000) = -Real.log (500000000000 / 1002031497601) := by
    rw [show ((1002031497601 / 500000000000) : ℝ) = ((500000000000 / 1002031497601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (99416531 / 200000000) ≤ -Real.log (500000000000 / 821959196407) ∧
    -Real.log (500000000000 / 821959196407) ≤ (15533833 / 31250000) := by
  have h := checkLog_sound (w := (321959196407 / 1321959196407)) (n := 12)
    (lo := (99416531 / 200000000)) (hi := (15533833 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821959196407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821959196407 / 500000000000) = 1/(500000000000 / 821959196407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (99416531 / 200000000) (15533833 / 31250000) (Real.log (821959196407 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (821959196407 / 500000000000) = -Real.log (500000000000 / 821959196407) := by
    rw [show ((821959196407 / 500000000000) : ℝ) = ((500000000000 / 821959196407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (497790711 / 1000000000) ≤ -Real.log (250000000000 / 411270697773) ∧
    -Real.log (250000000000 / 411270697773) ≤ (62223839 / 125000000) := by
  have h := checkLog_sound (w := (161270697773 / 661270697773)) (n := 12)
    (lo := (497790711 / 1000000000)) (hi := (62223839 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411270697773 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411270697773 / 250000000000) = 1/(250000000000 / 411270697773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (497790711 / 1000000000) (62223839 / 125000000) (Real.log (411270697773 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (411270697773 / 250000000000) = -Real.log (250000000000 / 411270697773) := by
    rw [show ((411270697773 / 250000000000) : ℝ) = ((250000000000 / 411270697773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0358

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0359Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0359
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

theorem reflection_log_1_neg : (105005409 / 500000000) ≤ -Real.log (10240 / 12633) ∧
    -Real.log (10240 / 12633) ≤ (210010819 / 1000000000) := by
  have h := checkLog_sound (w := (2393 / 22873)) (n := 12)
    (lo := (105005409 / 500000000)) (hi := (210010819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12633 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12633 / 10240) = 1/(10240 / 12633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (105005409 / 500000000) (210010819 / 1000000000) (Real.log (12633 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12633 / 10240) = -Real.log (10240 / 12633) := by
    rw [show ((12633 / 10240) : ℝ) = ((10240 / 12633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (133085163 / 500000000) ≤ -Real.log (7847 / 10240) ∧
    -Real.log (7847 / 10240) ≤ (266170327 / 1000000000) := by
  have h := checkLog_sound (w := (2393 / 18087)) (n := 12)
    (lo := (133085163 / 500000000)) (hi := (266170327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7847) = 1/(7847 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-266170327 / 1000000000) (-133085163 / 500000000) (Real.log (7847 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (52443329 / 250000000) ≤ -Real.log (1024 / 1263) ∧
    -Real.log (1024 / 1263) ≤ (209773317 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 2287)) (n := 12)
    (lo := (52443329 / 250000000)) (hi := (209773317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1263 / 1024) = 1/(1024 / 1263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (52443329 / 250000000) (209773317 / 1000000000) (Real.log (1263 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1263 / 1024) = -Real.log (1024 / 1263) := by
    rw [show ((1263 / 1024) : ℝ) = ((1024 / 1263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (265788087 / 1000000000) ≤ -Real.log (785 / 1024) ∧
    -Real.log (785 / 1024) ≤ (33223511 / 125000000) := by
  have h := checkLog_sound (w := (239 / 1809)) (n := 12)
    (lo := (265788087 / 1000000000)) (hi := (33223511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 785) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 785) = 1/(785 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33223511 / 125000000) (-265788087 / 1000000000) (Real.log (785 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (191740207 / 500000000) ≤ -Real.log (5120 / 7513) ∧
    -Real.log (5120 / 7513) ≤ (76696083 / 200000000) := by
  have h := checkLog_sound (w := (2393 / 12633)) (n := 12)
    (lo := (191740207 / 500000000)) (hi := (76696083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7513 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7513 / 5120) = 1/(5120 / 7513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (191740207 / 500000000) (76696083 / 200000000) (Real.log (7513 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7513 / 5120) = -Real.log (5120 / 7513) := by
    rw [show ((7513 / 5120) : ℝ) = ((5120 / 7513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (125990467 / 200000000) ≤ -Real.log (2727 / 5120) ∧
    -Real.log (2727 / 5120) ≤ (39372021 / 62500000) := by
  have h := checkLog_sound (w := (2393 / 7847)) (n := 12)
    (lo := (125990467 / 200000000)) (hi := (39372021 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2727) = 1/(2727 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-39372021 / 62500000) (-125990467 / 200000000) (Real.log (2727 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (191540513 / 500000000) ≤ -Real.log (512 / 751) ∧
    -Real.log (512 / 751) ≤ (383081027 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 1263)) (n := 12)
    (lo := (191540513 / 500000000)) (hi := (383081027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751 / 512) = 1/(512 / 751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (191540513 / 500000000) (383081027 / 1000000000) (Real.log (751 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (751 / 512) = -Real.log (512 / 751) := by
    rw [show ((751 / 512) : ℝ) = ((512 / 751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (628852829 / 1000000000) ≤ -Real.log (273 / 512) ∧
    -Real.log (273 / 512) ≤ (62885283 / 100000000) := by
  have h := checkLog_sound (w := (239 / 785)) (n := 12)
    (lo := (628852829 / 1000000000)) (hi := (62885283 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 273) = 1/(273 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-62885283 / 100000000) (-628852829 / 1000000000) (Real.log (273 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (287716321 / 1000000000) ≤ -Real.log (1000000 / 1333379) ∧
    -Real.log (1000000 / 1333379) ≤ (143858161 / 500000000) := by
  have h := checkLog_sound (w := (333379 / 2333379)) (n := 12)
    (lo := (287716321 / 1000000000)) (hi := (143858161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1333379 / 1000000) = 1/(1000000 / 1333379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (287716321 / 1000000000) (143858161 / 500000000) (Real.log (1333379 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1333379 / 1000000) = -Real.log (1000000 / 1333379) := by
    rw [show ((1333379 / 1000000) : ℝ) = ((1000000 / 1333379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (40553361 / 100000000) ≤ -Real.log (666621 / 1000000) ∧
    -Real.log (666621 / 1000000) ≤ (405533611 / 1000000000) := by
  have h := checkLog_sound (w := (333379 / 1666621)) (n := 12)
    (lo := (40553361 / 100000000)) (hi := (405533611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 666621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 666621) = 1/(666621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-405533611 / 1000000000) (-40553361 / 100000000) (Real.log (666621 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (288037259 / 1000000000) ≤ -Real.log (1000000 / 1333807) ∧
    -Real.log (1000000 / 1333807) ≤ (14401863 / 50000000) := by
  have h := checkLog_sound (w := (333807 / 2333807)) (n := 12)
    (lo := (288037259 / 1000000000)) (hi := (14401863 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1333807 / 1000000) = 1/(1000000 / 1333807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (288037259 / 1000000000) (14401863 / 50000000) (Real.log (1333807 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1333807 / 1000000) = -Real.log (1000000 / 1333807) := by
    rw [show ((1333807 / 1000000) : ℝ) = ((1000000 / 1333807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (20308793 / 50000000) ≤ -Real.log (666193 / 1000000) ∧
    -Real.log (666193 / 1000000) ≤ (406175861 / 1000000000) := by
  have h := checkLog_sound (w := (333807 / 1666193)) (n := 12)
    (lo := (20308793 / 50000000)) (hi := (406175861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 666193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 666193) = 1/(666193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-406175861 / 1000000000) (-20308793 / 50000000) (Real.log (666193 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (108850383 / 500000000) ≤ -Real.log (200000 / 248643) ∧
    -Real.log (200000 / 248643) ≤ (217700767 / 1000000000) := by
  have h := checkLog_sound (w := (48643 / 448643)) (n := 12)
    (lo := (108850383 / 500000000)) (hi := (217700767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248643 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248643 / 200000) = 1/(200000 / 248643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (108850383 / 500000000) (217700767 / 1000000000) (Real.log (248643 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (248643 / 200000) = -Real.log (200000 / 248643) := by
    rw [show ((248643 / 200000) : ℝ) = ((200000 / 248643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (278676081 / 1000000000) ≤ -Real.log (151357 / 200000) ∧
    -Real.log (151357 / 200000) ≤ (139338041 / 500000000) := by
  have h := checkLog_sound (w := (48643 / 351357)) (n := 12)
    (lo := (278676081 / 1000000000)) (hi := (139338041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151357) = 1/(151357 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-139338041 / 500000000) (-278676081 / 1000000000) (Real.log (151357 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (27246073 / 125000000) ≤ -Real.log (250000 / 310887) ∧
    -Real.log (250000 / 310887) ≤ (43593717 / 200000000) := by
  have h := checkLog_sound (w := (60887 / 560887)) (n := 12)
    (lo := (27246073 / 125000000)) (hi := (43593717 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310887 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310887 / 250000) = 1/(250000 / 310887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (27246073 / 125000000) (43593717 / 200000000) (Real.log (310887 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (310887 / 250000) = -Real.log (250000 / 310887) := by
    rw [show ((310887 / 250000) : ℝ) = ((250000 / 310887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (279116197 / 1000000000) ≤ -Real.log (189113 / 250000) ∧
    -Real.log (189113 / 250000) ≤ (139558099 / 500000000) := by
  have h := checkLog_sound (w := (60887 / 439113)) (n := 12)
    (lo := (279116197 / 1000000000)) (hi := (139558099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 189113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 189113) = 1/(189113 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-139558099 / 500000000) (-279116197 / 1000000000) (Real.log (189113 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (693249931 / 1000000000) ≤ -Real.log (250000000000 / 500051378519) ∧
    -Real.log (250000000000 / 500051378519) ≤ (693249933 / 1000000000) := by
  have h := checkLog_sound (w := (51378519 / 1000051378519)) (n := 12)
    (lo := (102751 / 1000000000)) (hi := (3211 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500051378519 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500051378519 / 500000000000) = 1/(250000000000 / 500051378519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (693249931 / 1000000000) (693249933 / 1000000000) (Real.log (500051378519 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (500051378519 / 250000000000) = -Real.log (250000000000 / 500051378519) := by
    rw [show ((500051378519 / 250000000000) : ℝ) = ((250000000000 / 500051378519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (694213119 / 1000000000) ≤ -Real.log (250000000000 / 500533253877) ∧
    -Real.log (250000000000 / 500533253877) ≤ (694213121 / 1000000000) := by
  have h := checkLog_sound (w := (533253877 / 1000533253877)) (n := 12)
    (lo := (1065939 / 1000000000)) (hi := (53297 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500533253877 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500533253877 / 500000000000) = 1/(250000000000 / 500533253877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (694213119 / 1000000000) (694213121 / 1000000000) (Real.log (500533253877 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (500533253877 / 250000000000) = -Real.log (250000000000 / 500533253877) := by
    rw [show ((500533253877 / 250000000000) : ℝ) = ((250000000000 / 500533253877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (496376847 / 1000000000) ≤ -Real.log (500000000000 / 821379255667) ∧
    -Real.log (500000000000 / 821379255667) ≤ (31023553 / 62500000) := by
  have h := checkLog_sound (w := (321379255667 / 1321379255667)) (n := 12)
    (lo := (496376847 / 1000000000)) (hi := (31023553 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821379255667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821379255667 / 500000000000) = 1/(500000000000 / 821379255667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (496376847 / 1000000000) (31023553 / 62500000) (Real.log (821379255667 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (821379255667 / 500000000000) = -Real.log (500000000000 / 821379255667) := by
    rw [show ((821379255667 / 500000000000) : ℝ) = ((500000000000 / 821379255667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (248542391 / 500000000) ≤ -Real.log (250000000000 / 410980471993) ∧
    -Real.log (250000000000 / 410980471993) ≤ (497084783 / 1000000000) := by
  have h := checkLog_sound (w := (160980471993 / 660980471993)) (n := 12)
    (lo := (248542391 / 500000000)) (hi := (497084783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410980471993 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410980471993 / 250000000000) = 1/(250000000000 / 410980471993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (248542391 / 500000000) (497084783 / 1000000000) (Real.log (410980471993 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (410980471993 / 250000000000) = -Real.log (250000000000 / 410980471993) := by
    rw [show ((410980471993 / 250000000000) : ℝ) = ((250000000000 / 410980471993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0359

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0360Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0360
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

theorem reflection_log_1_neg : (52443329 / 250000000) ≤ -Real.log (1024 / 1263) ∧
    -Real.log (1024 / 1263) ≤ (209773317 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 2287)) (n := 12)
    (lo := (52443329 / 250000000)) (hi := (209773317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1263 / 1024) = 1/(1024 / 1263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (52443329 / 250000000) (209773317 / 1000000000) (Real.log (1263 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1263 / 1024) = -Real.log (1024 / 1263) := by
    rw [show ((1263 / 1024) : ℝ) = ((1024 / 1263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (265788087 / 1000000000) ≤ -Real.log (785 / 1024) ∧
    -Real.log (785 / 1024) ≤ (33223511 / 125000000) := by
  have h := checkLog_sound (w := (239 / 1809)) (n := 12)
    (lo := (265788087 / 1000000000)) (hi := (33223511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 785) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 785) = 1/(785 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33223511 / 125000000) (-265788087 / 1000000000) (Real.log (785 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (104767879 / 500000000) ≤ -Real.log (10240 / 12627) ∧
    -Real.log (10240 / 12627) ≤ (209535759 / 1000000000) := by
  have h := checkLog_sound (w := (2387 / 22867)) (n := 12)
    (lo := (104767879 / 500000000)) (hi := (209535759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12627 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12627 / 10240) = 1/(10240 / 12627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (104767879 / 500000000) (209535759 / 1000000000) (Real.log (12627 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12627 / 10240) = -Real.log (10240 / 12627) := by
    rw [show ((12627 / 10240) : ℝ) = ((10240 / 12627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (53081199 / 200000000) ≤ -Real.log (7853 / 10240) ∧
    -Real.log (7853 / 10240) ≤ (66351499 / 250000000) := by
  have h := checkLog_sound (w := (2387 / 18093)) (n := 12)
    (lo := (53081199 / 200000000)) (hi := (66351499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7853) = 1/(7853 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-66351499 / 250000000) (-53081199 / 200000000) (Real.log (7853 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (191540513 / 500000000) ≤ -Real.log (512 / 751) ∧
    -Real.log (512 / 751) ≤ (383081027 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 1263)) (n := 12)
    (lo := (191540513 / 500000000)) (hi := (383081027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751 / 512) = 1/(512 / 751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (191540513 / 500000000) (383081027 / 1000000000) (Real.log (751 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (751 / 512) = -Real.log (512 / 751) := by
    rw [show ((751 / 512) : ℝ) = ((512 / 751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (628852829 / 1000000000) ≤ -Real.log (273 / 512) ∧
    -Real.log (273 / 512) ≤ (62885283 / 100000000) := by
  have h := checkLog_sound (w := (239 / 785)) (n := 12)
    (lo := (628852829 / 1000000000)) (hi := (62885283 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 273) = 1/(273 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-62885283 / 100000000) (-628852829 / 1000000000) (Real.log (273 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (382681479 / 1000000000) ≤ -Real.log (5120 / 7507) ∧
    -Real.log (5120 / 7507) ≤ (9567037 / 25000000) := by
  have h := checkLog_sound (w := (2387 / 12627)) (n := 12)
    (lo := (382681479 / 1000000000)) (hi := (9567037 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7507 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7507 / 5120) = 1/(5120 / 7507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (382681479 / 1000000000) (9567037 / 25000000) (Real.log (7507 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7507 / 5120) = -Real.log (5120 / 7507) := by
    rw [show ((7507 / 5120) : ℝ) = ((5120 / 7507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (156938633 / 250000000) ≤ -Real.log (2733 / 5120) ∧
    -Real.log (2733 / 5120) ≤ (627754533 / 1000000000) := by
  have h := checkLog_sound (w := (2387 / 7853)) (n := 12)
    (lo := (156938633 / 250000000)) (hi := (627754533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2733) = 1/(2733 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-627754533 / 1000000000) (-156938633 / 250000000) (Real.log (2733 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (287395281 / 1000000000) ≤ -Real.log (1000000 / 1332951) ∧
    -Real.log (1000000 / 1332951) ≤ (143697641 / 500000000) := by
  have h := checkLog_sound (w := (332951 / 2332951)) (n := 12)
    (lo := (287395281 / 1000000000)) (hi := (143697641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1332951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1332951 / 1000000) = 1/(1000000 / 1332951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (287395281 / 1000000000) (143697641 / 500000000) (Real.log (1332951 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1332951 / 1000000) = -Real.log (1000000 / 1332951) := by
    rw [show ((1332951 / 1000000) : ℝ) = ((1000000 / 1332951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (101222943 / 250000000) ≤ -Real.log (667049 / 1000000) ∧
    -Real.log (667049 / 1000000) ≤ (404891773 / 1000000000) := by
  have h := checkLog_sound (w := (332951 / 1667049)) (n := 12)
    (lo := (101222943 / 250000000)) (hi := (404891773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 667049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 667049) = 1/(667049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-404891773 / 1000000000) (-101222943 / 250000000) (Real.log (667049 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (287717071 / 1000000000) ≤ -Real.log (50000 / 66669) ∧
    -Real.log (50000 / 66669) ≤ (17982317 / 62500000) := by
  have h := checkLog_sound (w := (16669 / 116669)) (n := 12)
    (lo := (287717071 / 1000000000)) (hi := (17982317 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66669 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66669 / 50000) = 1/(50000 / 66669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (287717071 / 1000000000) (17982317 / 62500000) (Real.log (66669 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (66669 / 50000) = -Real.log (50000 / 66669) := by
    rw [show ((66669 / 50000) : ℝ) = ((50000 / 66669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (40553511 / 100000000) ≤ -Real.log (33331 / 50000) ∧
    -Real.log (33331 / 50000) ≤ (405535111 / 1000000000) := by
  have h := checkLog_sound (w := (16669 / 83331)) (n := 12)
    (lo := (40553511 / 100000000)) (hi := (405535111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33331) = 1/(33331 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-405535111 / 1000000000) (-40553511 / 100000000) (Real.log (33331 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (43486897 / 200000000) ≤ -Real.log (250000 / 310721) ∧
    -Real.log (250000 / 310721) ≤ (108717243 / 500000000) := by
  have h := checkLog_sound (w := (60721 / 560721)) (n := 12)
    (lo := (43486897 / 200000000)) (hi := (108717243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310721 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310721 / 250000) = 1/(250000 / 310721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (43486897 / 200000000) (108717243 / 500000000) (Real.log (310721 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (310721 / 250000) = -Real.log (250000 / 310721) := by
    rw [show ((310721 / 250000) : ℝ) = ((250000 / 310721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (695597 / 2500000) ≤ -Real.log (189279 / 250000) ∧
    -Real.log (189279 / 250000) ≤ (278238801 / 1000000000) := by
  have h := checkLog_sound (w := (60721 / 439279)) (n := 12)
    (lo := (695597 / 2500000)) (hi := (278238801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 189279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 189279) = 1/(189279 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-278238801 / 1000000000) (-695597 / 2500000) (Real.log (189279 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21770157 / 100000000) ≤ -Real.log (62500 / 77701) ∧
    -Real.log (62500 / 77701) ≤ (217701571 / 1000000000) := by
  have h := checkLog_sound (w := (15201 / 140201)) (n := 12)
    (lo := (21770157 / 100000000)) (hi := (217701571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77701 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77701 / 62500) = 1/(62500 / 77701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21770157 / 100000000) (217701571 / 1000000000) (Real.log (77701 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (77701 / 62500) = -Real.log (62500 / 77701) := by
    rw [show ((77701 / 62500) : ℝ) = ((62500 / 77701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (278677403 / 1000000000) ≤ -Real.log (47299 / 62500) ∧
    -Real.log (47299 / 62500) ≤ (69669351 / 250000000) := by
  have h := checkLog_sound (w := (15201 / 109799)) (n := 12)
    (lo := (278677403 / 1000000000)) (hi := (69669351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 47299) = 1/(47299 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-69669351 / 250000000) (-278677403 / 1000000000) (Real.log (47299 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (692287053 / 1000000000) ≤ -Real.log (50000000000 / 99914024307) ∧
    -Real.log (50000000000 / 99914024307) ≤ (346143527 / 500000000) := by
  have h := checkLog_sound (w := (49914024307 / 149914024307)) (n := 12)
    (lo := (692287053 / 1000000000)) (hi := (346143527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99914024307 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99914024307 / 50000000000) = 1/(50000000000 / 99914024307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (692287053 / 1000000000) (346143527 / 500000000) (Real.log (99914024307 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (99914024307 / 50000000000) = -Real.log (50000000000 / 99914024307) := by
    rw [show ((99914024307 / 50000000000) : ℝ) = ((50000000000 / 99914024307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (693252181 / 1000000000) ≤ -Real.log (500000000000 / 1000105007351) ∧
    -Real.log (500000000000 / 1000105007351) ≤ (693252183 / 1000000000) := by
  have h := checkLog_sound (w := (105007351 / 2000105007351)) (n := 12)
    (lo := (105001 / 1000000000)) (hi := (52501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000105007351 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1000105007351 / 1000000000000) = 1/(500000000000 / 1000105007351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (693252181 / 1000000000) (693252183 / 1000000000) (Real.log (1000105007351 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1000105007351 / 500000000000) = -Real.log (500000000000 / 1000105007351) := by
    rw [show ((1000105007351 / 500000000000) : ℝ) = ((500000000000 / 1000105007351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (247836643 / 500000000) ≤ -Real.log (100000000000 / 164160313611) ∧
    -Real.log (100000000000 / 164160313611) ≤ (495673287 / 1000000000) := by
  have h := checkLog_sound (w := (64160313611 / 264160313611)) (n := 12)
    (lo := (247836643 / 500000000)) (hi := (495673287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164160313611 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164160313611 / 100000000000) = 1/(100000000000 / 164160313611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (247836643 / 500000000) (495673287 / 1000000000) (Real.log (164160313611 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (164160313611 / 100000000000) = -Real.log (100000000000 / 164160313611) := by
    rw [show ((164160313611 / 100000000000) : ℝ) = ((100000000000 / 164160313611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (496378973 / 1000000000) ≤ -Real.log (500000000000 / 821381001713) ∧
    -Real.log (500000000000 / 821381001713) ≤ (248189487 / 500000000) := by
  have h := checkLog_sound (w := (321381001713 / 1321381001713)) (n := 12)
    (lo := (496378973 / 1000000000)) (hi := (248189487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821381001713 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821381001713 / 500000000000) = 1/(500000000000 / 821381001713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (496378973 / 1000000000) (248189487 / 500000000) (Real.log (821381001713 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (821381001713 / 500000000000) = -Real.log (500000000000 / 821381001713) := by
    rw [show ((821381001713 / 500000000000) : ℝ) = ((500000000000 / 821381001713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0360

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0361Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0361
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

theorem reflection_log_1_neg : (104767879 / 500000000) ≤ -Real.log (10240 / 12627) ∧
    -Real.log (10240 / 12627) ≤ (209535759 / 1000000000) := by
  have h := checkLog_sound (w := (2387 / 22867)) (n := 12)
    (lo := (104767879 / 500000000)) (hi := (209535759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12627 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12627 / 10240) = 1/(10240 / 12627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (104767879 / 500000000) (209535759 / 1000000000) (Real.log (12627 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12627 / 10240) = -Real.log (10240 / 12627) := by
    rw [show ((12627 / 10240) : ℝ) = ((10240 / 12627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (53081199 / 200000000) ≤ -Real.log (7853 / 10240) ∧
    -Real.log (7853 / 10240) ≤ (66351499 / 250000000) := by
  have h := checkLog_sound (w := (2387 / 18093)) (n := 12)
    (lo := (53081199 / 200000000)) (hi := (66351499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7853) = 1/(7853 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-66351499 / 250000000) (-53081199 / 200000000) (Real.log (7853 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (6540567 / 31250000) ≤ -Real.log (640 / 789) ∧
    -Real.log (640 / 789) ≤ (41859629 / 200000000) := by
  have h := checkLog_sound (w := (149 / 1429)) (n := 12)
    (lo := (6540567 / 31250000)) (hi := (41859629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789 / 640) = 1/(640 / 789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (6540567 / 31250000) (41859629 / 200000000) (Real.log (789 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (789 / 640) = -Real.log (640 / 789) := by
    rw [show ((789 / 640) : ℝ) = ((640 / 789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16564003 / 62500000) ≤ -Real.log (491 / 640) ∧
    -Real.log (491 / 640) ≤ (265024049 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 1131)) (n := 12)
    (lo := (16564003 / 62500000)) (hi := (265024049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 491) = 1/(491 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-265024049 / 1000000000) (-16564003 / 62500000) (Real.log (491 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (382681479 / 1000000000) ≤ -Real.log (5120 / 7507) ∧
    -Real.log (5120 / 7507) ≤ (9567037 / 25000000) := by
  have h := checkLog_sound (w := (2387 / 12627)) (n := 12)
    (lo := (382681479 / 1000000000)) (hi := (9567037 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7507 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7507 / 5120) = 1/(5120 / 7507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (382681479 / 1000000000) (9567037 / 25000000) (Real.log (7507 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7507 / 5120) = -Real.log (5120 / 7507) := by
    rw [show ((7507 / 5120) : ℝ) = ((5120 / 7507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (156938633 / 250000000) ≤ -Real.log (2733 / 5120) ∧
    -Real.log (2733 / 5120) ≤ (627754533 / 1000000000) := by
  have h := checkLog_sound (w := (2387 / 7853)) (n := 12)
    (lo := (156938633 / 250000000)) (hi := (627754533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2733) = 1/(2733 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-627754533 / 1000000000) (-156938633 / 250000000) (Real.log (2733 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (95570443 / 250000000) ≤ -Real.log (320 / 469) ∧
    -Real.log (320 / 469) ≤ (382281773 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 789)) (n := 12)
    (lo := (95570443 / 250000000)) (hi := (382281773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469 / 320) = 1/(320 / 469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (95570443 / 250000000) (382281773 / 1000000000) (Real.log (469 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (469 / 320) = -Real.log (320 / 469) := by
    rw [show ((469 / 320) : ℝ) = ((320 / 469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (626657439 / 1000000000) ≤ -Real.log (171 / 320) ∧
    -Real.log (171 / 320) ≤ (3916609 / 6250000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 171) = 1/(171 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3916609 / 6250000) (-626657439 / 1000000000) (Real.log (171 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35884361 / 125000000) ≤ -Real.log (250000 / 333131) ∧
    -Real.log (250000 / 333131) ≤ (287074889 / 1000000000) := by
  have h := checkLog_sound (w := (83131 / 583131)) (n := 12)
    (lo := (35884361 / 125000000)) (hi := (287074889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333131 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333131 / 250000) = 1/(250000 / 333131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35884361 / 125000000) (287074889 / 1000000000) (Real.log (333131 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (333131 / 250000) = -Real.log (250000 / 333131) := by
    rw [show ((333131 / 250000) : ℝ) = ((250000 / 333131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (101062961 / 250000000) ≤ -Real.log (166869 / 250000) ∧
    -Real.log (166869 / 250000) ≤ (80850369 / 200000000) := by
  have h := checkLog_sound (w := (83131 / 416869)) (n := 12)
    (lo := (101062961 / 250000000)) (hi := (80850369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 166869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 166869) = 1/(166869 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-80850369 / 200000000) (-101062961 / 250000000) (Real.log (166869 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (287396031 / 1000000000) ≤ -Real.log (125000 / 166619) ∧
    -Real.log (125000 / 166619) ≤ (4490563 / 15625000) := by
  have h := checkLog_sound (w := (41619 / 291619)) (n := 12)
    (lo := (287396031 / 1000000000)) (hi := (4490563 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166619 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166619 / 125000) = 1/(125000 / 166619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (287396031 / 1000000000) (4490563 / 15625000) (Real.log (166619 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (166619 / 125000) = -Real.log (125000 / 166619) := by
    rw [show ((166619 / 125000) : ℝ) = ((125000 / 166619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (404893271 / 1000000000) ≤ -Real.log (83381 / 125000) ∧
    -Real.log (83381 / 125000) ≤ (50611659 / 125000000) := by
  have h := checkLog_sound (w := (41619 / 208381)) (n := 12)
    (lo := (404893271 / 1000000000)) (hi := (50611659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 83381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 83381) = 1/(83381 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-50611659 / 125000000) (-404893271 / 1000000000) (Real.log (83381 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (217167329 / 1000000000) ≤ -Real.log (125000 / 155319) ∧
    -Real.log (125000 / 155319) ≤ (21716733 / 100000000) := by
  have h := checkLog_sound (w := (30319 / 280319)) (n := 12)
    (lo := (217167329 / 1000000000)) (hi := (21716733 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155319 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155319 / 125000) = 1/(125000 / 155319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (217167329 / 1000000000) (21716733 / 100000000) (Real.log (155319 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (155319 / 125000) = -Real.log (125000 / 155319) := by
    rw [show ((155319 / 125000) : ℝ) = ((125000 / 155319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (27780039 / 100000000) ≤ -Real.log (94681 / 125000) ∧
    -Real.log (94681 / 125000) ≤ (277800391 / 1000000000) := by
  have h := checkLog_sound (w := (30319 / 219681)) (n := 12)
    (lo := (27780039 / 100000000)) (hi := (277800391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94681) = 1/(94681 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-277800391 / 1000000000) (-27780039 / 100000000) (Real.log (94681 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21743529 / 100000000) ≤ -Real.log (200000 / 248577) ∧
    -Real.log (200000 / 248577) ≤ (217435291 / 1000000000) := by
  have h := checkLog_sound (w := (48577 / 448577)) (n := 12)
    (lo := (21743529 / 100000000)) (hi := (217435291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248577 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248577 / 200000) = 1/(200000 / 248577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21743529 / 100000000) (217435291 / 1000000000) (Real.log (248577 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (248577 / 200000) = -Real.log (200000 / 248577) := by
    rw [show ((248577 / 200000) : ℝ) = ((200000 / 248577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (278240121 / 1000000000) ≤ -Real.log (151423 / 200000) ∧
    -Real.log (151423 / 200000) ≤ (139120061 / 500000000) := by
  have h := checkLog_sound (w := (48577 / 351423)) (n := 12)
    (lo := (278240121 / 1000000000)) (hi := (139120061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151423) = 1/(151423 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-139120061 / 500000000) (-278240121 / 1000000000) (Real.log (151423 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (172831683 / 250000000) ≤ -Real.log (500000000000 / 998181208013) ∧
    -Real.log (500000000000 / 998181208013) ≤ (691326733 / 1000000000) := by
  have h := checkLog_sound (w := (498181208013 / 1498181208013)) (n := 12)
    (lo := (172831683 / 250000000)) (hi := (691326733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((998181208013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(998181208013 / 500000000000) = 1/(500000000000 / 998181208013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (172831683 / 250000000) (691326733 / 1000000000) (Real.log (998181208013 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (998181208013 / 500000000000) = -Real.log (500000000000 / 998181208013) := by
    rw [show ((998181208013 / 500000000000) : ℝ) = ((500000000000 / 998181208013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (692289303 / 1000000000) ≤ -Real.log (3906250000 / 7805800707) ∧
    -Real.log (3906250000 / 7805800707) ≤ (86536163 / 125000000) := by
  have h := checkLog_sound (w := (3899550707 / 11712050707)) (n := 12)
    (lo := (692289303 / 1000000000)) (hi := (86536163 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7805800707 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7805800707 / 3906250000) = 1/(3906250000 / 7805800707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (692289303 / 1000000000) (86536163 / 125000000) (Real.log (7805800707 / 3906250000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7805800707 / 3906250000) = -Real.log (3906250000 / 7805800707) := by
    rw [show ((7805800707 / 3906250000) : ℝ) = ((3906250000 / 7805800707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (12374193 / 25000000) ≤ -Real.log (250000000000 / 410111321173) ∧
    -Real.log (250000000000 / 410111321173) ≤ (494967721 / 1000000000) := by
  have h := checkLog_sound (w := (160111321173 / 660111321173)) (n := 12)
    (lo := (12374193 / 25000000)) (hi := (494967721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410111321173 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410111321173 / 250000000000) = 1/(250000000000 / 410111321173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (12374193 / 25000000) (494967721 / 1000000000) (Real.log (410111321173 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (410111321173 / 250000000000) = -Real.log (250000000000 / 410111321173) := by
    rw [show ((410111321173 / 250000000000) : ℝ) = ((250000000000 / 410111321173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (495675411 / 1000000000) ≤ -Real.log (20000000000 / 32832132503) ∧
    -Real.log (20000000000 / 32832132503) ≤ (123918853 / 250000000) := by
  have h := checkLog_sound (w := (12832132503 / 52832132503)) (n := 12)
    (lo := (495675411 / 1000000000)) (hi := (123918853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32832132503 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32832132503 / 20000000000) = 1/(20000000000 / 32832132503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (495675411 / 1000000000) (123918853 / 250000000) (Real.log (32832132503 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (32832132503 / 20000000000) = -Real.log (20000000000 / 32832132503) := by
    rw [show ((32832132503 / 20000000000) : ℝ) = ((20000000000 / 32832132503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0361

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0362Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0362
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

theorem reflection_log_1_neg : (6540567 / 31250000) ≤ -Real.log (640 / 789) ∧
    -Real.log (640 / 789) ≤ (41859629 / 200000000) := by
  have h := checkLog_sound (w := (149 / 1429)) (n := 12)
    (lo := (6540567 / 31250000)) (hi := (41859629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789 / 640) = 1/(640 / 789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (6540567 / 31250000) (41859629 / 200000000) (Real.log (789 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (789 / 640) = -Real.log (640 / 789) := by
    rw [show ((789 / 640) : ℝ) = ((640 / 789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16564003 / 62500000) ≤ -Real.log (491 / 640) ∧
    -Real.log (491 / 640) ≤ (265024049 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 1131)) (n := 12)
    (lo := (16564003 / 62500000)) (hi := (265024049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 491) = 1/(491 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-265024049 / 1000000000) (-16564003 / 62500000) (Real.log (491 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (209060473 / 1000000000) ≤ -Real.log (10240 / 12621) ∧
    -Real.log (10240 / 12621) ≤ (104530237 / 500000000) := by
  have h := checkLog_sound (w := (2381 / 22861)) (n := 12)
    (lo := (209060473 / 1000000000)) (hi := (104530237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12621 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12621 / 10240) = 1/(10240 / 12621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (209060473 / 1000000000) (104530237 / 500000000) (Real.log (12621 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12621 / 10240) = -Real.log (10240 / 12621) := by
    rw [show ((12621 / 10240) : ℝ) = ((10240 / 12621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (264642247 / 1000000000) ≤ -Real.log (7859 / 10240) ∧
    -Real.log (7859 / 10240) ≤ (33080281 / 125000000) := by
  have h := checkLog_sound (w := (2381 / 18099)) (n := 12)
    (lo := (264642247 / 1000000000)) (hi := (33080281 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7859) = 1/(7859 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33080281 / 125000000) (-264642247 / 1000000000) (Real.log (7859 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (95570443 / 250000000) ≤ -Real.log (320 / 469) ∧
    -Real.log (320 / 469) ≤ (382281773 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 789)) (n := 12)
    (lo := (95570443 / 250000000)) (hi := (382281773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469 / 320) = 1/(320 / 469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (95570443 / 250000000) (382281773 / 1000000000) (Real.log (469 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (469 / 320) = -Real.log (320 / 469) := by
    rw [show ((469 / 320) : ℝ) = ((320 / 469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (626657439 / 1000000000) ≤ -Real.log (171 / 320) ∧
    -Real.log (171 / 320) ≤ (3916609 / 6250000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 171) = 1/(171 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3916609 / 6250000) (-626657439 / 1000000000) (Real.log (171 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (76376381 / 200000000) ≤ -Real.log (5120 / 7501) ∧
    -Real.log (5120 / 7501) ≤ (190940953 / 500000000) := by
  have h := checkLog_sound (w := (2381 / 12621)) (n := 12)
    (lo := (76376381 / 200000000)) (hi := (190940953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7501 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7501 / 5120) = 1/(5120 / 7501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (76376381 / 200000000) (190940953 / 500000000) (Real.log (7501 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7501 / 5120) = -Real.log (5120 / 7501) := by
    rw [show ((7501 / 5120) : ℝ) = ((5120 / 7501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (156390387 / 250000000) ≤ -Real.log (2739 / 5120) ∧
    -Real.log (2739 / 5120) ≤ (625561549 / 1000000000) := by
  have h := checkLog_sound (w := (2381 / 7859)) (n := 12)
    (lo := (156390387 / 250000000)) (hi := (625561549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2739) = 1/(2739 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-625561549 / 1000000000) (-156390387 / 250000000) (Real.log (2739 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (286753641 / 1000000000) ≤ -Real.log (15625 / 20814) ∧
    -Real.log (15625 / 20814) ≤ (143376821 / 500000000) := by
  have h := checkLog_sound (w := (5189 / 36439)) (n := 12)
    (lo := (286753641 / 1000000000)) (hi := (143376821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20814 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20814 / 15625) = 1/(15625 / 20814) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (286753641 / 1000000000) (143376821 / 500000000) (Real.log (20814 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (20814 / 15625) = -Real.log (15625 / 20814) := by
    rw [show ((20814 / 15625) : ℝ) = ((15625 / 20814) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (100902707 / 250000000) ≤ -Real.log (10436 / 15625) ∧
    -Real.log (10436 / 15625) ≤ (403610829 / 1000000000) := by
  have h := checkLog_sound (w := (5189 / 26061)) (n := 12)
    (lo := (100902707 / 250000000)) (hi := (403610829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10436) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10436) = 1/(10436 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-403610829 / 1000000000) (-100902707 / 250000000) (Real.log (10436 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (143537819 / 500000000) ≤ -Real.log (40000 / 53301) ∧
    -Real.log (40000 / 53301) ≤ (287075639 / 1000000000) := by
  have h := checkLog_sound (w := (13301 / 93301)) (n := 12)
    (lo := (143537819 / 500000000)) (hi := (287075639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53301 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53301 / 40000) = 1/(40000 / 53301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (143537819 / 500000000) (287075639 / 1000000000) (Real.log (53301 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (53301 / 40000) = -Real.log (40000 / 53301) := by
    rw [show ((53301 / 40000) : ℝ) = ((40000 / 53301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (202126671 / 500000000) ≤ -Real.log (26699 / 40000) ∧
    -Real.log (26699 / 40000) ≤ (404253343 / 1000000000) := by
  have h := checkLog_sound (w := (13301 / 66699)) (n := 12)
    (lo := (202126671 / 500000000)) (hi := (404253343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26699) = 1/(26699 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-404253343 / 1000000000) (-202126671 / 500000000) (Real.log (26699 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (108450453 / 500000000) ≤ -Real.log (1000000 / 1242221) ∧
    -Real.log (1000000 / 1242221) ≤ (216900907 / 1000000000) := by
  have h := checkLog_sound (w := (242221 / 2242221)) (n := 12)
    (lo := (108450453 / 500000000)) (hi := (216900907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1242221 / 1000000) = 1/(1000000 / 1242221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (108450453 / 500000000) (216900907 / 1000000000) (Real.log (1242221 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1242221 / 1000000) = -Real.log (1000000 / 1242221) := by
    rw [show ((1242221 / 1000000) : ℝ) = ((1000000 / 1242221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69340873 / 250000000) ≤ -Real.log (757779 / 1000000) ∧
    -Real.log (757779 / 1000000) ≤ (277363493 / 1000000000) := by
  have h := checkLog_sound (w := (242221 / 1757779)) (n := 12)
    (lo := (69340873 / 250000000)) (hi := (277363493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 757779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 757779) = 1/(757779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-277363493 / 1000000000) (-69340873 / 250000000) (Real.log (757779 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (108584067 / 500000000) ≤ -Real.log (1000000 / 1242553) ∧
    -Real.log (1000000 / 1242553) ≤ (43433627 / 200000000) := by
  have h := checkLog_sound (w := (242553 / 2242553)) (n := 12)
    (lo := (108584067 / 500000000)) (hi := (43433627 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1242553 / 1000000) = 1/(1000000 / 1242553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (108584067 / 500000000) (43433627 / 200000000) (Real.log (1242553 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1242553 / 1000000) = -Real.log (1000000 / 1242553) := by
    rw [show ((1242553 / 1000000) : ℝ) = ((1000000 / 1242553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (277801711 / 1000000000) ≤ -Real.log (757447 / 1000000) ∧
    -Real.log (757447 / 1000000) ≤ (17362607 / 62500000) := by
  have h := checkLog_sound (w := (242553 / 1757447)) (n := 12)
    (lo := (277801711 / 1000000000)) (hi := (17362607 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 757447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 757447) = 1/(757447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-17362607 / 62500000) (-277801711 / 1000000000) (Real.log (757447 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (690364469 / 1000000000) ≤ -Real.log (500000000000 / 997221157531) ∧
    -Real.log (500000000000 / 997221157531) ≤ (69036447 / 100000000) := by
  have h := checkLog_sound (w := (497221157531 / 1497221157531)) (n := 12)
    (lo := (690364469 / 1000000000)) (hi := (69036447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997221157531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997221157531 / 500000000000) = 1/(500000000000 / 997221157531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (690364469 / 1000000000) (69036447 / 100000000) (Real.log (997221157531 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (997221157531 / 500000000000) = -Real.log (500000000000 / 997221157531) := by
    rw [show ((997221157531 / 500000000000) : ℝ) = ((500000000000 / 997221157531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (691328981 / 1000000000) ≤ -Real.log (125000000000 / 249545863141) ∧
    -Real.log (125000000000 / 249545863141) ≤ (345664491 / 500000000) := by
  have h := checkLog_sound (w := (124545863141 / 374545863141)) (n := 12)
    (lo := (691328981 / 1000000000)) (hi := (345664491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249545863141 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249545863141 / 125000000000) = 1/(125000000000 / 249545863141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (691328981 / 1000000000) (345664491 / 500000000) (Real.log (249545863141 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (249545863141 / 125000000000) = -Real.log (125000000000 / 249545863141) := by
    rw [show ((249545863141 / 125000000000) : ℝ) = ((125000000000 / 249545863141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (494264399 / 1000000000) ≤ -Real.log (25000000000 / 40982298269) ∧
    -Real.log (25000000000 / 40982298269) ≤ (1235661 / 2500000) := by
  have h := checkLog_sound (w := (15982298269 / 65982298269)) (n := 12)
    (lo := (494264399 / 1000000000)) (hi := (1235661 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40982298269 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40982298269 / 25000000000) = 1/(25000000000 / 40982298269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (494264399 / 1000000000) (1235661 / 2500000) (Real.log (40982298269 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (40982298269 / 25000000000) = -Real.log (25000000000 / 40982298269) := by
    rw [show ((40982298269 / 25000000000) : ℝ) = ((25000000000 / 40982298269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (98993969 / 200000000) ≤ -Real.log (500000000000 / 820224385337) ∧
    -Real.log (500000000000 / 820224385337) ≤ (247484923 / 500000000) := by
  have h := checkLog_sound (w := (320224385337 / 1320224385337)) (n := 12)
    (lo := (98993969 / 200000000)) (hi := (247484923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((820224385337 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(820224385337 / 500000000000) = 1/(500000000000 / 820224385337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (98993969 / 200000000) (247484923 / 500000000) (Real.log (820224385337 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (820224385337 / 500000000000) = -Real.log (500000000000 / 820224385337) := by
    rw [show ((820224385337 / 500000000000) : ℝ) = ((500000000000 / 820224385337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0362

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0363Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0363
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

theorem reflection_log_1_neg : (209060473 / 1000000000) ≤ -Real.log (10240 / 12621) ∧
    -Real.log (10240 / 12621) ≤ (104530237 / 500000000) := by
  have h := checkLog_sound (w := (2381 / 22861)) (n := 12)
    (lo := (209060473 / 1000000000)) (hi := (104530237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12621 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12621 / 10240) = 1/(10240 / 12621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (209060473 / 1000000000) (104530237 / 500000000) (Real.log (12621 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12621 / 10240) = -Real.log (10240 / 12621) := by
    rw [show ((12621 / 10240) : ℝ) = ((10240 / 12621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (264642247 / 1000000000) ≤ -Real.log (7859 / 10240) ∧
    -Real.log (7859 / 10240) ≤ (33080281 / 125000000) := by
  have h := checkLog_sound (w := (2381 / 18099)) (n := 12)
    (lo := (264642247 / 1000000000)) (hi := (33080281 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7859) = 1/(7859 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33080281 / 125000000) (-264642247 / 1000000000) (Real.log (7859 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (104411373 / 500000000) ≤ -Real.log (5120 / 6309) ∧
    -Real.log (5120 / 6309) ≤ (208822747 / 1000000000) := by
  have h := checkLog_sound (w := (1189 / 11429)) (n := 12)
    (lo := (104411373 / 500000000)) (hi := (208822747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6309 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6309 / 5120) = 1/(5120 / 6309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (104411373 / 500000000) (208822747 / 1000000000) (Real.log (6309 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6309 / 5120) = -Real.log (5120 / 6309) := by
    rw [show ((6309 / 5120) : ℝ) = ((5120 / 6309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16516287 / 62500000) ≤ -Real.log (3931 / 5120) ∧
    -Real.log (3931 / 5120) ≤ (264260593 / 1000000000) := by
  have h := checkLog_sound (w := (1189 / 9051)) (n := 12)
    (lo := (16516287 / 62500000)) (hi := (264260593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3931) = 1/(3931 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-264260593 / 1000000000) (-16516287 / 62500000) (Real.log (3931 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (76376381 / 200000000) ≤ -Real.log (5120 / 7501) ∧
    -Real.log (5120 / 7501) ≤ (190940953 / 500000000) := by
  have h := checkLog_sound (w := (2381 / 12621)) (n := 12)
    (lo := (76376381 / 200000000)) (hi := (190940953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7501 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7501 / 5120) = 1/(5120 / 7501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (76376381 / 200000000) (190940953 / 500000000) (Real.log (7501 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7501 / 5120) = -Real.log (5120 / 7501) := by
    rw [show ((7501 / 5120) : ℝ) = ((5120 / 7501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (156390387 / 250000000) ≤ -Real.log (2739 / 5120) ∧
    -Real.log (2739 / 5120) ≤ (625561549 / 1000000000) := by
  have h := checkLog_sound (w := (2381 / 7859)) (n := 12)
    (lo := (156390387 / 250000000)) (hi := (625561549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2739) = 1/(2739 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-625561549 / 1000000000) (-156390387 / 250000000) (Real.log (2739 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (381481879 / 1000000000) ≤ -Real.log (2560 / 3749) ∧
    -Real.log (2560 / 3749) ≤ (9537047 / 25000000) := by
  have h := checkLog_sound (w := (1189 / 6309)) (n := 12)
    (lo := (381481879 / 1000000000)) (hi := (9537047 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3749 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3749 / 2560) = 1/(2560 / 3749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (381481879 / 1000000000) (9537047 / 25000000) (Real.log (3749 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3749 / 2560) = -Real.log (2560 / 3749) := by
    rw [show ((3749 / 2560) : ℝ) = ((2560 / 3749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (624466857 / 1000000000) ≤ -Real.log (1371 / 2560) ∧
    -Real.log (1371 / 2560) ≤ (312233429 / 500000000) := by
  have h := checkLog_sound (w := (1189 / 3931)) (n := 12)
    (lo := (624466857 / 1000000000)) (hi := (312233429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1371) = 1/(1371 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-312233429 / 500000000) (-624466857 / 1000000000) (Real.log (1371 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (143216521 / 500000000) ≤ -Real.log (1000000 / 1331669) ∧
    -Real.log (1000000 / 1331669) ≤ (286433043 / 1000000000) := by
  have h := checkLog_sound (w := (331669 / 2331669)) (n := 12)
    (lo := (143216521 / 500000000)) (hi := (286433043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331669 / 1000000) = 1/(1000000 / 1331669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (143216521 / 500000000) (286433043 / 1000000000) (Real.log (1331669 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1331669 / 1000000) = -Real.log (1000000 / 1331669) := by
    rw [show ((1331669 / 1000000) : ℝ) = ((1000000 / 1331669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (402971719 / 1000000000) ≤ -Real.log (668331 / 1000000) ∧
    -Real.log (668331 / 1000000) ≤ (10074293 / 25000000) := by
  have h := checkLog_sound (w := (331669 / 1668331)) (n := 12)
    (lo := (402971719 / 1000000000)) (hi := (10074293 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 668331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 668331) = 1/(668331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-10074293 / 25000000) (-402971719 / 1000000000) (Real.log (668331 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35844299 / 125000000) ≤ -Real.log (1000000 / 1332097) ∧
    -Real.log (1000000 / 1332097) ≤ (286754393 / 1000000000) := by
  have h := checkLog_sound (w := (332097 / 2332097)) (n := 12)
    (lo := (35844299 / 125000000)) (hi := (286754393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1332097 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1332097 / 1000000) = 1/(1000000 / 1332097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35844299 / 125000000) (286754393 / 1000000000) (Real.log (1332097 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1332097 / 1000000) = -Real.log (1000000 / 1332097) := by
    rw [show ((1332097 / 1000000) : ℝ) = ((1000000 / 1332097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (16144493 / 40000000) ≤ -Real.log (667903 / 1000000) ∧
    -Real.log (667903 / 1000000) ≤ (201806163 / 500000000) := by
  have h := checkLog_sound (w := (332097 / 1667903)) (n := 12)
    (lo := (16144493 / 40000000)) (hi := (201806163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 667903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 667903) = 1/(667903 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-201806163 / 500000000) (-16144493 / 40000000) (Real.log (667903 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (216633607 / 1000000000) ≤ -Real.log (1000000 / 1241889) ∧
    -Real.log (1000000 / 1241889) ≤ (27079201 / 125000000) := by
  have h := checkLog_sound (w := (241889 / 2241889)) (n := 12)
    (lo := (216633607 / 1000000000)) (hi := (27079201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241889 / 1000000) = 1/(1000000 / 1241889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (216633607 / 1000000000) (27079201 / 125000000) (Real.log (1241889 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1241889 / 1000000) = -Real.log (1000000 / 1241889) := by
    rw [show ((1241889 / 1000000) : ℝ) = ((1000000 / 1241889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (138462733 / 500000000) ≤ -Real.log (758111 / 1000000) ∧
    -Real.log (758111 / 1000000) ≤ (276925467 / 1000000000) := by
  have h := checkLog_sound (w := (241889 / 1758111)) (n := 12)
    (lo := (138462733 / 500000000)) (hi := (276925467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758111) = 1/(758111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-276925467 / 1000000000) (-138462733 / 500000000) (Real.log (758111 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (216901711 / 1000000000) ≤ -Real.log (500000 / 621111) ∧
    -Real.log (500000 / 621111) ≤ (13556357 / 62500000) := by
  have h := checkLog_sound (w := (121111 / 1121111)) (n := 12)
    (lo := (216901711 / 1000000000)) (hi := (13556357 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621111 / 500000) = 1/(500000 / 621111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (216901711 / 1000000000) (13556357 / 62500000) (Real.log (621111 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (621111 / 500000) = -Real.log (500000 / 621111) := by
    rw [show ((621111 / 500000) : ℝ) = ((500000 / 621111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (69341203 / 250000000) ≤ -Real.log (378889 / 500000) ∧
    -Real.log (378889 / 500000) ≤ (277364813 / 1000000000) := by
  have h := checkLog_sound (w := (121111 / 878889)) (n := 12)
    (lo := (69341203 / 250000000)) (hi := (277364813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378889) = 1/(378889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-277364813 / 1000000000) (-69341203 / 250000000) (Real.log (378889 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (689404761 / 1000000000) ≤ -Real.log (500000000000 / 996264575487) ∧
    -Real.log (500000000000 / 996264575487) ≤ (344702381 / 500000000) := by
  have h := checkLog_sound (w := (496264575487 / 1496264575487)) (n := 12)
    (lo := (689404761 / 1000000000)) (hi := (344702381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((996264575487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(996264575487 / 500000000000) = 1/(500000000000 / 996264575487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (689404761 / 1000000000) (344702381 / 500000000) (Real.log (996264575487 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (996264575487 / 500000000000) = -Real.log (500000000000 / 996264575487) := by
    rw [show ((996264575487 / 500000000000) : ℝ) = ((500000000000 / 996264575487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (690366717 / 1000000000) ≤ -Real.log (500000000000 / 997223399207) ∧
    -Real.log (500000000000 / 997223399207) ≤ (345183359 / 500000000) := by
  have h := checkLog_sound (w := (497223399207 / 1497223399207)) (n := 12)
    (lo := (690366717 / 1000000000)) (hi := (345183359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997223399207 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997223399207 / 500000000000) = 1/(500000000000 / 997223399207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (690366717 / 1000000000) (345183359 / 500000000) (Real.log (997223399207 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (997223399207 / 500000000000) = -Real.log (500000000000 / 997223399207) := by
    rw [show ((997223399207 / 500000000000) : ℝ) = ((500000000000 / 997223399207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (493559073 / 1000000000) ≤ -Real.log (500000000000 / 819068052039) ∧
    -Real.log (500000000000 / 819068052039) ≤ (246779537 / 500000000) := by
  have h := checkLog_sound (w := (319068052039 / 1319068052039)) (n := 12)
    (lo := (493559073 / 1000000000)) (hi := (246779537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819068052039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819068052039 / 500000000000) = 1/(500000000000 / 819068052039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (493559073 / 1000000000) (246779537 / 500000000) (Real.log (819068052039 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (819068052039 / 500000000000) = -Real.log (500000000000 / 819068052039) := by
    rw [show ((819068052039 / 500000000000) : ℝ) = ((500000000000 / 819068052039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (494266523 / 1000000000) ≤ -Real.log (500000000000 / 819647706849) ∧
    -Real.log (500000000000 / 819647706849) ≤ (123566631 / 250000000) := by
  have h := checkLog_sound (w := (319647706849 / 1319647706849)) (n := 12)
    (lo := (494266523 / 1000000000)) (hi := (123566631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819647706849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819647706849 / 500000000000) = 1/(500000000000 / 819647706849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (494266523 / 1000000000) (123566631 / 250000000) (Real.log (819647706849 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (819647706849 / 500000000000) = -Real.log (500000000000 / 819647706849) := by
    rw [show ((819647706849 / 500000000000) : ℝ) = ((500000000000 / 819647706849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0363

end


