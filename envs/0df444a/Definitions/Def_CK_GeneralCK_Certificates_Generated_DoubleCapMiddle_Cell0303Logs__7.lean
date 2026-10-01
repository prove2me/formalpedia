-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0303Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0303Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:34:37.244167+00:00
-- url     : https://prove2.me/theorems/ef346fcd-240d-40c4-97d9-5df74c3b15f2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0303Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0304Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0303Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0304Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0305Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0306Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0307Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0308Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0309Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0303Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0304Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0305Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0306Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0307Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0308Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0309Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0303Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0304Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0305Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0306Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0307Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0308Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0309Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0303Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0304Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0305Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0306Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0307Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0308Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0309Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0303Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0303
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

theorem reflection_log_1_neg : (223221673 / 1000000000) ≤ -Real.log (10240 / 12801) ∧
    -Real.log (10240 / 12801) ≤ (111610837 / 500000000) := by
  have h := checkLog_sound (w := (2561 / 23041)) (n := 12)
    (lo := (223221673 / 1000000000)) (hi := (111610837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12801 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12801 / 10240) = 1/(10240 / 12801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (223221673 / 1000000000) (111610837 / 500000000) (Real.log (12801 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12801 / 10240) = -Real.log (10240 / 12801) := by
    rw [show ((12801 / 10240) : ℝ) = ((10240 / 12801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (287812289 / 1000000000) ≤ -Real.log (7679 / 10240) ∧
    -Real.log (7679 / 10240) ≤ (28781229 / 100000000) := by
  have h := checkLog_sound (w := (2561 / 17919)) (n := 12)
    (lo := (287812289 / 1000000000)) (hi := (28781229 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7679) = 1/(7679 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-28781229 / 100000000) (-287812289 / 1000000000) (Real.log (7679 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (222987289 / 1000000000) ≤ -Real.log (5120 / 6399) ∧
    -Real.log (5120 / 6399) ≤ (22298729 / 100000000) := by
  have h := checkLog_sound (w := (1279 / 11519)) (n := 12)
    (lo := (222987289 / 1000000000)) (hi := (22298729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6399 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6399 / 5120) = 1/(5120 / 6399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (222987289 / 1000000000) (22298729 / 100000000) (Real.log (6399 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6399 / 5120) = -Real.log (5120 / 6399) := by
    rw [show ((6399 / 5120) : ℝ) = ((5120 / 6399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (287421689 / 1000000000) ≤ -Real.log (3841 / 5120) ∧
    -Real.log (3841 / 5120) ≤ (28742169 / 100000000) := by
  have h := checkLog_sound (w := (1279 / 8961)) (n := 12)
    (lo := (287421689 / 1000000000)) (hi := (28742169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3841) = 1/(3841 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-28742169 / 100000000) (-287421689 / 1000000000) (Real.log (3841 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (405595307 / 1000000000) ≤ -Real.log (5120 / 7681) ∧
    -Real.log (5120 / 7681) ≤ (101398827 / 250000000) := by
  have h := checkLog_sound (w := (2561 / 12801)) (n := 12)
    (lo := (405595307 / 1000000000)) (hi := (101398827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7681 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7681 / 5120) = 1/(5120 / 7681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (405595307 / 1000000000) (101398827 / 250000000) (Real.log (7681 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7681 / 5120) = -Real.log (5120 / 7681) := by
    rw [show ((7681 / 5120) : ℝ) = ((5120 / 7681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (693537881 / 1000000000) ≤ -Real.log (2559 / 5120) ∧
    -Real.log (2559 / 5120) ≤ (693537883 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5119)) (n := 12)
    (lo := (390701 / 1000000000)) (hi := (195351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2559) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2559) = 1/(2559 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-693537883 / 1000000000) (-693537881 / 1000000000) (Real.log (2559 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (405204657 / 1000000000) ≤ -Real.log (2560 / 3839) ∧
    -Real.log (2560 / 3839) ≤ (202602329 / 500000000) := by
  have h := checkLog_sound (w := (1279 / 6399)) (n := 12)
    (lo := (405204657 / 1000000000)) (hi := (202602329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3839 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3839 / 2560) = 1/(2560 / 3839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (405204657 / 1000000000) (202602329 / 500000000) (Real.log (3839 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3839 / 2560) = -Real.log (2560 / 3839) := by
    rw [show ((3839 / 2560) : ℝ) = ((2560 / 3839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (138473247 / 200000000) ≤ -Real.log (1281 / 2560) ∧
    -Real.log (1281 / 2560) ≤ (173091559 / 250000000) := by
  have h := checkLog_sound (w := (1279 / 3841)) (n := 12)
    (lo := (138473247 / 200000000)) (hi := (173091559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1281) = 1/(1281 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-173091559 / 250000000) (-138473247 / 200000000) (Real.log (1281 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (305565211 / 1000000000) ≤ -Real.log (62500 / 84837) ∧
    -Real.log (62500 / 84837) ≤ (76391303 / 250000000) := by
  have h := checkLog_sound (w := (22337 / 147337)) (n := 12)
    (lo := (305565211 / 1000000000)) (hi := (76391303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84837 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84837 / 62500) = 1/(62500 / 84837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (305565211 / 1000000000) (76391303 / 250000000) (Real.log (84837 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (84837 / 62500) = -Real.log (62500 / 84837) := by
    rw [show ((84837 / 62500) : ℝ) = ((62500 / 84837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (221110191 / 500000000) ≤ -Real.log (40163 / 62500) ∧
    -Real.log (40163 / 62500) ≤ (442220383 / 1000000000) := by
  have h := checkLog_sound (w := (22337 / 102663)) (n := 12)
    (lo := (221110191 / 500000000)) (hi := (442220383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 40163) = 1/(40163 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-442220383 / 1000000000) (-221110191 / 500000000) (Real.log (40163 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (305882681 / 1000000000) ≤ -Real.log (1000000 / 1357823) ∧
    -Real.log (1000000 / 1357823) ≤ (152941341 / 500000000) := by
  have h := checkLog_sound (w := (357823 / 2357823)) (n := 12)
    (lo := (305882681 / 1000000000)) (hi := (152941341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357823 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357823 / 1000000) = 1/(1000000 / 1357823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (305882681 / 1000000000) (152941341 / 500000000) (Real.log (1357823 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1357823 / 1000000) = -Real.log (1000000 / 1357823) := by
    rw [show ((1357823 / 1000000) : ℝ) = ((1000000 / 1357823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27680707 / 62500000) ≤ -Real.log (642177 / 1000000) ∧
    -Real.log (642177 / 1000000) ≤ (442891313 / 1000000000) := by
  have h := checkLog_sound (w := (357823 / 1642177)) (n := 12)
    (lo := (27680707 / 62500000)) (hi := (442891313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 642177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 642177) = 1/(642177 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-442891313 / 1000000000) (-27680707 / 62500000) (Real.log (642177 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7271087 / 31250000) ≤ -Real.log (1000000 / 1261971) ∧
    -Real.log (1000000 / 1261971) ≤ (46534957 / 200000000) := by
  have h := checkLog_sound (w := (261971 / 2261971)) (n := 12)
    (lo := (7271087 / 31250000)) (hi := (46534957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261971 / 1000000) = 1/(1000000 / 1261971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7271087 / 31250000) (46534957 / 200000000) (Real.log (1261971 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1261971 / 1000000) = -Real.log (1000000 / 1261971) := by
    rw [show ((1261971 / 1000000) : ℝ) = ((1000000 / 1261971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (303772159 / 1000000000) ≤ -Real.log (738029 / 1000000) ∧
    -Real.log (738029 / 1000000) ≤ (118661 / 390625) := by
  have h := checkLog_sound (w := (261971 / 1738029)) (n := 12)
    (lo := (303772159 / 1000000000)) (hi := (118661 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738029) = 1/(738029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-118661 / 390625) (-303772159 / 1000000000) (Real.log (738029 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (232944167 / 1000000000) ≤ -Real.log (1000000 / 1262311) ∧
    -Real.log (1000000 / 1262311) ≤ (29118021 / 125000000) := by
  have h := checkLog_sound (w := (262311 / 2262311)) (n := 12)
    (lo := (232944167 / 1000000000)) (hi := (29118021 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1262311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1262311 / 1000000) = 1/(1000000 / 1262311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (232944167 / 1000000000) (29118021 / 125000000) (Real.log (1262311 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1262311 / 1000000) = -Real.log (1000000 / 1262311) := by
    rw [show ((1262311 / 1000000) : ℝ) = ((1000000 / 1262311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (38029119 / 125000000) ≤ -Real.log (737689 / 1000000) ∧
    -Real.log (737689 / 1000000) ≤ (304232953 / 1000000000) := by
  have h := checkLog_sound (w := (262311 / 1737689)) (n := 12)
    (lo := (38029119 / 125000000)) (hi := (304232953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 737689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 737689) = 1/(737689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-304232953 / 1000000000) (-38029119 / 125000000) (Real.log (737689 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (373892797 / 500000000) ≤ -Real.log (500000000000 / 1056158653487) ∧
    -Real.log (500000000000 / 1056158653487) ≤ (186946399 / 250000000) := by
  have h := checkLog_sound (w := (56158653487 / 2056158653487)) (n := 12)
    (lo := (27319207 / 500000000)) (hi := (10927683 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056158653487 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1056158653487 / 1000000000000) = 1/(500000000000 / 1056158653487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (373892797 / 500000000) (186946399 / 250000000) (Real.log (1056158653487 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1056158653487 / 500000000000) = -Real.log (500000000000 / 1056158653487) := by
    rw [show ((1056158653487 / 500000000000) : ℝ) = ((500000000000 / 1056158653487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (748773993 / 1000000000) ≤ -Real.log (500000000000 / 1057203076411) ∧
    -Real.log (500000000000 / 1057203076411) ≤ (149754799 / 200000000) := by
  have h := checkLog_sound (w := (57203076411 / 2057203076411)) (n := 12)
    (lo := (55626813 / 1000000000)) (hi := (27813407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1057203076411 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1057203076411 / 1000000000000) = 1/(500000000000 / 1057203076411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (748773993 / 1000000000) (149754799 / 200000000) (Real.log (1057203076411 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1057203076411 / 500000000000) = -Real.log (500000000000 / 1057203076411) := by
    rw [show ((1057203076411 / 500000000000) : ℝ) = ((500000000000 / 1057203076411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16763967 / 31250000) ≤ -Real.log (500000000000 / 854960306437) ∧
    -Real.log (500000000000 / 854960306437) ≤ (107289389 / 200000000) := by
  have h := checkLog_sound (w := (354960306437 / 1354960306437)) (n := 12)
    (lo := (16763967 / 31250000)) (hi := (107289389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854960306437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(854960306437 / 500000000000) = 1/(500000000000 / 854960306437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (16763967 / 31250000) (107289389 / 200000000) (Real.log (854960306437 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (854960306437 / 500000000000) = -Real.log (500000000000 / 854960306437) := by
    rw [show ((854960306437 / 500000000000) : ℝ) = ((500000000000 / 854960306437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3357357 / 6250000) ≤ -Real.log (31250000000 / 53474050379) ∧
    -Real.log (31250000000 / 53474050379) ≤ (537177121 / 1000000000) := by
  have h := checkLog_sound (w := (22224050379 / 84724050379)) (n := 12)
    (lo := (3357357 / 6250000)) (hi := (537177121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53474050379 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53474050379 / 31250000000) = 1/(31250000000 / 53474050379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3357357 / 6250000) (537177121 / 1000000000) (Real.log (53474050379 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (53474050379 / 31250000000) = -Real.log (31250000000 / 53474050379) := by
    rw [show ((53474050379 / 31250000000) : ℝ) = ((31250000000 / 53474050379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0303

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0304Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0304
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

theorem reflection_log_1_neg : (222987289 / 1000000000) ≤ -Real.log (5120 / 6399) ∧
    -Real.log (5120 / 6399) ≤ (22298729 / 100000000) := by
  have h := checkLog_sound (w := (1279 / 11519)) (n := 12)
    (lo := (222987289 / 1000000000)) (hi := (22298729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6399 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6399 / 5120) = 1/(5120 / 6399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (222987289 / 1000000000) (22298729 / 100000000) (Real.log (6399 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6399 / 5120) = -Real.log (5120 / 6399) := by
    rw [show ((6399 / 5120) : ℝ) = ((5120 / 6399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (287421689 / 1000000000) ≤ -Real.log (3841 / 5120) ∧
    -Real.log (3841 / 5120) ≤ (28742169 / 100000000) := by
  have h := checkLog_sound (w := (1279 / 8961)) (n := 12)
    (lo := (287421689 / 1000000000)) (hi := (28742169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3841) = 1/(3841 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-28742169 / 100000000) (-287421689 / 1000000000) (Real.log (3841 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (4455057 / 20000000) ≤ -Real.log (2048 / 2559) ∧
    -Real.log (2048 / 2559) ≤ (222752851 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 4607)) (n := 12)
    (lo := (4455057 / 20000000)) (hi := (222752851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2559 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2559 / 2048) = 1/(2048 / 2559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (4455057 / 20000000) (222752851 / 1000000000) (Real.log (2559 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2559 / 2048) = -Real.log (2048 / 2559) := by
    rw [show ((2559 / 2048) : ℝ) = ((2048 / 2559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (143515621 / 500000000) ≤ -Real.log (1537 / 2048) ∧
    -Real.log (1537 / 2048) ≤ (287031243 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 3585)) (n := 12)
    (lo := (143515621 / 500000000)) (hi := (287031243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1537) = 1/(1537 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-287031243 / 1000000000) (-143515621 / 500000000) (Real.log (1537 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (405204657 / 1000000000) ≤ -Real.log (2560 / 3839) ∧
    -Real.log (2560 / 3839) ≤ (202602329 / 500000000) := by
  have h := checkLog_sound (w := (1279 / 6399)) (n := 12)
    (lo := (405204657 / 1000000000)) (hi := (202602329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3839 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3839 / 2560) = 1/(2560 / 3839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (405204657 / 1000000000) (202602329 / 500000000) (Real.log (3839 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3839 / 2560) = -Real.log (2560 / 3839) := by
    rw [show ((3839 / 2560) : ℝ) = ((2560 / 3839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (138473247 / 200000000) ≤ -Real.log (1281 / 2560) ∧
    -Real.log (1281 / 2560) ≤ (173091559 / 250000000) := by
  have h := checkLog_sound (w := (1279 / 3841)) (n := 12)
    (lo := (138473247 / 200000000)) (hi := (173091559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1281) = 1/(1281 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-173091559 / 250000000) (-138473247 / 200000000) (Real.log (1281 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (202406927 / 500000000) ≤ -Real.log (1024 / 1535) ∧
    -Real.log (1024 / 1535) ≤ (80962771 / 200000000) := by
  have h := checkLog_sound (w := (511 / 2559)) (n := 12)
    (lo := (202406927 / 500000000)) (hi := (80962771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1535 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1535 / 1024) = 1/(1024 / 1535) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (202406927 / 500000000) (80962771 / 200000000) (Real.log (1535 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1535 / 1024) = -Real.log (1024 / 1535) := by
    rw [show ((1535 / 1024) : ℝ) = ((1024 / 1535) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (17279899 / 25000000) ≤ -Real.log (513 / 1024) ∧
    -Real.log (513 / 1024) ≤ (691195961 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 1537)) (n := 12)
    (lo := (17279899 / 25000000)) (hi := (691195961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 513) = 1/(513 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-691195961 / 1000000000) (-17279899 / 25000000) (Real.log (513 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (305248377 / 1000000000) ≤ -Real.log (500000 / 678481) ∧
    -Real.log (500000 / 678481) ≤ (152624189 / 500000000) := by
  have h := checkLog_sound (w := (178481 / 1178481)) (n := 12)
    (lo := (305248377 / 1000000000)) (hi := (152624189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678481 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678481 / 500000) = 1/(500000 / 678481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (305248377 / 1000000000) (152624189 / 500000000) (Real.log (678481 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (678481 / 500000) = -Real.log (500000 / 678481) := by
    rw [show ((678481 / 500000) : ℝ) = ((500000 / 678481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (220775729 / 500000000) ≤ -Real.log (321519 / 500000) ∧
    -Real.log (321519 / 500000) ≤ (441551459 / 1000000000) := by
  have h := checkLog_sound (w := (178481 / 821519)) (n := 12)
    (lo := (220775729 / 500000000)) (hi := (441551459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 321519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 321519) = 1/(321519 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-441551459 / 1000000000) (-220775729 / 500000000) (Real.log (321519 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (76391487 / 250000000) ≤ -Real.log (1000000 / 1357393) ∧
    -Real.log (1000000 / 1357393) ≤ (305565949 / 1000000000) := by
  have h := checkLog_sound (w := (357393 / 2357393)) (n := 12)
    (lo := (76391487 / 250000000)) (hi := (305565949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357393 / 1000000) = 1/(1000000 / 1357393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (76391487 / 250000000) (305565949 / 1000000000) (Real.log (1357393 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1357393 / 1000000) = -Real.log (1000000 / 1357393) := by
    rw [show ((1357393 / 1000000) : ℝ) = ((1000000 / 1357393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (442221939 / 1000000000) ≤ -Real.log (642607 / 1000000) ∧
    -Real.log (642607 / 1000000) ≤ (22111097 / 50000000) := by
  have h := checkLog_sound (w := (357393 / 1642607)) (n := 12)
    (lo := (442221939 / 1000000000)) (hi := (22111097 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 642607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 642607) = 1/(642607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22111097 / 50000000) (-442221939 / 1000000000) (Real.log (642607 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (232406913 / 1000000000) ≤ -Real.log (1000000 / 1261633) ∧
    -Real.log (1000000 / 1261633) ≤ (116203457 / 500000000) := by
  have h := checkLog_sound (w := (261633 / 2261633)) (n := 12)
    (lo := (232406913 / 1000000000)) (hi := (116203457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261633 / 1000000) = 1/(1000000 / 1261633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (232406913 / 1000000000) (116203457 / 500000000) (Real.log (1261633 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1261633 / 1000000) = -Real.log (1000000 / 1261633) := by
    rw [show ((1261633 / 1000000) : ℝ) = ((1000000 / 1261633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (18957143 / 62500000) ≤ -Real.log (738367 / 1000000) ∧
    -Real.log (738367 / 1000000) ≤ (303314289 / 1000000000) := by
  have h := checkLog_sound (w := (261633 / 1738367)) (n := 12)
    (lo := (18957143 / 62500000)) (hi := (303314289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738367) = 1/(738367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-303314289 / 1000000000) (-18957143 / 62500000) (Real.log (738367 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (29084447 / 125000000) ≤ -Real.log (250000 / 315493) ∧
    -Real.log (250000 / 315493) ≤ (232675577 / 1000000000) := by
  have h := checkLog_sound (w := (65493 / 565493)) (n := 12)
    (lo := (29084447 / 125000000)) (hi := (232675577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315493 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315493 / 250000) = 1/(250000 / 315493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (29084447 / 125000000) (232675577 / 1000000000) (Real.log (315493 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (315493 / 250000) = -Real.log (250000 / 315493) := by
    rw [show ((315493 / 250000) : ℝ) = ((250000 / 315493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (151886757 / 500000000) ≤ -Real.log (184507 / 250000) ∧
    -Real.log (184507 / 250000) ≤ (60754703 / 200000000) := by
  have h := checkLog_sound (w := (65493 / 434507)) (n := 12)
    (lo := (151886757 / 500000000)) (hi := (60754703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 184507) = 1/(184507 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-60754703 / 200000000) (-151886757 / 500000000) (Real.log (184507 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (149359967 / 200000000) ≤ -Real.log (500000000000 / 1055118049011) ∧
    -Real.log (500000000000 / 1055118049011) ≤ (746799837 / 1000000000) := by
  have h := checkLog_sound (w := (55118049011 / 2055118049011)) (n := 12)
    (lo := (10730531 / 200000000)) (hi := (3353291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1055118049011 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1055118049011 / 1000000000000) = 1/(500000000000 / 1055118049011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (149359967 / 200000000) (746799837 / 1000000000) (Real.log (1055118049011 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1055118049011 / 500000000000) = -Real.log (500000000000 / 1055118049011) := by
    rw [show ((1055118049011 / 500000000000) : ℝ) = ((500000000000 / 1055118049011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (373893943 / 500000000) ≤ -Real.log (500000000000 / 1056161075121) ∧
    -Real.log (500000000000 / 1056161075121) ≤ (46736743 / 62500000) := by
  have h := checkLog_sound (w := (56161075121 / 2056161075121)) (n := 12)
    (lo := (27320353 / 500000000)) (hi := (54640707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056161075121 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1056161075121 / 1000000000000) = 1/(500000000000 / 1056161075121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (373893943 / 500000000) (46736743 / 62500000) (Real.log (1056161075121 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1056161075121 / 500000000000) = -Real.log (500000000000 / 1056161075121) := by
    rw [show ((1056161075121 / 500000000000) : ℝ) = ((500000000000 / 1056161075121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (535721201 / 1000000000) ≤ -Real.log (62500000000 / 106792506301) ∧
    -Real.log (62500000000 / 106792506301) ≤ (267860601 / 500000000) := by
  have h := checkLog_sound (w := (44292506301 / 169292506301)) (n := 12)
    (lo := (535721201 / 1000000000)) (hi := (267860601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106792506301 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106792506301 / 62500000000) = 1/(62500000000 / 106792506301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (535721201 / 1000000000) (267860601 / 500000000) (Real.log (106792506301 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (106792506301 / 62500000000) = -Real.log (62500000000 / 106792506301) := by
    rw [show ((106792506301 / 62500000000) : ℝ) = ((62500000000 / 106792506301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (536449091 / 1000000000) ≤ -Real.log (250000000000 / 427481071179) ∧
    -Real.log (250000000000 / 427481071179) ≤ (134112273 / 250000000) := by
  have h := checkLog_sound (w := (177481071179 / 677481071179)) (n := 12)
    (lo := (536449091 / 1000000000)) (hi := (134112273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427481071179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427481071179 / 250000000000) = 1/(250000000000 / 427481071179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (536449091 / 1000000000) (134112273 / 250000000) (Real.log (427481071179 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (427481071179 / 250000000000) = -Real.log (250000000000 / 427481071179) := by
    rw [show ((427481071179 / 250000000000) : ℝ) = ((250000000000 / 427481071179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0304

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0305Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0305
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

theorem reflection_log_1_neg : (4455057 / 20000000) ≤ -Real.log (2048 / 2559) ∧
    -Real.log (2048 / 2559) ≤ (222752851 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 4607)) (n := 12)
    (lo := (4455057 / 20000000)) (hi := (222752851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2559 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2559 / 2048) = 1/(2048 / 2559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (4455057 / 20000000) (222752851 / 1000000000) (Real.log (2559 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2559 / 2048) = -Real.log (2048 / 2559) := by
    rw [show ((2559 / 2048) : ℝ) = ((2048 / 2559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (143515621 / 500000000) ≤ -Real.log (1537 / 2048) ∧
    -Real.log (1537 / 2048) ≤ (287031243 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 3585)) (n := 12)
    (lo := (143515621 / 500000000)) (hi := (287031243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1537) = 1/(1537 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-287031243 / 1000000000) (-143515621 / 500000000) (Real.log (1537 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (44503671 / 200000000) ≤ -Real.log (1280 / 1599) ∧
    -Real.log (1280 / 1599) ≤ (55629589 / 250000000) := by
  have h := checkLog_sound (w := (319 / 2879)) (n := 12)
    (lo := (44503671 / 200000000)) (hi := (55629589 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1599 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1599 / 1280) = 1/(1280 / 1599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (44503671 / 200000000) (55629589 / 250000000) (Real.log (1599 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1599 / 1280) = -Real.log (1280 / 1599) := by
    rw [show ((1599 / 1280) : ℝ) = ((1280 / 1599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (286640947 / 1000000000) ≤ -Real.log (961 / 1280) ∧
    -Real.log (961 / 1280) ≤ (71660237 / 250000000) := by
  have h := checkLog_sound (w := (319 / 2241)) (n := 12)
    (lo := (286640947 / 1000000000)) (hi := (71660237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 961) = 1/(961 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-71660237 / 250000000) (-286640947 / 1000000000) (Real.log (961 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (202406927 / 500000000) ≤ -Real.log (1024 / 1535) ∧
    -Real.log (1024 / 1535) ≤ (80962771 / 200000000) := by
  have h := checkLog_sound (w := (511 / 2559)) (n := 12)
    (lo := (202406927 / 500000000)) (hi := (80962771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1535 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1535 / 1024) = 1/(1024 / 1535) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (202406927 / 500000000) (80962771 / 200000000) (Real.log (1535 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1535 / 1024) = -Real.log (1024 / 1535) := by
    rw [show ((1535 / 1024) : ℝ) = ((1024 / 1535) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (17279899 / 25000000) ≤ -Real.log (513 / 1024) ∧
    -Real.log (513 / 1024) ≤ (691195961 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 1537)) (n := 12)
    (lo := (17279899 / 25000000)) (hi := (691195961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 513) = 1/(513 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-691195961 / 1000000000) (-17279899 / 25000000) (Real.log (513 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (202211449 / 500000000) ≤ -Real.log (640 / 959) ∧
    -Real.log (640 / 959) ≤ (404422899 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1599)) (n := 12)
    (lo := (202211449 / 500000000)) (hi := (404422899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959 / 640) = 1/(640 / 959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (202211449 / 500000000) (404422899 / 1000000000) (Real.log (959 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (959 / 640) = -Real.log (640 / 959) := by
    rw [show ((959 / 640) : ℝ) = ((640 / 959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (690027053 / 1000000000) ≤ -Real.log (321 / 640) ∧
    -Real.log (321 / 640) ≤ (345013527 / 500000000) := by
  have h := checkLog_sound (w := (319 / 961)) (n := 12)
    (lo := (690027053 / 1000000000)) (hi := (345013527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 321) = 1/(321 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-345013527 / 500000000) (-690027053 / 1000000000) (Real.log (321 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (152465721 / 500000000) ≤ -Real.log (250000 / 339133) ∧
    -Real.log (250000 / 339133) ≤ (304931443 / 1000000000) := by
  have h := checkLog_sound (w := (89133 / 589133)) (n := 12)
    (lo := (152465721 / 500000000)) (hi := (304931443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339133 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339133 / 250000) = 1/(250000 / 339133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (152465721 / 500000000) (304931443 / 1000000000) (Real.log (339133 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (339133 / 250000) = -Real.log (250000 / 339133) := by
    rw [show ((339133 / 250000) : ℝ) = ((250000 / 339133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (440882981 / 1000000000) ≤ -Real.log (160867 / 250000) ∧
    -Real.log (160867 / 250000) ≤ (220441491 / 500000000) := by
  have h := checkLog_sound (w := (89133 / 410867)) (n := 12)
    (lo := (440882981 / 1000000000)) (hi := (220441491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 160867) = 1/(160867 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-220441491 / 500000000) (-440882981 / 1000000000) (Real.log (160867 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (152624557 / 500000000) ≤ -Real.log (1000000 / 1356963) ∧
    -Real.log (1000000 / 1356963) ≤ (61049823 / 200000000) := by
  have h := checkLog_sound (w := (356963 / 2356963)) (n := 12)
    (lo := (152624557 / 500000000)) (hi := (61049823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356963 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1356963 / 1000000) = 1/(1000000 / 1356963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (152624557 / 500000000) (61049823 / 200000000) (Real.log (1356963 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1356963 / 1000000) = -Real.log (1000000 / 1356963) := by
    rw [show ((1356963 / 1000000) : ℝ) = ((1000000 / 1356963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (441553013 / 1000000000) ≤ -Real.log (643037 / 1000000) ∧
    -Real.log (643037 / 1000000) ≤ (220776507 / 500000000) := by
  have h := checkLog_sound (w := (356963 / 1643037)) (n := 12)
    (lo := (441553013 / 1000000000)) (hi := (220776507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 643037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 643037) = 1/(643037 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-220776507 / 500000000) (-441553013 / 1000000000) (Real.log (643037 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23213897 / 100000000) ≤ -Real.log (200000 / 252259) ∧
    -Real.log (200000 / 252259) ≤ (232138971 / 1000000000) := by
  have h := checkLog_sound (w := (52259 / 452259)) (n := 12)
    (lo := (23213897 / 100000000)) (hi := (232138971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252259 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(252259 / 200000) = 1/(200000 / 252259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23213897 / 100000000) (232138971 / 1000000000) (Real.log (252259 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (252259 / 200000) = -Real.log (200000 / 252259) := by
    rw [show ((252259 / 200000) : ℝ) = ((200000 / 252259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2422853 / 8000000) ≤ -Real.log (147741 / 200000) ∧
    -Real.log (147741 / 200000) ≤ (151428313 / 500000000) := by
  have h := checkLog_sound (w := (52259 / 347741)) (n := 12)
    (lo := (2422853 / 8000000)) (hi := (151428313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 147741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 147741) = 1/(147741 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-151428313 / 500000000) (-2422853 / 8000000) (Real.log (147741 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (116203853 / 500000000) ≤ -Real.log (500000 / 630817) ∧
    -Real.log (500000 / 630817) ≤ (232407707 / 1000000000) := by
  have h := checkLog_sound (w := (130817 / 1130817)) (n := 12)
    (lo := (116203853 / 500000000)) (hi := (232407707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630817 / 500000) = 1/(500000 / 630817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (116203853 / 500000000) (232407707 / 1000000000) (Real.log (630817 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (630817 / 500000) = -Real.log (500000 / 630817) := by
    rw [show ((630817 / 500000) : ℝ) = ((500000 / 630817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (151657821 / 500000000) ≤ -Real.log (369183 / 500000) ∧
    -Real.log (369183 / 500000) ≤ (303315643 / 1000000000) := by
  have h := checkLog_sound (w := (130817 / 869183)) (n := 12)
    (lo := (151657821 / 500000000)) (hi := (303315643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 369183) = 1/(369183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-303315643 / 1000000000) (-151657821 / 500000000) (Real.log (369183 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (745814423 / 1000000000) ≤ -Real.log (500000000000 / 1054078835311) ∧
    -Real.log (500000000000 / 1054078835311) ≤ (29832577 / 40000000) := by
  have h := checkLog_sound (w := (54078835311 / 2054078835311)) (n := 12)
    (lo := (52667243 / 1000000000)) (hi := (13166811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1054078835311 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1054078835311 / 1000000000000) = 1/(500000000000 / 1054078835311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (745814423 / 1000000000) (29832577 / 40000000) (Real.log (1054078835311 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1054078835311 / 500000000000) = -Real.log (500000000000 / 1054078835311) := by
    rw [show ((1054078835311 / 500000000000) : ℝ) = ((500000000000 / 1054078835311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (746802127 / 1000000000) ≤ -Real.log (31250000000 / 65945029213) ∧
    -Real.log (31250000000 / 65945029213) ≤ (746802129 / 1000000000) := by
  have h := checkLog_sound (w := (3445029213 / 128445029213)) (n := 12)
    (lo := (53654947 / 1000000000)) (hi := (13413737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65945029213 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65945029213 / 62500000000) = 1/(31250000000 / 65945029213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (746802127 / 1000000000) (746802129 / 1000000000) (Real.log (65945029213 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (65945029213 / 31250000000) = -Real.log (31250000000 / 65945029213) := by
    rw [show ((65945029213 / 31250000000) : ℝ) = ((31250000000 / 65945029213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (133748899 / 250000000) ≤ -Real.log (488281250 / 833711291) ∧
    -Real.log (488281250 / 833711291) ≤ (534995597 / 1000000000) := by
  have h := checkLog_sound (w := (345430041 / 1321992541)) (n := 12)
    (lo := (133748899 / 250000000)) (hi := (534995597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833711291 / 488281250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833711291 / 488281250) = 1/(488281250 / 833711291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (133748899 / 250000000) (534995597 / 1000000000) (Real.log (833711291 / 488281250)) := by
  have h := reflection_log_19_neg
  have he : Real.log (833711291 / 488281250) = -Real.log (488281250 / 833711291) := by
    rw [show ((833711291 / 488281250) : ℝ) = ((488281250 / 833711291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (133930837 / 250000000) ≤ -Real.log (62500000000 / 106792735581) ∧
    -Real.log (62500000000 / 106792735581) ≤ (535723349 / 1000000000) := by
  have h := checkLog_sound (w := (44292735581 / 169292735581)) (n := 12)
    (lo := (133930837 / 250000000)) (hi := (535723349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106792735581 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106792735581 / 62500000000) = 1/(62500000000 / 106792735581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (133930837 / 250000000) (535723349 / 1000000000) (Real.log (106792735581 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (106792735581 / 62500000000) = -Real.log (62500000000 / 106792735581) := by
    rw [show ((106792735581 / 62500000000) : ℝ) = ((62500000000 / 106792735581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0305

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0306Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0306
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

theorem reflection_log_1_neg : (44503671 / 200000000) ≤ -Real.log (1280 / 1599) ∧
    -Real.log (1280 / 1599) ≤ (55629589 / 250000000) := by
  have h := checkLog_sound (w := (319 / 2879)) (n := 12)
    (lo := (44503671 / 200000000)) (hi := (55629589 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1599 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1599 / 1280) = 1/(1280 / 1599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (44503671 / 200000000) (55629589 / 250000000) (Real.log (1599 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1599 / 1280) = -Real.log (1280 / 1599) := by
    rw [show ((1599 / 1280) : ℝ) = ((1280 / 1599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (286640947 / 1000000000) ≤ -Real.log (961 / 1280) ∧
    -Real.log (961 / 1280) ≤ (71660237 / 250000000) := by
  have h := checkLog_sound (w := (319 / 2241)) (n := 12)
    (lo := (286640947 / 1000000000)) (hi := (71660237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 961) = 1/(961 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-71660237 / 250000000) (-286640947 / 1000000000) (Real.log (961 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (111141903 / 500000000) ≤ -Real.log (10240 / 12789) ∧
    -Real.log (10240 / 12789) ≤ (222283807 / 1000000000) := by
  have h := checkLog_sound (w := (2549 / 23029)) (n := 12)
    (lo := (111141903 / 500000000)) (hi := (222283807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12789 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12789 / 10240) = 1/(10240 / 12789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (111141903 / 500000000) (222283807 / 1000000000) (Real.log (12789 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12789 / 10240) = -Real.log (10240 / 12789) := by
    rw [show ((12789 / 10240) : ℝ) = ((10240 / 12789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57250161 / 200000000) ≤ -Real.log (7691 / 10240) ∧
    -Real.log (7691 / 10240) ≤ (143125403 / 500000000) := by
  have h := checkLog_sound (w := (2549 / 17931)) (n := 12)
    (lo := (57250161 / 200000000)) (hi := (143125403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7691) = 1/(7691 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-143125403 / 500000000) (-57250161 / 200000000) (Real.log (7691 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (202211449 / 500000000) ≤ -Real.log (640 / 959) ∧
    -Real.log (640 / 959) ≤ (404422899 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1599)) (n := 12)
    (lo := (202211449 / 500000000)) (hi := (404422899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959 / 640) = 1/(640 / 959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (202211449 / 500000000) (404422899 / 1000000000) (Real.log (959 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (959 / 640) = -Real.log (640 / 959) := by
    rw [show ((959 / 640) : ℝ) = ((640 / 959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (690027053 / 1000000000) ≤ -Real.log (321 / 640) ∧
    -Real.log (321 / 640) ≤ (345013527 / 500000000) := by
  have h := checkLog_sound (w := (319 / 961)) (n := 12)
    (lo := (690027053 / 1000000000)) (hi := (345013527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 321) = 1/(321 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-345013527 / 500000000) (-690027053 / 1000000000) (Real.log (321 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (404031789 / 1000000000) ≤ -Real.log (5120 / 7669) ∧
    -Real.log (5120 / 7669) ≤ (40403179 / 100000000) := by
  have h := checkLog_sound (w := (2549 / 12789)) (n := 12)
    (lo := (404031789 / 1000000000)) (hi := (40403179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7669 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7669 / 5120) = 1/(5120 / 7669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (404031789 / 1000000000) (40403179 / 100000000) (Real.log (7669 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7669 / 5120) = -Real.log (5120 / 7669) := by
    rw [show ((7669 / 5120) : ℝ) = ((5120 / 7669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (68885951 / 100000000) ≤ -Real.log (2571 / 5120) ∧
    -Real.log (2571 / 5120) ≤ (688859511 / 1000000000) := by
  have h := checkLog_sound (w := (2549 / 7691)) (n := 12)
    (lo := (68885951 / 100000000)) (hi := (688859511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2571) = 1/(2571 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-688859511 / 1000000000) (-68885951 / 100000000) (Real.log (2571 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (304614407 / 1000000000) ≤ -Real.log (500000 / 678051) ∧
    -Real.log (500000 / 678051) ≤ (38076801 / 125000000) := by
  have h := checkLog_sound (w := (178051 / 1178051)) (n := 12)
    (lo := (304614407 / 1000000000)) (hi := (38076801 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678051 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678051 / 500000) = 1/(500000 / 678051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (304614407 / 1000000000) (38076801 / 125000000) (Real.log (678051 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (678051 / 500000) = -Real.log (500000 / 678051) := by
    rw [show ((678051 / 500000) : ℝ) = ((500000 / 678051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8804299 / 20000000) ≤ -Real.log (321949 / 500000) ∧
    -Real.log (321949 / 500000) ≤ (440214951 / 1000000000) := by
  have h := checkLog_sound (w := (178051 / 821949)) (n := 12)
    (lo := (8804299 / 20000000)) (hi := (440214951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 321949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 321949) = 1/(321949 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-440214951 / 1000000000) (-8804299 / 20000000) (Real.log (321949 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15246609 / 50000000) ≤ -Real.log (1000000 / 1356533) ∧
    -Real.log (1000000 / 1356533) ≤ (304932181 / 1000000000) := by
  have h := checkLog_sound (w := (356533 / 2356533)) (n := 12)
    (lo := (15246609 / 50000000)) (hi := (304932181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1356533 / 1000000) = 1/(1000000 / 1356533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15246609 / 50000000) (304932181 / 1000000000) (Real.log (1356533 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1356533 / 1000000) = -Real.log (1000000 / 1356533) := by
    rw [show ((1356533 / 1000000) : ℝ) = ((1000000 / 1356533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (88176907 / 200000000) ≤ -Real.log (643467 / 1000000) ∧
    -Real.log (643467 / 1000000) ≤ (55110567 / 125000000) := by
  have h := checkLog_sound (w := (356533 / 1643467)) (n := 12)
    (lo := (88176907 / 200000000)) (hi := (55110567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 643467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 643467) = 1/(643467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-55110567 / 125000000) (-88176907 / 200000000) (Real.log (643467 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (57967739 / 250000000) ≤ -Real.log (1000000 / 1260957) ∧
    -Real.log (1000000 / 1260957) ≤ (231870957 / 1000000000) := by
  have h := checkLog_sound (w := (260957 / 2260957)) (n := 12)
    (lo := (57967739 / 250000000)) (hi := (231870957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260957 / 1000000) = 1/(1000000 / 1260957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (57967739 / 250000000) (231870957 / 1000000000) (Real.log (1260957 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1260957 / 1000000) = -Real.log (1000000 / 1260957) := by
    rw [show ((1260957 / 1000000) : ℝ) = ((1000000 / 1260957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (75599793 / 250000000) ≤ -Real.log (739043 / 1000000) ∧
    -Real.log (739043 / 1000000) ≤ (302399173 / 1000000000) := by
  have h := checkLog_sound (w := (260957 / 1739043)) (n := 12)
    (lo := (75599793 / 250000000)) (hi := (302399173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739043) = 1/(739043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-302399173 / 1000000000) (-75599793 / 250000000) (Real.log (739043 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (232139763 / 1000000000) ≤ -Real.log (62500 / 78831) ∧
    -Real.log (62500 / 78831) ≤ (58034941 / 250000000) := by
  have h := checkLog_sound (w := (16331 / 141331)) (n := 12)
    (lo := (232139763 / 1000000000)) (hi := (58034941 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78831 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78831 / 62500) = 1/(62500 / 78831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (232139763 / 1000000000) (58034941 / 250000000) (Real.log (78831 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (78831 / 62500) = -Real.log (62500 / 78831) := by
    rw [show ((78831 / 62500) : ℝ) = ((62500 / 78831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (302857979 / 1000000000) ≤ -Real.log (46169 / 62500) ∧
    -Real.log (46169 / 62500) ≤ (15142899 / 50000000) := by
  have h := checkLog_sound (w := (16331 / 108669)) (n := 12)
    (lo := (302857979 / 1000000000)) (hi := (15142899 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46169) = 1/(46169 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-15142899 / 50000000) (-302857979 / 1000000000) (Real.log (46169 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (744829357 / 1000000000) ≤ -Real.log (312500000 / 658150631) ∧
    -Real.log (312500000 / 658150631) ≤ (744829359 / 1000000000) := by
  have h := checkLog_sound (w := (33150631 / 1283150631)) (n := 12)
    (lo := (51682177 / 1000000000)) (hi := (25841089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658150631 / 625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(658150631 / 625000000) = 1/(312500000 / 658150631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (744829357 / 1000000000) (744829359 / 1000000000) (Real.log (658150631 / 312500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (658150631 / 312500000) = -Real.log (312500000 / 658150631) := by
    rw [show ((658150631 / 312500000) : ℝ) = ((312500000 / 658150631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (372908357 / 500000000) ≤ -Real.log (125000000000 / 263520312619) ∧
    -Real.log (125000000000 / 263520312619) ≤ (186454179 / 250000000) := by
  have h := checkLog_sound (w := (13520312619 / 513520312619)) (n := 12)
    (lo := (26334767 / 500000000)) (hi := (10533907 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263520312619 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(263520312619 / 250000000000) = 1/(125000000000 / 263520312619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (372908357 / 500000000) (186454179 / 250000000) (Real.log (263520312619 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (263520312619 / 125000000000) = -Real.log (125000000000 / 263520312619) := by
    rw [show ((263520312619 / 125000000000) : ℝ) = ((125000000000 / 263520312619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (534270129 / 1000000000) ≤ -Real.log (500000000000 / 853101240387) ∧
    -Real.log (500000000000 / 853101240387) ≤ (53427013 / 100000000) := by
  have h := checkLog_sound (w := (353101240387 / 1353101240387)) (n := 12)
    (lo := (534270129 / 1000000000)) (hi := (53427013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853101240387 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853101240387 / 500000000000) = 1/(500000000000 / 853101240387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (534270129 / 1000000000) (53427013 / 100000000) (Real.log (853101240387 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (853101240387 / 500000000000) = -Real.log (500000000000 / 853101240387) := by
    rw [show ((853101240387 / 500000000000) : ℝ) = ((500000000000 / 853101240387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (534997743 / 1000000000) ≤ -Real.log (500000000000 / 853722194547) ∧
    -Real.log (500000000000 / 853722194547) ≤ (33437359 / 62500000) := by
  have h := checkLog_sound (w := (353722194547 / 1353722194547)) (n := 12)
    (lo := (534997743 / 1000000000)) (hi := (33437359 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853722194547 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853722194547 / 500000000000) = 1/(500000000000 / 853722194547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (534997743 / 1000000000) (33437359 / 62500000) (Real.log (853722194547 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (853722194547 / 500000000000) = -Real.log (500000000000 / 853722194547) := by
    rw [show ((853722194547 / 500000000000) : ℝ) = ((500000000000 / 853722194547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0306

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0307Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0307
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

theorem reflection_log_1_neg : (111141903 / 500000000) ≤ -Real.log (10240 / 12789) ∧
    -Real.log (10240 / 12789) ≤ (222283807 / 1000000000) := by
  have h := checkLog_sound (w := (2549 / 23029)) (n := 12)
    (lo := (111141903 / 500000000)) (hi := (222283807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12789 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12789 / 10240) = 1/(10240 / 12789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (111141903 / 500000000) (222283807 / 1000000000) (Real.log (12789 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12789 / 10240) = -Real.log (10240 / 12789) := by
    rw [show ((12789 / 10240) : ℝ) = ((10240 / 12789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57250161 / 200000000) ≤ -Real.log (7691 / 10240) ∧
    -Real.log (7691 / 10240) ≤ (143125403 / 500000000) := by
  have h := checkLog_sound (w := (2549 / 17931)) (n := 12)
    (lo := (57250161 / 200000000)) (hi := (143125403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7691) = 1/(7691 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-143125403 / 500000000) (-57250161 / 200000000) (Real.log (7691 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (111024601 / 500000000) ≤ -Real.log (5120 / 6393) ∧
    -Real.log (5120 / 6393) ≤ (222049203 / 1000000000) := by
  have h := checkLog_sound (w := (1273 / 11513)) (n := 12)
    (lo := (111024601 / 500000000)) (hi := (222049203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6393 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6393 / 5120) = 1/(5120 / 6393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (111024601 / 500000000) (222049203 / 1000000000) (Real.log (6393 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6393 / 5120) = -Real.log (5120 / 6393) := by
    rw [show ((6393 / 5120) : ℝ) = ((5120 / 6393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57172163 / 200000000) ≤ -Real.log (3847 / 5120) ∧
    -Real.log (3847 / 5120) ≤ (17866301 / 62500000) := by
  have h := checkLog_sound (w := (1273 / 8967)) (n := 12)
    (lo := (57172163 / 200000000)) (hi := (17866301 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3847) = 1/(3847 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-17866301 / 62500000) (-57172163 / 200000000) (Real.log (3847 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (404031789 / 1000000000) ≤ -Real.log (5120 / 7669) ∧
    -Real.log (5120 / 7669) ≤ (40403179 / 100000000) := by
  have h := checkLog_sound (w := (2549 / 12789)) (n := 12)
    (lo := (404031789 / 1000000000)) (hi := (40403179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7669 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7669 / 5120) = 1/(5120 / 7669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (404031789 / 1000000000) (40403179 / 100000000) (Real.log (7669 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7669 / 5120) = -Real.log (5120 / 7669) := by
    rw [show ((7669 / 5120) : ℝ) = ((5120 / 7669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (68885951 / 100000000) ≤ -Real.log (2571 / 5120) ∧
    -Real.log (2571 / 5120) ≤ (688859511 / 1000000000) := by
  have h := checkLog_sound (w := (2549 / 7691)) (n := 12)
    (lo := (68885951 / 100000000)) (hi := (688859511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2571) = 1/(2571 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-688859511 / 1000000000) (-68885951 / 100000000) (Real.log (2571 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (403640527 / 1000000000) ≤ -Real.log (2560 / 3833) ∧
    -Real.log (2560 / 3833) ≤ (25227533 / 62500000) := by
  have h := checkLog_sound (w := (1273 / 6393)) (n := 12)
    (lo := (403640527 / 1000000000)) (hi := (25227533 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3833 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3833 / 2560) = 1/(2560 / 3833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (403640527 / 1000000000) (25227533 / 62500000) (Real.log (3833 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3833 / 2560) = -Real.log (2560 / 3833) := by
    rw [show ((3833 / 2560) : ℝ) = ((2560 / 3833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (687693329 / 1000000000) ≤ -Real.log (1287 / 2560) ∧
    -Real.log (1287 / 2560) ≤ (68769333 / 100000000) := by
  have h := checkLog_sound (w := (1273 / 3847)) (n := 12)
    (lo := (687693329 / 1000000000)) (hi := (68769333 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1287) = 1/(1287 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-68769333 / 100000000) (-687693329 / 1000000000) (Real.log (1287 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38037159 / 125000000) ≤ -Real.log (125000 / 169459) ∧
    -Real.log (125000 / 169459) ≤ (304297273 / 1000000000) := by
  have h := checkLog_sound (w := (44459 / 294459)) (n := 12)
    (lo := (38037159 / 125000000)) (hi := (304297273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169459 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169459 / 125000) = 1/(125000 / 169459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38037159 / 125000000) (304297273 / 1000000000) (Real.log (169459 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (169459 / 125000) = -Real.log (125000 / 169459) := by
    rw [show ((169459 / 125000) : ℝ) = ((125000 / 169459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (87909473 / 200000000) ≤ -Real.log (80541 / 125000) ∧
    -Real.log (80541 / 125000) ≤ (219773683 / 500000000) := by
  have h := checkLog_sound (w := (44459 / 205541)) (n := 12)
    (lo := (87909473 / 200000000)) (hi := (219773683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 80541) = 1/(80541 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-219773683 / 500000000) (-87909473 / 200000000) (Real.log (80541 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (60923029 / 200000000) ≤ -Real.log (1000000 / 1356103) ∧
    -Real.log (1000000 / 1356103) ≤ (152307573 / 500000000) := by
  have h := checkLog_sound (w := (356103 / 2356103)) (n := 12)
    (lo := (60923029 / 200000000)) (hi := (152307573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1356103 / 1000000) = 1/(1000000 / 1356103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (60923029 / 200000000) (152307573 / 500000000) (Real.log (1356103 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1356103 / 1000000) = -Real.log (1000000 / 1356103) := by
    rw [show ((1356103 / 1000000) : ℝ) = ((1000000 / 1356103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (440216503 / 1000000000) ≤ -Real.log (643897 / 1000000) ∧
    -Real.log (643897 / 1000000) ≤ (55027063 / 125000000) := by
  have h := checkLog_sound (w := (356103 / 1643897)) (n := 12)
    (lo := (440216503 / 1000000000)) (hi := (55027063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 643897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 643897) = 1/(643897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-55027063 / 125000000) (-440216503 / 1000000000) (Real.log (643897 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23160287 / 100000000) ≤ -Real.log (1000000 / 1260619) ∧
    -Real.log (1000000 / 1260619) ≤ (231602871 / 1000000000) := by
  have h := checkLog_sound (w := (260619 / 2260619)) (n := 12)
    (lo := (23160287 / 100000000)) (hi := (231602871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260619 / 1000000) = 1/(1000000 / 1260619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23160287 / 100000000) (231602871 / 1000000000) (Real.log (1260619 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1260619 / 1000000) = -Real.log (1000000 / 1260619) := by
    rw [show ((1260619 / 1000000) : ℝ) = ((1000000 / 1260619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (301941929 / 1000000000) ≤ -Real.log (739381 / 1000000) ∧
    -Real.log (739381 / 1000000) ≤ (30194193 / 100000000) := by
  have h := checkLog_sound (w := (260619 / 1739381)) (n := 12)
    (lo := (301941929 / 1000000000)) (hi := (30194193 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739381) = 1/(739381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-30194193 / 100000000) (-301941929 / 1000000000) (Real.log (739381 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (231871749 / 1000000000) ≤ -Real.log (500000 / 630479) ∧
    -Real.log (500000 / 630479) ≤ (927487 / 4000000) := by
  have h := checkLog_sound (w := (130479 / 1130479)) (n := 12)
    (lo := (231871749 / 1000000000)) (hi := (927487 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630479 / 500000) = 1/(500000 / 630479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (231871749 / 1000000000) (927487 / 4000000) (Real.log (630479 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (630479 / 500000) = -Real.log (500000 / 630479) := by
    rw [show ((630479 / 500000) : ℝ) = ((500000 / 630479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (151200263 / 500000000) ≤ -Real.log (369521 / 500000) ∧
    -Real.log (369521 / 500000) ≤ (302400527 / 1000000000) := by
  have h := checkLog_sound (w := (130479 / 869521)) (n := 12)
    (lo := (151200263 / 500000000)) (hi := (302400527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 369521) = 1/(369521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-302400527 / 1000000000) (-151200263 / 500000000) (Real.log (369521 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (743844637 / 1000000000) ≤ -Real.log (500000000000 / 1052004569101) ∧
    -Real.log (500000000000 / 1052004569101) ≤ (743844639 / 1000000000) := by
  have h := checkLog_sound (w := (52004569101 / 2052004569101)) (n := 12)
    (lo := (50697457 / 1000000000)) (hi := (25348729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1052004569101 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1052004569101 / 1000000000000) = 1/(500000000000 / 1052004569101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (743844637 / 1000000000) (743844639 / 1000000000) (Real.log (1052004569101 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1052004569101 / 500000000000) = -Real.log (500000000000 / 1052004569101) := by
    rw [show ((1052004569101 / 500000000000) : ℝ) = ((500000000000 / 1052004569101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (23275989 / 31250000) ≤ -Real.log (250000000000 / 526521710771) ∧
    -Real.log (250000000000 / 526521710771) ≤ (14896633 / 20000000) := by
  have h := checkLog_sound (w := (26521710771 / 1026521710771)) (n := 12)
    (lo := (12921117 / 250000000)) (hi := (51684469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((526521710771 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(526521710771 / 500000000000) = 1/(250000000000 / 526521710771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (23275989 / 31250000) (14896633 / 20000000) (Real.log (526521710771 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (526521710771 / 250000000000) = -Real.log (250000000000 / 526521710771) := by
    rw [show ((526521710771 / 250000000000) : ℝ) = ((250000000000 / 526521710771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (533544799 / 1000000000) ≤ -Real.log (12500000000 / 21312067121) ∧
    -Real.log (12500000000 / 21312067121) ≤ (666931 / 1250000) := by
  have h := checkLog_sound (w := (8812067121 / 33812067121)) (n := 12)
    (lo := (533544799 / 1000000000)) (hi := (666931 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21312067121 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21312067121 / 12500000000) = 1/(12500000000 / 21312067121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (533544799 / 1000000000) (666931 / 1250000) (Real.log (21312067121 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (21312067121 / 12500000000) = -Real.log (12500000000 / 21312067121) := by
    rw [show ((21312067121 / 12500000000) : ℝ) = ((12500000000 / 21312067121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (21370891 / 40000000) ≤ -Real.log (250000000000 / 426551535637) ∧
    -Real.log (250000000000 / 426551535637) ≤ (133568069 / 250000000) := by
  have h := checkLog_sound (w := (176551535637 / 676551535637)) (n := 12)
    (lo := (21370891 / 40000000)) (hi := (133568069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((426551535637 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(426551535637 / 250000000000) = 1/(250000000000 / 426551535637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (21370891 / 40000000) (133568069 / 250000000) (Real.log (426551535637 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (426551535637 / 250000000000) = -Real.log (250000000000 / 426551535637) := by
    rw [show ((426551535637 / 250000000000) : ℝ) = ((250000000000 / 426551535637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0307

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0308Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0308
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

theorem reflection_log_1_neg : (111024601 / 500000000) ≤ -Real.log (5120 / 6393) ∧
    -Real.log (5120 / 6393) ≤ (222049203 / 1000000000) := by
  have h := checkLog_sound (w := (1273 / 11513)) (n := 12)
    (lo := (111024601 / 500000000)) (hi := (222049203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6393 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6393 / 5120) = 1/(5120 / 6393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (111024601 / 500000000) (222049203 / 1000000000) (Real.log (6393 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6393 / 5120) = -Real.log (5120 / 6393) := by
    rw [show ((6393 / 5120) : ℝ) = ((5120 / 6393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57172163 / 200000000) ≤ -Real.log (3847 / 5120) ∧
    -Real.log (3847 / 5120) ≤ (17866301 / 62500000) := by
  have h := checkLog_sound (w := (1273 / 8967)) (n := 12)
    (lo := (57172163 / 200000000)) (hi := (17866301 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3847) = 1/(3847 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-17866301 / 62500000) (-57172163 / 200000000) (Real.log (3847 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (221814543 / 1000000000) ≤ -Real.log (10240 / 12783) ∧
    -Real.log (10240 / 12783) ≤ (13863409 / 62500000) := by
  have h := checkLog_sound (w := (2543 / 23023)) (n := 12)
    (lo := (221814543 / 1000000000)) (hi := (13863409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12783 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12783 / 10240) = 1/(10240 / 12783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (221814543 / 1000000000) (13863409 / 62500000) (Real.log (12783 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12783 / 10240) = -Real.log (10240 / 12783) := by
    rw [show ((12783 / 10240) : ℝ) = ((10240 / 12783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (285470977 / 1000000000) ≤ -Real.log (7697 / 10240) ∧
    -Real.log (7697 / 10240) ≤ (142735489 / 500000000) := by
  have h := checkLog_sound (w := (2543 / 17937)) (n := 12)
    (lo := (285470977 / 1000000000)) (hi := (142735489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7697) = 1/(7697 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-142735489 / 500000000) (-285470977 / 1000000000) (Real.log (7697 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (403640527 / 1000000000) ≤ -Real.log (2560 / 3833) ∧
    -Real.log (2560 / 3833) ≤ (25227533 / 62500000) := by
  have h := checkLog_sound (w := (1273 / 6393)) (n := 12)
    (lo := (403640527 / 1000000000)) (hi := (25227533 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3833 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3833 / 2560) = 1/(2560 / 3833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (403640527 / 1000000000) (25227533 / 62500000) (Real.log (3833 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3833 / 2560) = -Real.log (2560 / 3833) := by
    rw [show ((3833 / 2560) : ℝ) = ((2560 / 3833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (687693329 / 1000000000) ≤ -Real.log (1287 / 2560) ∧
    -Real.log (1287 / 2560) ≤ (68769333 / 100000000) := by
  have h := checkLog_sound (w := (1273 / 3847)) (n := 12)
    (lo := (687693329 / 1000000000)) (hi := (68769333 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1287) = 1/(1287 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-68769333 / 100000000) (-687693329 / 1000000000) (Real.log (1287 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (50406139 / 125000000) ≤ -Real.log (5120 / 7663) ∧
    -Real.log (5120 / 7663) ≤ (403249113 / 1000000000) := by
  have h := checkLog_sound (w := (2543 / 12783)) (n := 12)
    (lo := (50406139 / 125000000)) (hi := (403249113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7663 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7663 / 5120) = 1/(5120 / 7663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (50406139 / 125000000) (403249113 / 1000000000) (Real.log (7663 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7663 / 5120) = -Real.log (5120 / 7663) := by
    rw [show ((7663 / 5120) : ℝ) = ((5120 / 7663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (686528507 / 1000000000) ≤ -Real.log (2577 / 5120) ∧
    -Real.log (2577 / 5120) ≤ (171632127 / 250000000) := by
  have h := checkLog_sound (w := (2543 / 7697)) (n := 12)
    (lo := (686528507 / 1000000000)) (hi := (171632127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2577) = 1/(2577 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-171632127 / 250000000) (-686528507 / 1000000000) (Real.log (2577 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75995009 / 250000000) ≤ -Real.log (500000 / 677621) ∧
    -Real.log (500000 / 677621) ≤ (303980037 / 1000000000) := by
  have h := checkLog_sound (w := (177621 / 1177621)) (n := 12)
    (lo := (75995009 / 250000000)) (hi := (303980037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677621 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677621 / 500000) = 1/(500000 / 677621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75995009 / 250000000) (303980037 / 1000000000) (Real.log (677621 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (677621 / 500000) = -Real.log (500000 / 677621) := by
    rw [show ((677621 / 500000) : ℝ) = ((500000 / 677621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (219440113 / 500000000) ≤ -Real.log (322379 / 500000) ∧
    -Real.log (322379 / 500000) ≤ (438880227 / 1000000000) := by
  have h := checkLog_sound (w := (177621 / 822379)) (n := 12)
    (lo := (219440113 / 500000000)) (hi := (438880227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 322379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 322379) = 1/(322379 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-438880227 / 1000000000) (-219440113 / 500000000) (Real.log (322379 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (304298009 / 1000000000) ≤ -Real.log (1000000 / 1355673) ∧
    -Real.log (1000000 / 1355673) ≤ (30429801 / 100000000) := by
  have h := checkLog_sound (w := (355673 / 2355673)) (n := 12)
    (lo := (304298009 / 1000000000)) (hi := (30429801 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355673 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1355673 / 1000000) = 1/(1000000 / 1355673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (304298009 / 1000000000) (30429801 / 100000000) (Real.log (1355673 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1355673 / 1000000) = -Real.log (1000000 / 1355673) := by
    rw [show ((1355673 / 1000000) : ℝ) = ((1000000 / 1355673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (439548917 / 1000000000) ≤ -Real.log (644327 / 1000000) ∧
    -Real.log (644327 / 1000000) ≤ (219774459 / 500000000) := by
  have h := checkLog_sound (w := (355673 / 1644327)) (n := 12)
    (lo := (439548917 / 1000000000)) (hi := (219774459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 644327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 644327) = 1/(644327 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-219774459 / 500000000) (-439548917 / 1000000000) (Real.log (644327 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (46267101 / 200000000) ≤ -Real.log (500000 / 630141) ∧
    -Real.log (500000 / 630141) ≤ (115667753 / 500000000) := by
  have h := checkLog_sound (w := (130141 / 1130141)) (n := 12)
    (lo := (46267101 / 200000000)) (hi := (115667753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630141 / 500000) = 1/(500000 / 630141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (46267101 / 200000000) (115667753 / 500000000) (Real.log (630141 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (630141 / 500000) = -Real.log (500000 / 630141) := by
    rw [show ((630141 / 500000) : ℝ) = ((500000 / 630141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (150743123 / 500000000) ≤ -Real.log (369859 / 500000) ∧
    -Real.log (369859 / 500000) ≤ (301486247 / 1000000000) := by
  have h := checkLog_sound (w := (130141 / 869859)) (n := 12)
    (lo := (150743123 / 500000000)) (hi := (301486247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 369859) = 1/(369859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-301486247 / 1000000000) (-150743123 / 500000000) (Real.log (369859 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (231603663 / 1000000000) ≤ -Real.log (50000 / 63031) ∧
    -Real.log (50000 / 63031) ≤ (14475229 / 62500000) := by
  have h := checkLog_sound (w := (13031 / 113031)) (n := 12)
    (lo := (231603663 / 1000000000)) (hi := (14475229 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63031 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63031 / 50000) = 1/(50000 / 63031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (231603663 / 1000000000) (14475229 / 62500000) (Real.log (63031 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (63031 / 50000) = -Real.log (50000 / 63031) := by
    rw [show ((63031 / 50000) : ℝ) = ((50000 / 63031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (301943281 / 1000000000) ≤ -Real.log (36969 / 50000) ∧
    -Real.log (36969 / 50000) ≤ (150971641 / 500000000) := by
  have h := checkLog_sound (w := (13031 / 86969)) (n := 12)
    (lo := (301943281 / 1000000000)) (hi := (150971641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36969) = 1/(36969 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-150971641 / 500000000) (-301943281 / 1000000000) (Real.log (36969 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (742860261 / 1000000000) ≤ -Real.log (500000000000 / 1050969511041) ∧
    -Real.log (500000000000 / 1050969511041) ≤ (742860263 / 1000000000) := by
  have h := checkLog_sound (w := (50969511041 / 2050969511041)) (n := 12)
    (lo := (49713081 / 1000000000)) (hi := (24856541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1050969511041 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1050969511041 / 1000000000000) = 1/(500000000000 / 1050969511041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (742860261 / 1000000000) (742860263 / 1000000000) (Real.log (1050969511041 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1050969511041 / 500000000000) = -Real.log (500000000000 / 1050969511041) := by
    rw [show ((1050969511041 / 500000000000) : ℝ) = ((500000000000 / 1050969511041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (743846927 / 1000000000) ≤ -Real.log (15625000000 / 32875218057) ∧
    -Real.log (15625000000 / 32875218057) ≤ (743846929 / 1000000000) := by
  have h := checkLog_sound (w := (1625218057 / 64125218057)) (n := 12)
    (lo := (50699747 / 1000000000)) (hi := (12674937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32875218057 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32875218057 / 31250000000) = 1/(15625000000 / 32875218057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (743846927 / 1000000000) (743846929 / 1000000000) (Real.log (32875218057 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (32875218057 / 15625000000) = -Real.log (15625000000 / 32875218057) := by
    rw [show ((32875218057 / 15625000000) : ℝ) = ((15625000000 / 32875218057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (532821751 / 1000000000) ≤ -Real.log (500000000000 / 851866522107) ∧
    -Real.log (500000000000 / 851866522107) ≤ (66602719 / 125000000) := by
  have h := checkLog_sound (w := (351866522107 / 1351866522107)) (n := 12)
    (lo := (532821751 / 1000000000)) (hi := (66602719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851866522107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851866522107 / 500000000000) = 1/(500000000000 / 851866522107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (532821751 / 1000000000) (66602719 / 125000000) (Real.log (851866522107 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (851866522107 / 500000000000) = -Real.log (500000000000 / 851866522107) := by
    rw [show ((851866522107 / 500000000000) : ℝ) = ((500000000000 / 851866522107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (106709389 / 200000000) ≤ -Real.log (500000000000 / 852484514053) ∧
    -Real.log (500000000000 / 852484514053) ≤ (266773473 / 500000000) := by
  have h := checkLog_sound (w := (352484514053 / 1352484514053)) (n := 12)
    (lo := (106709389 / 200000000)) (hi := (266773473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((852484514053 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(852484514053 / 500000000000) = 1/(500000000000 / 852484514053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (106709389 / 200000000) (266773473 / 500000000) (Real.log (852484514053 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (852484514053 / 500000000000) = -Real.log (500000000000 / 852484514053) := by
    rw [show ((852484514053 / 500000000000) : ℝ) = ((500000000000 / 852484514053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0308

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0309Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0309
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

theorem reflection_log_1_neg : (221814543 / 1000000000) ≤ -Real.log (10240 / 12783) ∧
    -Real.log (10240 / 12783) ≤ (13863409 / 62500000) := by
  have h := checkLog_sound (w := (2543 / 23023)) (n := 12)
    (lo := (221814543 / 1000000000)) (hi := (13863409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12783 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12783 / 10240) = 1/(10240 / 12783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (221814543 / 1000000000) (13863409 / 62500000) (Real.log (12783 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12783 / 10240) = -Real.log (10240 / 12783) := by
    rw [show ((12783 / 10240) : ℝ) = ((10240 / 12783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (285470977 / 1000000000) ≤ -Real.log (7697 / 10240) ∧
    -Real.log (7697 / 10240) ≤ (142735489 / 500000000) := by
  have h := checkLog_sound (w := (2543 / 17937)) (n := 12)
    (lo := (285470977 / 1000000000)) (hi := (142735489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7697) = 1/(7697 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-142735489 / 500000000) (-285470977 / 1000000000) (Real.log (7697 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (221579829 / 1000000000) ≤ -Real.log (512 / 639) ∧
    -Real.log (512 / 639) ≤ (22157983 / 100000000) := by
  have h := checkLog_sound (w := (127 / 1151)) (n := 12)
    (lo := (221579829 / 1000000000)) (hi := (22157983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639 / 512) = 1/(512 / 639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (221579829 / 1000000000) (22157983 / 100000000) (Real.log (639 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (639 / 512) = -Real.log (512 / 639) := by
    rw [show ((639 / 512) : ℝ) = ((512 / 639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (28508129 / 100000000) ≤ -Real.log (385 / 512) ∧
    -Real.log (385 / 512) ≤ (285081291 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 897)) (n := 12)
    (lo := (28508129 / 100000000)) (hi := (285081291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 385) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 385) = 1/(385 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-285081291 / 1000000000) (-28508129 / 100000000) (Real.log (385 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (50406139 / 125000000) ≤ -Real.log (5120 / 7663) ∧
    -Real.log (5120 / 7663) ≤ (403249113 / 1000000000) := by
  have h := checkLog_sound (w := (2543 / 12783)) (n := 12)
    (lo := (50406139 / 125000000)) (hi := (403249113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7663 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7663 / 5120) = 1/(5120 / 7663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (50406139 / 125000000) (403249113 / 1000000000) (Real.log (7663 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7663 / 5120) = -Real.log (5120 / 7663) := by
    rw [show ((7663 / 5120) : ℝ) = ((5120 / 7663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (686528507 / 1000000000) ≤ -Real.log (2577 / 5120) ∧
    -Real.log (2577 / 5120) ≤ (171632127 / 250000000) := by
  have h := checkLog_sound (w := (2543 / 7697)) (n := 12)
    (lo := (686528507 / 1000000000)) (hi := (171632127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2577) = 1/(2577 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-171632127 / 250000000) (-686528507 / 1000000000) (Real.log (2577 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (50357193 / 125000000) ≤ -Real.log (256 / 383) ∧
    -Real.log (256 / 383) ≤ (80571509 / 200000000) := by
  have h := checkLog_sound (w := (127 / 639)) (n := 12)
    (lo := (50357193 / 125000000)) (hi := (80571509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383 / 256) = 1/(256 / 383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (50357193 / 125000000) (80571509 / 200000000) (Real.log (383 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (383 / 256) = -Real.log (256 / 383) := by
    rw [show ((383 / 256) : ℝ) = ((256 / 383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (8567063 / 12500000) ≤ -Real.log (129 / 256) ∧
    -Real.log (129 / 256) ≤ (685365041 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 385)) (n := 12)
    (lo := (8567063 / 12500000)) (hi := (685365041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 129) = 1/(129 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-685365041 / 1000000000) (-8567063 / 12500000) (Real.log (129 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (303662699 / 1000000000) ≤ -Real.log (250000 / 338703) ∧
    -Real.log (250000 / 338703) ≤ (3036627 / 10000000) := by
  have h := checkLog_sound (w := (88703 / 588703)) (n := 12)
    (lo := (303662699 / 1000000000)) (hi := (3036627 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338703 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338703 / 250000) = 1/(250000 / 338703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (303662699 / 1000000000) (3036627 / 10000000) (Real.log (338703 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (338703 / 250000) = -Real.log (250000 / 338703) := by
    rw [show ((338703 / 250000) : ℝ) = ((250000 / 338703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (438213531 / 1000000000) ≤ -Real.log (161297 / 250000) ∧
    -Real.log (161297 / 250000) ≤ (109553383 / 250000000) := by
  have h := checkLog_sound (w := (88703 / 411297)) (n := 12)
    (lo := (438213531 / 1000000000)) (hi := (109553383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 161297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 161297) = 1/(161297 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-109553383 / 250000000) (-438213531 / 1000000000) (Real.log (161297 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (151990387 / 500000000) ≤ -Real.log (1000000 / 1355243) ∧
    -Real.log (1000000 / 1355243) ≤ (12159231 / 40000000) := by
  have h := checkLog_sound (w := (355243 / 2355243)) (n := 12)
    (lo := (151990387 / 500000000)) (hi := (12159231 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1355243 / 1000000) = 1/(1000000 / 1355243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (151990387 / 500000000) (12159231 / 40000000) (Real.log (1355243 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1355243 / 1000000) = -Real.log (1000000 / 1355243) := by
    rw [show ((1355243 / 1000000) : ℝ) = ((1000000 / 1355243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (438881777 / 1000000000) ≤ -Real.log (644757 / 1000000) ∧
    -Real.log (644757 / 1000000) ≤ (219440889 / 500000000) := by
  have h := checkLog_sound (w := (355243 / 1644757)) (n := 12)
    (lo := (438881777 / 1000000000)) (hi := (219440889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 644757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 644757) = 1/(644757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-219440889 / 500000000) (-438881777 / 1000000000) (Real.log (644757 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9242691 / 40000000) ≤ -Real.log (125000 / 157493) ∧
    -Real.log (125000 / 157493) ≤ (57766819 / 250000000) := by
  have h := checkLog_sound (w := (32493 / 282493)) (n := 12)
    (lo := (9242691 / 40000000)) (hi := (57766819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157493 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157493 / 125000) = 1/(125000 / 157493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9242691 / 40000000) (57766819 / 250000000) (Real.log (157493 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (157493 / 125000) = -Real.log (125000 / 157493) := by
    rw [show ((157493 / 125000) : ℝ) = ((125000 / 157493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (301029419 / 1000000000) ≤ -Real.log (92507 / 125000) ∧
    -Real.log (92507 / 125000) ≤ (15051471 / 50000000) := by
  have h := checkLog_sound (w := (32493 / 217507)) (n := 12)
    (lo := (301029419 / 1000000000)) (hi := (15051471 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 92507) = 1/(92507 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-15051471 / 50000000) (-301029419 / 1000000000) (Real.log (92507 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (115668149 / 500000000) ≤ -Real.log (1000000 / 1260283) ∧
    -Real.log (1000000 / 1260283) ≤ (231336299 / 1000000000) := by
  have h := checkLog_sound (w := (260283 / 2260283)) (n := 12)
    (lo := (115668149 / 500000000)) (hi := (231336299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260283 / 1000000) = 1/(1000000 / 1260283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (115668149 / 500000000) (231336299 / 1000000000) (Real.log (1260283 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1260283 / 1000000) = -Real.log (1000000 / 1260283) := by
    rw [show ((1260283 / 1000000) : ℝ) = ((1000000 / 1260283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (150743799 / 500000000) ≤ -Real.log (739717 / 1000000) ∧
    -Real.log (739717 / 1000000) ≤ (301487599 / 1000000000) := by
  have h := checkLog_sound (w := (260283 / 1739717)) (n := 12)
    (lo := (150743799 / 500000000)) (hi := (301487599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739717) = 1/(739717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-301487599 / 1000000000) (-150743799 / 500000000) (Real.log (739717 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (74187623 / 100000000) ≤ -Real.log (31250000000 / 65620989541) ∧
    -Real.log (31250000000 / 65620989541) ≤ (92734529 / 125000000) := by
  have h := checkLog_sound (w := (3120989541 / 128120989541)) (n := 12)
    (lo := (974581 / 20000000)) (hi := (48729051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65620989541 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65620989541 / 62500000000) = 1/(31250000000 / 65620989541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (74187623 / 100000000) (92734529 / 125000000) (Real.log (65620989541 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (65620989541 / 31250000000) = -Real.log (31250000000 / 65620989541) := by
    rw [show ((65620989541 / 31250000000) : ℝ) = ((31250000000 / 65620989541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (14857251 / 20000000) ≤ -Real.log (62500000000 / 131371489569) ∧
    -Real.log (62500000000 / 131371489569) ≤ (92857819 / 125000000) := by
  have h := checkLog_sound (w := (6371489569 / 256371489569)) (n := 12)
    (lo := (4971537 / 100000000)) (hi := (49715371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131371489569 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(131371489569 / 125000000000) = 1/(62500000000 / 131371489569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (14857251 / 20000000) (92857819 / 125000000) (Real.log (131371489569 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (131371489569 / 62500000000) = -Real.log (62500000000 / 131371489569) := by
    rw [show ((131371489569 / 62500000000) : ℝ) = ((62500000000 / 131371489569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (106419339 / 200000000) ≤ -Real.log (500000000000 / 851249094663) ∧
    -Real.log (500000000000 / 851249094663) ≤ (66512087 / 125000000) := by
  have h := checkLog_sound (w := (351249094663 / 1351249094663)) (n := 12)
    (lo := (106419339 / 200000000)) (hi := (66512087 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851249094663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851249094663 / 500000000000) = 1/(500000000000 / 851249094663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (106419339 / 200000000) (66512087 / 125000000) (Real.log (851249094663 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (851249094663 / 500000000000) = -Real.log (500000000000 / 851249094663) := by
    rw [show ((851249094663 / 500000000000) : ℝ) = ((500000000000 / 851249094663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (532823897 / 1000000000) ≤ -Real.log (500000000000 / 851868349653) ∧
    -Real.log (500000000000 / 851868349653) ≤ (266411949 / 500000000) := by
  have h := checkLog_sound (w := (351868349653 / 1351868349653)) (n := 12)
    (lo := (532823897 / 1000000000)) (hi := (266411949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851868349653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851868349653 / 500000000000) = 1/(500000000000 / 851868349653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (532823897 / 1000000000) (266411949 / 500000000) (Real.log (851868349653 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (851868349653 / 500000000000) = -Real.log (500000000000 / 851868349653) := by
    rw [show ((851868349653 / 500000000000) : ℝ) = ((500000000000 / 851868349653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0309

end


