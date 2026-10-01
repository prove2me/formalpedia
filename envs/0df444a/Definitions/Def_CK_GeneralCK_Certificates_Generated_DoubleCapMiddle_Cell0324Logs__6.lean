-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0324Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0324Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:34:05.045043+00:00
-- url     : https://prove2.me/theorems/ea7ccadc-8f9a-48c9-8915-6f787746a513
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0324Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0325Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0324Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0325Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0326Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0327Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0328Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0329Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0324Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0325Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0326Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0327Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0328Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0329Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0324Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0325Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0326Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0327Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0328Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0329Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0324Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0325Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0326Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0327Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0328Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0329Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0324Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0324
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

theorem reflection_log_1_neg : (6821501 / 31250000) ≤ -Real.log (5120 / 6369) ∧
    -Real.log (5120 / 6369) ≤ (218288033 / 1000000000) := by
  have h := checkLog_sound (w := (1249 / 11489)) (n := 12)
    (lo := (6821501 / 31250000)) (hi := (218288033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6369 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6369 / 5120) = 1/(5120 / 6369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (6821501 / 31250000) (218288033 / 1000000000) (Real.log (6369 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6369 / 5120) = -Real.log (5120 / 6369) := by
    rw [show ((6369 / 5120) : ℝ) = ((5120 / 6369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (279641567 / 1000000000) ≤ -Real.log (3871 / 5120) ∧
    -Real.log (3871 / 5120) ≤ (8738799 / 31250000) := by
  have h := checkLog_sound (w := (1249 / 8991)) (n := 12)
    (lo := (279641567 / 1000000000)) (hi := (8738799 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3871) = 1/(3871 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-8738799 / 31250000) (-279641567 / 1000000000) (Real.log (3871 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27256561 / 125000000) ≤ -Real.log (2048 / 2547) ∧
    -Real.log (2048 / 2547) ≤ (218052489 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 4595)) (n := 12)
    (lo := (27256561 / 125000000)) (hi := (218052489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2547 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2547 / 2048) = 1/(2048 / 2547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27256561 / 125000000) (218052489 / 1000000000) (Real.log (2547 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2547 / 2048) = -Real.log (2048 / 2547) := by
    rw [show ((2547 / 2048) : ℝ) = ((2048 / 2547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (55850829 / 200000000) ≤ -Real.log (1549 / 2048) ∧
    -Real.log (1549 / 2048) ≤ (139627073 / 500000000) := by
  have h := checkLog_sound (w := (499 / 3597)) (n := 12)
    (lo := (55850829 / 200000000)) (hi := (139627073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1549) = 1/(1549 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-139627073 / 500000000) (-55850829 / 200000000) (Real.log (1549 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (397359429 / 1000000000) ≤ -Real.log (2560 / 3809) ∧
    -Real.log (2560 / 3809) ≤ (39735943 / 100000000) := by
  have h := checkLog_sound (w := (1249 / 6369)) (n := 12)
    (lo := (397359429 / 1000000000)) (hi := (39735943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3809 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3809 / 2560) = 1/(2560 / 3809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (397359429 / 1000000000) (39735943 / 100000000) (Real.log (3809 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3809 / 2560) = -Real.log (2560 / 3809) := by
    rw [show ((3809 / 2560) : ℝ) = ((2560 / 3809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (669217053 / 1000000000) ≤ -Real.log (1311 / 2560) ∧
    -Real.log (1311 / 2560) ≤ (334608527 / 500000000) := by
  have h := checkLog_sound (w := (1249 / 3871)) (n := 12)
    (lo := (669217053 / 1000000000)) (hi := (334608527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1311) = 1/(1311 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-334608527 / 500000000) (-669217053 / 1000000000) (Real.log (1311 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (396965547 / 1000000000) ≤ -Real.log (1024 / 1523) ∧
    -Real.log (1024 / 1523) ≤ (99241387 / 250000000) := by
  have h := checkLog_sound (w := (499 / 2547)) (n := 12)
    (lo := (396965547 / 1000000000)) (hi := (99241387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1523 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1523 / 1024) = 1/(1024 / 1523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (396965547 / 1000000000) (99241387 / 250000000) (Real.log (1523 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1523 / 1024) = -Real.log (1024 / 1523) := by
    rw [show ((1523 / 1024) : ℝ) = ((1024 / 1523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (668073543 / 1000000000) ≤ -Real.log (525 / 1024) ∧
    -Real.log (525 / 1024) ≤ (83509193 / 125000000) := by
  have h := checkLog_sound (w := (499 / 1549)) (n := 12)
    (lo := (668073543 / 1000000000)) (hi := (83509193 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 525) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 525) = 1/(525 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-83509193 / 125000000) (-668073543 / 1000000000) (Real.log (525 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (298897197 / 1000000000) ≤ -Real.log (1000000 / 1348371) ∧
    -Real.log (1000000 / 1348371) ≤ (149448599 / 500000000) := by
  have h := checkLog_sound (w := (348371 / 2348371)) (n := 12)
    (lo := (298897197 / 1000000000)) (hi := (149448599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1348371 / 1000000) = 1/(1000000 / 1348371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (298897197 / 1000000000) (149448599 / 500000000) (Real.log (1348371 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1348371 / 1000000) = -Real.log (1000000 / 1348371) := by
    rw [show ((1348371 / 1000000) : ℝ) = ((1000000 / 1348371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (428279897 / 1000000000) ≤ -Real.log (651629 / 1000000) ∧
    -Real.log (651629 / 1000000) ≤ (214139949 / 500000000) := by
  have h := checkLog_sound (w := (348371 / 1651629)) (n := 12)
    (lo := (428279897 / 1000000000)) (hi := (214139949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 651629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 651629) = 1/(651629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-214139949 / 500000000) (-428279897 / 1000000000) (Real.log (651629 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (299216049 / 1000000000) ≤ -Real.log (1000000 / 1348801) ∧
    -Real.log (1000000 / 1348801) ≤ (5984321 / 20000000) := by
  have h := checkLog_sound (w := (348801 / 2348801)) (n := 12)
    (lo := (299216049 / 1000000000)) (hi := (5984321 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1348801 / 1000000) = 1/(1000000 / 1348801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (299216049 / 1000000000) (5984321 / 20000000) (Real.log (1348801 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1348801 / 1000000) = -Real.log (1000000 / 1348801) := by
    rw [show ((1348801 / 1000000) : ℝ) = ((1000000 / 1348801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (428939999 / 1000000000) ≤ -Real.log (651199 / 1000000) ∧
    -Real.log (651199 / 1000000) ≤ (21447 / 50000) := by
  have h := checkLog_sound (w := (348801 / 1651199)) (n := 12)
    (lo := (428939999 / 1000000000)) (hi := (21447 / 50000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 651199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 651199) = 1/(651199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-21447 / 50000) (-428939999 / 1000000000) (Real.log (651199 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (227051903 / 1000000000) ≤ -Real.log (200000 / 250979) ∧
    -Real.log (200000 / 250979) ≤ (1773843 / 7812500) := by
  have h := checkLog_sound (w := (50979 / 450979)) (n := 12)
    (lo := (227051903 / 1000000000)) (hi := (1773843 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250979 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250979 / 200000) = 1/(200000 / 250979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (227051903 / 1000000000) (1773843 / 7812500) (Real.log (250979 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (250979 / 200000) = -Real.log (200000 / 250979) := by
    rw [show ((250979 / 200000) : ℝ) = ((200000 / 250979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (29423013 / 100000000) ≤ -Real.log (149021 / 200000) ∧
    -Real.log (149021 / 200000) ≤ (294230131 / 1000000000) := by
  have h := checkLog_sound (w := (50979 / 349021)) (n := 12)
    (lo := (29423013 / 100000000)) (hi := (294230131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 149021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 149021) = 1/(149021 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-294230131 / 1000000000) (-29423013 / 100000000) (Real.log (149021 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (7103763 / 31250000) ≤ -Real.log (15625 / 19613) ∧
    -Real.log (15625 / 19613) ≤ (227320417 / 1000000000) := by
  have h := checkLog_sound (w := (1994 / 17619)) (n := 12)
    (lo := (7103763 / 31250000)) (hi := (227320417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19613 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19613 / 15625) = 1/(15625 / 19613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (7103763 / 31250000) (227320417 / 1000000000) (Real.log (19613 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (19613 / 15625) = -Real.log (15625 / 19613) := by
    rw [show ((19613 / 15625) : ℝ) = ((15625 / 19613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (147341259 / 500000000) ≤ -Real.log (11637 / 15625) ∧
    -Real.log (11637 / 15625) ≤ (294682519 / 1000000000) := by
  have h := checkLog_sound (w := (1994 / 13631)) (n := 12)
    (lo := (147341259 / 500000000)) (hi := (294682519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11637) = 1/(11637 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-294682519 / 1000000000) (-147341259 / 500000000) (Real.log (11637 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (363588547 / 500000000) ≤ -Real.log (62500000000 / 129326944473) ∧
    -Real.log (62500000000 / 129326944473) ≤ (90897137 / 125000000) := by
  have h := checkLog_sound (w := (4326944473 / 254326944473)) (n := 12)
    (lo := (17014957 / 500000000)) (hi := (6805983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129326944473 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(129326944473 / 125000000000) = 1/(62500000000 / 129326944473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (363588547 / 500000000) (90897137 / 125000000) (Real.log (129326944473 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (129326944473 / 62500000000) = -Real.log (62500000000 / 129326944473) := by
    rw [show ((129326944473 / 62500000000) : ℝ) = ((62500000000 / 129326944473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (728156049 / 1000000000) ≤ -Real.log (25000000000 / 51781444689) ∧
    -Real.log (25000000000 / 51781444689) ≤ (728156051 / 1000000000) := by
  have h := checkLog_sound (w := (1781444689 / 101781444689)) (n := 12)
    (lo := (35008869 / 1000000000)) (hi := (3500887 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51781444689 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51781444689 / 50000000000) = 1/(25000000000 / 51781444689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (728156049 / 1000000000) (728156051 / 1000000000) (Real.log (51781444689 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (51781444689 / 25000000000) = -Real.log (25000000000 / 51781444689) := by
    rw [show ((51781444689 / 25000000000) : ℝ) = ((25000000000 / 51781444689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (260641017 / 500000000) ≤ -Real.log (250000000000 / 421046362593) ∧
    -Real.log (250000000000 / 421046362593) ≤ (104256407 / 200000000) := by
  have h := checkLog_sound (w := (171046362593 / 671046362593)) (n := 12)
    (lo := (260641017 / 500000000)) (hi := (104256407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421046362593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421046362593 / 250000000000) = 1/(250000000000 / 421046362593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (260641017 / 500000000) (104256407 / 200000000) (Real.log (421046362593 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (421046362593 / 250000000000) = -Real.log (250000000000 / 421046362593) := by
    rw [show ((421046362593 / 250000000000) : ℝ) = ((250000000000 / 421046362593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (261001467 / 500000000) ≤ -Real.log (250000000000 / 421350004297) ∧
    -Real.log (250000000000 / 421350004297) ≤ (104400587 / 200000000) := by
  have h := checkLog_sound (w := (171350004297 / 671350004297)) (n := 12)
    (lo := (261001467 / 500000000)) (hi := (104400587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421350004297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421350004297 / 250000000000) = 1/(250000000000 / 421350004297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (261001467 / 500000000) (104400587 / 200000000) (Real.log (421350004297 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (421350004297 / 250000000000) = -Real.log (250000000000 / 421350004297) := by
    rw [show ((421350004297 / 250000000000) : ℝ) = ((250000000000 / 421350004297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0324

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0325Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0325
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

theorem reflection_log_1_neg : (27256561 / 125000000) ≤ -Real.log (2048 / 2547) ∧
    -Real.log (2048 / 2547) ≤ (218052489 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 4595)) (n := 12)
    (lo := (27256561 / 125000000)) (hi := (218052489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2547 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2547 / 2048) = 1/(2048 / 2547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27256561 / 125000000) (218052489 / 1000000000) (Real.log (2547 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2547 / 2048) = -Real.log (2048 / 2547) := by
    rw [show ((2547 / 2048) : ℝ) = ((2048 / 2547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (55850829 / 200000000) ≤ -Real.log (1549 / 2048) ∧
    -Real.log (1549 / 2048) ≤ (139627073 / 500000000) := by
  have h := checkLog_sound (w := (499 / 3597)) (n := 12)
    (lo := (55850829 / 200000000)) (hi := (139627073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1549) = 1/(1549 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-139627073 / 500000000) (-55850829 / 200000000) (Real.log (1549 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (217816889 / 1000000000) ≤ -Real.log (2560 / 3183) ∧
    -Real.log (2560 / 3183) ≤ (21781689 / 100000000) := by
  have h := checkLog_sound (w := (623 / 5743)) (n := 12)
    (lo := (217816889 / 1000000000)) (hi := (21781689 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3183 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3183 / 2560) = 1/(2560 / 3183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (217816889 / 1000000000) (21781689 / 100000000) (Real.log (3183 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3183 / 2560) = -Real.log (2560 / 3183) := by
    rw [show ((3183 / 2560) : ℝ) = ((2560 / 3183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (139433437 / 500000000) ≤ -Real.log (1937 / 2560) ∧
    -Real.log (1937 / 2560) ≤ (446187 / 1600000) := by
  have h := checkLog_sound (w := (623 / 4497)) (n := 12)
    (lo := (139433437 / 500000000)) (hi := (446187 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1937) = 1/(1937 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-446187 / 1600000) (-139433437 / 500000000) (Real.log (1937 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (396965547 / 1000000000) ≤ -Real.log (1024 / 1523) ∧
    -Real.log (1024 / 1523) ≤ (99241387 / 250000000) := by
  have h := checkLog_sound (w := (499 / 2547)) (n := 12)
    (lo := (396965547 / 1000000000)) (hi := (99241387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1523 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1523 / 1024) = 1/(1024 / 1523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (396965547 / 1000000000) (99241387 / 250000000) (Real.log (1523 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1523 / 1024) = -Real.log (1024 / 1523) := by
    rw [show ((1523 / 1024) : ℝ) = ((1024 / 1523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (668073543 / 1000000000) ≤ -Real.log (525 / 1024) ∧
    -Real.log (525 / 1024) ≤ (83509193 / 125000000) := by
  have h := checkLog_sound (w := (499 / 1549)) (n := 12)
    (lo := (668073543 / 1000000000)) (hi := (83509193 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 525) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 525) = 1/(525 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-83509193 / 125000000) (-668073543 / 1000000000) (Real.log (525 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (39657151 / 100000000) ≤ -Real.log (1280 / 1903) ∧
    -Real.log (1280 / 1903) ≤ (396571511 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 3183)) (n := 12)
    (lo := (39657151 / 100000000)) (hi := (396571511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1903 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1903 / 1280) = 1/(1280 / 1903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (39657151 / 100000000) (396571511 / 1000000000) (Real.log (1903 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1903 / 1280) = -Real.log (1280 / 1903) := by
    rw [show ((1903 / 1280) : ℝ) = ((1280 / 1903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (333465669 / 500000000) ≤ -Real.log (657 / 1280) ∧
    -Real.log (657 / 1280) ≤ (666931339 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 1937)) (n := 12)
    (lo := (333465669 / 500000000)) (hi := (666931339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 657) = 1/(657 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-666931339 / 1000000000) (-333465669 / 500000000) (Real.log (657 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (37322373 / 125000000) ≤ -Real.log (500000 / 673971) ∧
    -Real.log (500000 / 673971) ≤ (59715797 / 200000000) := by
  have h := checkLog_sound (w := (173971 / 1173971)) (n := 12)
    (lo := (37322373 / 125000000)) (hi := (59715797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673971 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673971 / 500000) = 1/(500000 / 673971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (37322373 / 125000000) (59715797 / 200000000) (Real.log (673971 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (673971 / 500000) = -Real.log (500000 / 673971) := by
    rw [show ((673971 / 500000) : ℝ) = ((500000 / 673971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (427621763 / 1000000000) ≤ -Real.log (326029 / 500000) ∧
    -Real.log (326029 / 500000) ≤ (106905441 / 250000000) := by
  have h := checkLog_sound (w := (173971 / 826029)) (n := 12)
    (lo := (427621763 / 1000000000)) (hi := (106905441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 326029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 326029) = 1/(326029 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-106905441 / 250000000) (-427621763 / 1000000000) (Real.log (326029 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (149448969 / 500000000) ≤ -Real.log (250000 / 337093) ∧
    -Real.log (250000 / 337093) ≤ (298897939 / 1000000000) := by
  have h := checkLog_sound (w := (87093 / 587093)) (n := 12)
    (lo := (149448969 / 500000000)) (hi := (298897939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337093 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337093 / 250000) = 1/(250000 / 337093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (149448969 / 500000000) (298897939 / 1000000000) (Real.log (337093 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (337093 / 250000) = -Real.log (250000 / 337093) := by
    rw [show ((337093 / 250000) : ℝ) = ((250000 / 337093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53535179 / 125000000) ≤ -Real.log (162907 / 250000) ∧
    -Real.log (162907 / 250000) ≤ (428281433 / 1000000000) := by
  have h := checkLog_sound (w := (87093 / 412907)) (n := 12)
    (lo := (53535179 / 125000000)) (hi := (428281433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 162907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 162907) = 1/(162907 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-428281433 / 1000000000) (-53535179 / 125000000) (Real.log (162907 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (56696029 / 250000000) ≤ -Real.log (1000000 / 1254559) ∧
    -Real.log (1000000 / 1254559) ≤ (226784117 / 1000000000) := by
  have h := checkLog_sound (w := (254559 / 2254559)) (n := 12)
    (lo := (56696029 / 250000000)) (hi := (226784117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254559 / 1000000) = 1/(1000000 / 1254559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (56696029 / 250000000) (226784117 / 1000000000) (Real.log (1254559 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1254559 / 1000000) = -Real.log (1000000 / 1254559) := by
    rw [show ((1254559 / 1000000) : ℝ) = ((1000000 / 1254559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (293779289 / 1000000000) ≤ -Real.log (745441 / 1000000) ∧
    -Real.log (745441 / 1000000) ≤ (29377929 / 100000000) := by
  have h := checkLog_sound (w := (254559 / 1745441)) (n := 12)
    (lo := (293779289 / 1000000000)) (hi := (29377929 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745441) = 1/(745441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-29377929 / 100000000) (-293779289 / 1000000000) (Real.log (745441 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (2270527 / 10000000) ≤ -Real.log (62500 / 78431) ∧
    -Real.log (62500 / 78431) ≤ (227052701 / 1000000000) := by
  have h := checkLog_sound (w := (15931 / 140931)) (n := 12)
    (lo := (2270527 / 10000000)) (hi := (227052701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78431 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78431 / 62500) = 1/(62500 / 78431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (2270527 / 10000000) (227052701 / 1000000000) (Real.log (78431 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (78431 / 62500) = -Real.log (62500 / 78431) := by
    rw [show ((78431 / 62500) : ℝ) = ((62500 / 78431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (294231473 / 1000000000) ≤ -Real.log (46569 / 62500) ∧
    -Real.log (46569 / 62500) ≤ (147115737 / 500000000) := by
  have h := checkLog_sound (w := (15931 / 109069)) (n := 12)
    (lo := (294231473 / 1000000000)) (hi := (147115737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46569) = 1/(46569 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-147115737 / 500000000) (-294231473 / 1000000000) (Real.log (46569 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (181550187 / 250000000) ≤ -Real.log (500000000000 / 1033605906223) ∧
    -Real.log (500000000000 / 1033605906223) ≤ (2904803 / 4000000) := by
  have h := checkLog_sound (w := (33605906223 / 2033605906223)) (n := 12)
    (lo := (258231 / 7812500)) (hi := (33053569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1033605906223 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1033605906223 / 1000000000000) = 1/(500000000000 / 1033605906223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (181550187 / 250000000) (2904803 / 4000000) (Real.log (1033605906223 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1033605906223 / 500000000000) = -Real.log (500000000000 / 1033605906223) := by
    rw [show ((1033605906223 / 500000000000) : ℝ) = ((500000000000 / 1033605906223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (72717937 / 100000000) ≤ -Real.log (500000000000 / 1034617910833) ∧
    -Real.log (500000000000 / 1034617910833) ≤ (181794843 / 250000000) := by
  have h := checkLog_sound (w := (34617910833 / 2034617910833)) (n := 12)
    (lo := (3403219 / 100000000)) (hi := (34032191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1034617910833 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1034617910833 / 1000000000000) = 1/(500000000000 / 1034617910833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (72717937 / 100000000) (181794843 / 250000000) (Real.log (1034617910833 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1034617910833 / 500000000000) = -Real.log (500000000000 / 1034617910833) := by
    rw [show ((1034617910833 / 500000000000) : ℝ) = ((500000000000 / 1034617910833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (104112681 / 200000000) ≤ -Real.log (31250000000 / 52592986903) ∧
    -Real.log (31250000000 / 52592986903) ≤ (260281703 / 500000000) := by
  have h := checkLog_sound (w := (21342986903 / 83842986903)) (n := 12)
    (lo := (104112681 / 200000000)) (hi := (260281703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52592986903 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52592986903 / 31250000000) = 1/(31250000000 / 52592986903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (104112681 / 200000000) (260281703 / 500000000) (Real.log (52592986903 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (52592986903 / 31250000000) = -Real.log (31250000000 / 52592986903) := by
    rw [show ((52592986903 / 31250000000) : ℝ) = ((31250000000 / 52592986903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (521284173 / 1000000000) ≤ -Real.log (250000000000 / 421047263201) ∧
    -Real.log (250000000000 / 421047263201) ≤ (260642087 / 500000000) := by
  have h := checkLog_sound (w := (171047263201 / 671047263201)) (n := 12)
    (lo := (521284173 / 1000000000)) (hi := (260642087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421047263201 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421047263201 / 250000000000) = 1/(250000000000 / 421047263201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (521284173 / 1000000000) (260642087 / 500000000) (Real.log (421047263201 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (421047263201 / 250000000000) = -Real.log (250000000000 / 421047263201) := by
    rw [show ((421047263201 / 250000000000) : ℝ) = ((250000000000 / 421047263201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0325

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0326Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0326
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

theorem reflection_log_1_neg : (217816889 / 1000000000) ≤ -Real.log (2560 / 3183) ∧
    -Real.log (2560 / 3183) ≤ (21781689 / 100000000) := by
  have h := checkLog_sound (w := (623 / 5743)) (n := 12)
    (lo := (217816889 / 1000000000)) (hi := (21781689 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3183 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3183 / 2560) = 1/(2560 / 3183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (217816889 / 1000000000) (21781689 / 100000000) (Real.log (3183 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3183 / 2560) = -Real.log (2560 / 3183) := by
    rw [show ((3183 / 2560) : ℝ) = ((2560 / 3183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (139433437 / 500000000) ≤ -Real.log (1937 / 2560) ∧
    -Real.log (1937 / 2560) ≤ (446187 / 1600000) := by
  have h := checkLog_sound (w := (623 / 4497)) (n := 12)
    (lo := (139433437 / 500000000)) (hi := (446187 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1937) = 1/(1937 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-446187 / 1600000) (-139433437 / 500000000) (Real.log (1937 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (43516247 / 200000000) ≤ -Real.log (10240 / 12729) ∧
    -Real.log (10240 / 12729) ≤ (54395309 / 250000000) := by
  have h := checkLog_sound (w := (2489 / 22969)) (n := 12)
    (lo := (43516247 / 200000000)) (hi := (54395309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12729 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12729 / 10240) = 1/(10240 / 12729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (43516247 / 200000000) (54395309 / 250000000) (Real.log (12729 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12729 / 10240) = -Real.log (10240 / 12729) := by
    rw [show ((12729 / 10240) : ℝ) = ((10240 / 12729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (34809969 / 125000000) ≤ -Real.log (7751 / 10240) ∧
    -Real.log (7751 / 10240) ≤ (278479753 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 17991)) (n := 12)
    (lo := (34809969 / 125000000)) (hi := (278479753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7751) = 1/(7751 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-278479753 / 1000000000) (-34809969 / 125000000) (Real.log (7751 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (39657151 / 100000000) ≤ -Real.log (1280 / 1903) ∧
    -Real.log (1280 / 1903) ≤ (396571511 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 3183)) (n := 12)
    (lo := (39657151 / 100000000)) (hi := (396571511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1903 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1903 / 1280) = 1/(1280 / 1903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (39657151 / 100000000) (396571511 / 1000000000) (Real.log (1903 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1903 / 1280) = -Real.log (1280 / 1903) := by
    rw [show ((1903 / 1280) : ℝ) = ((1280 / 1903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (333465669 / 500000000) ≤ -Real.log (657 / 1280) ∧
    -Real.log (657 / 1280) ≤ (666931339 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 1937)) (n := 12)
    (lo := (333465669 / 500000000)) (hi := (666931339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 657) = 1/(657 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-666931339 / 1000000000) (-333465669 / 500000000) (Real.log (657 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (198088659 / 500000000) ≤ -Real.log (5120 / 7609) ∧
    -Real.log (5120 / 7609) ≤ (396177319 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 12729)) (n := 12)
    (lo := (198088659 / 500000000)) (hi := (396177319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7609 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7609 / 5120) = 1/(5120 / 7609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (198088659 / 500000000) (396177319 / 1000000000) (Real.log (7609 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7609 / 5120) = -Real.log (5120 / 7609) := by
    rw [show ((7609 / 5120) : ℝ) = ((5120 / 7609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (166447609 / 250000000) ≤ -Real.log (2631 / 5120) ∧
    -Real.log (2631 / 5120) ≤ (665790437 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 7751)) (n := 12)
    (lo := (166447609 / 250000000)) (hi := (665790437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2631) = 1/(2631 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-665790437 / 1000000000) (-166447609 / 250000000) (Real.log (2631 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (298260671 / 1000000000) ≤ -Real.log (1000000 / 1347513) ∧
    -Real.log (1000000 / 1347513) ≤ (4660323 / 15625000) := by
  have h := checkLog_sound (w := (347513 / 2347513)) (n := 12)
    (lo := (298260671 / 1000000000)) (hi := (4660323 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1347513 / 1000000) = 1/(1000000 / 1347513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (298260671 / 1000000000) (4660323 / 15625000) (Real.log (1347513 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1347513 / 1000000) = -Real.log (1000000 / 1347513) := by
    rw [show ((1347513 / 1000000) : ℝ) = ((1000000 / 1347513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (426964063 / 1000000000) ≤ -Real.log (652487 / 1000000) ∧
    -Real.log (652487 / 1000000) ≤ (13342627 / 31250000) := by
  have h := checkLog_sound (w := (347513 / 1652487)) (n := 12)
    (lo := (426964063 / 1000000000)) (hi := (13342627 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 652487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 652487) = 1/(652487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13342627 / 31250000) (-426964063 / 1000000000) (Real.log (652487 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (149289863 / 500000000) ≤ -Real.log (1000000 / 1347943) ∧
    -Real.log (1000000 / 1347943) ≤ (298579727 / 1000000000) := by
  have h := checkLog_sound (w := (347943 / 2347943)) (n := 12)
    (lo := (149289863 / 500000000)) (hi := (298579727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1347943 / 1000000) = 1/(1000000 / 1347943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (149289863 / 500000000) (298579727 / 1000000000) (Real.log (1347943 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1347943 / 1000000) = -Real.log (1000000 / 1347943) := by
    rw [show ((1347943 / 1000000) : ℝ) = ((1000000 / 1347943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (427623297 / 1000000000) ≤ -Real.log (652057 / 1000000) ∧
    -Real.log (652057 / 1000000) ≤ (213811649 / 500000000) := by
  have h := checkLog_sound (w := (347943 / 1652057)) (n := 12)
    (lo := (427623297 / 1000000000)) (hi := (213811649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 652057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 652057) = 1/(652057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-213811649 / 500000000) (-427623297 / 1000000000) (Real.log (652057 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (113258527 / 500000000) ≤ -Real.log (62500 / 78389) ∧
    -Real.log (62500 / 78389) ≤ (45303411 / 200000000) := by
  have h := checkLog_sound (w := (15889 / 140889)) (n := 12)
    (lo := (113258527 / 500000000)) (hi := (45303411 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78389 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78389 / 62500) = 1/(62500 / 78389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (113258527 / 500000000) (45303411 / 200000000) (Real.log (78389 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (78389 / 62500) = -Real.log (62500 / 78389) := by
    rw [show ((78389 / 62500) : ℝ) = ((62500 / 78389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (293329991 / 1000000000) ≤ -Real.log (46611 / 62500) ∧
    -Real.log (46611 / 62500) ≤ (36666249 / 125000000) := by
  have h := checkLog_sound (w := (15889 / 109111)) (n := 12)
    (lo := (293329991 / 1000000000)) (hi := (36666249 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46611) = 1/(46611 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-36666249 / 125000000) (-293329991 / 1000000000) (Real.log (46611 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (22678571 / 100000000) ≤ -Real.log (1000000 / 1254561) ∧
    -Real.log (1000000 / 1254561) ≤ (226785711 / 1000000000) := by
  have h := checkLog_sound (w := (254561 / 2254561)) (n := 12)
    (lo := (22678571 / 100000000)) (hi := (226785711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254561 / 1000000) = 1/(1000000 / 1254561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22678571 / 100000000) (226785711 / 1000000000) (Real.log (1254561 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1254561 / 1000000) = -Real.log (1000000 / 1254561) := by
    rw [show ((1254561 / 1000000) : ℝ) = ((1000000 / 1254561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (73445493 / 250000000) ≤ -Real.log (745439 / 1000000) ∧
    -Real.log (745439 / 1000000) ≤ (293781973 / 1000000000) := by
  have h := checkLog_sound (w := (254561 / 1745439)) (n := 12)
    (lo := (73445493 / 250000000)) (hi := (293781973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745439) = 1/(745439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-293781973 / 1000000000) (-73445493 / 250000000) (Real.log (745439 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (362612367 / 500000000) ≤ -Real.log (500000000000 / 1032597584319) ∧
    -Real.log (500000000000 / 1032597584319) ≤ (22663273 / 31250000) := by
  have h := checkLog_sound (w := (32597584319 / 2032597584319)) (n := 12)
    (lo := (16038777 / 500000000)) (hi := (6415511 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1032597584319 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1032597584319 / 1000000000000) = 1/(500000000000 / 1032597584319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (362612367 / 500000000) (22663273 / 31250000) (Real.log (1032597584319 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1032597584319 / 500000000000) = -Real.log (500000000000 / 1032597584319) := by
    rw [show ((1032597584319 / 500000000000) : ℝ) = ((500000000000 / 1032597584319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (726203023 / 1000000000) ≤ -Real.log (250000000000 / 516804129087) ∧
    -Real.log (250000000000 / 516804129087) ≤ (29048121 / 40000000) := by
  have h := checkLog_sound (w := (16804129087 / 1016804129087)) (n := 12)
    (lo := (33055843 / 1000000000)) (hi := (8263961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((516804129087 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(516804129087 / 500000000000) = 1/(250000000000 / 516804129087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (726203023 / 1000000000) (29048121 / 40000000) (Real.log (516804129087 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (516804129087 / 250000000000) = -Real.log (250000000000 / 516804129087) := by
    rw [show ((516804129087 / 250000000000) : ℝ) = ((250000000000 / 516804129087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (259923523 / 500000000) ≤ -Real.log (125000000000 / 210221299693) ∧
    -Real.log (125000000000 / 210221299693) ≤ (519847047 / 1000000000) := by
  have h := checkLog_sound (w := (85221299693 / 335221299693)) (n := 12)
    (lo := (259923523 / 500000000)) (hi := (519847047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210221299693 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210221299693 / 125000000000) = 1/(125000000000 / 210221299693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (259923523 / 500000000) (519847047 / 1000000000) (Real.log (210221299693 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (210221299693 / 125000000000) = -Real.log (125000000000 / 210221299693) := by
    rw [show ((210221299693 / 125000000000) : ℝ) = ((125000000000 / 210221299693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (260283841 / 500000000) ≤ -Real.log (250000000000 / 420745694819) ∧
    -Real.log (250000000000 / 420745694819) ≤ (520567683 / 1000000000) := by
  have h := checkLog_sound (w := (170745694819 / 670745694819)) (n := 12)
    (lo := (260283841 / 500000000)) (hi := (520567683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420745694819 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(420745694819 / 250000000000) = 1/(250000000000 / 420745694819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (260283841 / 500000000) (520567683 / 1000000000) (Real.log (420745694819 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (420745694819 / 250000000000) = -Real.log (250000000000 / 420745694819) := by
    rw [show ((420745694819 / 250000000000) : ℝ) = ((250000000000 / 420745694819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0326

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0327Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0327
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

theorem reflection_log_1_neg : (43516247 / 200000000) ≤ -Real.log (10240 / 12729) ∧
    -Real.log (10240 / 12729) ≤ (54395309 / 250000000) := by
  have h := checkLog_sound (w := (2489 / 22969)) (n := 12)
    (lo := (43516247 / 200000000)) (hi := (54395309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12729 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12729 / 10240) = 1/(10240 / 12729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (43516247 / 200000000) (54395309 / 250000000) (Real.log (12729 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12729 / 10240) = -Real.log (10240 / 12729) := by
    rw [show ((12729 / 10240) : ℝ) = ((10240 / 12729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (34809969 / 125000000) ≤ -Real.log (7751 / 10240) ∧
    -Real.log (7751 / 10240) ≤ (278479753 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 17991)) (n := 12)
    (lo := (34809969 / 125000000)) (hi := (278479753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7751) = 1/(7751 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-278479753 / 1000000000) (-34809969 / 125000000) (Real.log (7751 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8693821 / 40000000) ≤ -Real.log (5120 / 6363) ∧
    -Real.log (5120 / 6363) ≤ (108672763 / 500000000) := by
  have h := checkLog_sound (w := (1243 / 11483)) (n := 12)
    (lo := (8693821 / 40000000)) (hi := (108672763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6363 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6363 / 5120) = 1/(5120 / 6363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8693821 / 40000000) (108672763 / 500000000) (Real.log (6363 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6363 / 5120) = -Real.log (5120 / 6363) := by
    rw [show ((6363 / 5120) : ℝ) = ((5120 / 6363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (13904639 / 50000000) ≤ -Real.log (3877 / 5120) ∧
    -Real.log (3877 / 5120) ≤ (278092781 / 1000000000) := by
  have h := checkLog_sound (w := (1243 / 8997)) (n := 12)
    (lo := (13904639 / 50000000)) (hi := (278092781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3877) = 1/(3877 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-278092781 / 1000000000) (-13904639 / 50000000) (Real.log (3877 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (198088659 / 500000000) ≤ -Real.log (5120 / 7609) ∧
    -Real.log (5120 / 7609) ≤ (396177319 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 12729)) (n := 12)
    (lo := (198088659 / 500000000)) (hi := (396177319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7609 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7609 / 5120) = 1/(5120 / 7609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (198088659 / 500000000) (396177319 / 1000000000) (Real.log (7609 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7609 / 5120) = -Real.log (5120 / 7609) := by
    rw [show ((7609 / 5120) : ℝ) = ((5120 / 7609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (166447609 / 250000000) ≤ -Real.log (2631 / 5120) ∧
    -Real.log (2631 / 5120) ≤ (665790437 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 7751)) (n := 12)
    (lo := (166447609 / 250000000)) (hi := (665790437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2631) = 1/(2631 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-665790437 / 1000000000) (-166447609 / 250000000) (Real.log (2631 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (39578297 / 100000000) ≤ -Real.log (2560 / 3803) ∧
    -Real.log (2560 / 3803) ≤ (395782971 / 1000000000) := by
  have h := checkLog_sound (w := (1243 / 6363)) (n := 12)
    (lo := (39578297 / 100000000)) (hi := (395782971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3803 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3803 / 2560) = 1/(2560 / 3803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (39578297 / 100000000) (395782971 / 1000000000) (Real.log (3803 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3803 / 2560) = -Real.log (2560 / 3803) := by
    rw [show ((3803 / 2560) : ℝ) = ((2560 / 3803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (132930167 / 200000000) ≤ -Real.log (1317 / 2560) ∧
    -Real.log (1317 / 2560) ≤ (166162709 / 250000000) := by
  have h := checkLog_sound (w := (1243 / 3877)) (n := 12)
    (lo := (132930167 / 200000000)) (hi := (166162709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1317) = 1/(1317 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-166162709 / 250000000) (-132930167 / 200000000) (Real.log (1317 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18621391 / 62500000) ≤ -Real.log (250000 / 336771) ∧
    -Real.log (250000 / 336771) ≤ (297942257 / 1000000000) := by
  have h := checkLog_sound (w := (86771 / 586771)) (n := 12)
    (lo := (18621391 / 62500000)) (hi := (297942257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336771 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336771 / 250000) = 1/(250000 / 336771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18621391 / 62500000) (297942257 / 1000000000) (Real.log (336771 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (336771 / 250000) = -Real.log (250000 / 336771) := by
    rw [show ((336771 / 250000) : ℝ) = ((250000 / 336771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (85261359 / 200000000) ≤ -Real.log (163229 / 250000) ∧
    -Real.log (163229 / 250000) ≤ (106576699 / 250000000) := by
  have h := checkLog_sound (w := (86771 / 413229)) (n := 12)
    (lo := (85261359 / 200000000)) (hi := (106576699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163229) = 1/(163229 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-106576699 / 250000000) (-85261359 / 200000000) (Real.log (163229 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (298261413 / 1000000000) ≤ -Real.log (500000 / 673757) ∧
    -Real.log (500000 / 673757) ≤ (149130707 / 500000000) := by
  have h := checkLog_sound (w := (173757 / 1173757)) (n := 12)
    (lo := (298261413 / 1000000000)) (hi := (149130707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673757 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673757 / 500000) = 1/(500000 / 673757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (298261413 / 1000000000) (149130707 / 500000000) (Real.log (673757 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (673757 / 500000) = -Real.log (500000 / 673757) := by
    rw [show ((673757 / 500000) : ℝ) = ((500000 / 673757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (85393119 / 200000000) ≤ -Real.log (326243 / 500000) ∧
    -Real.log (326243 / 500000) ≤ (106741399 / 250000000) := by
  have h := checkLog_sound (w := (173757 / 826243)) (n := 12)
    (lo := (85393119 / 200000000)) (hi := (106741399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 326243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 326243) = 1/(326243 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-106741399 / 250000000) (-85393119 / 200000000) (Real.log (326243 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (226249921 / 1000000000) ≤ -Real.log (1000000 / 1253889) ∧
    -Real.log (1000000 / 1253889) ≤ (113124961 / 500000000) := by
  have h := checkLog_sound (w := (253889 / 2253889)) (n := 12)
    (lo := (226249921 / 1000000000)) (hi := (113124961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253889 / 1000000) = 1/(1000000 / 1253889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (226249921 / 1000000000) (113124961 / 500000000) (Real.log (1253889 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1253889 / 1000000) = -Real.log (1000000 / 1253889) := by
    rw [show ((1253889 / 1000000) : ℝ) = ((1000000 / 1253889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (572033 / 1953125) ≤ -Real.log (746111 / 1000000) ∧
    -Real.log (746111 / 1000000) ≤ (292880897 / 1000000000) := by
  have h := checkLog_sound (w := (253889 / 1746111)) (n := 12)
    (lo := (572033 / 1953125)) (hi := (292880897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746111) = 1/(746111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-292880897 / 1000000000) (-572033 / 1953125) (Real.log (746111 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (226517851 / 1000000000) ≤ -Real.log (40000 / 50169) ∧
    -Real.log (40000 / 50169) ≤ (56629463 / 250000000) := by
  have h := checkLog_sound (w := (10169 / 90169)) (n := 12)
    (lo := (226517851 / 1000000000)) (hi := (56629463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50169 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50169 / 40000) = 1/(40000 / 50169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (226517851 / 1000000000) (56629463 / 250000000) (Real.log (50169 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (50169 / 40000) = -Real.log (40000 / 50169) := by
    rw [show ((50169 / 40000) : ℝ) = ((40000 / 50169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (73332833 / 250000000) ≤ -Real.log (29831 / 40000) ∧
    -Real.log (29831 / 40000) ≤ (293331333 / 1000000000) := by
  have h := checkLog_sound (w := (10169 / 69831)) (n := 12)
    (lo := (73332833 / 250000000)) (hi := (293331333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 29831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 29831) = 1/(29831 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-293331333 / 1000000000) (-73332833 / 250000000) (Real.log (29831 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (14484981 / 20000000) ≤ -Real.log (7812500000 / 16118602929) ∧
    -Real.log (7812500000 / 16118602929) ≤ (181062263 / 250000000) := by
  have h := checkLog_sound (w := (493602929 / 31743602929)) (n := 12)
    (lo := (3110187 / 100000000)) (hi := (31101871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16118602929 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16118602929 / 15625000000) = 1/(7812500000 / 16118602929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14484981 / 20000000) (181062263 / 250000000) (Real.log (16118602929 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (16118602929 / 7812500000) = -Real.log (7812500000 / 16118602929) := by
    rw [show ((16118602929 / 7812500000) : ℝ) = ((7812500000 / 16118602929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1416459 / 1953125) ≤ -Real.log (500000000000 / 1032599933179) ∧
    -Real.log (500000000000 / 1032599933179) ≤ (72522701 / 100000000) := by
  have h := checkLog_sound (w := (32599933179 / 2032599933179)) (n := 12)
    (lo := (8019957 / 250000000)) (hi := (32079829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1032599933179 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1032599933179 / 1000000000000) = 1/(500000000000 / 1032599933179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1416459 / 1953125) (72522701 / 100000000) (Real.log (1032599933179 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1032599933179 / 500000000000) = -Real.log (500000000000 / 1032599933179) := by
    rw [show ((1032599933179 / 500000000000) : ℝ) = ((500000000000 / 1032599933179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (519130817 / 1000000000) ≤ -Real.log (500000000000 / 840283148217) ∧
    -Real.log (500000000000 / 840283148217) ≤ (259565409 / 500000000) := by
  have h := checkLog_sound (w := (340283148217 / 1340283148217)) (n := 12)
    (lo := (519130817 / 1000000000)) (hi := (259565409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840283148217 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840283148217 / 500000000000) = 1/(500000000000 / 840283148217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (519130817 / 1000000000) (259565409 / 500000000) (Real.log (840283148217 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (840283148217 / 500000000000) = -Real.log (500000000000 / 840283148217) := by
    rw [show ((840283148217 / 500000000000) : ℝ) = ((500000000000 / 840283148217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (16245287 / 31250000) ≤ -Real.log (500000000000 / 840886996749) ∧
    -Real.log (500000000000 / 840886996749) ≤ (103969837 / 200000000) := by
  have h := checkLog_sound (w := (340886996749 / 1340886996749)) (n := 12)
    (lo := (16245287 / 31250000)) (hi := (103969837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840886996749 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840886996749 / 500000000000) = 1/(500000000000 / 840886996749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (16245287 / 31250000) (103969837 / 200000000) (Real.log (840886996749 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (840886996749 / 500000000000) = -Real.log (500000000000 / 840886996749) := by
    rw [show ((840886996749 / 500000000000) : ℝ) = ((500000000000 / 840886996749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0327

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0328Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0328
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

theorem reflection_log_1_neg : (8693821 / 40000000) ≤ -Real.log (5120 / 6363) ∧
    -Real.log (5120 / 6363) ≤ (108672763 / 500000000) := by
  have h := checkLog_sound (w := (1243 / 11483)) (n := 12)
    (lo := (8693821 / 40000000)) (hi := (108672763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6363 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6363 / 5120) = 1/(5120 / 6363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8693821 / 40000000) (108672763 / 500000000) (Real.log (6363 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6363 / 5120) = -Real.log (5120 / 6363) := by
    rw [show ((6363 / 5120) : ℝ) = ((5120 / 6363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (13904639 / 50000000) ≤ -Real.log (3877 / 5120) ∧
    -Real.log (3877 / 5120) ≤ (278092781 / 1000000000) := by
  have h := checkLog_sound (w := (1243 / 8997)) (n := 12)
    (lo := (13904639 / 50000000)) (hi := (278092781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3877) = 1/(3877 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-278092781 / 1000000000) (-13904639 / 50000000) (Real.log (3877 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (217109759 / 1000000000) ≤ -Real.log (10240 / 12723) ∧
    -Real.log (10240 / 12723) ≤ (169617 / 781250) := by
  have h := checkLog_sound (w := (2483 / 22963)) (n := 12)
    (lo := (217109759 / 1000000000)) (hi := (169617 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12723 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12723 / 10240) = 1/(10240 / 12723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (217109759 / 1000000000) (169617 / 781250) (Real.log (12723 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12723 / 10240) = -Real.log (10240 / 12723) := by
    rw [show ((12723 / 10240) : ℝ) = ((10240 / 12723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (138852979 / 500000000) ≤ -Real.log (7757 / 10240) ∧
    -Real.log (7757 / 10240) ≤ (277705959 / 1000000000) := by
  have h := checkLog_sound (w := (2483 / 17997)) (n := 12)
    (lo := (138852979 / 500000000)) (hi := (277705959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7757) = 1/(7757 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-277705959 / 1000000000) (-138852979 / 500000000) (Real.log (7757 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (39578297 / 100000000) ≤ -Real.log (2560 / 3803) ∧
    -Real.log (2560 / 3803) ≤ (395782971 / 1000000000) := by
  have h := checkLog_sound (w := (1243 / 6363)) (n := 12)
    (lo := (39578297 / 100000000)) (hi := (395782971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3803 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3803 / 2560) = 1/(2560 / 3803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (39578297 / 100000000) (395782971 / 1000000000) (Real.log (3803 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3803 / 2560) = -Real.log (2560 / 3803) := by
    rw [show ((3803 / 2560) : ℝ) = ((2560 / 3803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (132930167 / 200000000) ≤ -Real.log (1317 / 2560) ∧
    -Real.log (1317 / 2560) ≤ (166162709 / 250000000) := by
  have h := checkLog_sound (w := (1243 / 3877)) (n := 12)
    (lo := (132930167 / 200000000)) (hi := (166162709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1317) = 1/(1317 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-166162709 / 250000000) (-132930167 / 200000000) (Real.log (1317 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (395388467 / 1000000000) ≤ -Real.log (5120 / 7603) ∧
    -Real.log (5120 / 7603) ≤ (98847117 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 12723)) (n := 12)
    (lo := (395388467 / 1000000000)) (hi := (98847117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7603 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7603 / 5120) = 1/(5120 / 7603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (395388467 / 1000000000) (98847117 / 250000000) (Real.log (7603 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7603 / 5120) = -Real.log (5120 / 7603) := by
    rw [show ((7603 / 5120) : ℝ) = ((5120 / 7603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (663512531 / 1000000000) ≤ -Real.log (2637 / 5120) ∧
    -Real.log (2637 / 5120) ≤ (165878133 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 7757)) (n := 12)
    (lo := (663512531 / 1000000000)) (hi := (165878133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2637) = 1/(2637 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-165878133 / 250000000) (-663512531 / 1000000000) (Real.log (2637 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (297623739 / 1000000000) ≤ -Real.log (200000 / 269331) ∧
    -Real.log (200000 / 269331) ≤ (14881187 / 50000000) := by
  have h := checkLog_sound (w := (69331 / 469331)) (n := 12)
    (lo := (297623739 / 1000000000)) (hi := (14881187 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269331 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269331 / 200000) = 1/(200000 / 269331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (297623739 / 1000000000) (14881187 / 50000000) (Real.log (269331 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (269331 / 200000) = -Real.log (200000 / 269331) := by
    rw [show ((269331 / 200000) : ℝ) = ((200000 / 269331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (212824979 / 500000000) ≤ -Real.log (130669 / 200000) ∧
    -Real.log (130669 / 200000) ≤ (425649959 / 1000000000) := by
  have h := checkLog_sound (w := (69331 / 330669)) (n := 12)
    (lo := (212824979 / 500000000)) (hi := (425649959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 130669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 130669) = 1/(130669 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-425649959 / 1000000000) (-212824979 / 500000000) (Real.log (130669 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (148971499 / 500000000) ≤ -Real.log (200000 / 269417) ∧
    -Real.log (200000 / 269417) ≤ (297942999 / 1000000000) := by
  have h := checkLog_sound (w := (69417 / 469417)) (n := 12)
    (lo := (148971499 / 500000000)) (hi := (297942999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269417 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269417 / 200000) = 1/(200000 / 269417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (148971499 / 500000000) (297942999 / 1000000000) (Real.log (269417 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (269417 / 200000) = -Real.log (200000 / 269417) := by
    rw [show ((269417 / 200000) : ℝ) = ((200000 / 269417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (213154163 / 500000000) ≤ -Real.log (130583 / 200000) ∧
    -Real.log (130583 / 200000) ≤ (426308327 / 1000000000) := by
  have h := checkLog_sound (w := (69417 / 330583)) (n := 12)
    (lo := (213154163 / 500000000)) (hi := (426308327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 130583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 130583) = 1/(130583 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-426308327 / 1000000000) (-213154163 / 500000000) (Real.log (130583 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (225981919 / 1000000000) ≤ -Real.log (1000000 / 1253553) ∧
    -Real.log (1000000 / 1253553) ≤ (1412387 / 6250000) := by
  have h := checkLog_sound (w := (253553 / 2253553)) (n := 12)
    (lo := (225981919 / 1000000000)) (hi := (1412387 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253553 / 1000000) = 1/(1000000 / 1253553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (225981919 / 1000000000) (1412387 / 6250000) (Real.log (1253553 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1253553 / 1000000) = -Real.log (1000000 / 1253553) := by
    rw [show ((1253553 / 1000000) : ℝ) = ((1000000 / 1253553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (146215331 / 500000000) ≤ -Real.log (746447 / 1000000) ∧
    -Real.log (746447 / 1000000) ≤ (292430663 / 1000000000) := by
  have h := checkLog_sound (w := (253553 / 1746447)) (n := 12)
    (lo := (146215331 / 500000000)) (hi := (292430663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746447) = 1/(746447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-292430663 / 1000000000) (-146215331 / 500000000) (Real.log (746447 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (226250719 / 1000000000) ≤ -Real.log (100000 / 125389) ∧
    -Real.log (100000 / 125389) ≤ (1414067 / 6250000) := by
  have h := checkLog_sound (w := (25389 / 225389)) (n := 12)
    (lo := (226250719 / 1000000000)) (hi := (1414067 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125389 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125389 / 100000) = 1/(100000 / 125389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (226250719 / 1000000000) (1414067 / 6250000) (Real.log (125389 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (125389 / 100000) = -Real.log (100000 / 125389) := by
    rw [show ((125389 / 100000) : ℝ) = ((100000 / 125389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (73220559 / 250000000) ≤ -Real.log (74611 / 100000) ∧
    -Real.log (74611 / 100000) ≤ (292882237 / 1000000000) := by
  have h := checkLog_sound (w := (25389 / 174611)) (n := 12)
    (lo := (73220559 / 250000000)) (hi := (292882237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74611) = 1/(74611 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-292882237 / 1000000000) (-73220559 / 250000000) (Real.log (74611 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (723273697 / 1000000000) ≤ -Real.log (3906250000 / 8051444633) ∧
    -Real.log (3906250000 / 8051444633) ≤ (723273699 / 1000000000) := by
  have h := checkLog_sound (w := (238944633 / 15863944633)) (n := 12)
    (lo := (30126517 / 1000000000)) (hi := (15063259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8051444633 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8051444633 / 7812500000) = 1/(3906250000 / 8051444633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (723273697 / 1000000000) (723273699 / 1000000000) (Real.log (8051444633 / 3906250000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8051444633 / 3906250000) = -Real.log (3906250000 / 8051444633) := by
    rw [show ((8051444633 / 3906250000) : ℝ) = ((3906250000 / 8051444633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (181062831 / 250000000) ≤ -Real.log (500000000000 / 1031592933231) ∧
    -Real.log (500000000000 / 1031592933231) ≤ (362125663 / 500000000) := by
  have h := checkLog_sound (w := (31592933231 / 2031592933231)) (n := 12)
    (lo := (1944009 / 62500000)) (hi := (6220829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1031592933231 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1031592933231 / 1000000000000) = 1/(500000000000 / 1031592933231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (181062831 / 250000000) (362125663 / 500000000) (Real.log (1031592933231 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1031592933231 / 500000000000) = -Real.log (500000000000 / 1031592933231) := by
    rw [show ((1031592933231 / 500000000000) : ℝ) = ((500000000000 / 1031592933231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (518412581 / 1000000000) ≤ -Real.log (500000000000 / 839679843311) ∧
    -Real.log (500000000000 / 839679843311) ≤ (259206291 / 500000000) := by
  have h := checkLog_sound (w := (339679843311 / 1339679843311)) (n := 12)
    (lo := (518412581 / 1000000000)) (hi := (259206291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839679843311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839679843311 / 500000000000) = 1/(500000000000 / 839679843311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (518412581 / 1000000000) (259206291 / 500000000) (Real.log (839679843311 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (839679843311 / 500000000000) = -Real.log (500000000000 / 839679843311) := by
    rw [show ((839679843311 / 500000000000) : ℝ) = ((500000000000 / 839679843311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (103826591 / 200000000) ≤ -Real.log (25000000000 / 42014247229) ∧
    -Real.log (25000000000 / 42014247229) ≤ (129783239 / 250000000) := by
  have h := checkLog_sound (w := (17014247229 / 67014247229)) (n := 12)
    (lo := (103826591 / 200000000)) (hi := (129783239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42014247229 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42014247229 / 25000000000) = 1/(25000000000 / 42014247229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (103826591 / 200000000) (129783239 / 250000000) (Real.log (42014247229 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (42014247229 / 25000000000) = -Real.log (25000000000 / 42014247229) := by
    rw [show ((42014247229 / 25000000000) : ℝ) = ((25000000000 / 42014247229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0328

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0329Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0329
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

theorem reflection_log_1_neg : (217109759 / 1000000000) ≤ -Real.log (10240 / 12723) ∧
    -Real.log (10240 / 12723) ≤ (169617 / 781250) := by
  have h := checkLog_sound (w := (2483 / 22963)) (n := 12)
    (lo := (217109759 / 1000000000)) (hi := (169617 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12723 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12723 / 10240) = 1/(10240 / 12723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (217109759 / 1000000000) (169617 / 781250) (Real.log (12723 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12723 / 10240) = -Real.log (10240 / 12723) := by
    rw [show ((12723 / 10240) : ℝ) = ((10240 / 12723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (138852979 / 500000000) ≤ -Real.log (7757 / 10240) ∧
    -Real.log (7757 / 10240) ≤ (277705959 / 1000000000) := by
  have h := checkLog_sound (w := (2483 / 17997)) (n := 12)
    (lo := (138852979 / 500000000)) (hi := (277705959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7757) = 1/(7757 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-277705959 / 1000000000) (-138852979 / 500000000) (Real.log (7757 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (108436969 / 500000000) ≤ -Real.log (128 / 159) ∧
    -Real.log (128 / 159) ≤ (216873939 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 287)) (n := 12)
    (lo := (108436969 / 500000000)) (hi := (216873939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159 / 128) = 1/(128 / 159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (108436969 / 500000000) (216873939 / 1000000000) (Real.log (159 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (159 / 128) = -Real.log (128 / 159) := by
    rw [show ((159 / 128) : ℝ) = ((128 / 159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (55463857 / 200000000) ≤ -Real.log (97 / 128) ∧
    -Real.log (97 / 128) ≤ (138659643 / 500000000) := by
  have h := checkLog_sound (w := (31 / 225)) (n := 12)
    (lo := (55463857 / 200000000)) (hi := (138659643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 97) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 97) = 1/(97 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-138659643 / 500000000) (-55463857 / 200000000) (Real.log (97 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (395388467 / 1000000000) ≤ -Real.log (5120 / 7603) ∧
    -Real.log (5120 / 7603) ≤ (98847117 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 12723)) (n := 12)
    (lo := (395388467 / 1000000000)) (hi := (98847117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7603 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7603 / 5120) = 1/(5120 / 7603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (395388467 / 1000000000) (98847117 / 250000000) (Real.log (7603 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7603 / 5120) = -Real.log (5120 / 7603) := by
    rw [show ((7603 / 5120) : ℝ) = ((5120 / 7603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (663512531 / 1000000000) ≤ -Real.log (2637 / 5120) ∧
    -Real.log (2637 / 5120) ≤ (165878133 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 7757)) (n := 12)
    (lo := (663512531 / 1000000000)) (hi := (165878133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2637) = 1/(2637 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-165878133 / 250000000) (-663512531 / 1000000000) (Real.log (2637 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (24687113 / 62500000) ≤ -Real.log (64 / 95) ∧
    -Real.log (64 / 95) ≤ (394993809 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 159)) (n := 12)
    (lo := (24687113 / 62500000)) (hi := (394993809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95 / 64) = 1/(64 / 95) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (24687113 / 62500000) (394993809 / 1000000000) (Real.log (95 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (95 / 64) = -Real.log (64 / 95) := by
    rw [show ((95 / 64) : ℝ) = ((64 / 95) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (662375521 / 1000000000) ≤ -Real.log (33 / 64) ∧
    -Real.log (33 / 64) ≤ (331187761 / 500000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 33) = 1/(33 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-331187761 / 500000000) (-662375521 / 1000000000) (Real.log (33 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148652561 / 500000000) ≤ -Real.log (500000 / 673113) ∧
    -Real.log (500000 / 673113) ≤ (297305123 / 1000000000) := by
  have h := checkLog_sound (w := (173113 / 1173113)) (n := 12)
    (lo := (148652561 / 500000000)) (hi := (297305123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673113 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673113 / 500000) = 1/(500000 / 673113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148652561 / 500000000) (297305123 / 1000000000) (Real.log (673113 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (673113 / 500000) = -Real.log (500000 / 673113) := by
    rw [show ((673113 / 500000) : ℝ) = ((500000 / 673113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (26562097 / 62500000) ≤ -Real.log (326887 / 500000) ∧
    -Real.log (326887 / 500000) ≤ (424993553 / 1000000000) := by
  have h := checkLog_sound (w := (173113 / 826887)) (n := 12)
    (lo := (26562097 / 62500000)) (hi := (424993553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 326887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 326887) = 1/(326887 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-424993553 / 1000000000) (-26562097 / 62500000) (Real.log (326887 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (148812241 / 500000000) ≤ -Real.log (31250 / 42083) ∧
    -Real.log (31250 / 42083) ≤ (297624483 / 1000000000) := by
  have h := checkLog_sound (w := (10833 / 73333)) (n := 12)
    (lo := (148812241 / 500000000)) (hi := (297624483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42083 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42083 / 31250) = 1/(31250 / 42083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (148812241 / 500000000) (297624483 / 1000000000) (Real.log (42083 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (42083 / 31250) = -Real.log (31250 / 42083) := by
    rw [show ((42083 / 31250) : ℝ) = ((31250 / 42083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (425651489 / 1000000000) ≤ -Real.log (20417 / 31250) ∧
    -Real.log (20417 / 31250) ≤ (42565149 / 100000000) := by
  have h := checkLog_sound (w := (10833 / 51667)) (n := 12)
    (lo := (425651489 / 1000000000)) (hi := (42565149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 20417) = 1/(20417 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-42565149 / 100000000) (-425651489 / 1000000000) (Real.log (20417 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (225714643 / 1000000000) ≤ -Real.log (500000 / 626609) ∧
    -Real.log (500000 / 626609) ≤ (56428661 / 250000000) := by
  have h := checkLog_sound (w := (126609 / 1126609)) (n := 12)
    (lo := (225714643 / 1000000000)) (hi := (56428661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626609 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626609 / 500000) = 1/(500000 / 626609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (225714643 / 1000000000) (56428661 / 250000000) (Real.log (626609 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (626609 / 500000) = -Real.log (500000 / 626609) := by
    rw [show ((626609 / 500000) : ℝ) = ((500000 / 626609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (29198197 / 100000000) ≤ -Real.log (373391 / 500000) ∧
    -Real.log (373391 / 500000) ≤ (291981971 / 1000000000) := by
  have h := checkLog_sound (w := (126609 / 873391)) (n := 12)
    (lo := (29198197 / 100000000)) (hi := (291981971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373391) = 1/(373391 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-291981971 / 1000000000) (-29198197 / 100000000) (Real.log (373391 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (225982717 / 1000000000) ≤ -Real.log (500000 / 626777) ∧
    -Real.log (500000 / 626777) ≤ (112991359 / 500000000) := by
  have h := checkLog_sound (w := (126777 / 1126777)) (n := 12)
    (lo := (225982717 / 1000000000)) (hi := (112991359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626777 / 500000) = 1/(500000 / 626777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (225982717 / 1000000000) (112991359 / 500000000) (Real.log (626777 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (626777 / 500000) = -Real.log (500000 / 626777) := by
    rw [show ((626777 / 500000) : ℝ) = ((500000 / 626777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (146216001 / 500000000) ≤ -Real.log (373223 / 500000) ∧
    -Real.log (373223 / 500000) ≤ (292432003 / 1000000000) := by
  have h := checkLog_sound (w := (126777 / 873223)) (n := 12)
    (lo := (146216001 / 500000000)) (hi := (292432003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373223) = 1/(373223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-292432003 / 1000000000) (-146216001 / 500000000) (Real.log (373223 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (361149337 / 500000000) ≤ -Real.log (500000000000 / 1029580558419) ∧
    -Real.log (500000000000 / 1029580558419) ≤ (180574669 / 250000000) := by
  have h := checkLog_sound (w := (29580558419 / 2029580558419)) (n := 12)
    (lo := (14575747 / 500000000)) (hi := (5830299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1029580558419 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1029580558419 / 1000000000000) = 1/(500000000000 / 1029580558419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (361149337 / 500000000) (180574669 / 250000000) (Real.log (1029580558419 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1029580558419 / 500000000000) = -Real.log (500000000000 / 1029580558419) := by
    rw [show ((1029580558419 / 500000000000) : ℝ) = ((500000000000 / 1029580558419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (72327597 / 100000000) ≤ -Real.log (500000000000 / 1030587255719) ∧
    -Real.log (500000000000 / 1030587255719) ≤ (180818993 / 250000000) := by
  have h := checkLog_sound (w := (30587255719 / 2030587255719)) (n := 12)
    (lo := (3012879 / 100000000)) (hi := (30128791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1030587255719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1030587255719 / 1000000000000) = 1/(500000000000 / 1030587255719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (72327597 / 100000000) (180818993 / 250000000) (Real.log (1030587255719 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1030587255719 / 500000000000) = -Real.log (500000000000 / 1030587255719) := by
    rw [show ((1030587255719 / 500000000000) : ℝ) = ((500000000000 / 1030587255719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (517696613 / 1000000000) ≤ -Real.log (500000000000 / 839078874423) ∧
    -Real.log (500000000000 / 839078874423) ≤ (258848307 / 500000000) := by
  have h := checkLog_sound (w := (339078874423 / 1339078874423)) (n := 12)
    (lo := (517696613 / 1000000000)) (hi := (258848307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839078874423 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839078874423 / 500000000000) = 1/(500000000000 / 839078874423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (517696613 / 1000000000) (258848307 / 500000000) (Real.log (839078874423 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (839078874423 / 500000000000) = -Real.log (500000000000 / 839078874423) := by
    rw [show ((839078874423 / 500000000000) : ℝ) = ((500000000000 / 839078874423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (518414719 / 1000000000) ≤ -Real.log (62500000000 / 104960204757) ∧
    -Real.log (62500000000 / 104960204757) ≤ (810023 / 1562500) := by
  have h := checkLog_sound (w := (42460204757 / 167460204757)) (n := 12)
    (lo := (518414719 / 1000000000)) (hi := (810023 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104960204757 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104960204757 / 62500000000) = 1/(62500000000 / 104960204757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (518414719 / 1000000000) (810023 / 1562500) (Real.log (104960204757 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (104960204757 / 62500000000) = -Real.log (62500000000 / 104960204757) := by
    rw [show ((104960204757 / 62500000000) : ℝ) = ((62500000000 / 104960204757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0329

end


