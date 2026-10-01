-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0417Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0417Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:37:04.854897+00:00
-- url     : https://prove2.me/theorems/236dbd4a-b5eb-41f6-8554-ea0f1b33a30c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0417Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0418Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0417Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0418Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0419Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0420Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0421Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0422Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0417Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0418Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0419Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0420Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0421Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0422Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0417Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0418Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0419Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0420Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0421Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0422Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0417Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0418Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0419Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0420Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0421Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0422Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0417Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0417
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

theorem reflection_log_1_neg : (196141633 / 1000000000) ≤ -Real.log (10240 / 12459) ∧
    -Real.log (10240 / 12459) ≤ (98070817 / 500000000) := by
  have h := checkLog_sound (w := (2219 / 22699)) (n := 12)
    (lo := (196141633 / 1000000000)) (hi := (98070817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12459 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12459 / 10240) = 1/(10240 / 12459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (196141633 / 1000000000) (98070817 / 500000000) (Real.log (12459 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12459 / 10240) = -Real.log (10240 / 12459) := by
    rw [show ((12459 / 10240) : ℝ) = ((10240 / 12459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (244238517 / 1000000000) ≤ -Real.log (8021 / 10240) ∧
    -Real.log (8021 / 10240) ≤ (122119259 / 500000000) := by
  have h := checkLog_sound (w := (2219 / 18261)) (n := 12)
    (lo := (244238517 / 1000000000)) (hi := (122119259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8021) = 1/(8021 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122119259 / 500000000) (-244238517 / 1000000000) (Real.log (8021 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (97950407 / 500000000) ≤ -Real.log (1280 / 1557) ∧
    -Real.log (1280 / 1557) ≤ (39180163 / 200000000) := by
  have h := checkLog_sound (w := (277 / 2837)) (n := 12)
    (lo := (97950407 / 500000000)) (hi := (39180163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1557 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1557 / 1280) = 1/(1280 / 1557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (97950407 / 500000000) (39180163 / 200000000) (Real.log (1557 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1557 / 1280) = -Real.log (1280 / 1557) := by
    rw [show ((1557 / 1280) : ℝ) = ((1280 / 1557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (30483071 / 125000000) ≤ -Real.log (1003 / 1280) ∧
    -Real.log (1003 / 1280) ≤ (243864569 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 2283)) (n := 12)
    (lo := (30483071 / 125000000)) (hi := (243864569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1003) = 1/(1003 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-243864569 / 1000000000) (-30483071 / 125000000) (Real.log (1003 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (180024077 / 500000000) ≤ -Real.log (5120 / 7339) ∧
    -Real.log (5120 / 7339) ≤ (72009631 / 200000000) := by
  have h := checkLog_sound (w := (2219 / 12459)) (n := 12)
    (lo := (180024077 / 500000000)) (hi := (72009631 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7339 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7339 / 5120) = 1/(5120 / 7339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (180024077 / 500000000) (72009631 / 200000000) (Real.log (7339 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7339 / 5120) = -Real.log (5120 / 7339) := by
    rw [show ((7339 / 5120) : ℝ) = ((5120 / 7339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (568098933 / 1000000000) ≤ -Real.log (2901 / 5120) ∧
    -Real.log (2901 / 5120) ≤ (284049467 / 500000000) := by
  have h := checkLog_sound (w := (2219 / 8021)) (n := 12)
    (lo := (568098933 / 1000000000)) (hi := (284049467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2901) = 1/(2901 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-284049467 / 500000000) (-568098933 / 1000000000) (Real.log (2901 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (71927859 / 200000000) ≤ -Real.log (640 / 917) ∧
    -Real.log (640 / 917) ≤ (1404841 / 3906250) := by
  have h := checkLog_sound (w := (277 / 1557)) (n := 12)
    (lo := (71927859 / 200000000)) (hi := (1404841 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917 / 640) = 1/(640 / 917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (71927859 / 200000000) (1404841 / 3906250) (Real.log (917 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (917 / 640) = -Real.log (640 / 917) := by
    rw [show ((917 / 640) : ℝ) = ((640 / 917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (283532671 / 500000000) ≤ -Real.log (363 / 640) ∧
    -Real.log (363 / 640) ≤ (567065343 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1003)) (n := 12)
    (lo := (283532671 / 500000000)) (hi := (567065343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 363) = 1/(363 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-567065343 / 1000000000) (-283532671 / 500000000) (Real.log (363 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (53797533 / 200000000) ≤ -Real.log (1000000 / 1308639) ∧
    -Real.log (1000000 / 1308639) ≤ (134493833 / 500000000) := by
  have h := checkLog_sound (w := (308639 / 2308639)) (n := 12)
    (lo := (53797533 / 200000000)) (hi := (134493833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1308639 / 1000000) = 1/(1000000 / 1308639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (53797533 / 200000000) (134493833 / 500000000) (Real.log (1308639 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1308639 / 1000000) = -Real.log (1000000 / 1308639) := by
    rw [show ((1308639 / 1000000) : ℝ) = ((1000000 / 1308639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9227329 / 25000000) ≤ -Real.log (691361 / 1000000) ∧
    -Real.log (691361 / 1000000) ≤ (369093161 / 1000000000) := by
  have h := checkLog_sound (w := (308639 / 1691361)) (n := 12)
    (lo := (9227329 / 25000000)) (hi := (369093161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 691361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 691361) = 1/(691361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-369093161 / 1000000000) (-9227329 / 25000000) (Real.log (691361 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (53862781 / 200000000) ≤ -Real.log (500000 / 654533) ∧
    -Real.log (500000 / 654533) ≤ (134656953 / 500000000) := by
  have h := checkLog_sound (w := (154533 / 1154533)) (n := 12)
    (lo := (53862781 / 200000000)) (hi := (134656953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654533 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654533 / 500000) = 1/(500000 / 654533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (53862781 / 200000000) (134656953 / 500000000) (Real.log (654533 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (654533 / 500000) = -Real.log (500000 / 654533) := by
    rw [show ((654533 / 500000) : ℝ) = ((500000 / 654533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (369710973 / 1000000000) ≤ -Real.log (345467 / 500000) ∧
    -Real.log (345467 / 500000) ≤ (184855487 / 500000000) := by
  have h := checkLog_sound (w := (154533 / 845467)) (n := 12)
    (lo := (369710973 / 1000000000)) (hi := (184855487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 345467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 345467) = 1/(345467 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-184855487 / 500000000) (-369710973 / 1000000000) (Real.log (345467 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (202248359 / 1000000000) ≤ -Real.log (125000 / 153019) ∧
    -Real.log (125000 / 153019) ≤ (5056209 / 25000000) := by
  have h := checkLog_sound (w := (28019 / 278019)) (n := 12)
    (lo := (202248359 / 1000000000)) (hi := (5056209 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153019 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153019 / 125000) = 1/(125000 / 153019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (202248359 / 1000000000) (5056209 / 25000000) (Real.log (153019 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (153019 / 125000) = -Real.log (125000 / 153019) := by
    rw [show ((153019 / 125000) : ℝ) = ((125000 / 153019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (126899327 / 500000000) ≤ -Real.log (96981 / 125000) ∧
    -Real.log (96981 / 125000) ≤ (50759731 / 200000000) := by
  have h := checkLog_sound (w := (28019 / 221981)) (n := 12)
    (lo := (126899327 / 500000000)) (hi := (50759731 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96981) = 1/(96981 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-50759731 / 200000000) (-126899327 / 500000000) (Real.log (96981 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (202515447 / 1000000000) ≤ -Real.log (1000000 / 1224479) ∧
    -Real.log (1000000 / 1224479) ≤ (25314431 / 125000000) := by
  have h := checkLog_sound (w := (224479 / 2224479)) (n := 12)
    (lo := (202515447 / 1000000000)) (hi := (25314431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1224479 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1224479 / 1000000) = 1/(1000000 / 1224479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (202515447 / 1000000000) (25314431 / 125000000) (Real.log (1224479 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1224479 / 1000000) = -Real.log (1000000 / 1224479) := by
    rw [show ((1224479 / 1000000) : ℝ) = ((1000000 / 1224479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (254220217 / 1000000000) ≤ -Real.log (775521 / 1000000) ∧
    -Real.log (775521 / 1000000) ≤ (127110109 / 500000000) := by
  have h := checkLog_sound (w := (224479 / 1775521)) (n := 12)
    (lo := (254220217 / 1000000000)) (hi := (127110109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 775521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 775521) = 1/(775521 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-127110109 / 500000000) (-254220217 / 1000000000) (Real.log (775521 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (319040413 / 500000000) ≤ -Real.log (250000000000 / 473211173323) ∧
    -Real.log (250000000000 / 473211173323) ≤ (638080827 / 1000000000) := by
  have h := checkLog_sound (w := (223211173323 / 723211173323)) (n := 12)
    (lo := (319040413 / 500000000)) (hi := (638080827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473211173323 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473211173323 / 250000000000) = 1/(250000000000 / 473211173323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (319040413 / 500000000) (638080827 / 1000000000) (Real.log (473211173323 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (473211173323 / 250000000000) = -Real.log (250000000000 / 473211173323) := by
    rw [show ((473211173323 / 250000000000) : ℝ) = ((250000000000 / 473211173323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (639024879 / 1000000000) ≤ -Real.log (250000000000 / 473658120747) ∧
    -Real.log (250000000000 / 473658120747) ≤ (7987811 / 12500000) := by
  have h := checkLog_sound (w := (223658120747 / 723658120747)) (n := 12)
    (lo := (639024879 / 1000000000)) (hi := (7987811 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473658120747 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473658120747 / 250000000000) = 1/(250000000000 / 473658120747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (639024879 / 1000000000) (7987811 / 12500000) (Real.log (473658120747 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (473658120747 / 250000000000) = -Real.log (250000000000 / 473658120747) := by
    rw [show ((473658120747 / 250000000000) : ℝ) = ((250000000000 / 473658120747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (456047013 / 1000000000) ≤ -Real.log (125000000000 / 197228065291) ∧
    -Real.log (125000000000 / 197228065291) ≤ (228023507 / 500000000) := by
  have h := checkLog_sound (w := (72228065291 / 322228065291)) (n := 12)
    (lo := (456047013 / 1000000000)) (hi := (228023507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197228065291 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197228065291 / 125000000000) = 1/(125000000000 / 197228065291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (456047013 / 1000000000) (228023507 / 500000000) (Real.log (197228065291 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (197228065291 / 125000000000) = -Real.log (125000000000 / 197228065291) := by
    rw [show ((197228065291 / 125000000000) : ℝ) = ((125000000000 / 197228065291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (28545979 / 62500000) ≤ -Real.log (50000000000 / 78945573363) ∧
    -Real.log (50000000000 / 78945573363) ≤ (91347133 / 200000000) := by
  have h := checkLog_sound (w := (28945573363 / 128945573363)) (n := 12)
    (lo := (28545979 / 62500000)) (hi := (91347133 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78945573363 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78945573363 / 50000000000) = 1/(50000000000 / 78945573363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (28545979 / 62500000) (91347133 / 200000000) (Real.log (78945573363 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (78945573363 / 50000000000) = -Real.log (50000000000 / 78945573363) := by
    rw [show ((78945573363 / 50000000000) : ℝ) = ((50000000000 / 78945573363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0417

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0418Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0418
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

theorem reflection_log_1_neg : (97950407 / 500000000) ≤ -Real.log (1280 / 1557) ∧
    -Real.log (1280 / 1557) ≤ (39180163 / 200000000) := by
  have h := checkLog_sound (w := (277 / 2837)) (n := 12)
    (lo := (97950407 / 500000000)) (hi := (39180163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1557 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1557 / 1280) = 1/(1280 / 1557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (97950407 / 500000000) (39180163 / 200000000) (Real.log (1557 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1557 / 1280) = -Real.log (1280 / 1557) := by
    rw [show ((1557 / 1280) : ℝ) = ((1280 / 1557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (30483071 / 125000000) ≤ -Real.log (1003 / 1280) ∧
    -Real.log (1003 / 1280) ≤ (243864569 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 2283)) (n := 12)
    (lo := (30483071 / 125000000)) (hi := (243864569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1003) = 1/(1003 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-243864569 / 1000000000) (-30483071 / 125000000) (Real.log (1003 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (97829969 / 500000000) ≤ -Real.log (10240 / 12453) ∧
    -Real.log (10240 / 12453) ≤ (195659939 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 22693)) (n := 12)
    (lo := (97829969 / 500000000)) (hi := (195659939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12453 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12453 / 10240) = 1/(10240 / 12453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (97829969 / 500000000) (195659939 / 1000000000) (Real.log (12453 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12453 / 10240) = -Real.log (10240 / 12453) := by
    rw [show ((12453 / 10240) : ℝ) = ((10240 / 12453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (6087269 / 25000000) ≤ -Real.log (8027 / 10240) ∧
    -Real.log (8027 / 10240) ≤ (243490761 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 18267)) (n := 12)
    (lo := (6087269 / 25000000)) (hi := (243490761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8027) = 1/(8027 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-243490761 / 1000000000) (-6087269 / 25000000) (Real.log (8027 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (71927859 / 200000000) ≤ -Real.log (640 / 917) ∧
    -Real.log (640 / 917) ≤ (1404841 / 3906250) := by
  have h := checkLog_sound (w := (277 / 1557)) (n := 12)
    (lo := (71927859 / 200000000)) (hi := (1404841 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917 / 640) = 1/(640 / 917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (71927859 / 200000000) (1404841 / 3906250) (Real.log (917 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (917 / 640) = -Real.log (640 / 917) := by
    rw [show ((917 / 640) : ℝ) = ((640 / 917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (283532671 / 500000000) ≤ -Real.log (363 / 640) ∧
    -Real.log (363 / 640) ≤ (567065343 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1003)) (n := 12)
    (lo := (283532671 / 500000000)) (hi := (567065343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 363) = 1/(363 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-567065343 / 1000000000) (-283532671 / 500000000) (Real.log (363 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (35923027 / 100000000) ≤ -Real.log (5120 / 7333) ∧
    -Real.log (5120 / 7333) ≤ (359230271 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 12453)) (n := 12)
    (lo := (35923027 / 100000000)) (hi := (359230271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7333 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7333 / 5120) = 1/(5120 / 7333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (35923027 / 100000000) (359230271 / 1000000000) (Real.log (7333 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7333 / 5120) = -Real.log (5120 / 7333) := by
    rw [show ((7333 / 5120) : ℝ) = ((5120 / 7333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (566032817 / 1000000000) ≤ -Real.log (2907 / 5120) ∧
    -Real.log (2907 / 5120) ≤ (283016409 / 500000000) := by
  have h := checkLog_sound (w := (2213 / 8027)) (n := 12)
    (lo := (566032817 / 1000000000)) (hi := (283016409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2907) = 1/(2907 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-283016409 / 500000000) (-566032817 / 1000000000) (Real.log (2907 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4197857 / 15625000) ≤ -Real.log (500000 / 654107) ∧
    -Real.log (500000 / 654107) ≤ (268662849 / 1000000000) := by
  have h := checkLog_sound (w := (154107 / 1154107)) (n := 12)
    (lo := (4197857 / 15625000)) (hi := (268662849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654107 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654107 / 500000) = 1/(500000 / 654107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4197857 / 15625000) (268662849 / 1000000000) (Real.log (654107 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (654107 / 500000) = -Real.log (500000 / 654107) := by
    rw [show ((654107 / 500000) : ℝ) = ((500000 / 654107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (368478619 / 1000000000) ≤ -Real.log (345893 / 500000) ∧
    -Real.log (345893 / 500000) ≤ (18423931 / 50000000) := by
  have h := checkLog_sound (w := (154107 / 845893)) (n := 12)
    (lo := (368478619 / 1000000000)) (hi := (18423931 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 345893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 345893) = 1/(345893 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18423931 / 50000000) (-368478619 / 1000000000) (Real.log (345893 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (26898843 / 100000000) ≤ -Real.log (6250 / 8179) ∧
    -Real.log (6250 / 8179) ≤ (268988431 / 1000000000) := by
  have h := checkLog_sound (w := (1929 / 14429)) (n := 12)
    (lo := (26898843 / 100000000)) (hi := (268988431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8179 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8179 / 6250) = 1/(6250 / 8179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (26898843 / 100000000) (268988431 / 1000000000) (Real.log (8179 / 6250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (8179 / 6250) = -Real.log (6250 / 8179) := by
    rw [show ((8179 / 6250) : ℝ) = ((6250 / 8179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (184547303 / 500000000) ≤ -Real.log (4321 / 6250) ∧
    -Real.log (4321 / 6250) ≤ (369094607 / 1000000000) := by
  have h := checkLog_sound (w := (1929 / 10571)) (n := 12)
    (lo := (184547303 / 500000000)) (hi := (369094607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 4321) = 1/(4321 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-369094607 / 1000000000) (-184547303 / 500000000) (Real.log (4321 / 6250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (100991417 / 500000000) ≤ -Real.log (1000000 / 1223827) ∧
    -Real.log (1000000 / 1223827) ≤ (40396567 / 200000000) := by
  have h := checkLog_sound (w := (223827 / 2223827)) (n := 12)
    (lo := (100991417 / 500000000)) (hi := (40396567 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223827 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223827 / 1000000) = 1/(1000000 / 1223827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (100991417 / 500000000) (40396567 / 200000000) (Real.log (1223827 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1223827 / 1000000) = -Real.log (1000000 / 1223827) := by
    rw [show ((1223827 / 1000000) : ℝ) = ((1000000 / 1223827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (50675969 / 200000000) ≤ -Real.log (776173 / 1000000) ∧
    -Real.log (776173 / 1000000) ≤ (126689923 / 500000000) := by
  have h := checkLog_sound (w := (223827 / 1776173)) (n := 12)
    (lo := (50675969 / 200000000)) (hi := (126689923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776173) = 1/(776173 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-126689923 / 500000000) (-50675969 / 200000000) (Real.log (776173 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (25281147 / 125000000) ≤ -Real.log (1000000 / 1224153) ∧
    -Real.log (1000000 / 1224153) ≤ (202249177 / 1000000000) := by
  have h := checkLog_sound (w := (224153 / 2224153)) (n := 12)
    (lo := (25281147 / 125000000)) (hi := (202249177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1224153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1224153 / 1000000) = 1/(1000000 / 1224153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (25281147 / 125000000) (202249177 / 1000000000) (Real.log (1224153 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1224153 / 1000000) = -Real.log (1000000 / 1224153) := by
    rw [show ((1224153 / 1000000) : ℝ) = ((1000000 / 1224153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (253799943 / 1000000000) ≤ -Real.log (775847 / 1000000) ∧
    -Real.log (775847 / 1000000) ≤ (31724993 / 125000000) := by
  have h := checkLog_sound (w := (224153 / 1775847)) (n := 12)
    (lo := (253799943 / 1000000000)) (hi := (31724993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 775847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 775847) = 1/(775847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-31724993 / 125000000) (-253799943 / 1000000000) (Real.log (775847 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (637141467 / 1000000000) ≤ -Real.log (25000000000 / 47276686721) ∧
    -Real.log (25000000000 / 47276686721) ≤ (159285367 / 250000000) := by
  have h := checkLog_sound (w := (22276686721 / 72276686721)) (n := 12)
    (lo := (637141467 / 1000000000)) (hi := (159285367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47276686721 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47276686721 / 25000000000) = 1/(25000000000 / 47276686721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (637141467 / 1000000000) (159285367 / 250000000) (Real.log (47276686721 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (47276686721 / 25000000000) = -Real.log (25000000000 / 47276686721) := by
    rw [show ((47276686721 / 25000000000) : ℝ) = ((25000000000 / 47276686721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (159520759 / 250000000) ≤ -Real.log (125000000000 / 236606109697) ∧
    -Real.log (125000000000 / 236606109697) ≤ (638083037 / 1000000000) := by
  have h := checkLog_sound (w := (111606109697 / 361606109697)) (n := 12)
    (lo := (159520759 / 250000000)) (hi := (638083037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236606109697 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236606109697 / 125000000000) = 1/(125000000000 / 236606109697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (159520759 / 250000000) (638083037 / 1000000000) (Real.log (236606109697 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (236606109697 / 125000000000) = -Real.log (125000000000 / 236606109697) := by
    rw [show ((236606109697 / 125000000000) : ℝ) = ((125000000000 / 236606109697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (455362679 / 1000000000) ≤ -Real.log (20000000000 / 31534902657) ∧
    -Real.log (20000000000 / 31534902657) ≤ (11384067 / 25000000) := by
  have h := checkLog_sound (w := (11534902657 / 51534902657)) (n := 12)
    (lo := (455362679 / 1000000000)) (hi := (11384067 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31534902657 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31534902657 / 20000000000) = 1/(20000000000 / 31534902657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (455362679 / 1000000000) (11384067 / 25000000) (Real.log (31534902657 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (31534902657 / 20000000000) = -Real.log (20000000000 / 31534902657) := by
    rw [show ((31534902657 / 20000000000) : ℝ) = ((20000000000 / 31534902657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (456049119 / 1000000000) ≤ -Real.log (250000000000 / 394456961231) ∧
    -Real.log (250000000000 / 394456961231) ≤ (2850307 / 6250000) := by
  have h := checkLog_sound (w := (144456961231 / 644456961231)) (n := 12)
    (lo := (456049119 / 1000000000)) (hi := (2850307 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394456961231 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394456961231 / 250000000000) = 1/(250000000000 / 394456961231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (456049119 / 1000000000) (2850307 / 6250000) (Real.log (394456961231 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (394456961231 / 250000000000) = -Real.log (250000000000 / 394456961231) := by
    rw [show ((394456961231 / 250000000000) : ℝ) = ((250000000000 / 394456961231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0418

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0419Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0419
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

theorem reflection_log_1_neg : (97829969 / 500000000) ≤ -Real.log (10240 / 12453) ∧
    -Real.log (10240 / 12453) ≤ (195659939 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 22693)) (n := 12)
    (lo := (97829969 / 500000000)) (hi := (195659939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12453 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12453 / 10240) = 1/(10240 / 12453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (97829969 / 500000000) (195659939 / 1000000000) (Real.log (12453 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12453 / 10240) = -Real.log (10240 / 12453) := by
    rw [show ((12453 / 10240) : ℝ) = ((10240 / 12453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (6087269 / 25000000) ≤ -Real.log (8027 / 10240) ∧
    -Real.log (8027 / 10240) ≤ (243490761 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 18267)) (n := 12)
    (lo := (6087269 / 25000000)) (hi := (243490761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8027) = 1/(8027 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-243490761 / 1000000000) (-6087269 / 25000000) (Real.log (8027 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (195419003 / 1000000000) ≤ -Real.log (1024 / 1245) ∧
    -Real.log (1024 / 1245) ≤ (48854751 / 250000000) := by
  have h := checkLog_sound (w := (221 / 2269)) (n := 12)
    (lo := (195419003 / 1000000000)) (hi := (48854751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245 / 1024) = 1/(1024 / 1245) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (195419003 / 1000000000) (48854751 / 250000000) (Real.log (1245 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1245 / 1024) = -Real.log (1024 / 1245) := by
    rw [show ((1245 / 1024) : ℝ) = ((1024 / 1245) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (243117091 / 1000000000) ≤ -Real.log (803 / 1024) ∧
    -Real.log (803 / 1024) ≤ (60779273 / 250000000) := by
  have h := checkLog_sound (w := (221 / 1827)) (n := 12)
    (lo := (243117091 / 1000000000)) (hi := (60779273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 803) = 1/(803 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-60779273 / 250000000) (-243117091 / 1000000000) (Real.log (803 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (35923027 / 100000000) ≤ -Real.log (5120 / 7333) ∧
    -Real.log (5120 / 7333) ≤ (359230271 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 12453)) (n := 12)
    (lo := (35923027 / 100000000)) (hi := (359230271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7333 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7333 / 5120) = 1/(5120 / 7333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (35923027 / 100000000) (359230271 / 1000000000) (Real.log (7333 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7333 / 5120) = -Real.log (5120 / 7333) := by
    rw [show ((7333 / 5120) : ℝ) = ((5120 / 7333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (566032817 / 1000000000) ≤ -Real.log (2907 / 5120) ∧
    -Real.log (2907 / 5120) ≤ (283016409 / 500000000) := by
  have h := checkLog_sound (w := (2213 / 8027)) (n := 12)
    (lo := (566032817 / 1000000000)) (hi := (283016409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2907) = 1/(2907 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-283016409 / 500000000) (-566032817 / 1000000000) (Real.log (2907 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (89705269 / 250000000) ≤ -Real.log (512 / 733) ∧
    -Real.log (512 / 733) ≤ (358821077 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1245)) (n := 12)
    (lo := (89705269 / 250000000)) (hi := (358821077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733 / 512) = 1/(512 / 733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (89705269 / 250000000) (358821077 / 1000000000) (Real.log (733 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (733 / 512) = -Real.log (512 / 733) := by
    rw [show ((733 / 512) : ℝ) = ((512 / 733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (565001357 / 1000000000) ≤ -Real.log (291 / 512) ∧
    -Real.log (291 / 512) ≤ (282500679 / 500000000) := by
  have h := checkLog_sound (w := (221 / 803)) (n := 12)
    (lo := (565001357 / 1000000000)) (hi := (282500679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 291) = 1/(291 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-282500679 / 500000000) (-565001357 / 1000000000) (Real.log (291 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6708429 / 25000000) ≤ -Real.log (250000 / 326947) ∧
    -Real.log (250000 / 326947) ≤ (268337161 / 1000000000) := by
  have h := checkLog_sound (w := (76947 / 576947)) (n := 12)
    (lo := (6708429 / 25000000)) (hi := (268337161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326947 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326947 / 250000) = 1/(250000 / 326947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6708429 / 25000000) (268337161 / 1000000000) (Real.log (326947 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (326947 / 250000) = -Real.log (250000 / 326947) := by
    rw [show ((326947 / 250000) : ℝ) = ((250000 / 326947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (367863011 / 1000000000) ≤ -Real.log (173053 / 250000) ∧
    -Real.log (173053 / 250000) ≤ (91965753 / 250000000) := by
  have h := checkLog_sound (w := (76947 / 423053)) (n := 12)
    (lo := (367863011 / 1000000000)) (hi := (91965753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 173053) = 1/(173053 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91965753 / 250000000) (-367863011 / 1000000000) (Real.log (173053 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67165903 / 250000000) ≤ -Real.log (200000 / 261643) ∧
    -Real.log (200000 / 261643) ≤ (268663613 / 1000000000) := by
  have h := checkLog_sound (w := (61643 / 461643)) (n := 12)
    (lo := (67165903 / 250000000)) (hi := (268663613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261643 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261643 / 200000) = 1/(200000 / 261643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67165903 / 250000000) (268663613 / 1000000000) (Real.log (261643 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (261643 / 200000) = -Real.log (200000 / 261643) := by
    rw [show ((261643 / 200000) : ℝ) = ((200000 / 261643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (73696013 / 200000000) ≤ -Real.log (138357 / 200000) ∧
    -Real.log (138357 / 200000) ≤ (184240033 / 500000000) := by
  have h := checkLog_sound (w := (61643 / 338357)) (n := 12)
    (lo := (73696013 / 200000000)) (hi := (184240033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 138357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 138357) = 1/(138357 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-184240033 / 500000000) (-73696013 / 200000000) (Real.log (138357 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (201716421 / 1000000000) ≤ -Real.log (1000000 / 1223501) ∧
    -Real.log (1000000 / 1223501) ≤ (100858211 / 500000000) := by
  have h := checkLog_sound (w := (223501 / 2223501)) (n := 12)
    (lo := (201716421 / 1000000000)) (hi := (100858211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223501 / 1000000) = 1/(1000000 / 1223501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (201716421 / 1000000000) (100858211 / 500000000) (Real.log (1223501 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1223501 / 1000000) = -Real.log (1000000 / 1223501) := by
    rw [show ((1223501 / 1000000) : ℝ) = ((1000000 / 1223501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (63239981 / 250000000) ≤ -Real.log (776499 / 1000000) ∧
    -Real.log (776499 / 1000000) ≤ (10118397 / 40000000) := by
  have h := checkLog_sound (w := (223501 / 1776499)) (n := 12)
    (lo := (63239981 / 250000000)) (hi := (10118397 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776499) = 1/(776499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10118397 / 40000000) (-63239981 / 250000000) (Real.log (776499 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (201983651 / 1000000000) ≤ -Real.log (250000 / 305957) ∧
    -Real.log (250000 / 305957) ≤ (50495913 / 250000000) := by
  have h := checkLog_sound (w := (55957 / 555957)) (n := 12)
    (lo := (201983651 / 1000000000)) (hi := (50495913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305957 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305957 / 250000) = 1/(250000 / 305957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (201983651 / 1000000000) (50495913 / 250000000) (Real.log (305957 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (305957 / 250000) = -Real.log (250000 / 305957) := by
    rw [show ((305957 / 250000) : ℝ) = ((250000 / 305957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (253381133 / 1000000000) ≤ -Real.log (194043 / 250000) ∧
    -Real.log (194043 / 250000) ≤ (126690567 / 500000000) := by
  have h := checkLog_sound (w := (55957 / 444043)) (n := 12)
    (lo := (253381133 / 1000000000)) (hi := (126690567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194043) = 1/(194043 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-126690567 / 500000000) (-253381133 / 1000000000) (Real.log (194043 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (159050043 / 250000000) ≤ -Real.log (100000000000 / 188928825273) ∧
    -Real.log (100000000000 / 188928825273) ≤ (636200173 / 1000000000) := by
  have h := checkLog_sound (w := (88928825273 / 288928825273)) (n := 12)
    (lo := (159050043 / 250000000)) (hi := (636200173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188928825273 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188928825273 / 100000000000) = 1/(100000000000 / 188928825273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (159050043 / 250000000) (636200173 / 1000000000) (Real.log (188928825273 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (188928825273 / 100000000000) = -Real.log (100000000000 / 188928825273) := by
    rw [show ((188928825273 / 100000000000) : ℝ) = ((100000000000 / 188928825273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (637143677 / 1000000000) ≤ -Real.log (62500000000 / 118191977999) ∧
    -Real.log (62500000000 / 118191977999) ≤ (318571839 / 500000000) := by
  have h := checkLog_sound (w := (55691977999 / 180691977999)) (n := 12)
    (lo := (637143677 / 1000000000)) (hi := (318571839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118191977999 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118191977999 / 62500000000) = 1/(62500000000 / 118191977999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (637143677 / 1000000000) (318571839 / 500000000) (Real.log (118191977999 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (118191977999 / 62500000000) = -Real.log (62500000000 / 118191977999) := by
    rw [show ((118191977999 / 62500000000) : ℝ) = ((62500000000 / 118191977999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (90935269 / 200000000) ≤ -Real.log (500000000000 / 787831664947) ∧
    -Real.log (500000000000 / 787831664947) ≤ (227338173 / 500000000) := by
  have h := checkLog_sound (w := (287831664947 / 1287831664947)) (n := 12)
    (lo := (90935269 / 200000000)) (hi := (227338173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787831664947 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787831664947 / 500000000000) = 1/(500000000000 / 787831664947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (90935269 / 200000000) (227338173 / 500000000) (Real.log (787831664947 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (787831664947 / 500000000000) = -Real.log (500000000000 / 787831664947) := by
    rw [show ((787831664947 / 500000000000) : ℝ) = ((500000000000 / 787831664947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (91072957 / 200000000) ≤ -Real.log (125000000000 / 197093556583) ∧
    -Real.log (125000000000 / 197093556583) ≤ (227682393 / 500000000) := by
  have h := checkLog_sound (w := (72093556583 / 322093556583)) (n := 12)
    (lo := (91072957 / 200000000)) (hi := (227682393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197093556583 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197093556583 / 125000000000) = 1/(125000000000 / 197093556583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (91072957 / 200000000) (227682393 / 500000000) (Real.log (197093556583 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (197093556583 / 125000000000) = -Real.log (125000000000 / 197093556583) := by
    rw [show ((197093556583 / 125000000000) : ℝ) = ((125000000000 / 197093556583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0419

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0420Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0420
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

theorem reflection_log_1_neg : (195419003 / 1000000000) ≤ -Real.log (1024 / 1245) ∧
    -Real.log (1024 / 1245) ≤ (48854751 / 250000000) := by
  have h := checkLog_sound (w := (221 / 2269)) (n := 12)
    (lo := (195419003 / 1000000000)) (hi := (48854751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245 / 1024) = 1/(1024 / 1245) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (195419003 / 1000000000) (48854751 / 250000000) (Real.log (1245 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1245 / 1024) = -Real.log (1024 / 1245) := by
    rw [show ((1245 / 1024) : ℝ) = ((1024 / 1245) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (243117091 / 1000000000) ≤ -Real.log (803 / 1024) ∧
    -Real.log (803 / 1024) ≤ (60779273 / 250000000) := by
  have h := checkLog_sound (w := (221 / 1827)) (n := 12)
    (lo := (243117091 / 1000000000)) (hi := (60779273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 803) = 1/(803 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-60779273 / 250000000) (-243117091 / 1000000000) (Real.log (803 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (19517801 / 100000000) ≤ -Real.log (10240 / 12447) ∧
    -Real.log (10240 / 12447) ≤ (195178011 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 22687)) (n := 12)
    (lo := (19517801 / 100000000)) (hi := (195178011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12447 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12447 / 10240) = 1/(10240 / 12447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (19517801 / 100000000) (195178011 / 1000000000) (Real.log (12447 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12447 / 10240) = -Real.log (10240 / 12447) := by
    rw [show ((12447 / 10240) : ℝ) = ((10240 / 12447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (121371781 / 500000000) ≤ -Real.log (8033 / 10240) ∧
    -Real.log (8033 / 10240) ≤ (242743563 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 18273)) (n := 12)
    (lo := (121371781 / 500000000)) (hi := (242743563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8033) = 1/(8033 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-242743563 / 1000000000) (-121371781 / 500000000) (Real.log (8033 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (89705269 / 250000000) ≤ -Real.log (512 / 733) ∧
    -Real.log (512 / 733) ≤ (358821077 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1245)) (n := 12)
    (lo := (89705269 / 250000000)) (hi := (358821077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733 / 512) = 1/(512 / 733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (89705269 / 250000000) (358821077 / 1000000000) (Real.log (733 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (733 / 512) = -Real.log (512 / 733) := by
    rw [show ((733 / 512) : ℝ) = ((512 / 733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (565001357 / 1000000000) ≤ -Real.log (291 / 512) ∧
    -Real.log (291 / 512) ≤ (282500679 / 500000000) := by
  have h := checkLog_sound (w := (221 / 803)) (n := 12)
    (lo := (565001357 / 1000000000)) (hi := (282500679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 291) = 1/(291 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-282500679 / 500000000) (-565001357 / 1000000000) (Real.log (291 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (89602929 / 250000000) ≤ -Real.log (5120 / 7327) ∧
    -Real.log (5120 / 7327) ≤ (358411717 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 12447)) (n := 12)
    (lo := (89602929 / 250000000)) (hi := (358411717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7327 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7327 / 5120) = 1/(5120 / 7327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (89602929 / 250000000) (358411717 / 1000000000) (Real.log (7327 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7327 / 5120) = -Real.log (5120 / 7327) := by
    rw [show ((7327 / 5120) : ℝ) = ((5120 / 7327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (563970961 / 1000000000) ≤ -Real.log (2913 / 5120) ∧
    -Real.log (2913 / 5120) ≤ (281985481 / 500000000) := by
  have h := checkLog_sound (w := (2207 / 8033)) (n := 12)
    (lo := (563970961 / 1000000000)) (hi := (281985481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2913) = 1/(2913 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-281985481 / 500000000) (-563970961 / 1000000000) (Real.log (2913 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (268010601 / 1000000000) ≤ -Real.log (1000000 / 1307361) ∧
    -Real.log (1000000 / 1307361) ≤ (134005301 / 500000000) := by
  have h := checkLog_sound (w := (307361 / 2307361)) (n := 12)
    (lo := (268010601 / 1000000000)) (hi := (134005301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307361 / 1000000) = 1/(1000000 / 1307361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (268010601 / 1000000000) (134005301 / 500000000) (Real.log (1307361 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1307361 / 1000000) = -Real.log (1000000 / 1307361) := by
    rw [show ((1307361 / 1000000) : ℝ) = ((1000000 / 1307361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (367246339 / 1000000000) ≤ -Real.log (692639 / 1000000) ∧
    -Real.log (692639 / 1000000) ≤ (18362317 / 50000000) := by
  have h := checkLog_sound (w := (307361 / 1692639)) (n := 12)
    (lo := (367246339 / 1000000000)) (hi := (18362317 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 692639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 692639) = 1/(692639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18362317 / 50000000) (-367246339 / 1000000000) (Real.log (692639 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (10733517 / 40000000) ≤ -Real.log (1000000 / 1307789) ∧
    -Real.log (1000000 / 1307789) ≤ (134168963 / 500000000) := by
  have h := checkLog_sound (w := (307789 / 2307789)) (n := 12)
    (lo := (10733517 / 40000000)) (hi := (134168963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307789 / 1000000) = 1/(1000000 / 1307789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (10733517 / 40000000) (134168963 / 500000000) (Real.log (1307789 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1307789 / 1000000) = -Real.log (1000000 / 1307789) := by
    rw [show ((1307789 / 1000000) : ℝ) = ((1000000 / 1307789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (45983057 / 125000000) ≤ -Real.log (692211 / 1000000) ∧
    -Real.log (692211 / 1000000) ≤ (367864457 / 1000000000) := by
  have h := checkLog_sound (w := (307789 / 1692211)) (n := 12)
    (lo := (45983057 / 125000000)) (hi := (367864457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 692211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 692211) = 1/(692211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-367864457 / 1000000000) (-45983057 / 125000000) (Real.log (692211 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (100725377 / 500000000) ≤ -Real.log (125000 / 152897) ∧
    -Real.log (125000 / 152897) ≤ (40290151 / 200000000) := by
  have h := checkLog_sound (w := (27897 / 277897)) (n := 12)
    (lo := (100725377 / 500000000)) (hi := (40290151 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152897 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152897 / 125000) = 1/(125000 / 152897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (100725377 / 500000000) (40290151 / 200000000) (Real.log (152897 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (152897 / 125000) = -Real.log (125000 / 152897) := by
    rw [show ((152897 / 125000) : ℝ) = ((125000 / 152897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (126270733 / 500000000) ≤ -Real.log (97103 / 125000) ∧
    -Real.log (97103 / 125000) ≤ (252541467 / 1000000000) := by
  have h := checkLog_sound (w := (27897 / 222103)) (n := 12)
    (lo := (126270733 / 500000000)) (hi := (252541467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97103) = 1/(97103 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-252541467 / 1000000000) (-126270733 / 500000000) (Real.log (97103 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (100858619 / 500000000) ≤ -Real.log (500000 / 611751) ∧
    -Real.log (500000 / 611751) ≤ (201717239 / 1000000000) := by
  have h := checkLog_sound (w := (111751 / 1111751)) (n := 12)
    (lo := (100858619 / 500000000)) (hi := (201717239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611751 / 500000) = 1/(500000 / 611751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (100858619 / 500000000) (201717239 / 1000000000) (Real.log (611751 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (611751 / 500000) = -Real.log (500000 / 611751) := by
    rw [show ((611751 / 500000) : ℝ) = ((500000 / 611751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (63240303 / 250000000) ≤ -Real.log (388249 / 500000) ∧
    -Real.log (388249 / 500000) ≤ (252961213 / 1000000000) := by
  have h := checkLog_sound (w := (111751 / 888249)) (n := 12)
    (lo := (63240303 / 250000000)) (hi := (252961213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388249) = 1/(388249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-252961213 / 1000000000) (-63240303 / 250000000) (Real.log (388249 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (31762847 / 50000000) ≤ -Real.log (125000000000 / 235938382043) ∧
    -Real.log (125000000000 / 235938382043) ≤ (635256941 / 1000000000) := by
  have h := checkLog_sound (w := (110938382043 / 360938382043)) (n := 12)
    (lo := (31762847 / 50000000)) (hi := (635256941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235938382043 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235938382043 / 125000000000) = 1/(125000000000 / 235938382043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (31762847 / 50000000) (635256941 / 1000000000) (Real.log (235938382043 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (235938382043 / 125000000000) = -Real.log (125000000000 / 235938382043) := by
    rw [show ((235938382043 / 125000000000) : ℝ) = ((125000000000 / 235938382043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (636202381 / 1000000000) ≤ -Real.log (250000000000 / 472323106683) ∧
    -Real.log (250000000000 / 472323106683) ≤ (318101191 / 500000000) := by
  have h := checkLog_sound (w := (222323106683 / 722323106683)) (n := 12)
    (lo := (636202381 / 1000000000)) (hi := (318101191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((472323106683 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(472323106683 / 250000000000) = 1/(250000000000 / 472323106683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (636202381 / 1000000000) (318101191 / 500000000) (Real.log (472323106683 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (472323106683 / 250000000000) = -Real.log (250000000000 / 472323106683) := by
    rw [show ((472323106683 / 250000000000) : ℝ) = ((250000000000 / 472323106683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (453992221 / 1000000000) ≤ -Real.log (31250000000 / 49205804661) ∧
    -Real.log (31250000000 / 49205804661) ≤ (226996111 / 500000000) := by
  have h := checkLog_sound (w := (17955804661 / 80455804661)) (n := 12)
    (lo := (453992221 / 1000000000)) (hi := (226996111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49205804661 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49205804661 / 31250000000) = 1/(31250000000 / 49205804661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (453992221 / 1000000000) (226996111 / 500000000) (Real.log (49205804661 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49205804661 / 31250000000) = -Real.log (31250000000 / 49205804661) := by
    rw [show ((49205804661 / 31250000000) : ℝ) = ((31250000000 / 49205804661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (9093569 / 20000000) ≤ -Real.log (25000000000 / 39391666173) ∧
    -Real.log (25000000000 / 39391666173) ≤ (454678451 / 1000000000) := by
  have h := checkLog_sound (w := (14391666173 / 64391666173)) (n := 12)
    (lo := (9093569 / 20000000)) (hi := (454678451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39391666173 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39391666173 / 25000000000) = 1/(25000000000 / 39391666173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (9093569 / 20000000) (454678451 / 1000000000) (Real.log (39391666173 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (39391666173 / 25000000000) = -Real.log (25000000000 / 39391666173) := by
    rw [show ((39391666173 / 25000000000) : ℝ) = ((25000000000 / 39391666173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0420

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0421Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0421
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

theorem reflection_log_1_neg : (19517801 / 100000000) ≤ -Real.log (10240 / 12447) ∧
    -Real.log (10240 / 12447) ≤ (195178011 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 22687)) (n := 12)
    (lo := (19517801 / 100000000)) (hi := (195178011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12447 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12447 / 10240) = 1/(10240 / 12447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (19517801 / 100000000) (195178011 / 1000000000) (Real.log (12447 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12447 / 10240) = -Real.log (10240 / 12447) := by
    rw [show ((12447 / 10240) : ℝ) = ((10240 / 12447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (121371781 / 500000000) ≤ -Real.log (8033 / 10240) ∧
    -Real.log (8033 / 10240) ≤ (242743563 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 18273)) (n := 12)
    (lo := (121371781 / 500000000)) (hi := (242743563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8033) = 1/(8033 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-242743563 / 1000000000) (-121371781 / 500000000) (Real.log (8033 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (194936959 / 1000000000) ≤ -Real.log (2560 / 3111) ∧
    -Real.log (2560 / 3111) ≤ (304589 / 1562500) := by
  have h := checkLog_sound (w := (551 / 5671)) (n := 12)
    (lo := (194936959 / 1000000000)) (hi := (304589 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3111 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3111 / 2560) = 1/(2560 / 3111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (194936959 / 1000000000) (304589 / 1562500) (Real.log (3111 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3111 / 2560) = -Real.log (2560 / 3111) := by
    rw [show ((3111 / 2560) : ℝ) = ((2560 / 3111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (60592543 / 250000000) ≤ -Real.log (2009 / 2560) ∧
    -Real.log (2009 / 2560) ≤ (242370173 / 1000000000) := by
  have h := checkLog_sound (w := (551 / 4569)) (n := 12)
    (lo := (60592543 / 250000000)) (hi := (242370173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2009) = 1/(2009 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-242370173 / 1000000000) (-60592543 / 250000000) (Real.log (2009 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (89602929 / 250000000) ≤ -Real.log (5120 / 7327) ∧
    -Real.log (5120 / 7327) ≤ (358411717 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 12447)) (n := 12)
    (lo := (89602929 / 250000000)) (hi := (358411717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7327 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7327 / 5120) = 1/(5120 / 7327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (89602929 / 250000000) (358411717 / 1000000000) (Real.log (7327 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7327 / 5120) = -Real.log (5120 / 7327) := by
    rw [show ((7327 / 5120) : ℝ) = ((5120 / 7327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (563970961 / 1000000000) ≤ -Real.log (2913 / 5120) ∧
    -Real.log (2913 / 5120) ≤ (281985481 / 500000000) := by
  have h := checkLog_sound (w := (2207 / 8033)) (n := 12)
    (lo := (563970961 / 1000000000)) (hi := (281985481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2913) = 1/(2913 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-281985481 / 500000000) (-563970961 / 1000000000) (Real.log (2913 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (358002187 / 1000000000) ≤ -Real.log (1280 / 1831) ∧
    -Real.log (1280 / 1831) ≤ (89500547 / 250000000) := by
  have h := checkLog_sound (w := (551 / 3111)) (n := 12)
    (lo := (358002187 / 1000000000)) (hi := (89500547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1831 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1831 / 1280) = 1/(1280 / 1831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (358002187 / 1000000000) (89500547 / 250000000) (Real.log (1831 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1831 / 1280) = -Real.log (1280 / 1831) := by
    rw [show ((1831 / 1280) : ℝ) = ((1280 / 1831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (70367703 / 125000000) ≤ -Real.log (729 / 1280) ∧
    -Real.log (729 / 1280) ≤ (4503533 / 8000000) := by
  have h := checkLog_sound (w := (551 / 2009)) (n := 12)
    (lo := (70367703 / 125000000)) (hi := (4503533 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 729) = 1/(729 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4503533 / 8000000) (-70367703 / 125000000) (Real.log (729 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66921749 / 250000000) ≤ -Real.log (500000 / 653469) ∧
    -Real.log (500000 / 653469) ≤ (267686997 / 1000000000) := by
  have h := checkLog_sound (w := (153469 / 1153469)) (n := 12)
    (lo := (66921749 / 250000000)) (hi := (267686997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653469 / 500000) = 1/(500000 / 653469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66921749 / 250000000) (267686997 / 1000000000) (Real.log (653469 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (653469 / 500000) = -Real.log (500000 / 653469) := by
    rw [show ((653469 / 500000) : ℝ) = ((500000 / 653469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (366635817 / 1000000000) ≤ -Real.log (346531 / 500000) ∧
    -Real.log (346531 / 500000) ≤ (183317909 / 500000000) := by
  have h := checkLog_sound (w := (153469 / 846531)) (n := 12)
    (lo := (366635817 / 1000000000)) (hi := (183317909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 346531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 346531) = 1/(346531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-183317909 / 500000000) (-366635817 / 1000000000) (Real.log (346531 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (8375403 / 31250000) ≤ -Real.log (250000 / 326841) ∧
    -Real.log (250000 / 326841) ≤ (268012897 / 1000000000) := by
  have h := checkLog_sound (w := (76841 / 576841)) (n := 12)
    (lo := (8375403 / 31250000)) (hi := (268012897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326841 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326841 / 250000) = 1/(250000 / 326841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (8375403 / 31250000) (268012897 / 1000000000) (Real.log (326841 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (326841 / 250000) = -Real.log (250000 / 326841) := by
    rw [show ((326841 / 250000) : ℝ) = ((250000 / 326841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (36725067 / 100000000) ≤ -Real.log (173159 / 250000) ∧
    -Real.log (173159 / 250000) ≤ (367250671 / 1000000000) := by
  have h := checkLog_sound (w := (76841 / 423159)) (n := 12)
    (lo := (36725067 / 100000000)) (hi := (367250671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 173159) = 1/(173159 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-367250671 / 1000000000) (-36725067 / 100000000) (Real.log (173159 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (201184199 / 1000000000) ≤ -Real.log (20000 / 24457) ∧
    -Real.log (20000 / 24457) ≤ (1005921 / 5000000) := by
  have h := checkLog_sound (w := (4457 / 44457)) (n := 12)
    (lo := (201184199 / 1000000000)) (hi := (1005921 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24457 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24457 / 20000) = 1/(20000 / 24457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (201184199 / 1000000000) (1005921 / 5000000) (Real.log (24457 / 20000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (24457 / 20000) = -Real.log (20000 / 24457) := by
    rw [show ((24457 / 20000) : ℝ) = ((20000 / 24457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (252121897 / 1000000000) ≤ -Real.log (15543 / 20000) ∧
    -Real.log (15543 / 20000) ≤ (126060949 / 500000000) := by
  have h := checkLog_sound (w := (4457 / 35543)) (n := 12)
    (lo := (252121897 / 1000000000)) (hi := (126060949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15543) = 1/(15543 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-126060949 / 500000000) (-252121897 / 1000000000) (Real.log (15543 / 20000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (50362893 / 250000000) ≤ -Real.log (1000000 / 1223177) ∧
    -Real.log (1000000 / 1223177) ≤ (201451573 / 1000000000) := by
  have h := checkLog_sound (w := (223177 / 2223177)) (n := 12)
    (lo := (50362893 / 250000000)) (hi := (201451573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223177 / 1000000) = 1/(1000000 / 1223177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (50362893 / 250000000) (201451573 / 1000000000) (Real.log (1223177 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1223177 / 1000000) = -Real.log (1000000 / 1223177) := by
    rw [show ((1223177 / 1000000) : ℝ) = ((1000000 / 1223177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (252542753 / 1000000000) ≤ -Real.log (776823 / 1000000) ∧
    -Real.log (776823 / 1000000) ≤ (126271377 / 500000000) := by
  have h := checkLog_sound (w := (223177 / 1776823)) (n := 12)
    (lo := (252542753 / 1000000000)) (hi := (126271377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776823) = 1/(776823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-126271377 / 500000000) (-252542753 / 1000000000) (Real.log (776823 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (317161407 / 500000000) ≤ -Real.log (250000000000 / 471436177427) ∧
    -Real.log (250000000000 / 471436177427) ≤ (126864563 / 200000000) := by
  have h := checkLog_sound (w := (221436177427 / 721436177427)) (n := 12)
    (lo := (317161407 / 500000000)) (hi := (126864563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471436177427 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471436177427 / 250000000000) = 1/(250000000000 / 471436177427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (317161407 / 500000000) (126864563 / 200000000) (Real.log (471436177427 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (471436177427 / 250000000000) = -Real.log (250000000000 / 471436177427) := by
    rw [show ((471436177427 / 250000000000) : ℝ) = ((250000000000 / 471436177427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (317631783 / 500000000) ≤ -Real.log (500000000000 / 943759781473) ∧
    -Real.log (500000000000 / 943759781473) ≤ (635263567 / 1000000000) := by
  have h := checkLog_sound (w := (443759781473 / 1443759781473)) (n := 12)
    (lo := (317631783 / 500000000)) (hi := (635263567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((943759781473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(943759781473 / 500000000000) = 1/(500000000000 / 943759781473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (317631783 / 500000000) (635263567 / 1000000000) (Real.log (943759781473 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (943759781473 / 500000000000) = -Real.log (500000000000 / 943759781473) := by
    rw [show ((943759781473 / 500000000000) : ℝ) = ((500000000000 / 943759781473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (453306097 / 1000000000) ≤ -Real.log (500000000000 / 786752879109) ∧
    -Real.log (500000000000 / 786752879109) ≤ (226653049 / 500000000) := by
  have h := checkLog_sound (w := (286752879109 / 1286752879109)) (n := 12)
    (lo := (453306097 / 1000000000)) (hi := (226653049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786752879109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786752879109 / 500000000000) = 1/(500000000000 / 786752879109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (453306097 / 1000000000) (226653049 / 500000000) (Real.log (786752879109 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (786752879109 / 500000000000) = -Real.log (500000000000 / 786752879109) := by
    rw [show ((786752879109 / 500000000000) : ℝ) = ((500000000000 / 786752879109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (226997163 / 500000000) ≤ -Real.log (250000000000 / 393647265851) ∧
    -Real.log (250000000000 / 393647265851) ≤ (453994327 / 1000000000) := by
  have h := checkLog_sound (w := (143647265851 / 643647265851)) (n := 12)
    (lo := (226997163 / 500000000)) (hi := (453994327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393647265851 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393647265851 / 250000000000) = 1/(250000000000 / 393647265851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (226997163 / 500000000) (453994327 / 1000000000) (Real.log (393647265851 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (393647265851 / 250000000000) = -Real.log (250000000000 / 393647265851) := by
    rw [show ((393647265851 / 250000000000) : ℝ) = ((250000000000 / 393647265851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0421

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0422Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0422
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

theorem reflection_log_1_neg : (194936959 / 1000000000) ≤ -Real.log (2560 / 3111) ∧
    -Real.log (2560 / 3111) ≤ (304589 / 1562500) := by
  have h := checkLog_sound (w := (551 / 5671)) (n := 12)
    (lo := (194936959 / 1000000000)) (hi := (304589 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3111 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3111 / 2560) = 1/(2560 / 3111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (194936959 / 1000000000) (304589 / 1562500) (Real.log (3111 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3111 / 2560) = -Real.log (2560 / 3111) := by
    rw [show ((3111 / 2560) : ℝ) = ((2560 / 3111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (60592543 / 250000000) ≤ -Real.log (2009 / 2560) ∧
    -Real.log (2009 / 2560) ≤ (242370173 / 1000000000) := by
  have h := checkLog_sound (w := (551 / 4569)) (n := 12)
    (lo := (60592543 / 250000000)) (hi := (242370173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2009) = 1/(2009 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-242370173 / 1000000000) (-60592543 / 250000000) (Real.log (2009 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (3893917 / 20000000) ≤ -Real.log (10240 / 12441) ∧
    -Real.log (10240 / 12441) ≤ (194695851 / 1000000000) := by
  have h := checkLog_sound (w := (2201 / 22681)) (n := 12)
    (lo := (3893917 / 20000000)) (hi := (194695851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12441 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12441 / 10240) = 1/(10240 / 12441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (3893917 / 20000000) (194695851 / 1000000000) (Real.log (12441 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12441 / 10240) = -Real.log (10240 / 12441) := by
    rw [show ((12441 / 10240) : ℝ) = ((10240 / 12441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (120998461 / 500000000) ≤ -Real.log (8039 / 10240) ∧
    -Real.log (8039 / 10240) ≤ (241996923 / 1000000000) := by
  have h := checkLog_sound (w := (2201 / 18279)) (n := 12)
    (lo := (120998461 / 500000000)) (hi := (241996923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8039) = 1/(8039 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-241996923 / 1000000000) (-120998461 / 500000000) (Real.log (8039 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (358002187 / 1000000000) ≤ -Real.log (1280 / 1831) ∧
    -Real.log (1280 / 1831) ≤ (89500547 / 250000000) := by
  have h := checkLog_sound (w := (551 / 3111)) (n := 12)
    (lo := (358002187 / 1000000000)) (hi := (89500547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1831 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1831 / 1280) = 1/(1280 / 1831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (358002187 / 1000000000) (89500547 / 250000000) (Real.log (1831 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1831 / 1280) = -Real.log (1280 / 1831) := by
    rw [show ((1831 / 1280) : ℝ) = ((1280 / 1831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (70367703 / 125000000) ≤ -Real.log (729 / 1280) ∧
    -Real.log (729 / 1280) ≤ (4503533 / 8000000) := by
  have h := checkLog_sound (w := (551 / 2009)) (n := 12)
    (lo := (70367703 / 125000000)) (hi := (4503533 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 729) = 1/(729 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4503533 / 8000000) (-70367703 / 125000000) (Real.log (729 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (357592491 / 1000000000) ≤ -Real.log (5120 / 7321) ∧
    -Real.log (5120 / 7321) ≤ (89398123 / 250000000) := by
  have h := checkLog_sound (w := (2201 / 12441)) (n := 12)
    (lo := (357592491 / 1000000000)) (hi := (89398123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7321 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7321 / 5120) = 1/(5120 / 7321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (357592491 / 1000000000) (89398123 / 250000000) (Real.log (7321 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7321 / 5120) = -Real.log (5120 / 7321) := by
    rw [show ((7321 / 5120) : ℝ) = ((5120 / 7321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (561913347 / 1000000000) ≤ -Real.log (2919 / 5120) ∧
    -Real.log (2919 / 5120) ≤ (140478337 / 250000000) := by
  have h := checkLog_sound (w := (2201 / 8039)) (n := 12)
    (lo := (561913347 / 1000000000)) (hi := (140478337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2919) = 1/(2919 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-140478337 / 250000000) (-561913347 / 1000000000) (Real.log (2919 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (26736099 / 100000000) ≤ -Real.log (62500 / 81657) ∧
    -Real.log (62500 / 81657) ≤ (267360991 / 1000000000) := by
  have h := checkLog_sound (w := (19157 / 144157)) (n := 12)
    (lo := (26736099 / 100000000)) (hi := (267360991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81657 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81657 / 62500) = 1/(62500 / 81657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (26736099 / 100000000) (267360991 / 1000000000) (Real.log (81657 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (81657 / 62500) = -Real.log (62500 / 81657) := by
    rw [show ((81657 / 62500) : ℝ) = ((62500 / 81657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (183010671 / 500000000) ≤ -Real.log (43343 / 62500) ∧
    -Real.log (43343 / 62500) ≤ (366021343 / 1000000000) := by
  have h := checkLog_sound (w := (19157 / 105843)) (n := 12)
    (lo := (183010671 / 500000000)) (hi := (366021343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 43343) = 1/(43343 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-366021343 / 1000000000) (-183010671 / 500000000) (Real.log (43343 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (267687761 / 1000000000) ≤ -Real.log (1000000 / 1306939) ∧
    -Real.log (1000000 / 1306939) ≤ (133843881 / 500000000) := by
  have h := checkLog_sound (w := (306939 / 2306939)) (n := 12)
    (lo := (267687761 / 1000000000)) (hi := (133843881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306939 / 1000000) = 1/(1000000 / 1306939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (267687761 / 1000000000) (133843881 / 500000000) (Real.log (1306939 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1306939 / 1000000) = -Real.log (1000000 / 1306939) := by
    rw [show ((1306939 / 1000000) : ℝ) = ((1000000 / 1306939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18331863 / 50000000) ≤ -Real.log (693061 / 1000000) ∧
    -Real.log (693061 / 1000000) ≤ (366637261 / 1000000000) := by
  have h := checkLog_sound (w := (306939 / 1693061)) (n := 12)
    (lo := (18331863 / 50000000)) (hi := (366637261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693061) = 1/(693061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-366637261 / 1000000000) (-18331863 / 50000000) (Real.log (693061 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (25114799 / 125000000) ≤ -Real.log (40000 / 48901) ∧
    -Real.log (40000 / 48901) ≤ (200918393 / 1000000000) := by
  have h := checkLog_sound (w := (8901 / 88901)) (n := 12)
    (lo := (25114799 / 125000000)) (hi := (200918393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48901 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48901 / 40000) = 1/(40000 / 48901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (25114799 / 125000000) (200918393 / 1000000000) (Real.log (48901 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (48901 / 40000) = -Real.log (40000 / 48901) := by
    rw [show ((48901 / 40000) : ℝ) = ((40000 / 48901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (251703789 / 1000000000) ≤ -Real.log (31099 / 40000) ∧
    -Real.log (31099 / 40000) ≤ (25170379 / 100000000) := by
  have h := checkLog_sound (w := (8901 / 71099)) (n := 12)
    (lo := (251703789 / 1000000000)) (hi := (25170379 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31099) = 1/(31099 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-25170379 / 100000000) (-251703789 / 1000000000) (Real.log (31099 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (201185017 / 1000000000) ≤ -Real.log (1000000 / 1222851) ∧
    -Real.log (1000000 / 1222851) ≤ (100592509 / 500000000) := by
  have h := checkLog_sound (w := (222851 / 2222851)) (n := 12)
    (lo := (201185017 / 1000000000)) (hi := (100592509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222851 / 1000000) = 1/(1000000 / 1222851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (201185017 / 1000000000) (100592509 / 500000000) (Real.log (1222851 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1222851 / 1000000) = -Real.log (1000000 / 1222851) := by
    rw [show ((1222851 / 1000000) : ℝ) = ((1000000 / 1222851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (252123183 / 1000000000) ≤ -Real.log (777149 / 1000000) ∧
    -Real.log (777149 / 1000000) ≤ (15757699 / 62500000) := by
  have h := checkLog_sound (w := (222851 / 1777149)) (n := 12)
    (lo := (252123183 / 1000000000)) (hi := (15757699 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777149) = 1/(777149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-15757699 / 62500000) (-252123183 / 1000000000) (Real.log (777149 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (633382333 / 1000000000) ≤ -Real.log (500000000000 / 941986018503) ∧
    -Real.log (500000000000 / 941986018503) ≤ (316691167 / 500000000) := by
  have h := checkLog_sound (w := (441986018503 / 1441986018503)) (n := 12)
    (lo := (633382333 / 1000000000)) (hi := (316691167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941986018503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941986018503 / 500000000000) = 1/(500000000000 / 941986018503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (633382333 / 1000000000) (316691167 / 500000000) (Real.log (941986018503 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (941986018503 / 500000000000) = -Real.log (500000000000 / 941986018503) := by
    rw [show ((941986018503 / 500000000000) : ℝ) = ((500000000000 / 941986018503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (317162511 / 500000000) ≤ -Real.log (250000000000 / 471437218369) ∧
    -Real.log (250000000000 / 471437218369) ≤ (634325023 / 1000000000) := by
  have h := checkLog_sound (w := (221437218369 / 721437218369)) (n := 12)
    (lo := (317162511 / 500000000)) (hi := (634325023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471437218369 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471437218369 / 250000000000) = 1/(250000000000 / 471437218369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (317162511 / 500000000) (634325023 / 1000000000) (Real.log (471437218369 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (471437218369 / 250000000000) = -Real.log (250000000000 / 471437218369) := by
    rw [show ((471437218369 / 250000000000) : ℝ) = ((250000000000 / 471437218369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (452622181 / 1000000000) ≤ -Real.log (100000000000 / 157242998167) ∧
    -Real.log (100000000000 / 157242998167) ≤ (226311091 / 500000000) := by
  have h := checkLog_sound (w := (57242998167 / 257242998167)) (n := 12)
    (lo := (452622181 / 1000000000)) (hi := (226311091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157242998167 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157242998167 / 100000000000) = 1/(100000000000 / 157242998167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (452622181 / 1000000000) (226311091 / 500000000) (Real.log (157242998167 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (157242998167 / 100000000000) = -Real.log (100000000000 / 157242998167) := by
    rw [show ((157242998167 / 100000000000) : ℝ) = ((100000000000 / 157242998167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (453308201 / 1000000000) ≤ -Real.log (100000000000 / 157350906969) ∧
    -Real.log (100000000000 / 157350906969) ≤ (226654101 / 500000000) := by
  have h := checkLog_sound (w := (57350906969 / 257350906969)) (n := 12)
    (lo := (453308201 / 1000000000)) (hi := (226654101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157350906969 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157350906969 / 100000000000) = 1/(100000000000 / 157350906969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (453308201 / 1000000000) (226654101 / 500000000) (Real.log (157350906969 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (157350906969 / 100000000000) = -Real.log (100000000000 / 157350906969) := by
    rw [show ((157350906969 / 100000000000) : ℝ) = ((100000000000 / 157350906969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0422

end


