-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0295Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0295Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:12:06.104292+00:00
-- url     : https://prove2.me/theorems/3cd6811b-24cd-4acf-8cdc-54b6136be114
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0295Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0296Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0295Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0296Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0297Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0298Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0299Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0300Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0301Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0302Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0295Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0296Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0297Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0298Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0299Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0300Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0301Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0302Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0295Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0296Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0297Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0298Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0299Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0300Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0301Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0302Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0295Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0296Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0297Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0298Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0299Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0300Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0301Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0302Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0295Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0295
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

theorem reflection_log_1_neg : (225094771 / 1000000000) ≤ -Real.log (2048 / 2565) ∧
    -Real.log (2048 / 2565) ≤ (56273693 / 250000000) := by
  have h := checkLog_sound (w := (517 / 4613)) (n := 12)
    (lo := (225094771 / 1000000000)) (hi := (56273693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2565 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2565 / 2048) = 1/(2048 / 2565) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (225094771 / 1000000000) (56273693 / 250000000) (Real.log (2565 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2565 / 2048) = -Real.log (2048 / 2565) := by
    rw [show ((2565 / 2048) : ℝ) = ((2048 / 2565) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (29094259 / 100000000) ≤ -Real.log (1531 / 2048) ∧
    -Real.log (1531 / 2048) ≤ (290942591 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 3579)) (n := 12)
    (lo := (29094259 / 100000000)) (hi := (290942591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1531) = 1/(1531 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-290942591 / 1000000000) (-29094259 / 100000000) (Real.log (1531 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8994433 / 40000000) ≤ -Real.log (5120 / 6411) ∧
    -Real.log (5120 / 6411) ≤ (112430413 / 500000000) := by
  have h := checkLog_sound (w := (1291 / 11531)) (n := 12)
    (lo := (8994433 / 40000000)) (hi := (112430413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6411 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6411 / 5120) = 1/(5120 / 6411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8994433 / 40000000) (112430413 / 500000000) (Real.log (6411 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6411 / 5120) = -Real.log (5120 / 6411) := by
    rw [show ((6411 / 5120) : ℝ) = ((5120 / 6411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (145275383 / 500000000) ≤ -Real.log (3829 / 5120) ∧
    -Real.log (3829 / 5120) ≤ (290550767 / 1000000000) := by
  have h := checkLog_sound (w := (1291 / 8949)) (n := 12)
    (lo := (145275383 / 500000000)) (hi := (290550767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3829) = 1/(3829 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-290550767 / 1000000000) (-145275383 / 500000000) (Real.log (3829 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (408715029 / 1000000000) ≤ -Real.log (1024 / 1541) ∧
    -Real.log (1024 / 1541) ≤ (40871503 / 100000000) := by
  have h := checkLog_sound (w := (517 / 2565)) (n := 12)
    (lo := (408715029 / 1000000000)) (hi := (40871503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1541 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1541 / 1024) = 1/(1024 / 1541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (408715029 / 1000000000) (40871503 / 100000000) (Real.log (1541 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1541 / 1024) = -Real.log (1024 / 1541) := by
    rw [show ((1541 / 1024) : ℝ) = ((1024 / 1541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (702960801 / 1000000000) ≤ -Real.log (507 / 1024) ∧
    -Real.log (507 / 1024) ≤ (702960803 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 1019)) (n := 12)
    (lo := (9813621 / 1000000000)) (hi := (4906811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512 / 507) = 1/(507 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-702960803 / 1000000000) (-702960801 / 1000000000) (Real.log (507 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (102081399 / 250000000) ≤ -Real.log (2560 / 3851) ∧
    -Real.log (2560 / 3851) ≤ (408325597 / 1000000000) := by
  have h := checkLog_sound (w := (1291 / 6411)) (n := 12)
    (lo := (102081399 / 250000000)) (hi := (408325597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3851 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3851 / 2560) = 1/(2560 / 3851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (102081399 / 250000000) (408325597 / 1000000000) (Real.log (3851 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3851 / 2560) = -Real.log (2560 / 3851) := by
    rw [show ((3851 / 2560) : ℝ) = ((2560 / 3851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (701778069 / 1000000000) ≤ -Real.log (1269 / 2560) ∧
    -Real.log (1269 / 2560) ≤ (701778071 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 2549)) (n := 12)
    (lo := (8630889 / 1000000000)) (hi := (863089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1269) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1269) = 1/(1269 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-701778071 / 1000000000) (-701778069 / 1000000000) (Real.log (1269 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (77024253 / 250000000) ≤ -Real.log (1000000 / 1360833) ∧
    -Real.log (1000000 / 1360833) ≤ (308097013 / 1000000000) := by
  have h := checkLog_sound (w := (360833 / 2360833)) (n := 12)
    (lo := (77024253 / 250000000)) (hi := (308097013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1360833 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1360833 / 1000000) = 1/(1000000 / 1360833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (77024253 / 250000000) (308097013 / 1000000000) (Real.log (1360833 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1360833 / 1000000) = -Real.log (1000000 / 1360833) := by
    rw [show ((1360833 / 1000000) : ℝ) = ((1000000 / 1360833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (55948689 / 125000000) ≤ -Real.log (639167 / 1000000) ∧
    -Real.log (639167 / 1000000) ≤ (447589513 / 1000000000) := by
  have h := checkLog_sound (w := (360833 / 1639167)) (n := 12)
    (lo := (55948689 / 125000000)) (hi := (447589513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 639167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 639167) = 1/(639167 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-447589513 / 1000000000) (-55948689 / 125000000) (Real.log (639167 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (154207207 / 500000000) ≤ -Real.log (200000 / 272253) ∧
    -Real.log (200000 / 272253) ≤ (61682883 / 200000000) := by
  have h := checkLog_sound (w := (72253 / 472253)) (n := 12)
    (lo := (154207207 / 500000000)) (hi := (61682883 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272253 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272253 / 200000) = 1/(200000 / 272253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (154207207 / 500000000) (61682883 / 200000000) (Real.log (272253 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (272253 / 200000) = -Real.log (200000 / 272253) := by
    rw [show ((272253 / 200000) : ℝ) = ((200000 / 272253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (448265621 / 1000000000) ≤ -Real.log (127747 / 200000) ∧
    -Real.log (127747 / 200000) ≤ (224132811 / 500000000) := by
  have h := checkLog_sound (w := (72253 / 327747)) (n := 12)
    (lo := (448265621 / 1000000000)) (hi := (224132811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 127747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 127747) = 1/(127747 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-224132811 / 500000000) (-448265621 / 1000000000) (Real.log (127747 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (58704979 / 250000000) ≤ -Real.log (1000000 / 1264681) ∧
    -Real.log (1000000 / 1264681) ≤ (234819917 / 1000000000) := by
  have h := checkLog_sound (w := (264681 / 2264681)) (n := 12)
    (lo := (58704979 / 250000000)) (hi := (234819917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264681 / 1000000) = 1/(1000000 / 1264681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (58704979 / 250000000) (234819917 / 1000000000) (Real.log (1264681 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1264681 / 1000000) = -Real.log (1000000 / 1264681) := by
    rw [show ((1264681 / 1000000) : ℝ) = ((1000000 / 1264681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (15372543 / 50000000) ≤ -Real.log (735319 / 1000000) ∧
    -Real.log (735319 / 1000000) ≤ (307450861 / 1000000000) := by
  have h := checkLog_sound (w := (264681 / 1735319)) (n := 12)
    (lo := (15372543 / 50000000)) (hi := (307450861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735319) = 1/(735319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-307450861 / 1000000000) (-15372543 / 50000000) (Real.log (735319 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (117544361 / 500000000) ≤ -Real.log (1000000 / 1265021) ∧
    -Real.log (1000000 / 1265021) ≤ (235088723 / 1000000000) := by
  have h := checkLog_sound (w := (265021 / 2265021)) (n := 12)
    (lo := (117544361 / 500000000)) (hi := (235088723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1265021 / 1000000) = 1/(1000000 / 1265021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (117544361 / 500000000) (235088723 / 1000000000) (Real.log (1265021 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1265021 / 1000000) = -Real.log (1000000 / 1265021) := by
    rw [show ((1265021 / 1000000) : ℝ) = ((1000000 / 1265021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (307913351 / 1000000000) ≤ -Real.log (734979 / 1000000) ∧
    -Real.log (734979 / 1000000) ≤ (38489169 / 125000000) := by
  have h := checkLog_sound (w := (265021 / 1734979)) (n := 12)
    (lo := (307913351 / 1000000000)) (hi := (38489169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 734979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 734979) = 1/(734979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-38489169 / 125000000) (-307913351 / 1000000000) (Real.log (734979 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (188921631 / 250000000) ≤ -Real.log (62500000000 / 133067042729) ∧
    -Real.log (62500000000 / 133067042729) ≤ (377843263 / 500000000) := by
  have h := checkLog_sound (w := (8067042729 / 258067042729)) (n := 12)
    (lo := (3908709 / 62500000)) (hi := (12507869 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133067042729 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(133067042729 / 125000000000) = 1/(62500000000 / 133067042729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (188921631 / 250000000) (377843263 / 500000000) (Real.log (133067042729 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (133067042729 / 62500000000) = -Real.log (62500000000 / 133067042729) := by
    rw [show ((133067042729 / 62500000000) : ℝ) = ((62500000000 / 133067042729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (151336007 / 200000000) ≤ -Real.log (50000000000 / 106559449537) ∧
    -Real.log (50000000000 / 106559449537) ≤ (756680037 / 1000000000) := by
  have h := checkLog_sound (w := (6559449537 / 206559449537)) (n := 12)
    (lo := (12706571 / 200000000)) (hi := (7941607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106559449537 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(106559449537 / 100000000000) = 1/(50000000000 / 106559449537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (151336007 / 200000000) (756680037 / 1000000000) (Real.log (106559449537 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (106559449537 / 50000000000) = -Real.log (50000000000 / 106559449537) := by
    rw [show ((106559449537 / 50000000000) : ℝ) = ((50000000000 / 106559449537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (67783847 / 125000000) ≤ -Real.log (500000000000 / 859953979157) ∧
    -Real.log (500000000000 / 859953979157) ≤ (542270777 / 1000000000) := by
  have h := checkLog_sound (w := (359953979157 / 1359953979157)) (n := 12)
    (lo := (67783847 / 125000000)) (hi := (542270777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859953979157 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859953979157 / 500000000000) = 1/(500000000000 / 859953979157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (67783847 / 125000000) (542270777 / 1000000000) (Real.log (859953979157 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (859953979157 / 500000000000) = -Real.log (500000000000 / 859953979157) := by
    rw [show ((859953979157 / 500000000000) : ℝ) = ((500000000000 / 859953979157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (271501037 / 500000000) ≤ -Real.log (50000000000 / 86058309149) ∧
    -Real.log (50000000000 / 86058309149) ≤ (21720083 / 40000000) := by
  have h := checkLog_sound (w := (36058309149 / 136058309149)) (n := 12)
    (lo := (271501037 / 500000000)) (hi := (21720083 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86058309149 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86058309149 / 50000000000) = 1/(50000000000 / 86058309149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (271501037 / 500000000) (21720083 / 40000000) (Real.log (86058309149 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (86058309149 / 50000000000) = -Real.log (50000000000 / 86058309149) := by
    rw [show ((86058309149 / 50000000000) : ℝ) = ((50000000000 / 86058309149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0295

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0296Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0296
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

theorem reflection_log_1_neg : (8994433 / 40000000) ≤ -Real.log (5120 / 6411) ∧
    -Real.log (5120 / 6411) ≤ (112430413 / 500000000) := by
  have h := checkLog_sound (w := (1291 / 11531)) (n := 12)
    (lo := (8994433 / 40000000)) (hi := (112430413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6411 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6411 / 5120) = 1/(5120 / 6411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8994433 / 40000000) (112430413 / 500000000) (Real.log (6411 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6411 / 5120) = -Real.log (5120 / 6411) := by
    rw [show ((6411 / 5120) : ℝ) = ((5120 / 6411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (145275383 / 500000000) ≤ -Real.log (3829 / 5120) ∧
    -Real.log (3829 / 5120) ≤ (290550767 / 1000000000) := by
  have h := checkLog_sound (w := (1291 / 8949)) (n := 12)
    (lo := (145275383 / 500000000)) (hi := (290550767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3829) = 1/(3829 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-290550767 / 1000000000) (-145275383 / 500000000) (Real.log (3829 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8985073 / 40000000) ≤ -Real.log (10240 / 12819) ∧
    -Real.log (10240 / 12819) ≤ (112313413 / 500000000) := by
  have h := checkLog_sound (w := (2579 / 23059)) (n := 12)
    (lo := (8985073 / 40000000)) (hi := (112313413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12819 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12819 / 10240) = 1/(10240 / 12819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8985073 / 40000000) (112313413 / 500000000) (Real.log (12819 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12819 / 10240) = -Real.log (10240 / 12819) := by
    rw [show ((12819 / 10240) : ℝ) = ((10240 / 12819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (36269887 / 125000000) ≤ -Real.log (7661 / 10240) ∧
    -Real.log (7661 / 10240) ≤ (290159097 / 1000000000) := by
  have h := checkLog_sound (w := (2579 / 17901)) (n := 12)
    (lo := (36269887 / 125000000)) (hi := (290159097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7661) = 1/(7661 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-290159097 / 1000000000) (-36269887 / 125000000) (Real.log (7661 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (102081399 / 250000000) ≤ -Real.log (2560 / 3851) ∧
    -Real.log (2560 / 3851) ≤ (408325597 / 1000000000) := by
  have h := checkLog_sound (w := (1291 / 6411)) (n := 12)
    (lo := (102081399 / 250000000)) (hi := (408325597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3851 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3851 / 2560) = 1/(2560 / 3851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (102081399 / 250000000) (408325597 / 1000000000) (Real.log (3851 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3851 / 2560) = -Real.log (2560 / 3851) := by
    rw [show ((3851 / 2560) : ℝ) = ((2560 / 3851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (701778069 / 1000000000) ≤ -Real.log (1269 / 2560) ∧
    -Real.log (1269 / 2560) ≤ (701778071 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 2549)) (n := 12)
    (lo := (8630889 / 1000000000)) (hi := (863089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1269) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1269) = 1/(1269 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-701778071 / 1000000000) (-701778069 / 1000000000) (Real.log (1269 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (407936011 / 1000000000) ≤ -Real.log (5120 / 7699) ∧
    -Real.log (5120 / 7699) ≤ (101984003 / 250000000) := by
  have h := checkLog_sound (w := (2579 / 12819)) (n := 12)
    (lo := (407936011 / 1000000000)) (hi := (101984003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7699 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7699 / 5120) = 1/(5120 / 7699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (407936011 / 1000000000) (101984003 / 250000000) (Real.log (7699 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7699 / 5120) = -Real.log (5120 / 7699) := by
    rw [show ((7699 / 5120) : ℝ) = ((5120 / 7699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (350298367 / 500000000) ≤ -Real.log (2541 / 5120) ∧
    -Real.log (2541 / 5120) ≤ (1368353 / 1953125) := by
  have h := checkLog_sound (w := (19 / 5101)) (n := 12)
    (lo := (3724777 / 500000000)) (hi := (1489911 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2541) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2541) = 1/(2541 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1368353 / 1953125) (-350298367 / 500000000) (Real.log (2541 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (307780979 / 1000000000) ≤ -Real.log (1000000 / 1360403) ∧
    -Real.log (1000000 / 1360403) ≤ (15389049 / 50000000) := by
  have h := checkLog_sound (w := (360403 / 2360403)) (n := 12)
    (lo := (307780979 / 1000000000)) (hi := (15389049 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1360403 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1360403 / 1000000) = 1/(1000000 / 1360403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (307780979 / 1000000000) (15389049 / 50000000) (Real.log (1360403 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1360403 / 1000000) = -Real.log (1000000 / 1360403) := by
    rw [show ((1360403 / 1000000) : ℝ) = ((1000000 / 1360403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (111729247 / 250000000) ≤ -Real.log (639597 / 1000000) ∧
    -Real.log (639597 / 1000000) ≤ (446916989 / 1000000000) := by
  have h := checkLog_sound (w := (360403 / 1639597)) (n := 12)
    (lo := (111729247 / 250000000)) (hi := (446916989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 639597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 639597) = 1/(639597 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-446916989 / 1000000000) (-111729247 / 250000000) (Real.log (639597 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (308097747 / 1000000000) ≤ -Real.log (500000 / 680417) ∧
    -Real.log (500000 / 680417) ≤ (77024437 / 250000000) := by
  have h := checkLog_sound (w := (180417 / 1180417)) (n := 12)
    (lo := (308097747 / 1000000000)) (hi := (77024437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680417 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680417 / 500000) = 1/(500000 / 680417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (308097747 / 1000000000) (77024437 / 250000000) (Real.log (680417 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (680417 / 500000) = -Real.log (500000 / 680417) := by
    rw [show ((680417 / 500000) : ℝ) = ((500000 / 680417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (447591077 / 1000000000) ≤ -Real.log (319583 / 500000) ∧
    -Real.log (319583 / 500000) ≤ (223795539 / 500000000) := by
  have h := checkLog_sound (w := (180417 / 819583)) (n := 12)
    (lo := (447591077 / 1000000000)) (hi := (223795539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 319583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 319583) = 1/(319583 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-223795539 / 500000000) (-447591077 / 1000000000) (Real.log (319583 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (58637957 / 250000000) ≤ -Real.log (500000 / 632171) ∧
    -Real.log (500000 / 632171) ≤ (234551829 / 1000000000) := by
  have h := checkLog_sound (w := (132171 / 1132171)) (n := 12)
    (lo := (58637957 / 250000000)) (hi := (234551829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((632171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(632171 / 500000) = 1/(500000 / 632171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (58637957 / 250000000) (234551829 / 1000000000) (Real.log (632171 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (632171 / 500000) = -Real.log (500000 / 632171) := by
    rw [show ((632171 / 500000) : ℝ) = ((500000 / 632171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (153494971 / 500000000) ≤ -Real.log (367829 / 500000) ∧
    -Real.log (367829 / 500000) ≤ (306989943 / 1000000000) := by
  have h := checkLog_sound (w := (132171 / 867829)) (n := 12)
    (lo := (153494971 / 500000000)) (hi := (306989943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 367829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 367829) = 1/(367829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-306989943 / 1000000000) (-153494971 / 500000000) (Real.log (367829 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (234820707 / 1000000000) ≤ -Real.log (500000 / 632341) ∧
    -Real.log (500000 / 632341) ≤ (58705177 / 250000000) := by
  have h := checkLog_sound (w := (132341 / 1132341)) (n := 12)
    (lo := (234820707 / 1000000000)) (hi := (58705177 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((632341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(632341 / 500000) = 1/(500000 / 632341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (234820707 / 1000000000) (58705177 / 250000000) (Real.log (632341 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (632341 / 500000) = -Real.log (500000 / 632341) := by
    rw [show ((632341 / 500000) : ℝ) = ((500000 / 632341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (15372611 / 50000000) ≤ -Real.log (367659 / 500000) ∧
    -Real.log (367659 / 500000) ≤ (307452221 / 1000000000) := by
  have h := checkLog_sound (w := (132341 / 867659)) (n := 12)
    (lo := (15372611 / 50000000)) (hi := (307452221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 367659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 367659) = 1/(367659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-307452221 / 1000000000) (-15372611 / 50000000) (Real.log (367659 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (754697967 / 1000000000) ≤ -Real.log (10000000000 / 21269690133) ∧
    -Real.log (10000000000 / 21269690133) ≤ (754697969 / 1000000000) := by
  have h := checkLog_sound (w := (1269690133 / 41269690133)) (n := 12)
    (lo := (61550787 / 1000000000)) (hi := (15387697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21269690133 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(21269690133 / 20000000000) = 1/(10000000000 / 21269690133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (754697967 / 1000000000) (754697969 / 1000000000) (Real.log (21269690133 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (21269690133 / 10000000000) = -Real.log (10000000000 / 21269690133) := by
    rw [show ((21269690133 / 10000000000) : ℝ) = ((10000000000 / 21269690133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (755688823 / 1000000000) ≤ -Real.log (500000000000 / 1064538789611) ∧
    -Real.log (500000000000 / 1064538789611) ≤ (30227553 / 40000000) := by
  have h := checkLog_sound (w := (64538789611 / 2064538789611)) (n := 12)
    (lo := (62541643 / 1000000000)) (hi := (15635411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1064538789611 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1064538789611 / 1000000000000) = 1/(500000000000 / 1064538789611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (755688823 / 1000000000) (30227553 / 40000000) (Real.log (1064538789611 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1064538789611 / 500000000000) = -Real.log (500000000000 / 1064538789611) := by
    rw [show ((1064538789611 / 500000000000) : ℝ) = ((500000000000 / 1064538789611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (54154177 / 100000000) ≤ -Real.log (500000000000 / 859327296107) ∧
    -Real.log (500000000000 / 859327296107) ≤ (541541771 / 1000000000) := by
  have h := checkLog_sound (w := (359327296107 / 1359327296107)) (n := 12)
    (lo := (54154177 / 100000000)) (hi := (541541771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859327296107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859327296107 / 500000000000) = 1/(500000000000 / 859327296107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (54154177 / 100000000) (541541771 / 1000000000) (Real.log (859327296107 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (859327296107 / 500000000000) = -Real.log (500000000000 / 859327296107) := by
    rw [show ((859327296107 / 500000000000) : ℝ) = ((500000000000 / 859327296107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (542272927 / 1000000000) ≤ -Real.log (100000000000 / 171991165727) ∧
    -Real.log (100000000000 / 171991165727) ≤ (16946029 / 31250000) := by
  have h := checkLog_sound (w := (71991165727 / 271991165727)) (n := 12)
    (lo := (542272927 / 1000000000)) (hi := (16946029 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171991165727 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171991165727 / 100000000000) = 1/(100000000000 / 171991165727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (542272927 / 1000000000) (16946029 / 31250000) (Real.log (171991165727 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (171991165727 / 100000000000) = -Real.log (100000000000 / 171991165727) := by
    rw [show ((171991165727 / 100000000000) : ℝ) = ((100000000000 / 171991165727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0296

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0297Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0297
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

theorem reflection_log_1_neg : (8985073 / 40000000) ≤ -Real.log (10240 / 12819) ∧
    -Real.log (10240 / 12819) ≤ (112313413 / 500000000) := by
  have h := checkLog_sound (w := (2579 / 23059)) (n := 12)
    (lo := (8985073 / 40000000)) (hi := (112313413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12819 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12819 / 10240) = 1/(10240 / 12819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8985073 / 40000000) (112313413 / 500000000) (Real.log (12819 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12819 / 10240) = -Real.log (10240 / 12819) := by
    rw [show ((12819 / 10240) : ℝ) = ((10240 / 12819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (36269887 / 125000000) ≤ -Real.log (7661 / 10240) ∧
    -Real.log (7661 / 10240) ≤ (290159097 / 1000000000) := by
  have h := checkLog_sound (w := (2579 / 17901)) (n := 12)
    (lo := (36269887 / 125000000)) (hi := (290159097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7661) = 1/(7661 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-290159097 / 1000000000) (-36269887 / 125000000) (Real.log (7661 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (22439277 / 100000000) ≤ -Real.log (640 / 801) ∧
    -Real.log (640 / 801) ≤ (224392771 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1441)) (n := 12)
    (lo := (22439277 / 100000000)) (hi := (224392771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801 / 640) = 1/(640 / 801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (22439277 / 100000000) (224392771 / 1000000000) (Real.log (801 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (801 / 640) = -Real.log (640 / 801) := by
    rw [show ((801 / 640) : ℝ) = ((640 / 801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (144883789 / 500000000) ≤ -Real.log (479 / 640) ∧
    -Real.log (479 / 640) ≤ (289767579 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1119)) (n := 12)
    (lo := (144883789 / 500000000)) (hi := (289767579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 479) = 1/(479 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-289767579 / 1000000000) (-144883789 / 500000000) (Real.log (479 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (407936011 / 1000000000) ≤ -Real.log (5120 / 7699) ∧
    -Real.log (5120 / 7699) ≤ (101984003 / 250000000) := by
  have h := checkLog_sound (w := (2579 / 12819)) (n := 12)
    (lo := (407936011 / 1000000000)) (hi := (101984003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7699 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7699 / 5120) = 1/(5120 / 7699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (407936011 / 1000000000) (101984003 / 250000000) (Real.log (7699 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7699 / 5120) = -Real.log (5120 / 7699) := by
    rw [show ((7699 / 5120) : ℝ) = ((5120 / 7699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (350298367 / 500000000) ≤ -Real.log (2541 / 5120) ∧
    -Real.log (2541 / 5120) ≤ (1368353 / 1953125) := by
  have h := checkLog_sound (w := (19 / 5101)) (n := 12)
    (lo := (3724777 / 500000000)) (hi := (1489911 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2541) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2541) = 1/(2541 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1368353 / 1953125) (-350298367 / 500000000) (Real.log (2541 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (203773137 / 500000000) ≤ -Real.log (320 / 481) ∧
    -Real.log (320 / 481) ≤ (16301851 / 40000000) := by
  have h := checkLog_sound (w := (161 / 801)) (n := 12)
    (lo := (203773137 / 500000000)) (hi := (16301851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481 / 320) = 1/(320 / 481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (203773137 / 500000000) (16301851 / 40000000) (Real.log (481 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (481 / 320) = -Real.log (320 / 481) := by
    rw [show ((481 / 320) : ℝ) = ((320 / 481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (699416793 / 1000000000) ≤ -Real.log (159 / 320) ∧
    -Real.log (159 / 320) ≤ (139883359 / 200000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 159) = 1/(159 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-139883359 / 200000000) (-699416793 / 1000000000) (Real.log (159 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (153732423 / 500000000) ≤ -Real.log (1000000 / 1359973) ∧
    -Real.log (1000000 / 1359973) ≤ (307464847 / 1000000000) := by
  have h := checkLog_sound (w := (359973 / 2359973)) (n := 12)
    (lo := (153732423 / 500000000)) (hi := (307464847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359973 / 1000000) = 1/(1000000 / 1359973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (153732423 / 500000000) (307464847 / 1000000000) (Real.log (1359973 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1359973 / 1000000) = -Real.log (1000000 / 1359973) := by
    rw [show ((1359973 / 1000000) : ℝ) = ((1000000 / 1359973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (111561229 / 250000000) ≤ -Real.log (640027 / 1000000) ∧
    -Real.log (640027 / 1000000) ≤ (446244917 / 1000000000) := by
  have h := checkLog_sound (w := (359973 / 1640027)) (n := 12)
    (lo := (111561229 / 250000000)) (hi := (446244917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 640027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 640027) = 1/(640027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-446244917 / 1000000000) (-111561229 / 250000000) (Real.log (640027 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (153890857 / 500000000) ≤ -Real.log (250000 / 340101) ∧
    -Real.log (250000 / 340101) ≤ (61556343 / 200000000) := by
  have h := checkLog_sound (w := (90101 / 590101)) (n := 12)
    (lo := (153890857 / 500000000)) (hi := (61556343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340101 / 250000) = 1/(250000 / 340101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (153890857 / 500000000) (61556343 / 200000000) (Real.log (340101 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (340101 / 250000) = -Real.log (250000 / 340101) := by
    rw [show ((340101 / 250000) : ℝ) = ((250000 / 340101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (446918551 / 1000000000) ≤ -Real.log (159899 / 250000) ∧
    -Real.log (159899 / 250000) ≤ (55864819 / 125000000) := by
  have h := checkLog_sound (w := (90101 / 409899)) (n := 12)
    (lo := (446918551 / 1000000000)) (hi := (55864819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159899) = 1/(159899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-55864819 / 125000000) (-446918551 / 1000000000) (Real.log (159899 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (234283669 / 1000000000) ≤ -Real.log (1000000 / 1264003) ∧
    -Real.log (1000000 / 1264003) ≤ (23428367 / 100000000) := by
  have h := checkLog_sound (w := (264003 / 2264003)) (n := 12)
    (lo := (234283669 / 1000000000)) (hi := (23428367 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264003 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264003 / 1000000) = 1/(1000000 / 1264003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (234283669 / 1000000000) (23428367 / 100000000) (Real.log (1264003 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1264003 / 1000000) = -Real.log (1000000 / 1264003) := by
    rw [show ((1264003 / 1000000) : ℝ) = ((1000000 / 1264003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (76632309 / 250000000) ≤ -Real.log (735997 / 1000000) ∧
    -Real.log (735997 / 1000000) ≤ (306529237 / 1000000000) := by
  have h := checkLog_sound (w := (264003 / 1735997)) (n := 12)
    (lo := (76632309 / 250000000)) (hi := (306529237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735997) = 1/(735997 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-306529237 / 1000000000) (-76632309 / 250000000) (Real.log (735997 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (234552619 / 1000000000) ≤ -Real.log (1000000 / 1264343) ∧
    -Real.log (1000000 / 1264343) ≤ (11727631 / 50000000) := by
  have h := checkLog_sound (w := (264343 / 2264343)) (n := 12)
    (lo := (234552619 / 1000000000)) (hi := (11727631 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264343 / 1000000) = 1/(1000000 / 1264343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (234552619 / 1000000000) (11727631 / 50000000) (Real.log (1264343 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1264343 / 1000000) = -Real.log (1000000 / 1264343) := by
    rw [show ((1264343 / 1000000) : ℝ) = ((1000000 / 1264343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (306991301 / 1000000000) ≤ -Real.log (735657 / 1000000) ∧
    -Real.log (735657 / 1000000) ≤ (153495651 / 500000000) := by
  have h := checkLog_sound (w := (264343 / 1735657)) (n := 12)
    (lo := (306991301 / 1000000000)) (hi := (153495651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735657) = 1/(735657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-153495651 / 500000000) (-306991301 / 1000000000) (Real.log (735657 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (376854881 / 500000000) ≤ -Real.log (125000000000 / 265608521203) ∧
    -Real.log (125000000000 / 265608521203) ≤ (188427441 / 250000000) := by
  have h := checkLog_sound (w := (15608521203 / 515608521203)) (n := 12)
    (lo := (30281291 / 500000000)) (hi := (60562583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265608521203 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(265608521203 / 250000000000) = 1/(125000000000 / 265608521203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (376854881 / 500000000) (188427441 / 250000000) (Real.log (265608521203 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (265608521203 / 125000000000) = -Real.log (125000000000 / 265608521203) := by
    rw [show ((265608521203 / 125000000000) : ℝ) = ((125000000000 / 265608521203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (150940053 / 200000000) ≤ -Real.log (250000000000 / 531743475569) ∧
    -Real.log (250000000000 / 531743475569) ≤ (754700267 / 1000000000) := by
  have h := checkLog_sound (w := (31743475569 / 1031743475569)) (n := 12)
    (lo := (12310617 / 200000000)) (hi := (30776543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((531743475569 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(531743475569 / 500000000000) = 1/(250000000000 / 531743475569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (150940053 / 200000000) (754700267 / 1000000000) (Real.log (531743475569 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (531743475569 / 250000000000) = -Real.log (250000000000 / 531743475569) := by
    rw [show ((531743475569 / 250000000000) : ℝ) = ((250000000000 / 531743475569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (108162581 / 200000000) ≤ -Real.log (250000000000 / 429350595179) ∧
    -Real.log (250000000000 / 429350595179) ≤ (270406453 / 500000000) := by
  have h := checkLog_sound (w := (179350595179 / 679350595179)) (n := 12)
    (lo := (108162581 / 200000000)) (hi := (270406453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429350595179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429350595179 / 250000000000) = 1/(250000000000 / 429350595179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (108162581 / 200000000) (270406453 / 500000000) (Real.log (429350595179 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (429350595179 / 250000000000) = -Real.log (250000000000 / 429350595179) := by
    rw [show ((429350595179 / 250000000000) : ℝ) = ((250000000000 / 429350595179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (541543921 / 1000000000) ≤ -Real.log (500000000000 / 859329143881) ∧
    -Real.log (500000000000 / 859329143881) ≤ (270771961 / 500000000) := by
  have h := checkLog_sound (w := (359329143881 / 1359329143881)) (n := 12)
    (lo := (541543921 / 1000000000)) (hi := (270771961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859329143881 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859329143881 / 500000000000) = 1/(500000000000 / 859329143881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (541543921 / 1000000000) (270771961 / 500000000) (Real.log (859329143881 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (859329143881 / 500000000000) = -Real.log (500000000000 / 859329143881) := by
    rw [show ((859329143881 / 500000000000) : ℝ) = ((500000000000 / 859329143881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0297

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0298Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0298
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

theorem reflection_log_1_neg : (22439277 / 100000000) ≤ -Real.log (640 / 801) ∧
    -Real.log (640 / 801) ≤ (224392771 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1441)) (n := 12)
    (lo := (22439277 / 100000000)) (hi := (224392771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801 / 640) = 1/(640 / 801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (22439277 / 100000000) (224392771 / 1000000000) (Real.log (801 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (801 / 640) = -Real.log (640 / 801) := by
    rw [show ((801 / 640) : ℝ) = ((640 / 801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (144883789 / 500000000) ≤ -Real.log (479 / 640) ∧
    -Real.log (479 / 640) ≤ (289767579 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1119)) (n := 12)
    (lo := (144883789 / 500000000)) (hi := (289767579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 479) = 1/(479 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-289767579 / 1000000000) (-144883789 / 500000000) (Real.log (479 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11207933 / 50000000) ≤ -Real.log (10240 / 12813) ∧
    -Real.log (10240 / 12813) ≤ (224158661 / 1000000000) := by
  have h := checkLog_sound (w := (2573 / 23053)) (n := 12)
    (lo := (11207933 / 50000000)) (hi := (224158661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12813 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12813 / 10240) = 1/(10240 / 12813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11207933 / 50000000) (224158661 / 1000000000) (Real.log (12813 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12813 / 10240) = -Real.log (10240 / 12813) := by
    rw [show ((12813 / 10240) : ℝ) = ((10240 / 12813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57875243 / 200000000) ≤ -Real.log (7667 / 10240) ∧
    -Real.log (7667 / 10240) ≤ (36172027 / 125000000) := by
  have h := checkLog_sound (w := (2573 / 17907)) (n := 12)
    (lo := (57875243 / 200000000)) (hi := (36172027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7667) = 1/(7667 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-36172027 / 125000000) (-57875243 / 200000000) (Real.log (7667 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (203773137 / 500000000) ≤ -Real.log (320 / 481) ∧
    -Real.log (320 / 481) ≤ (16301851 / 40000000) := by
  have h := checkLog_sound (w := (161 / 801)) (n := 12)
    (lo := (203773137 / 500000000)) (hi := (16301851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481 / 320) = 1/(320 / 481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (203773137 / 500000000) (16301851 / 40000000) (Real.log (481 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (481 / 320) = -Real.log (320 / 481) := by
    rw [show ((481 / 320) : ℝ) = ((320 / 481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (699416793 / 1000000000) ≤ -Real.log (159 / 320) ∧
    -Real.log (159 / 320) ≤ (139883359 / 200000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 159) = 1/(159 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-139883359 / 200000000) (-699416793 / 1000000000) (Real.log (159 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (81431277 / 200000000) ≤ -Real.log (5120 / 7693) ∧
    -Real.log (5120 / 7693) ≤ (203578193 / 500000000) := by
  have h := checkLog_sound (w := (2573 / 12813)) (n := 12)
    (lo := (81431277 / 200000000)) (hi := (203578193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7693 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7693 / 5120) = 1/(5120 / 7693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (81431277 / 200000000) (203578193 / 500000000) (Real.log (7693 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7693 / 5120) = -Real.log (5120 / 7693) := by
    rw [show ((7693 / 5120) : ℝ) = ((5120 / 7693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (349119121 / 500000000) ≤ -Real.log (2547 / 5120) ∧
    -Real.log (2547 / 5120) ≤ (174559561 / 250000000) := by
  have h := checkLog_sound (w := (13 / 5107)) (n := 12)
    (lo := (2545531 / 500000000)) (hi := (5091063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2547) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2547) = 1/(2547 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-174559561 / 250000000) (-349119121 / 500000000) (Real.log (2547 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (153573939 / 500000000) ≤ -Real.log (500000 / 679771) ∧
    -Real.log (500000 / 679771) ≤ (307147879 / 1000000000) := by
  have h := checkLog_sound (w := (179771 / 1179771)) (n := 12)
    (lo := (153573939 / 500000000)) (hi := (307147879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679771 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679771 / 500000) = 1/(500000 / 679771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (153573939 / 500000000) (307147879 / 1000000000) (Real.log (679771 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (679771 / 500000) = -Real.log (500000 / 679771) := by
    rw [show ((679771 / 500000) : ℝ) = ((500000 / 679771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (445571733 / 1000000000) ≤ -Real.log (320229 / 500000) ∧
    -Real.log (320229 / 500000) ≤ (222785867 / 500000000) := by
  have h := checkLog_sound (w := (179771 / 820229)) (n := 12)
    (lo := (445571733 / 1000000000)) (hi := (222785867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 320229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 320229) = 1/(320229 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-222785867 / 500000000) (-445571733 / 1000000000) (Real.log (320229 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (307465581 / 1000000000) ≤ -Real.log (500000 / 679987) ∧
    -Real.log (500000 / 679987) ≤ (153732791 / 500000000) := by
  have h := checkLog_sound (w := (179987 / 1179987)) (n := 12)
    (lo := (307465581 / 1000000000)) (hi := (153732791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679987 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679987 / 500000) = 1/(500000 / 679987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (307465581 / 1000000000) (153732791 / 500000000) (Real.log (679987 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (679987 / 500000) = -Real.log (500000 / 679987) := by
    rw [show ((679987 / 500000) : ℝ) = ((500000 / 679987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (223123239 / 500000000) ≤ -Real.log (320013 / 500000) ∧
    -Real.log (320013 / 500000) ≤ (446246479 / 1000000000) := by
  have h := checkLog_sound (w := (179987 / 820013)) (n := 12)
    (lo := (223123239 / 500000000)) (hi := (446246479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 320013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 320013) = 1/(320013 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-446246479 / 1000000000) (-223123239 / 500000000) (Real.log (320013 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (234015437 / 1000000000) ≤ -Real.log (62500 / 78979) ∧
    -Real.log (62500 / 78979) ≤ (117007719 / 500000000) := by
  have h := checkLog_sound (w := (16479 / 141479)) (n := 12)
    (lo := (234015437 / 1000000000)) (hi := (117007719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78979 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78979 / 62500) = 1/(62500 / 78979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (234015437 / 1000000000) (117007719 / 500000000) (Real.log (78979 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (78979 / 62500) = -Real.log (62500 / 78979) := by
    rw [show ((78979 / 62500) : ℝ) = ((62500 / 78979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (153034371 / 500000000) ≤ -Real.log (46021 / 62500) ∧
    -Real.log (46021 / 62500) ≤ (306068743 / 1000000000) := by
  have h := checkLog_sound (w := (16479 / 108521)) (n := 12)
    (lo := (153034371 / 500000000)) (hi := (306068743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46021) = 1/(46021 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-306068743 / 1000000000) (-153034371 / 500000000) (Real.log (46021 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (11714223 / 50000000) ≤ -Real.log (250000 / 316001) ∧
    -Real.log (250000 / 316001) ≤ (234284461 / 1000000000) := by
  have h := checkLog_sound (w := (66001 / 566001)) (n := 12)
    (lo := (11714223 / 50000000)) (hi := (234284461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316001 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316001 / 250000) = 1/(250000 / 316001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (11714223 / 50000000) (234284461 / 1000000000) (Real.log (316001 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (316001 / 250000) = -Real.log (250000 / 316001) := by
    rw [show ((316001 / 250000) : ℝ) = ((250000 / 316001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (61306119 / 200000000) ≤ -Real.log (183999 / 250000) ∧
    -Real.log (183999 / 250000) ≤ (76632649 / 250000000) := by
  have h := checkLog_sound (w := (66001 / 433999)) (n := 12)
    (lo := (61306119 / 200000000)) (hi := (76632649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 183999) = 1/(183999 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-76632649 / 250000000) (-61306119 / 200000000) (Real.log (183999 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (752719611 / 1000000000) ≤ -Real.log (500000000000 / 1061382635551) ∧
    -Real.log (500000000000 / 1061382635551) ≤ (752719613 / 1000000000) := by
  have h := checkLog_sound (w := (61382635551 / 2061382635551)) (n := 12)
    (lo := (59572431 / 1000000000)) (hi := (3723277 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061382635551 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1061382635551 / 1000000000000) = 1/(500000000000 / 1061382635551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (752719611 / 1000000000) (752719613 / 1000000000) (Real.log (1061382635551 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1061382635551 / 500000000000) = -Real.log (500000000000 / 1061382635551) := by
    rw [show ((1061382635551 / 500000000000) : ℝ) = ((500000000000 / 1061382635551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (753712059 / 1000000000) ≤ -Real.log (500000000000 / 1062436526017) ∧
    -Real.log (500000000000 / 1062436526017) ≤ (753712061 / 1000000000) := by
  have h := checkLog_sound (w := (62436526017 / 2062436526017)) (n := 12)
    (lo := (60564879 / 1000000000)) (hi := (757061 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1062436526017 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1062436526017 / 1000000000000) = 1/(500000000000 / 1062436526017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (753712059 / 1000000000) (753712061 / 1000000000) (Real.log (1062436526017 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1062436526017 / 500000000000) = -Real.log (500000000000 / 1062436526017) := by
    rw [show ((1062436526017 / 500000000000) : ℝ) = ((500000000000 / 1062436526017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27004209 / 50000000) ≤ -Real.log (500000000000 / 858075661111) ∧
    -Real.log (500000000000 / 858075661111) ≤ (540084181 / 1000000000) := by
  have h := checkLog_sound (w := (358075661111 / 1358075661111)) (n := 12)
    (lo := (27004209 / 50000000)) (hi := (540084181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858075661111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858075661111 / 500000000000) = 1/(500000000000 / 858075661111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (27004209 / 50000000) (540084181 / 1000000000) (Real.log (858075661111 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (858075661111 / 500000000000) = -Real.log (500000000000 / 858075661111) := by
    rw [show ((858075661111 / 500000000000) : ℝ) = ((500000000000 / 858075661111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (108163011 / 200000000) ≤ -Real.log (50000000000 / 85870303643) ∧
    -Real.log (50000000000 / 85870303643) ≤ (33800941 / 62500000) := by
  have h := checkLog_sound (w := (35870303643 / 135870303643)) (n := 12)
    (lo := (108163011 / 200000000)) (hi := (33800941 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85870303643 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85870303643 / 50000000000) = 1/(50000000000 / 85870303643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (108163011 / 200000000) (33800941 / 62500000) (Real.log (85870303643 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (85870303643 / 50000000000) = -Real.log (50000000000 / 85870303643) := by
    rw [show ((85870303643 / 50000000000) : ℝ) = ((50000000000 / 85870303643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0298

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0299Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0299
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

theorem reflection_log_1_neg : (11207933 / 50000000) ≤ -Real.log (10240 / 12813) ∧
    -Real.log (10240 / 12813) ≤ (224158661 / 1000000000) := by
  have h := checkLog_sound (w := (2573 / 23053)) (n := 12)
    (lo := (11207933 / 50000000)) (hi := (224158661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12813 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12813 / 10240) = 1/(10240 / 12813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11207933 / 50000000) (224158661 / 1000000000) (Real.log (12813 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12813 / 10240) = -Real.log (10240 / 12813) := by
    rw [show ((12813 / 10240) : ℝ) = ((10240 / 12813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57875243 / 200000000) ≤ -Real.log (7667 / 10240) ∧
    -Real.log (7667 / 10240) ≤ (36172027 / 125000000) := by
  have h := checkLog_sound (w := (2573 / 17907)) (n := 12)
    (lo := (57875243 / 200000000)) (hi := (36172027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7667) = 1/(7667 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-36172027 / 125000000) (-57875243 / 200000000) (Real.log (7667 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13995281 / 62500000) ≤ -Real.log (1024 / 1281) ∧
    -Real.log (1024 / 1281) ≤ (223924497 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 2305)) (n := 12)
    (lo := (13995281 / 62500000)) (hi := (223924497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281 / 1024) = 1/(1024 / 1281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13995281 / 62500000) (223924497 / 1000000000) (Real.log (1281 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1281 / 1024) = -Real.log (1024 / 1281) := by
    rw [show ((1281 / 1024) : ℝ) = ((1024 / 1281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (72246251 / 250000000) ≤ -Real.log (767 / 1024) ∧
    -Real.log (767 / 1024) ≤ (57797001 / 200000000) := by
  have h := checkLog_sound (w := (257 / 1791)) (n := 12)
    (lo := (72246251 / 250000000)) (hi := (57797001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 767) = 1/(767 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-57797001 / 200000000) (-72246251 / 250000000) (Real.log (767 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (81431277 / 200000000) ≤ -Real.log (5120 / 7693) ∧
    -Real.log (5120 / 7693) ≤ (203578193 / 500000000) := by
  have h := checkLog_sound (w := (2573 / 12813)) (n := 12)
    (lo := (81431277 / 200000000)) (hi := (203578193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7693 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7693 / 5120) = 1/(5120 / 7693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (81431277 / 200000000) (203578193 / 500000000) (Real.log (7693 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7693 / 5120) = -Real.log (5120 / 7693) := by
    rw [show ((7693 / 5120) : ℝ) = ((5120 / 7693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (349119121 / 500000000) ≤ -Real.log (2547 / 5120) ∧
    -Real.log (2547 / 5120) ≤ (174559561 / 250000000) := by
  have h := checkLog_sound (w := (13 / 5107)) (n := 12)
    (lo := (2545531 / 500000000)) (hi := (5091063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2547) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2547) = 1/(2547 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-174559561 / 250000000) (-349119121 / 500000000) (Real.log (2547 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (50845793 / 125000000) ≤ -Real.log (512 / 769) ∧
    -Real.log (512 / 769) ≤ (81353269 / 200000000) := by
  have h := checkLog_sound (w := (257 / 1281)) (n := 12)
    (lo := (50845793 / 125000000)) (hi := (81353269 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769 / 512) = 1/(512 / 769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (50845793 / 125000000) (81353269 / 200000000) (Real.log (769 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (769 / 512) = -Real.log (512 / 769) := by
    rw [show ((769 / 512) : ℝ) = ((512 / 769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (697061079 / 1000000000) ≤ -Real.log (255 / 512) ∧
    -Real.log (255 / 512) ≤ (697061081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 511)) (n := 12)
    (lo := (3913899 / 1000000000)) (hi := (39139 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 255) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 255) = 1/(255 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-697061081 / 1000000000) (-697061079 / 1000000000) (Real.log (255 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (61366309 / 200000000) ≤ -Real.log (125000 / 169889) ∧
    -Real.log (125000 / 169889) ≤ (153415773 / 500000000) := by
  have h := checkLog_sound (w := (44889 / 294889)) (n := 12)
    (lo := (61366309 / 200000000)) (hi := (153415773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169889 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169889 / 125000) = 1/(125000 / 169889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (61366309 / 200000000) (153415773 / 500000000) (Real.log (169889 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (169889 / 125000) = -Real.log (125000 / 169889) := by
    rw [show ((169889 / 125000) : ℝ) = ((125000 / 169889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (111225141 / 250000000) ≤ -Real.log (80111 / 125000) ∧
    -Real.log (80111 / 125000) ≤ (88980113 / 200000000) := by
  have h := checkLog_sound (w := (44889 / 205111)) (n := 12)
    (lo := (111225141 / 250000000)) (hi := (88980113 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 80111) = 1/(80111 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-88980113 / 200000000) (-111225141 / 250000000) (Real.log (80111 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (307148613 / 1000000000) ≤ -Real.log (1000000 / 1359543) ∧
    -Real.log (1000000 / 1359543) ≤ (153574307 / 500000000) := by
  have h := checkLog_sound (w := (359543 / 2359543)) (n := 12)
    (lo := (307148613 / 1000000000)) (hi := (153574307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359543 / 1000000) = 1/(1000000 / 1359543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (307148613 / 1000000000) (153574307 / 500000000) (Real.log (1359543 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1359543 / 1000000) = -Real.log (1000000 / 1359543) := by
    rw [show ((1359543 / 1000000) : ℝ) = ((1000000 / 1359543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (222786647 / 500000000) ≤ -Real.log (640457 / 1000000) ∧
    -Real.log (640457 / 1000000) ≤ (89114659 / 200000000) := by
  have h := checkLog_sound (w := (359543 / 1640457)) (n := 12)
    (lo := (222786647 / 500000000)) (hi := (89114659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 640457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 640457) = 1/(640457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89114659 / 200000000) (-222786647 / 500000000) (Real.log (640457 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (116873567 / 500000000) ≤ -Real.log (40000 / 50533) ∧
    -Real.log (40000 / 50533) ≤ (46749427 / 200000000) := by
  have h := checkLog_sound (w := (10533 / 90533)) (n := 12)
    (lo := (116873567 / 500000000)) (hi := (46749427 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50533 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50533 / 40000) = 1/(40000 / 50533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (116873567 / 500000000) (46749427 / 200000000) (Real.log (50533 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (50533 / 40000) = -Real.log (40000 / 50533) := by
    rw [show ((50533 / 40000) : ℝ) = ((40000 / 50533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (15280423 / 50000000) ≤ -Real.log (29467 / 40000) ∧
    -Real.log (29467 / 40000) ≤ (305608461 / 1000000000) := by
  have h := checkLog_sound (w := (10533 / 69467)) (n := 12)
    (lo := (15280423 / 50000000)) (hi := (305608461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 29467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 29467) = 1/(29467 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-305608461 / 1000000000) (-15280423 / 50000000) (Real.log (29467 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (58504057 / 250000000) ≤ -Real.log (200000 / 252733) ∧
    -Real.log (200000 / 252733) ≤ (234016229 / 1000000000) := by
  have h := checkLog_sound (w := (52733 / 452733)) (n := 12)
    (lo := (58504057 / 250000000)) (hi := (234016229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252733 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(252733 / 200000) = 1/(200000 / 252733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (58504057 / 250000000) (234016229 / 1000000000) (Real.log (252733 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (252733 / 200000) = -Real.log (200000 / 252733) := by
    rw [show ((252733 / 200000) : ℝ) = ((200000 / 252733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3060701 / 10000000) ≤ -Real.log (147267 / 200000) ∧
    -Real.log (147267 / 200000) ≤ (306070101 / 1000000000) := by
  have h := checkLog_sound (w := (52733 / 347267)) (n := 12)
    (lo := (3060701 / 10000000)) (hi := (306070101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 147267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 147267) = 1/(147267 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-306070101 / 1000000000) (-3060701 / 10000000) (Real.log (147267 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (751732109 / 1000000000) ≤ -Real.log (250000000000 / 530167517569) ∧
    -Real.log (250000000000 / 530167517569) ≤ (751732111 / 1000000000) := by
  have h := checkLog_sound (w := (30167517569 / 1030167517569)) (n := 12)
    (lo := (58584929 / 1000000000)) (hi := (5858493 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((530167517569 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(530167517569 / 500000000000) = 1/(250000000000 / 530167517569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (751732109 / 1000000000) (751732111 / 1000000000) (Real.log (530167517569 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (530167517569 / 250000000000) = -Real.log (250000000000 / 530167517569) := by
    rw [show ((530167517569 / 250000000000) : ℝ) = ((250000000000 / 530167517569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (188180477 / 250000000) ≤ -Real.log (500000000000 / 1061385073471) ∧
    -Real.log (500000000000 / 1061385073471) ≤ (75272191 / 100000000) := by
  have h := checkLog_sound (w := (61385073471 / 2061385073471)) (n := 12)
    (lo := (7446841 / 125000000)) (hi := (59574729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061385073471 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1061385073471 / 1000000000000) = 1/(500000000000 / 1061385073471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (188180477 / 250000000) (75272191 / 100000000) (Real.log (1061385073471 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1061385073471 / 500000000000) = -Real.log (500000000000 / 1061385073471) := by
    rw [show ((1061385073471 / 500000000000) : ℝ) = ((500000000000 / 1061385073471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (107871119 / 200000000) ≤ -Real.log (500000000000 / 857450707571) ∧
    -Real.log (500000000000 / 857450707571) ≤ (134838899 / 250000000) := by
  have h := checkLog_sound (w := (357450707571 / 1357450707571)) (n := 12)
    (lo := (107871119 / 200000000)) (hi := (134838899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857450707571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857450707571 / 500000000000) = 1/(500000000000 / 857450707571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (107871119 / 200000000) (134838899 / 250000000) (Real.log (857450707571 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (857450707571 / 500000000000) = -Real.log (500000000000 / 857450707571) := by
    rw [show ((857450707571 / 500000000000) : ℝ) = ((500000000000 / 857450707571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (540086329 / 1000000000) ≤ -Real.log (125000000000 / 214519376371) ∧
    -Real.log (125000000000 / 214519376371) ≤ (54008633 / 100000000) := by
  have h := checkLog_sound (w := (89519376371 / 339519376371)) (n := 12)
    (lo := (540086329 / 1000000000)) (hi := (54008633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((214519376371 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(214519376371 / 125000000000) = 1/(125000000000 / 214519376371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (540086329 / 1000000000) (54008633 / 100000000) (Real.log (214519376371 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (214519376371 / 125000000000) = -Real.log (125000000000 / 214519376371) := by
    rw [show ((214519376371 / 125000000000) : ℝ) = ((125000000000 / 214519376371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0299

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0300Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0300
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

theorem reflection_log_1_neg : (13995281 / 62500000) ≤ -Real.log (1024 / 1281) ∧
    -Real.log (1024 / 1281) ≤ (223924497 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 2305)) (n := 12)
    (lo := (13995281 / 62500000)) (hi := (223924497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281 / 1024) = 1/(1024 / 1281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13995281 / 62500000) (223924497 / 1000000000) (Real.log (1281 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1281 / 1024) = -Real.log (1024 / 1281) := by
    rw [show ((1281 / 1024) : ℝ) = ((1024 / 1281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (72246251 / 250000000) ≤ -Real.log (767 / 1024) ∧
    -Real.log (767 / 1024) ≤ (57797001 / 200000000) := by
  have h := checkLog_sound (w := (257 / 1791)) (n := 12)
    (lo := (72246251 / 250000000)) (hi := (57797001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 767) = 1/(767 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-57797001 / 200000000) (-72246251 / 250000000) (Real.log (767 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (55922569 / 250000000) ≤ -Real.log (10240 / 12807) ∧
    -Real.log (10240 / 12807) ≤ (223690277 / 1000000000) := by
  have h := checkLog_sound (w := (2567 / 23047)) (n := 12)
    (lo := (55922569 / 250000000)) (hi := (223690277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12807 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12807 / 10240) = 1/(10240 / 12807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (55922569 / 250000000) (223690277 / 1000000000) (Real.log (12807 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12807 / 10240) = -Real.log (10240 / 12807) := by
    rw [show ((12807 / 10240) : ℝ) = ((10240 / 12807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (144296973 / 500000000) ≤ -Real.log (7673 / 10240) ∧
    -Real.log (7673 / 10240) ≤ (288593947 / 1000000000) := by
  have h := checkLog_sound (w := (2567 / 17913)) (n := 12)
    (lo := (144296973 / 500000000)) (hi := (288593947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7673) = 1/(7673 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-288593947 / 1000000000) (-144296973 / 500000000) (Real.log (7673 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (50845793 / 125000000) ≤ -Real.log (512 / 769) ∧
    -Real.log (512 / 769) ≤ (81353269 / 200000000) := by
  have h := checkLog_sound (w := (257 / 1281)) (n := 12)
    (lo := (50845793 / 125000000)) (hi := (81353269 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769 / 512) = 1/(512 / 769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (50845793 / 125000000) (81353269 / 200000000) (Real.log (769 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (769 / 512) = -Real.log (512 / 769) := by
    rw [show ((769 / 512) : ℝ) = ((512 / 769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (697061079 / 1000000000) ≤ -Real.log (255 / 512) ∧
    -Real.log (255 / 512) ≤ (697061081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 511)) (n := 12)
    (lo := (3913899 / 1000000000)) (hi := (39139 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 255) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 255) = 1/(255 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-697061081 / 1000000000) (-697061079 / 1000000000) (Real.log (255 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (406376151 / 1000000000) ≤ -Real.log (5120 / 7687) ∧
    -Real.log (5120 / 7687) ≤ (50797019 / 125000000) := by
  have h := checkLog_sound (w := (2567 / 12807)) (n := 12)
    (lo := (406376151 / 1000000000)) (hi := (50797019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7687 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7687 / 5120) = 1/(5120 / 7687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (406376151 / 1000000000) (50797019 / 125000000) (Real.log (7687 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7687 / 5120) = -Real.log (5120 / 7687) := by
    rw [show ((7687 / 5120) : ℝ) = ((5120 / 7687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6958853 / 10000000) ≤ -Real.log (2553 / 5120) ∧
    -Real.log (2553 / 5120) ≤ (347942651 / 500000000) := by
  have h := checkLog_sound (w := (7 / 5113)) (n := 12)
    (lo := (68453 / 25000000)) (hi := (2738121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2553) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2553) = 1/(2553 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-347942651 / 500000000) (-6958853 / 10000000) (Real.log (2553 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38314389 / 125000000) ≤ -Real.log (500000 / 679341) ∧
    -Real.log (500000 / 679341) ≤ (306515113 / 1000000000) := by
  have h := checkLog_sound (w := (179341 / 1179341)) (n := 12)
    (lo := (38314389 / 125000000)) (hi := (306515113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679341 / 500000) = 1/(500000 / 679341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38314389 / 125000000) (306515113 / 1000000000) (Real.log (679341 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (679341 / 500000) = -Real.log (500000 / 679341) := by
    rw [show ((679341 / 500000) : ℝ) = ((500000 / 679341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (88845969 / 200000000) ≤ -Real.log (320659 / 500000) ∧
    -Real.log (320659 / 500000) ≤ (222114923 / 500000000) := by
  have h := checkLog_sound (w := (179341 / 820659)) (n := 12)
    (lo := (88845969 / 200000000)) (hi := (222114923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 320659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 320659) = 1/(320659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-222114923 / 500000000) (-88845969 / 200000000) (Real.log (320659 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (306832281 / 1000000000) ≤ -Real.log (1000000 / 1359113) ∧
    -Real.log (1000000 / 1359113) ≤ (153416141 / 500000000) := by
  have h := checkLog_sound (w := (359113 / 2359113)) (n := 12)
    (lo := (306832281 / 1000000000)) (hi := (153416141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359113 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359113 / 1000000) = 1/(1000000 / 1359113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (306832281 / 1000000000) (153416141 / 500000000) (Real.log (1359113 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1359113 / 1000000) = -Real.log (1000000 / 1359113) := by
    rw [show ((1359113 / 1000000) : ℝ) = ((1000000 / 1359113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (111225531 / 250000000) ≤ -Real.log (640887 / 1000000) ∧
    -Real.log (640887 / 1000000) ≤ (3559217 / 8000000) := by
  have h := checkLog_sound (w := (359113 / 1640887)) (n := 12)
    (lo := (111225531 / 250000000)) (hi := (3559217 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 640887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 640887) = 1/(640887 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3559217 / 8000000) (-111225531 / 250000000) (Real.log (640887 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4669591 / 20000000) ≤ -Real.log (1000000 / 1262987) ∧
    -Real.log (1000000 / 1262987) ≤ (233479551 / 1000000000) := by
  have h := checkLog_sound (w := (262987 / 2262987)) (n := 12)
    (lo := (4669591 / 20000000)) (hi := (233479551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1262987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1262987 / 1000000) = 1/(1000000 / 1262987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4669591 / 20000000) (233479551 / 1000000000) (Real.log (1262987 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1262987 / 1000000) = -Real.log (1000000 / 1262987) := by
    rw [show ((1262987 / 1000000) : ℝ) = ((1000000 / 1262987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (305149747 / 1000000000) ≤ -Real.log (737013 / 1000000) ∧
    -Real.log (737013 / 1000000) ≤ (76287437 / 250000000) := by
  have h := checkLog_sound (w := (262987 / 1737013)) (n := 12)
    (lo := (305149747 / 1000000000)) (hi := (76287437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 737013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 737013) = 1/(737013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-76287437 / 250000000) (-305149747 / 1000000000) (Real.log (737013 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (9349917 / 40000000) ≤ -Real.log (500000 / 631663) ∧
    -Real.log (500000 / 631663) ≤ (116873963 / 500000000) := by
  have h := checkLog_sound (w := (131663 / 1131663)) (n := 12)
    (lo := (9349917 / 40000000)) (hi := (116873963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631663 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631663 / 500000) = 1/(500000 / 631663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (9349917 / 40000000) (116873963 / 500000000) (Real.log (631663 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (631663 / 500000) = -Real.log (500000 / 631663) := by
    rw [show ((631663 / 500000) : ℝ) = ((500000 / 631663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (152804909 / 500000000) ≤ -Real.log (368337 / 500000) ∧
    -Real.log (368337 / 500000) ≤ (305609819 / 1000000000) := by
  have h := checkLog_sound (w := (131663 / 868337)) (n := 12)
    (lo := (152804909 / 500000000)) (hi := (305609819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 368337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 368337) = 1/(368337 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-305609819 / 1000000000) (-152804909 / 500000000) (Real.log (368337 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (187686239 / 250000000) ≤ -Real.log (250000000000 / 529644419773) ∧
    -Real.log (250000000000 / 529644419773) ≤ (375372479 / 500000000) := by
  have h := checkLog_sound (w := (29644419773 / 1029644419773)) (n := 12)
    (lo := (3599861 / 62500000)) (hi := (57597777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529644419773 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(529644419773 / 500000000000) = 1/(250000000000 / 529644419773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (187686239 / 250000000) (375372479 / 500000000) (Real.log (529644419773 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (529644419773 / 250000000000) = -Real.log (250000000000 / 529644419773) := by
    rw [show ((529644419773 / 250000000000) : ℝ) = ((250000000000 / 529644419773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (150346881 / 200000000) ≤ -Real.log (125000000000 / 265084367447) ∧
    -Real.log (125000000000 / 265084367447) ≤ (751734407 / 1000000000) := by
  have h := checkLog_sound (w := (15084367447 / 515084367447)) (n := 12)
    (lo := (2343489 / 40000000)) (hi := (29293613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265084367447 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(265084367447 / 250000000000) = 1/(125000000000 / 265084367447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (150346881 / 200000000) (751734407 / 1000000000) (Real.log (265084367447 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (265084367447 / 125000000000) = -Real.log (125000000000 / 265084367447) := by
    rw [show ((265084367447 / 125000000000) : ℝ) = ((125000000000 / 265084367447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (269314649 / 500000000) ≤ -Real.log (500000000000 / 856828169923) ∧
    -Real.log (500000000000 / 856828169923) ≤ (538629299 / 1000000000) := by
  have h := checkLog_sound (w := (356828169923 / 1356828169923)) (n := 12)
    (lo := (269314649 / 500000000)) (hi := (538629299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((856828169923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(856828169923 / 500000000000) = 1/(500000000000 / 856828169923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (269314649 / 500000000) (538629299 / 1000000000) (Real.log (856828169923 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (856828169923 / 500000000000) = -Real.log (500000000000 / 856828169923) := by
    rw [show ((856828169923 / 500000000000) : ℝ) = ((500000000000 / 856828169923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (33709859 / 62500000) ≤ -Real.log (500000000000 / 857452550247) ∧
    -Real.log (500000000000 / 857452550247) ≤ (107871549 / 200000000) := by
  have h := checkLog_sound (w := (357452550247 / 1357452550247)) (n := 12)
    (lo := (33709859 / 62500000)) (hi := (107871549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857452550247 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857452550247 / 500000000000) = 1/(500000000000 / 857452550247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (33709859 / 62500000) (107871549 / 200000000) (Real.log (857452550247 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (857452550247 / 500000000000) = -Real.log (500000000000 / 857452550247) := by
    rw [show ((857452550247 / 500000000000) : ℝ) = ((500000000000 / 857452550247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0300

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0301Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0301
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

theorem reflection_log_1_neg : (55922569 / 250000000) ≤ -Real.log (10240 / 12807) ∧
    -Real.log (10240 / 12807) ≤ (223690277 / 1000000000) := by
  have h := checkLog_sound (w := (2567 / 23047)) (n := 12)
    (lo := (55922569 / 250000000)) (hi := (223690277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12807 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12807 / 10240) = 1/(10240 / 12807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (55922569 / 250000000) (223690277 / 1000000000) (Real.log (12807 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12807 / 10240) = -Real.log (10240 / 12807) := by
    rw [show ((12807 / 10240) : ℝ) = ((10240 / 12807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (144296973 / 500000000) ≤ -Real.log (7673 / 10240) ∧
    -Real.log (7673 / 10240) ≤ (288593947 / 1000000000) := by
  have h := checkLog_sound (w := (2567 / 17913)) (n := 12)
    (lo := (144296973 / 500000000)) (hi := (288593947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7673) = 1/(7673 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-288593947 / 1000000000) (-144296973 / 500000000) (Real.log (7673 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (111728001 / 500000000) ≤ -Real.log (2560 / 3201) ∧
    -Real.log (2560 / 3201) ≤ (223456003 / 1000000000) := by
  have h := checkLog_sound (w := (641 / 5761)) (n := 12)
    (lo := (111728001 / 500000000)) (hi := (223456003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3201 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3201 / 2560) = 1/(2560 / 3201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (111728001 / 500000000) (223456003 / 1000000000) (Real.log (3201 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3201 / 2560) = -Real.log (2560 / 3201) := by
    rw [show ((3201 / 2560) : ℝ) = ((2560 / 3201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (288203041 / 1000000000) ≤ -Real.log (1919 / 2560) ∧
    -Real.log (1919 / 2560) ≤ (144101521 / 500000000) := by
  have h := checkLog_sound (w := (641 / 4479)) (n := 12)
    (lo := (288203041 / 1000000000)) (hi := (144101521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1919) = 1/(1919 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-144101521 / 500000000) (-288203041 / 1000000000) (Real.log (1919 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (406376151 / 1000000000) ≤ -Real.log (5120 / 7687) ∧
    -Real.log (5120 / 7687) ≤ (50797019 / 125000000) := by
  have h := checkLog_sound (w := (2567 / 12807)) (n := 12)
    (lo := (406376151 / 1000000000)) (hi := (50797019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7687 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7687 / 5120) = 1/(5120 / 7687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (406376151 / 1000000000) (50797019 / 125000000) (Real.log (7687 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7687 / 5120) = -Real.log (5120 / 7687) := by
    rw [show ((7687 / 5120) : ℝ) = ((5120 / 7687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6958853 / 10000000) ≤ -Real.log (2553 / 5120) ∧
    -Real.log (2553 / 5120) ≤ (347942651 / 500000000) := by
  have h := checkLog_sound (w := (7 / 5113)) (n := 12)
    (lo := (68453 / 25000000)) (hi := (2738121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2553) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2553) = 1/(2553 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-347942651 / 500000000) (-6958853 / 10000000) (Real.log (2553 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (81197161 / 200000000) ≤ -Real.log (1280 / 1921) ∧
    -Real.log (1280 / 1921) ≤ (202992903 / 500000000) := by
  have h := checkLog_sound (w := (641 / 3201)) (n := 12)
    (lo := (81197161 / 200000000)) (hi := (202992903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1921 / 1280) = 1/(1280 / 1921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (81197161 / 200000000) (202992903 / 500000000) (Real.log (1921 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1921 / 1280) = -Real.log (1280 / 1921) := by
    rw [show ((1921 / 1280) : ℝ) = ((1280 / 1921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (694710901 / 1000000000) ≤ -Real.log (639 / 1280) ∧
    -Real.log (639 / 1280) ≤ (694710903 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 1279)) (n := 12)
    (lo := (1563721 / 1000000000)) (hi := (781861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 639) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 639) = 1/(639 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-694710903 / 1000000000) (-694710901 / 1000000000) (Real.log (639 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (153099289 / 500000000) ≤ -Real.log (250000 / 339563) ∧
    -Real.log (250000 / 339563) ≤ (306198579 / 1000000000) := by
  have h := checkLog_sound (w := (89563 / 589563)) (n := 12)
    (lo := (153099289 / 500000000)) (hi := (306198579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339563 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339563 / 250000) = 1/(250000 / 339563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (153099289 / 500000000) (306198579 / 1000000000) (Real.log (339563 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (339563 / 250000) = -Real.log (250000 / 339563) := by
    rw [show ((339563 / 250000) : ℝ) = ((250000 / 339563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (17742383 / 40000000) ≤ -Real.log (160437 / 250000) ∧
    -Real.log (160437 / 250000) ≤ (55444947 / 125000000) := by
  have h := checkLog_sound (w := (89563 / 410437)) (n := 12)
    (lo := (17742383 / 40000000)) (hi := (55444947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 160437) = 1/(160437 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55444947 / 125000000) (-17742383 / 40000000) (Real.log (160437 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (38314481 / 125000000) ≤ -Real.log (1000000 / 1358683) ∧
    -Real.log (1000000 / 1358683) ≤ (306515849 / 1000000000) := by
  have h := checkLog_sound (w := (358683 / 2358683)) (n := 12)
    (lo := (38314481 / 125000000)) (hi := (306515849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1358683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1358683 / 1000000) = 1/(1000000 / 1358683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (38314481 / 125000000) (306515849 / 1000000000) (Real.log (1358683 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1358683 / 1000000) = -Real.log (1000000 / 1358683) := by
    rw [show ((1358683 / 1000000) : ℝ) = ((1000000 / 1358683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (111057851 / 250000000) ≤ -Real.log (641317 / 1000000) ∧
    -Real.log (641317 / 1000000) ≤ (88846281 / 200000000) := by
  have h := checkLog_sound (w := (358683 / 1641317)) (n := 12)
    (lo := (111057851 / 250000000)) (hi := (88846281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 641317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 641317) = 1/(641317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-88846281 / 200000000) (-111057851 / 250000000) (Real.log (641317 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (233211103 / 1000000000) ≤ -Real.log (125000 / 157831) ∧
    -Real.log (125000 / 157831) ≤ (7287847 / 31250000) := by
  have h := checkLog_sound (w := (32831 / 282831)) (n := 12)
    (lo := (233211103 / 1000000000)) (hi := (7287847 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157831 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157831 / 125000) = 1/(125000 / 157831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (233211103 / 1000000000) (7287847 / 31250000) (Real.log (157831 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (157831 / 125000) = -Real.log (125000 / 157831) := by
    rw [show ((157831 / 125000) : ℝ) = ((125000 / 157831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (9521559 / 31250000) ≤ -Real.log (92169 / 125000) ∧
    -Real.log (92169 / 125000) ≤ (304689889 / 1000000000) := by
  have h := checkLog_sound (w := (32831 / 217169)) (n := 12)
    (lo := (9521559 / 31250000)) (hi := (304689889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 92169) = 1/(92169 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-304689889 / 1000000000) (-9521559 / 31250000) (Real.log (92169 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (116740171 / 500000000) ≤ -Real.log (250000 / 315747) ∧
    -Real.log (250000 / 315747) ≤ (233480343 / 1000000000) := by
  have h := checkLog_sound (w := (65747 / 565747)) (n := 12)
    (lo := (116740171 / 500000000)) (hi := (233480343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315747 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315747 / 250000) = 1/(250000 / 315747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (116740171 / 500000000) (233480343 / 1000000000) (Real.log (315747 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (315747 / 250000) = -Real.log (250000 / 315747) := by
    rw [show ((315747 / 250000) : ℝ) = ((250000 / 315747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2383993 / 7812500) ≤ -Real.log (184253 / 250000) ∧
    -Real.log (184253 / 250000) ≤ (61030221 / 200000000) := by
  have h := checkLog_sound (w := (65747 / 434253)) (n := 12)
    (lo := (2383993 / 7812500)) (hi := (61030221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 184253) = 1/(184253 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-61030221 / 200000000) (-2383993 / 7812500) (Real.log (184253 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (374879077 / 500000000) ≤ -Real.log (500000000000 / 1058244045949) ∧
    -Real.log (500000000000 / 1058244045949) ≤ (187439539 / 250000000) := by
  have h := checkLog_sound (w := (58244045949 / 2058244045949)) (n := 12)
    (lo := (28305487 / 500000000)) (hi := (2264439 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1058244045949 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1058244045949 / 1000000000000) = 1/(500000000000 / 1058244045949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (374879077 / 500000000) (187439539 / 250000000) (Real.log (1058244045949 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1058244045949 / 500000000000) = -Real.log (500000000000 / 1058244045949) := by
    rw [show ((1058244045949 / 500000000000) : ℝ) = ((500000000000 / 1058244045949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (187686813 / 250000000) ≤ -Real.log (125000000000 / 264822817733) ∧
    -Real.log (125000000000 / 264822817733) ≤ (375373627 / 500000000) := by
  have h := checkLog_sound (w := (14822817733 / 514822817733)) (n := 12)
    (lo := (7200009 / 125000000)) (hi := (57600073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264822817733 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(264822817733 / 250000000000) = 1/(125000000000 / 264822817733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (187686813 / 250000000) (375373627 / 500000000) (Real.log (264822817733 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (264822817733 / 125000000000) = -Real.log (125000000000 / 264822817733) := by
    rw [show ((264822817733 / 125000000000) : ℝ) = ((125000000000 / 264822817733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (537900991 / 1000000000) ≤ -Real.log (500000000000 / 856204363723) ∧
    -Real.log (500000000000 / 856204363723) ≤ (8404703 / 15625000) := by
  have h := checkLog_sound (w := (356204363723 / 1356204363723)) (n := 12)
    (lo := (537900991 / 1000000000)) (hi := (8404703 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((856204363723 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(856204363723 / 500000000000) = 1/(500000000000 / 856204363723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (537900991 / 1000000000) (8404703 / 15625000) (Real.log (856204363723 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (856204363723 / 500000000000) = -Real.log (500000000000 / 856204363723) := by
    rw [show ((856204363723 / 500000000000) : ℝ) = ((500000000000 / 856204363723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (269315723 / 500000000) ≤ -Real.log (500000000000 / 856830010909) ∧
    -Real.log (500000000000 / 856830010909) ≤ (538631447 / 1000000000) := by
  have h := checkLog_sound (w := (356830010909 / 1356830010909)) (n := 12)
    (lo := (269315723 / 500000000)) (hi := (538631447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((856830010909 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(856830010909 / 500000000000) = 1/(500000000000 / 856830010909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (269315723 / 500000000) (538631447 / 1000000000) (Real.log (856830010909 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (856830010909 / 500000000000) = -Real.log (500000000000 / 856830010909) := by
    rw [show ((856830010909 / 500000000000) : ℝ) = ((500000000000 / 856830010909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0301

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0302Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0302
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

theorem reflection_log_1_neg : (111728001 / 500000000) ≤ -Real.log (2560 / 3201) ∧
    -Real.log (2560 / 3201) ≤ (223456003 / 1000000000) := by
  have h := checkLog_sound (w := (641 / 5761)) (n := 12)
    (lo := (111728001 / 500000000)) (hi := (223456003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3201 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3201 / 2560) = 1/(2560 / 3201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (111728001 / 500000000) (223456003 / 1000000000) (Real.log (3201 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3201 / 2560) = -Real.log (2560 / 3201) := by
    rw [show ((3201 / 2560) : ℝ) = ((2560 / 3201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (288203041 / 1000000000) ≤ -Real.log (1919 / 2560) ∧
    -Real.log (1919 / 2560) ≤ (144101521 / 500000000) := by
  have h := checkLog_sound (w := (641 / 4479)) (n := 12)
    (lo := (288203041 / 1000000000)) (hi := (144101521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1919) = 1/(1919 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-144101521 / 500000000) (-288203041 / 1000000000) (Real.log (1919 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (223221673 / 1000000000) ≤ -Real.log (10240 / 12801) ∧
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


theorem reflection_log_3 : Bounds (223221673 / 1000000000) (111610837 / 500000000) (Real.log (12801 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12801 / 10240) = -Real.log (10240 / 12801) := by
    rw [show ((12801 / 10240) : ℝ) = ((10240 / 12801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (287812289 / 1000000000) ≤ -Real.log (7679 / 10240) ∧
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


theorem reflection_log_4 : Bounds (-28781229 / 100000000) (-287812289 / 1000000000) (Real.log (7679 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (81197161 / 200000000) ≤ -Real.log (1280 / 1921) ∧
    -Real.log (1280 / 1921) ≤ (202992903 / 500000000) := by
  have h := checkLog_sound (w := (641 / 3201)) (n := 12)
    (lo := (81197161 / 200000000)) (hi := (202992903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1921 / 1280) = 1/(1280 / 1921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (81197161 / 200000000) (202992903 / 500000000) (Real.log (1921 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1921 / 1280) = -Real.log (1280 / 1921) := by
    rw [show ((1921 / 1280) : ℝ) = ((1280 / 1921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (694710901 / 1000000000) ≤ -Real.log (639 / 1280) ∧
    -Real.log (639 / 1280) ≤ (694710903 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 1279)) (n := 12)
    (lo := (1563721 / 1000000000)) (hi := (781861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 639) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 639) = 1/(639 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-694710903 / 1000000000) (-694710901 / 1000000000) (Real.log (639 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (405595307 / 1000000000) ≤ -Real.log (5120 / 7681) ∧
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


theorem reflection_log_7 : Bounds (405595307 / 1000000000) (101398827 / 250000000) (Real.log (7681 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7681 / 5120) = -Real.log (5120 / 7681) := by
    rw [show ((7681 / 5120) : ℝ) = ((5120 / 7681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (693537881 / 1000000000) ≤ -Real.log (2559 / 5120) ∧
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


theorem reflection_log_8 : Bounds (-693537883 / 1000000000) (-693537881 / 1000000000) (Real.log (2559 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (61176389 / 200000000) ≤ -Real.log (500000 / 678911) ∧
    -Real.log (500000 / 678911) ≤ (152940973 / 500000000) := by
  have h := checkLog_sound (w := (178911 / 1178911)) (n := 12)
    (lo := (61176389 / 200000000)) (hi := (152940973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678911 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678911 / 500000) = 1/(500000 / 678911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (61176389 / 200000000) (152940973 / 500000000) (Real.log (678911 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (678911 / 500000) = -Real.log (500000 / 678911) := by
    rw [show ((678911 / 500000) : ℝ) = ((500000 / 678911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (88577951 / 200000000) ≤ -Real.log (321089 / 500000) ∧
    -Real.log (321089 / 500000) ≤ (110722439 / 250000000) := by
  have h := checkLog_sound (w := (178911 / 821089)) (n := 12)
    (lo := (88577951 / 200000000)) (hi := (110722439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 321089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 321089) = 1/(321089 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-110722439 / 250000000) (-88577951 / 200000000) (Real.log (321089 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (61239863 / 200000000) ≤ -Real.log (1000000 / 1358253) ∧
    -Real.log (1000000 / 1358253) ≤ (76549829 / 250000000) := by
  have h := checkLog_sound (w := (358253 / 2358253)) (n := 12)
    (lo := (61239863 / 200000000)) (hi := (76549829 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1358253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1358253 / 1000000) = 1/(1000000 / 1358253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (61239863 / 200000000) (76549829 / 250000000) (Real.log (1358253 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1358253 / 1000000) = -Real.log (1000000 / 1358253) := by
    rw [show ((1358253 / 1000000) : ℝ) = ((1000000 / 1358253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (443561133 / 1000000000) ≤ -Real.log (641747 / 1000000) ∧
    -Real.log (641747 / 1000000) ≤ (221780567 / 500000000) := by
  have h := checkLog_sound (w := (358253 / 1641747)) (n := 12)
    (lo := (443561133 / 1000000000)) (hi := (221780567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 641747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 641747) = 1/(641747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-221780567 / 500000000) (-443561133 / 1000000000) (Real.log (641747 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1863547 / 8000000) ≤ -Real.log (100000 / 126231) ∧
    -Real.log (100000 / 126231) ≤ (14558961 / 62500000) := by
  have h := checkLog_sound (w := (26231 / 226231)) (n := 12)
    (lo := (1863547 / 8000000)) (hi := (14558961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126231 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126231 / 100000) = 1/(100000 / 126231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1863547 / 8000000) (14558961 / 62500000) (Real.log (126231 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (126231 / 100000) = -Real.log (100000 / 126231) := by
    rw [show ((126231 / 100000) : ℝ) = ((100000 / 126231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (76057899 / 250000000) ≤ -Real.log (73769 / 100000) ∧
    -Real.log (73769 / 100000) ≤ (304231597 / 1000000000) := by
  have h := checkLog_sound (w := (26231 / 173769)) (n := 12)
    (lo := (76057899 / 250000000)) (hi := (304231597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 73769) = 1/(73769 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-304231597 / 1000000000) (-76057899 / 250000000) (Real.log (73769 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (46642379 / 200000000) ≤ -Real.log (1000000 / 1262649) ∧
    -Real.log (1000000 / 1262649) ≤ (29151487 / 125000000) := by
  have h := checkLog_sound (w := (262649 / 2262649)) (n := 12)
    (lo := (46642379 / 200000000)) (hi := (29151487 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1262649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1262649 / 1000000) = 1/(1000000 / 1262649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (46642379 / 200000000) (29151487 / 125000000) (Real.log (1262649 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1262649 / 1000000) = -Real.log (1000000 / 1262649) := by
    rw [show ((1262649 / 1000000) : ℝ) = ((1000000 / 1262649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (60938249 / 200000000) ≤ -Real.log (737351 / 1000000) ∧
    -Real.log (737351 / 1000000) ≤ (152345623 / 500000000) := by
  have h := checkLog_sound (w := (262649 / 1737351)) (n := 12)
    (lo := (60938249 / 200000000)) (hi := (152345623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 737351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 737351) = 1/(737351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-152345623 / 500000000) (-60938249 / 200000000) (Real.log (737351 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (7487717 / 10000000) ≤ -Real.log (125000000000 / 264300162883) ∧
    -Real.log (125000000000 / 264300162883) ≤ (374385851 / 500000000) := by
  have h := checkLog_sound (w := (14300162883 / 514300162883)) (n := 12)
    (lo := (1390613 / 25000000)) (hi := (55624521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264300162883 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(264300162883 / 250000000000) = 1/(125000000000 / 264300162883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (7487717 / 10000000) (374385851 / 500000000) (Real.log (264300162883 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (264300162883 / 125000000000) = -Real.log (125000000000 / 264300162883) := by
    rw [show ((264300162883 / 125000000000) : ℝ) = ((125000000000 / 264300162883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (11715007 / 15625000) ≤ -Real.log (250000000000 / 529123237039) ∧
    -Real.log (250000000000 / 529123237039) ≤ (14995209 / 20000000) := by
  have h := checkLog_sound (w := (29123237039 / 1029123237039)) (n := 12)
    (lo := (14153317 / 250000000)) (hi := (56613269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529123237039 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(529123237039 / 500000000000) = 1/(250000000000 / 529123237039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (11715007 / 15625000) (14995209 / 20000000) (Real.log (529123237039 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (529123237039 / 250000000000) = -Real.log (250000000000 / 529123237039) := by
    rw [show ((529123237039 / 250000000000) : ℝ) = ((250000000000 / 529123237039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (134293743 / 250000000) ≤ -Real.log (100000000000 / 171116593691) ∧
    -Real.log (100000000000 / 171116593691) ≤ (537174973 / 1000000000) := by
  have h := checkLog_sound (w := (71116593691 / 271116593691)) (n := 12)
    (lo := (134293743 / 250000000)) (hi := (537174973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171116593691 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171116593691 / 100000000000) = 1/(100000000000 / 171116593691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (134293743 / 250000000) (537174973 / 1000000000) (Real.log (171116593691 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (171116593691 / 100000000000) = -Real.log (100000000000 / 171116593691) := by
    rw [show ((171116593691 / 100000000000) : ℝ) = ((100000000000 / 171116593691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (26895157 / 50000000) ≤ -Real.log (62500000000 / 107025775377) ∧
    -Real.log (62500000000 / 107025775377) ≤ (537903141 / 1000000000) := by
  have h := checkLog_sound (w := (44525775377 / 169525775377)) (n := 12)
    (lo := (26895157 / 50000000)) (hi := (537903141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107025775377 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107025775377 / 62500000000) = 1/(62500000000 / 107025775377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (26895157 / 50000000) (537903141 / 1000000000) (Real.log (107025775377 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (107025775377 / 62500000000) = -Real.log (62500000000 / 107025775377) := by
    rw [show ((107025775377 / 62500000000) : ℝ) = ((62500000000 / 107025775377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0302

end


