-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0409Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0409Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:07:04.098149+00:00
-- url     : https://prove2.me/theorems/d7090868-150d-4f54-b1e2-b0565c8865a1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0409Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0410Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0409Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0410Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0411Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0412Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0413Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0414Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0415Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0416Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0409Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0410Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0411Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0412Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0413Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0414Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0415Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0416Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0409Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0410Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0411Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0412Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0413Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0414Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0415Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0416Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0409Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0410Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0411Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0412Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0413Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0414Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0415Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0416Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0409Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0409
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

theorem reflection_log_1_neg : (198066099 / 1000000000) ≤ -Real.log (10240 / 12483) ∧
    -Real.log (10240 / 12483) ≤ (1980661 / 10000000) := by
  have h := checkLog_sound (w := (2243 / 22723)) (n := 12)
    (lo := (198066099 / 1000000000)) (hi := (1980661 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12483 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12483 / 10240) = 1/(10240 / 12483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198066099 / 1000000000) (1980661 / 10000000) (Real.log (12483 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12483 / 10240) = -Real.log (10240 / 12483) := by
    rw [show ((12483 / 10240) : ℝ) = ((10240 / 12483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (61808787 / 250000000) ≤ -Real.log (7997 / 10240) ∧
    -Real.log (7997 / 10240) ≤ (247235149 / 1000000000) := by
  have h := checkLog_sound (w := (2243 / 18237)) (n := 12)
    (lo := (61808787 / 250000000)) (hi := (247235149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7997) = 1/(7997 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-247235149 / 1000000000) (-61808787 / 250000000) (Real.log (7997 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (197825743 / 1000000000) ≤ -Real.log (32 / 39) ∧
    -Real.log (32 / 39) ≤ (12364109 / 62500000) := by
  have h := checkLog_sound (w := (7 / 71)) (n := 12)
    (lo := (197825743 / 1000000000)) (hi := (12364109 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39 / 32) = 1/(32 / 39) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (197825743 / 1000000000) (12364109 / 62500000) (Real.log (39 / 32)) := by
  have h := reflection_log_3_neg
  have he : Real.log (39 / 32) = -Real.log (32 / 39) := by
    rw [show ((39 / 32) : ℝ) = ((32 / 39) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (246860077 / 1000000000) ≤ -Real.log (25 / 32) ∧
    -Real.log (25 / 32) ≤ (123430039 / 500000000) := by
  have h := checkLog_sound (w := (7 / 57)) (n := 12)
    (lo := (246860077 / 1000000000)) (hi := (123430039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 25) = 1/(25 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-123430039 / 500000000) (-246860077 / 1000000000) (Real.log (25 / 32)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (363313019 / 1000000000) ≤ -Real.log (5120 / 7363) ∧
    -Real.log (5120 / 7363) ≤ (18165651 / 50000000) := by
  have h := checkLog_sound (w := (2243 / 12483)) (n := 12)
    (lo := (363313019 / 1000000000)) (hi := (18165651 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7363 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7363 / 5120) = 1/(5120 / 7363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (363313019 / 1000000000) (18165651 / 50000000) (Real.log (7363 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7363 / 5120) = -Real.log (5120 / 7363) := by
    rw [show ((7363 / 5120) : ℝ) = ((5120 / 7363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (288203177 / 500000000) ≤ -Real.log (2877 / 5120) ∧
    -Real.log (2877 / 5120) ≤ (115281271 / 200000000) := by
  have h := checkLog_sound (w := (2243 / 7997)) (n := 12)
    (lo := (288203177 / 500000000)) (hi := (115281271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2877) = 1/(2877 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-115281271 / 200000000) (-288203177 / 500000000) (Real.log (2877 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (362905493 / 1000000000) ≤ -Real.log (16 / 23) ∧
    -Real.log (16 / 23) ≤ (181452747 / 500000000) := by
  have h := checkLog_sound (w := (7 / 39)) (n := 12)
    (lo := (362905493 / 1000000000)) (hi := (181452747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 16) = 1/(16 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (362905493 / 1000000000) (181452747 / 500000000) (Real.log (23 / 16)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23 / 16) = -Real.log (16 / 23) := by
    rw [show ((23 / 16) : ℝ) = ((16 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (35960259 / 62500000) ≤ -Real.log (9 / 16) ∧
    -Real.log (9 / 16) ≤ (115072829 / 200000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 9) = 1/(9 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115072829 / 200000000) (-35960259 / 62500000) (Real.log (9 / 16)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135793113 / 500000000) ≤ -Real.log (250000 / 328011) ∧
    -Real.log (250000 / 328011) ≤ (271586227 / 1000000000) := by
  have h := checkLog_sound (w := (78011 / 578011)) (n := 12)
    (lo := (135793113 / 500000000)) (hi := (271586227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328011 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328011 / 250000) = 1/(250000 / 328011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135793113 / 500000000) (271586227 / 1000000000) (Real.log (328011 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (328011 / 250000) = -Real.log (250000 / 328011) := by
    rw [show ((328011 / 250000) : ℝ) = ((250000 / 328011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (93507599 / 250000000) ≤ -Real.log (171989 / 250000) ∧
    -Real.log (171989 / 250000) ≤ (374030397 / 1000000000) := by
  have h := checkLog_sound (w := (78011 / 421989)) (n := 12)
    (lo := (93507599 / 250000000)) (hi := (374030397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171989) = 1/(171989 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-374030397 / 1000000000) (-93507599 / 250000000) (Real.log (171989 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (13595581 / 50000000) ≤ -Real.log (1000000 / 1312471) ∧
    -Real.log (1000000 / 1312471) ≤ (271911621 / 1000000000) := by
  have h := checkLog_sound (w := (312471 / 2312471)) (n := 12)
    (lo := (13595581 / 50000000)) (hi := (271911621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1312471 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1312471 / 1000000) = 1/(1000000 / 1312471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (13595581 / 50000000) (271911621 / 1000000000) (Real.log (1312471 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1312471 / 1000000) = -Real.log (1000000 / 1312471) := by
    rw [show ((1312471 / 1000000) : ℝ) = ((1000000 / 1312471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93662817 / 250000000) ≤ -Real.log (687529 / 1000000) ∧
    -Real.log (687529 / 1000000) ≤ (374651269 / 1000000000) := by
  have h := checkLog_sound (w := (312471 / 1687529)) (n := 12)
    (lo := (93662817 / 250000000)) (hi := (374651269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 687529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 687529) = 1/(687529 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-374651269 / 1000000000) (-93662817 / 250000000) (Real.log (687529 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (102188681 / 500000000) ≤ -Real.log (1000000 / 1226761) ∧
    -Real.log (1000000 / 1226761) ≤ (204377363 / 1000000000) := by
  have h := checkLog_sound (w := (226761 / 2226761)) (n := 12)
    (lo := (102188681 / 500000000)) (hi := (204377363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226761 / 1000000) = 1/(1000000 / 1226761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (102188681 / 500000000) (204377363 / 1000000000) (Real.log (1226761 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1226761 / 1000000) = -Real.log (1000000 / 1226761) := by
    rw [show ((1226761 / 1000000) : ℝ) = ((1000000 / 1226761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (257167093 / 1000000000) ≤ -Real.log (773239 / 1000000) ∧
    -Real.log (773239 / 1000000) ≤ (128583547 / 500000000) := by
  have h := checkLog_sound (w := (226761 / 1773239)) (n := 12)
    (lo := (257167093 / 1000000000)) (hi := (128583547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773239) = 1/(773239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-128583547 / 500000000) (-257167093 / 1000000000) (Real.log (773239 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (204644697 / 1000000000) ≤ -Real.log (1000000 / 1227089) ∧
    -Real.log (1000000 / 1227089) ≤ (102322349 / 500000000) := by
  have h := checkLog_sound (w := (227089 / 2227089)) (n := 12)
    (lo := (204644697 / 1000000000)) (hi := (102322349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227089 / 1000000) = 1/(1000000 / 1227089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (204644697 / 1000000000) (102322349 / 500000000) (Real.log (1227089 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1227089 / 1000000) = -Real.log (1000000 / 1227089) := by
    rw [show ((1227089 / 1000000) : ℝ) = ((1000000 / 1227089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (64397843 / 250000000) ≤ -Real.log (772911 / 1000000) ∧
    -Real.log (772911 / 1000000) ≤ (257591373 / 1000000000) := by
  have h := checkLog_sound (w := (227089 / 1772911)) (n := 12)
    (lo := (64397843 / 250000000)) (hi := (257591373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772911) = 1/(772911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-257591373 / 1000000000) (-64397843 / 250000000) (Real.log (772911 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (645616623 / 1000000000) ≤ -Real.log (500000000000 / 953581333689) ∧
    -Real.log (500000000000 / 953581333689) ≤ (40351039 / 62500000) := by
  have h := checkLog_sound (w := (453581333689 / 1453581333689)) (n := 12)
    (lo := (645616623 / 1000000000)) (hi := (40351039 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953581333689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953581333689 / 500000000000) = 1/(500000000000 / 953581333689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (645616623 / 1000000000) (40351039 / 62500000) (Real.log (953581333689 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (953581333689 / 500000000000) = -Real.log (500000000000 / 953581333689) := by
    rw [show ((953581333689 / 500000000000) : ℝ) = ((500000000000 / 953581333689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (80820361 / 125000000) ≤ -Real.log (250000000000 / 477242050881) ∧
    -Real.log (250000000000 / 477242050881) ≤ (646562889 / 1000000000) := by
  have h := checkLog_sound (w := (227242050881 / 727242050881)) (n := 12)
    (lo := (80820361 / 125000000)) (hi := (646562889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477242050881 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477242050881 / 250000000000) = 1/(250000000000 / 477242050881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (80820361 / 125000000) (646562889 / 1000000000) (Real.log (477242050881 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (477242050881 / 250000000000) = -Real.log (250000000000 / 477242050881) := by
    rw [show ((477242050881 / 250000000000) : ℝ) = ((250000000000 / 477242050881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (92308891 / 200000000) ≤ -Real.log (100000000000 / 158652240769) ∧
    -Real.log (100000000000 / 158652240769) ≤ (57693057 / 125000000) := by
  have h := checkLog_sound (w := (58652240769 / 258652240769)) (n := 12)
    (lo := (92308891 / 200000000)) (hi := (57693057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158652240769 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158652240769 / 100000000000) = 1/(100000000000 / 158652240769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (92308891 / 200000000) (57693057 / 125000000) (Real.log (158652240769 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (158652240769 / 100000000000) = -Real.log (100000000000 / 158652240769) := by
    rw [show ((158652240769 / 100000000000) : ℝ) = ((100000000000 / 158652240769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (46223607 / 100000000) ≤ -Real.log (500000000000 / 793810024699) ∧
    -Real.log (500000000000 / 793810024699) ≤ (462236071 / 1000000000) := by
  have h := checkLog_sound (w := (293810024699 / 1293810024699)) (n := 12)
    (lo := (46223607 / 100000000)) (hi := (462236071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793810024699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793810024699 / 500000000000) = 1/(500000000000 / 793810024699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (46223607 / 100000000) (462236071 / 1000000000) (Real.log (793810024699 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (793810024699 / 500000000000) = -Real.log (500000000000 / 793810024699) := by
    rw [show ((793810024699 / 500000000000) : ℝ) = ((500000000000 / 793810024699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0409

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0410Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0410
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

theorem reflection_log_1_neg : (197825743 / 1000000000) ≤ -Real.log (32 / 39) ∧
    -Real.log (32 / 39) ≤ (12364109 / 62500000) := by
  have h := checkLog_sound (w := (7 / 71)) (n := 12)
    (lo := (197825743 / 1000000000)) (hi := (12364109 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39 / 32) = 1/(32 / 39) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (197825743 / 1000000000) (12364109 / 62500000) (Real.log (39 / 32)) := by
  have h := reflection_log_1_neg
  have he : Real.log (39 / 32) = -Real.log (32 / 39) := by
    rw [show ((39 / 32) : ℝ) = ((32 / 39) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (246860077 / 1000000000) ≤ -Real.log (25 / 32) ∧
    -Real.log (25 / 32) ≤ (123430039 / 500000000) := by
  have h := checkLog_sound (w := (7 / 57)) (n := 12)
    (lo := (246860077 / 1000000000)) (hi := (123430039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 25) = 1/(25 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-123430039 / 500000000) (-246860077 / 1000000000) (Real.log (25 / 32)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (197585329 / 1000000000) ≤ -Real.log (10240 / 12477) ∧
    -Real.log (10240 / 12477) ≤ (19758533 / 100000000) := by
  have h := checkLog_sound (w := (2237 / 22717)) (n := 12)
    (lo := (197585329 / 1000000000)) (hi := (19758533 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12477 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12477 / 10240) = 1/(10240 / 12477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (197585329 / 1000000000) (19758533 / 100000000) (Real.log (12477 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12477 / 10240) = -Real.log (10240 / 12477) := by
    rw [show ((12477 / 10240) : ℝ) = ((10240 / 12477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (61621287 / 250000000) ≤ -Real.log (8003 / 10240) ∧
    -Real.log (8003 / 10240) ≤ (246485149 / 1000000000) := by
  have h := checkLog_sound (w := (2237 / 18243)) (n := 12)
    (lo := (61621287 / 250000000)) (hi := (246485149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8003) = 1/(8003 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-246485149 / 1000000000) (-61621287 / 250000000) (Real.log (8003 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (362905493 / 1000000000) ≤ -Real.log (16 / 23) ∧
    -Real.log (16 / 23) ≤ (181452747 / 500000000) := by
  have h := checkLog_sound (w := (7 / 39)) (n := 12)
    (lo := (362905493 / 1000000000)) (hi := (181452747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 16) = 1/(16 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (362905493 / 1000000000) (181452747 / 500000000) (Real.log (23 / 16)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23 / 16) = -Real.log (16 / 23) := by
    rw [show ((23 / 16) : ℝ) = ((16 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (35960259 / 62500000) ≤ -Real.log (9 / 16) ∧
    -Real.log (9 / 16) ≤ (115072829 / 200000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 9) = 1/(9 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-115072829 / 200000000) (-35960259 / 62500000) (Real.log (9 / 16)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (362497801 / 1000000000) ≤ -Real.log (5120 / 7357) ∧
    -Real.log (5120 / 7357) ≤ (181248901 / 500000000) := by
  have h := checkLog_sound (w := (2237 / 12477)) (n := 12)
    (lo := (362497801 / 1000000000)) (hi := (181248901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7357 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7357 / 5120) = 1/(5120 / 7357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (362497801 / 1000000000) (181248901 / 500000000) (Real.log (7357 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7357 / 5120) = -Real.log (5120 / 7357) := by
    rw [show ((7357 / 5120) : ℝ) = ((5120 / 7357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (28716151 / 50000000) ≤ -Real.log (2883 / 5120) ∧
    -Real.log (2883 / 5120) ≤ (574323021 / 1000000000) := by
  have h := checkLog_sound (w := (2237 / 8003)) (n := 12)
    (lo := (28716151 / 50000000)) (hi := (574323021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2883) = 1/(2883 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-574323021 / 1000000000) (-28716151 / 50000000) (Real.log (2883 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67815563 / 250000000) ≤ -Real.log (1000000 / 1311619) ∧
    -Real.log (1000000 / 1311619) ≤ (271262253 / 1000000000) := by
  have h := checkLog_sound (w := (311619 / 2311619)) (n := 12)
    (lo := (67815563 / 250000000)) (hi := (271262253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311619 / 1000000) = 1/(1000000 / 1311619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67815563 / 250000000) (271262253 / 1000000000) (Real.log (1311619 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1311619 / 1000000) = -Real.log (1000000 / 1311619) := by
    rw [show ((1311619 / 1000000) : ℝ) = ((1000000 / 1311619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (74682563 / 200000000) ≤ -Real.log (688381 / 1000000) ∧
    -Real.log (688381 / 1000000) ≤ (23338301 / 62500000) := by
  have h := checkLog_sound (w := (311619 / 1688381)) (n := 12)
    (lo := (74682563 / 200000000)) (hi := (23338301 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 688381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 688381) = 1/(688381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-23338301 / 62500000) (-74682563 / 200000000) (Real.log (688381 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67896747 / 250000000) ≤ -Real.log (200000 / 262409) ∧
    -Real.log (200000 / 262409) ≤ (271586989 / 1000000000) := by
  have h := checkLog_sound (w := (62409 / 462409)) (n := 12)
    (lo := (67896747 / 250000000)) (hi := (271586989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((262409 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(262409 / 200000) = 1/(200000 / 262409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67896747 / 250000000) (271586989 / 1000000000) (Real.log (262409 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (262409 / 200000) = -Real.log (200000 / 262409) := by
    rw [show ((262409 / 200000) : ℝ) = ((200000 / 262409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7480637 / 20000000) ≤ -Real.log (137591 / 200000) ∧
    -Real.log (137591 / 200000) ≤ (374031851 / 1000000000) := by
  have h := checkLog_sound (w := (62409 / 337591)) (n := 12)
    (lo := (7480637 / 20000000)) (hi := (374031851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 137591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 137591) = 1/(137591 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-374031851 / 1000000000) (-7480637 / 20000000) (Real.log (137591 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (102055793 / 500000000) ≤ -Real.log (200000 / 245287) ∧
    -Real.log (200000 / 245287) ≤ (204111587 / 1000000000) := by
  have h := checkLog_sound (w := (45287 / 445287)) (n := 12)
    (lo := (102055793 / 500000000)) (hi := (204111587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245287 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245287 / 200000) = 1/(200000 / 245287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (102055793 / 500000000) (204111587 / 1000000000) (Real.log (245287 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (245287 / 200000) = -Real.log (200000 / 245287) := by
    rw [show ((245287 / 200000) : ℝ) = ((200000 / 245287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (128372789 / 500000000) ≤ -Real.log (154713 / 200000) ∧
    -Real.log (154713 / 200000) ≤ (256745579 / 1000000000) := by
  have h := checkLog_sound (w := (45287 / 354713)) (n := 12)
    (lo := (128372789 / 500000000)) (hi := (256745579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 154713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 154713) = 1/(154713 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-256745579 / 1000000000) (-128372789 / 500000000) (Real.log (154713 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (204378177 / 1000000000) ≤ -Real.log (500000 / 613381) ∧
    -Real.log (500000 / 613381) ≤ (102189089 / 500000000) := by
  have h := checkLog_sound (w := (113381 / 1113381)) (n := 12)
    (lo := (204378177 / 1000000000)) (hi := (102189089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613381 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613381 / 500000) = 1/(500000 / 613381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (204378177 / 1000000000) (102189089 / 500000000) (Real.log (613381 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (613381 / 500000) = -Real.log (500000 / 613381) := by
    rw [show ((613381 / 500000) : ℝ) = ((500000 / 613381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (128584193 / 500000000) ≤ -Real.log (386619 / 500000) ∧
    -Real.log (386619 / 500000) ≤ (257168387 / 1000000000) := by
  have h := checkLog_sound (w := (113381 / 886619)) (n := 12)
    (lo := (128584193 / 500000000)) (hi := (257168387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386619) = 1/(386619 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-257168387 / 1000000000) (-128584193 / 500000000) (Real.log (386619 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (644675067 / 1000000000) ≤ -Real.log (10000000000 / 19053678123) ∧
    -Real.log (10000000000 / 19053678123) ≤ (161168767 / 250000000) := by
  have h := checkLog_sound (w := (9053678123 / 29053678123)) (n := 12)
    (lo := (644675067 / 1000000000)) (hi := (161168767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19053678123 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19053678123 / 10000000000) = 1/(10000000000 / 19053678123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (644675067 / 1000000000) (161168767 / 250000000) (Real.log (19053678123 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (19053678123 / 10000000000) = -Real.log (10000000000 / 19053678123) := by
    rw [show ((19053678123 / 10000000000) : ℝ) = ((10000000000 / 19053678123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (322809419 / 500000000) ≤ -Real.log (7812500000 / 14899741353) ∧
    -Real.log (7812500000 / 14899741353) ≤ (645618839 / 1000000000) := by
  have h := checkLog_sound (w := (7087241353 / 22712241353)) (n := 12)
    (lo := (322809419 / 500000000)) (hi := (645618839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14899741353 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14899741353 / 7812500000) = 1/(7812500000 / 14899741353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (322809419 / 500000000) (645618839 / 1000000000) (Real.log (14899741353 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14899741353 / 7812500000) = -Real.log (7812500000 / 14899741353) := by
    rw [show ((14899741353 / 7812500000) : ℝ) = ((7812500000 / 14899741353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (92171433 / 200000000) ≤ -Real.log (500000000000 / 792716190623) ∧
    -Real.log (500000000000 / 792716190623) ≤ (230428583 / 500000000) := by
  have h := checkLog_sound (w := (292716190623 / 1292716190623)) (n := 12)
    (lo := (92171433 / 200000000)) (hi := (230428583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792716190623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792716190623 / 500000000000) = 1/(500000000000 / 792716190623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (92171433 / 200000000) (230428583 / 500000000) (Real.log (792716190623 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (792716190623 / 500000000000) = -Real.log (500000000000 / 792716190623) := by
    rw [show ((792716190623 / 500000000000) : ℝ) = ((500000000000 / 792716190623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (115386641 / 250000000) ≤ -Real.log (125000000000 / 198315719093) ∧
    -Real.log (125000000000 / 198315719093) ≤ (92309313 / 200000000) := by
  have h := checkLog_sound (w := (73315719093 / 323315719093)) (n := 12)
    (lo := (115386641 / 250000000)) (hi := (92309313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198315719093 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198315719093 / 125000000000) = 1/(125000000000 / 198315719093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (115386641 / 250000000) (92309313 / 200000000) (Real.log (198315719093 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (198315719093 / 125000000000) = -Real.log (125000000000 / 198315719093) := by
    rw [show ((198315719093 / 125000000000) : ℝ) = ((125000000000 / 198315719093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0410

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0411Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0411
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

theorem reflection_log_1_neg : (197585329 / 1000000000) ≤ -Real.log (10240 / 12477) ∧
    -Real.log (10240 / 12477) ≤ (19758533 / 100000000) := by
  have h := checkLog_sound (w := (2237 / 22717)) (n := 12)
    (lo := (197585329 / 1000000000)) (hi := (19758533 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12477 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12477 / 10240) = 1/(10240 / 12477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (197585329 / 1000000000) (19758533 / 100000000) (Real.log (12477 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12477 / 10240) = -Real.log (10240 / 12477) := by
    rw [show ((12477 / 10240) : ℝ) = ((10240 / 12477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (61621287 / 250000000) ≤ -Real.log (8003 / 10240) ∧
    -Real.log (8003 / 10240) ≤ (246485149 / 1000000000) := by
  have h := checkLog_sound (w := (2237 / 18243)) (n := 12)
    (lo := (61621287 / 250000000)) (hi := (246485149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8003) = 1/(8003 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-246485149 / 1000000000) (-61621287 / 250000000) (Real.log (8003 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (98672429 / 500000000) ≤ -Real.log (5120 / 6237) ∧
    -Real.log (5120 / 6237) ≤ (197344859 / 1000000000) := by
  have h := checkLog_sound (w := (1117 / 11357)) (n := 12)
    (lo := (98672429 / 500000000)) (hi := (197344859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6237 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6237 / 5120) = 1/(5120 / 6237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (98672429 / 500000000) (197344859 / 1000000000) (Real.log (6237 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6237 / 5120) = -Real.log (5120 / 6237) := by
    rw [show ((6237 / 5120) : ℝ) = ((5120 / 6237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (246110359 / 1000000000) ≤ -Real.log (4003 / 5120) ∧
    -Real.log (4003 / 5120) ≤ (6152759 / 25000000) := by
  have h := checkLog_sound (w := (1117 / 9123)) (n := 12)
    (lo := (246110359 / 1000000000)) (hi := (6152759 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4003) = 1/(4003 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6152759 / 25000000) (-246110359 / 1000000000) (Real.log (4003 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (362497801 / 1000000000) ≤ -Real.log (5120 / 7357) ∧
    -Real.log (5120 / 7357) ≤ (181248901 / 500000000) := by
  have h := checkLog_sound (w := (2237 / 12477)) (n := 12)
    (lo := (362497801 / 1000000000)) (hi := (181248901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7357 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7357 / 5120) = 1/(5120 / 7357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (362497801 / 1000000000) (181248901 / 500000000) (Real.log (7357 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7357 / 5120) = -Real.log (5120 / 7357) := by
    rw [show ((7357 / 5120) : ℝ) = ((5120 / 7357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (28716151 / 50000000) ≤ -Real.log (2883 / 5120) ∧
    -Real.log (2883 / 5120) ≤ (574323021 / 1000000000) := by
  have h := checkLog_sound (w := (2237 / 8003)) (n := 12)
    (lo := (28716151 / 50000000)) (hi := (574323021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2883) = 1/(2883 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-574323021 / 1000000000) (-28716151 / 50000000) (Real.log (2883 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (362089943 / 1000000000) ≤ -Real.log (2560 / 3677) ∧
    -Real.log (2560 / 3677) ≤ (45261243 / 125000000) := by
  have h := checkLog_sound (w := (1117 / 6237)) (n := 12)
    (lo := (362089943 / 1000000000)) (hi := (45261243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3677 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3677 / 2560) = 1/(2560 / 3677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (362089943 / 1000000000) (45261243 / 125000000) (Real.log (3677 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3677 / 2560) = -Real.log (2560 / 3677) := by
    rw [show ((3677 / 2560) : ℝ) = ((2560 / 3677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (286641489 / 500000000) ≤ -Real.log (1443 / 2560) ∧
    -Real.log (1443 / 2560) ≤ (573282979 / 1000000000) := by
  have h := checkLog_sound (w := (1117 / 4003)) (n := 12)
    (lo := (286641489 / 500000000)) (hi := (573282979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1443) = 1/(1443 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-573282979 / 1000000000) (-286641489 / 500000000) (Real.log (1443 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (270937409 / 1000000000) ≤ -Real.log (1000000 / 1311193) ∧
    -Real.log (1000000 / 1311193) ≤ (27093741 / 100000000) := by
  have h := checkLog_sound (w := (311193 / 2311193)) (n := 12)
    (lo := (270937409 / 1000000000)) (hi := (27093741 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311193 / 1000000) = 1/(1000000 / 1311193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (270937409 / 1000000000) (27093741 / 100000000) (Real.log (1311193 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1311193 / 1000000) = -Real.log (1000000 / 1311193) := by
    rw [show ((1311193 / 1000000) : ℝ) = ((1000000 / 1311193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (372794163 / 1000000000) ≤ -Real.log (688807 / 1000000) ∧
    -Real.log (688807 / 1000000) ≤ (93198541 / 250000000) := by
  have h := checkLog_sound (w := (311193 / 1688807)) (n := 12)
    (lo := (372794163 / 1000000000)) (hi := (93198541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 688807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 688807) = 1/(688807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-93198541 / 250000000) (-372794163 / 1000000000) (Real.log (688807 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135631507 / 500000000) ≤ -Real.log (50000 / 65581) ∧
    -Real.log (50000 / 65581) ≤ (54252603 / 200000000) := by
  have h := checkLog_sound (w := (15581 / 115581)) (n := 12)
    (lo := (135631507 / 500000000)) (hi := (54252603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65581 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65581 / 50000) = 1/(50000 / 65581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135631507 / 500000000) (54252603 / 200000000) (Real.log (65581 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (65581 / 50000) = -Real.log (50000 / 65581) := by
    rw [show ((65581 / 50000) : ℝ) = ((50000 / 65581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (373414267 / 1000000000) ≤ -Real.log (34419 / 50000) ∧
    -Real.log (34419 / 50000) ≤ (93353567 / 250000000) := by
  have h := checkLog_sound (w := (15581 / 84419)) (n := 12)
    (lo := (373414267 / 1000000000)) (hi := (93353567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 34419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 34419) = 1/(34419 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-93353567 / 250000000) (-373414267 / 1000000000) (Real.log (34419 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (50961231 / 250000000) ≤ -Real.log (250000 / 306527) ∧
    -Real.log (250000 / 306527) ≤ (8153797 / 40000000) := by
  have h := checkLog_sound (w := (56527 / 556527)) (n := 12)
    (lo := (50961231 / 250000000)) (hi := (8153797 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306527 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306527 / 250000) = 1/(250000 / 306527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (50961231 / 250000000) (8153797 / 40000000) (Real.log (306527 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (306527 / 250000) = -Real.log (250000 / 306527) := by
    rw [show ((306527 / 250000) : ℝ) = ((250000 / 306527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (5126459 / 20000000) ≤ -Real.log (193473 / 250000) ∧
    -Real.log (193473 / 250000) ≤ (256322951 / 1000000000) := by
  have h := checkLog_sound (w := (56527 / 443473)) (n := 12)
    (lo := (5126459 / 20000000)) (hi := (256322951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193473) = 1/(193473 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-256322951 / 1000000000) (-5126459 / 20000000) (Real.log (193473 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (102056201 / 500000000) ≤ -Real.log (250000 / 306609) ∧
    -Real.log (250000 / 306609) ≤ (204112403 / 1000000000) := by
  have h := checkLog_sound (w := (56609 / 556609)) (n := 12)
    (lo := (102056201 / 500000000)) (hi := (204112403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306609 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306609 / 250000) = 1/(250000 / 306609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (102056201 / 500000000) (204112403 / 1000000000) (Real.log (306609 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (306609 / 250000) = -Real.log (250000 / 306609) := by
    rw [show ((306609 / 250000) : ℝ) = ((250000 / 306609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (256746871 / 1000000000) ≤ -Real.log (193391 / 250000) ∧
    -Real.log (193391 / 250000) ≤ (32093359 / 125000000) := by
  have h := checkLog_sound (w := (56609 / 443391)) (n := 12)
    (lo := (256746871 / 1000000000)) (hi := (32093359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193391) = 1/(193391 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-32093359 / 125000000) (-256746871 / 1000000000) (Real.log (193391 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (643731573 / 1000000000) ≤ -Real.log (50000000000 / 95178547837) ∧
    -Real.log (50000000000 / 95178547837) ≤ (321865787 / 500000000) := by
  have h := checkLog_sound (w := (45178547837 / 145178547837)) (n := 12)
    (lo := (643731573 / 1000000000)) (hi := (321865787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95178547837 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95178547837 / 50000000000) = 1/(50000000000 / 95178547837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (643731573 / 1000000000) (321865787 / 500000000) (Real.log (95178547837 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (95178547837 / 50000000000) = -Real.log (50000000000 / 95178547837) := by
    rw [show ((95178547837 / 50000000000) : ℝ) = ((50000000000 / 95178547837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (322338641 / 500000000) ≤ -Real.log (100000000000 / 190537203289) ∧
    -Real.log (100000000000 / 190537203289) ≤ (644677283 / 1000000000) := by
  have h := checkLog_sound (w := (90537203289 / 290537203289)) (n := 12)
    (lo := (322338641 / 500000000)) (hi := (644677283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190537203289 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190537203289 / 100000000000) = 1/(100000000000 / 190537203289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (322338641 / 500000000) (644677283 / 1000000000) (Real.log (190537203289 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (190537203289 / 100000000000) = -Real.log (100000000000 / 190537203289) := by
    rw [show ((190537203289 / 100000000000) : ℝ) = ((100000000000 / 190537203289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (230083937 / 500000000) ≤ -Real.log (125000000000 / 198042491717) ∧
    -Real.log (125000000000 / 198042491717) ≤ (3681343 / 8000000) := by
  have h := checkLog_sound (w := (73042491717 / 323042491717)) (n := 12)
    (lo := (230083937 / 500000000)) (hi := (3681343 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198042491717 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198042491717 / 125000000000) = 1/(125000000000 / 198042491717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (230083937 / 500000000) (3681343 / 8000000) (Real.log (198042491717 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (198042491717 / 125000000000) = -Real.log (125000000000 / 198042491717) := by
    rw [show ((198042491717 / 125000000000) : ℝ) = ((125000000000 / 198042491717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (460859273 / 1000000000) ≤ -Real.log (250000000000 / 396358930871) ∧
    -Real.log (250000000000 / 396358930871) ≤ (230429637 / 500000000) := by
  have h := checkLog_sound (w := (146358930871 / 646358930871)) (n := 12)
    (lo := (460859273 / 1000000000)) (hi := (230429637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396358930871 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396358930871 / 250000000000) = 1/(250000000000 / 396358930871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (460859273 / 1000000000) (230429637 / 500000000) (Real.log (396358930871 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (396358930871 / 250000000000) = -Real.log (250000000000 / 396358930871) := by
    rw [show ((396358930871 / 250000000000) : ℝ) = ((250000000000 / 396358930871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0411

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0412Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0412
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

theorem reflection_log_1_neg : (98672429 / 500000000) ≤ -Real.log (5120 / 6237) ∧
    -Real.log (5120 / 6237) ≤ (197344859 / 1000000000) := by
  have h := checkLog_sound (w := (1117 / 11357)) (n := 12)
    (lo := (98672429 / 500000000)) (hi := (197344859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6237 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6237 / 5120) = 1/(5120 / 6237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (98672429 / 500000000) (197344859 / 1000000000) (Real.log (6237 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6237 / 5120) = -Real.log (5120 / 6237) := by
    rw [show ((6237 / 5120) : ℝ) = ((5120 / 6237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (246110359 / 1000000000) ≤ -Real.log (4003 / 5120) ∧
    -Real.log (4003 / 5120) ≤ (6152759 / 25000000) := by
  have h := checkLog_sound (w := (1117 / 9123)) (n := 12)
    (lo := (246110359 / 1000000000)) (hi := (6152759 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4003) = 1/(4003 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6152759 / 25000000) (-246110359 / 1000000000) (Real.log (4003 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (197104329 / 1000000000) ≤ -Real.log (10240 / 12471) ∧
    -Real.log (10240 / 12471) ≤ (19710433 / 100000000) := by
  have h := checkLog_sound (w := (2231 / 22711)) (n := 12)
    (lo := (197104329 / 1000000000)) (hi := (19710433 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12471 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12471 / 10240) = 1/(10240 / 12471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (197104329 / 1000000000) (19710433 / 100000000) (Real.log (12471 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12471 / 10240) = -Real.log (10240 / 12471) := by
    rw [show ((12471 / 10240) : ℝ) = ((10240 / 12471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (24573571 / 100000000) ≤ -Real.log (8009 / 10240) ∧
    -Real.log (8009 / 10240) ≤ (245735711 / 1000000000) := by
  have h := checkLog_sound (w := (2231 / 18249)) (n := 12)
    (lo := (24573571 / 100000000)) (hi := (245735711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8009) = 1/(8009 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-245735711 / 1000000000) (-24573571 / 100000000) (Real.log (8009 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (362089943 / 1000000000) ≤ -Real.log (2560 / 3677) ∧
    -Real.log (2560 / 3677) ≤ (45261243 / 125000000) := by
  have h := checkLog_sound (w := (1117 / 6237)) (n := 12)
    (lo := (362089943 / 1000000000)) (hi := (45261243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3677 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3677 / 2560) = 1/(2560 / 3677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (362089943 / 1000000000) (45261243 / 125000000) (Real.log (3677 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3677 / 2560) = -Real.log (2560 / 3677) := by
    rw [show ((3677 / 2560) : ℝ) = ((2560 / 3677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (286641489 / 500000000) ≤ -Real.log (1443 / 2560) ∧
    -Real.log (1443 / 2560) ≤ (573282979 / 1000000000) := by
  have h := checkLog_sound (w := (1117 / 4003)) (n := 12)
    (lo := (286641489 / 500000000)) (hi := (573282979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1443) = 1/(1443 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-573282979 / 1000000000) (-286641489 / 500000000) (Real.log (1443 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (361681919 / 1000000000) ≤ -Real.log (5120 / 7351) ∧
    -Real.log (5120 / 7351) ≤ (141282 / 390625) := by
  have h := checkLog_sound (w := (2231 / 12471)) (n := 12)
    (lo := (361681919 / 1000000000)) (hi := (141282 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7351 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7351 / 5120) = 1/(5120 / 7351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (361681919 / 1000000000) (141282 / 390625) (Real.log (7351 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7351 / 5120) = -Real.log (5120 / 7351) := by
    rw [show ((7351 / 5120) : ℝ) = ((5120 / 7351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (572244017 / 1000000000) ≤ -Real.log (2889 / 5120) ∧
    -Real.log (2889 / 5120) ≤ (286122009 / 500000000) := by
  have h := checkLog_sound (w := (2231 / 8009)) (n := 12)
    (lo := (572244017 / 1000000000)) (hi := (286122009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2889) = 1/(2889 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-286122009 / 500000000) (-572244017 / 1000000000) (Real.log (2889 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135306231 / 500000000) ≤ -Real.log (1000000 / 1310767) ∧
    -Real.log (1000000 / 1310767) ≤ (270612463 / 1000000000) := by
  have h := checkLog_sound (w := (310767 / 2310767)) (n := 12)
    (lo := (135306231 / 500000000)) (hi := (270612463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1310767 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1310767 / 1000000) = 1/(1000000 / 1310767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135306231 / 500000000) (270612463 / 1000000000) (Real.log (1310767 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1310767 / 1000000) = -Real.log (1000000 / 1310767) := by
    rw [show ((1310767 / 1000000) : ℝ) = ((1000000 / 1310767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (372175893 / 1000000000) ≤ -Real.log (689233 / 1000000) ∧
    -Real.log (689233 / 1000000) ≤ (186087947 / 500000000) := by
  have h := checkLog_sound (w := (310767 / 1689233)) (n := 12)
    (lo := (372175893 / 1000000000)) (hi := (186087947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 689233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 689233) = 1/(689233 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-186087947 / 500000000) (-372175893 / 1000000000) (Real.log (689233 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67734543 / 250000000) ≤ -Real.log (500000 / 655597) ∧
    -Real.log (500000 / 655597) ≤ (270938173 / 1000000000) := by
  have h := checkLog_sound (w := (155597 / 1155597)) (n := 12)
    (lo := (67734543 / 250000000)) (hi := (270938173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655597 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655597 / 500000) = 1/(500000 / 655597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67734543 / 250000000) (270938173 / 1000000000) (Real.log (655597 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (655597 / 500000) = -Real.log (500000 / 655597) := by
    rw [show ((655597 / 500000) : ℝ) = ((500000 / 655597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (74559123 / 200000000) ≤ -Real.log (344403 / 500000) ∧
    -Real.log (344403 / 500000) ≤ (11649863 / 31250000) := by
  have h := checkLog_sound (w := (155597 / 844403)) (n := 12)
    (lo := (74559123 / 200000000)) (hi := (11649863 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 344403) = 1/(344403 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11649863 / 31250000) (-74559123 / 200000000) (Real.log (344403 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (203579007 / 1000000000) ≤ -Real.log (500000 / 612891) ∧
    -Real.log (500000 / 612891) ≤ (1590461 / 7812500) := by
  have h := checkLog_sound (w := (112891 / 1112891)) (n := 12)
    (lo := (203579007 / 1000000000)) (hi := (1590461 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612891 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612891 / 500000) = 1/(500000 / 612891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (203579007 / 1000000000) (1590461 / 7812500) (Real.log (612891 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (612891 / 500000) = -Real.log (500000 / 612891) := by
    rw [show ((612891 / 500000) : ℝ) = ((500000 / 612891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (255901791 / 1000000000) ≤ -Real.log (387109 / 500000) ∧
    -Real.log (387109 / 500000) ≤ (7996931 / 31250000) := by
  have h := checkLog_sound (w := (112891 / 887109)) (n := 12)
    (lo := (255901791 / 1000000000)) (hi := (7996931 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387109) = 1/(387109 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-7996931 / 31250000) (-255901791 / 1000000000) (Real.log (387109 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (10192287 / 50000000) ≤ -Real.log (1000000 / 1226109) ∧
    -Real.log (1000000 / 1226109) ≤ (203845741 / 1000000000) := by
  have h := checkLog_sound (w := (226109 / 2226109)) (n := 12)
    (lo := (10192287 / 50000000)) (hi := (203845741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226109 / 1000000) = 1/(1000000 / 1226109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (10192287 / 50000000) (203845741 / 1000000000) (Real.log (1226109 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1226109 / 1000000) = -Real.log (1000000 / 1226109) := by
    rw [show ((1226109 / 1000000) : ℝ) = ((1000000 / 1226109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (128162121 / 500000000) ≤ -Real.log (773891 / 1000000) ∧
    -Real.log (773891 / 1000000) ≤ (256324243 / 1000000000) := by
  have h := checkLog_sound (w := (226109 / 1773891)) (n := 12)
    (lo := (128162121 / 500000000)) (hi := (256324243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773891) = 1/(773891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-256324243 / 1000000000) (-128162121 / 500000000) (Real.log (773891 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (128557671 / 200000000) ≤ -Real.log (500000000000 / 950888161187) ∧
    -Real.log (500000000000 / 950888161187) ≤ (160697089 / 250000000) := by
  have h := checkLog_sound (w := (450888161187 / 1450888161187)) (n := 12)
    (lo := (128557671 / 200000000)) (hi := (160697089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((950888161187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(950888161187 / 500000000000) = 1/(500000000000 / 950888161187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (128557671 / 200000000) (160697089 / 250000000) (Real.log (950888161187 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (950888161187 / 500000000000) = -Real.log (500000000000 / 950888161187) := by
    rw [show ((950888161187 / 500000000000) : ℝ) = ((500000000000 / 950888161187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (643733787 / 1000000000) ≤ -Real.log (100000000000 / 190357517211) ∧
    -Real.log (100000000000 / 190357517211) ≤ (160933447 / 250000000) := by
  have h := checkLog_sound (w := (90357517211 / 290357517211)) (n := 12)
    (lo := (643733787 / 1000000000)) (hi := (160933447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190357517211 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190357517211 / 100000000000) = 1/(100000000000 / 190357517211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (643733787 / 1000000000) (160933447 / 250000000) (Real.log (190357517211 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (190357517211 / 100000000000) = -Real.log (100000000000 / 190357517211) := by
    rw [show ((190357517211 / 100000000000) : ℝ) = ((100000000000 / 190357517211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (229740399 / 500000000) ≤ -Real.log (31250000000 / 49476617051) ∧
    -Real.log (31250000000 / 49476617051) ≤ (459480799 / 1000000000) := by
  have h := checkLog_sound (w := (18226617051 / 80726617051)) (n := 12)
    (lo := (229740399 / 500000000)) (hi := (459480799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49476617051 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49476617051 / 31250000000) = 1/(31250000000 / 49476617051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (229740399 / 500000000) (459480799 / 1000000000) (Real.log (49476617051 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49476617051 / 31250000000) = -Real.log (31250000000 / 49476617051) := by
    rw [show ((49476617051 / 31250000000) : ℝ) = ((31250000000 / 49476617051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (230084991 / 500000000) ≤ -Real.log (20000000000 / 31686865463) ∧
    -Real.log (20000000000 / 31686865463) ≤ (460169983 / 1000000000) := by
  have h := checkLog_sound (w := (11686865463 / 51686865463)) (n := 12)
    (lo := (230084991 / 500000000)) (hi := (460169983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31686865463 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31686865463 / 20000000000) = 1/(20000000000 / 31686865463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (230084991 / 500000000) (460169983 / 1000000000) (Real.log (31686865463 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (31686865463 / 20000000000) = -Real.log (20000000000 / 31686865463) := by
    rw [show ((31686865463 / 20000000000) : ℝ) = ((20000000000 / 31686865463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0412

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0413Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0413
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

theorem reflection_log_1_neg : (197104329 / 1000000000) ≤ -Real.log (10240 / 12471) ∧
    -Real.log (10240 / 12471) ≤ (19710433 / 100000000) := by
  have h := checkLog_sound (w := (2231 / 22711)) (n := 12)
    (lo := (197104329 / 1000000000)) (hi := (19710433 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12471 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12471 / 10240) = 1/(10240 / 12471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (197104329 / 1000000000) (19710433 / 100000000) (Real.log (12471 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12471 / 10240) = -Real.log (10240 / 12471) := by
    rw [show ((12471 / 10240) : ℝ) = ((10240 / 12471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (24573571 / 100000000) ≤ -Real.log (8009 / 10240) ∧
    -Real.log (8009 / 10240) ≤ (245735711 / 1000000000) := by
  have h := checkLog_sound (w := (2231 / 18249)) (n := 12)
    (lo := (24573571 / 100000000)) (hi := (245735711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8009) = 1/(8009 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-245735711 / 1000000000) (-24573571 / 100000000) (Real.log (8009 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (98431871 / 500000000) ≤ -Real.log (2560 / 3117) ∧
    -Real.log (2560 / 3117) ≤ (196863743 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 5677)) (n := 12)
    (lo := (98431871 / 500000000)) (hi := (196863743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3117 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3117 / 2560) = 1/(2560 / 3117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (98431871 / 500000000) (196863743 / 1000000000) (Real.log (3117 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3117 / 2560) = -Real.log (2560 / 3117) := by
    rw [show ((3117 / 2560) : ℝ) = ((2560 / 3117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (245361201 / 1000000000) ≤ -Real.log (2003 / 2560) ∧
    -Real.log (2003 / 2560) ≤ (122680601 / 500000000) := by
  have h := checkLog_sound (w := (557 / 4563)) (n := 12)
    (lo := (245361201 / 1000000000)) (hi := (122680601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2003) = 1/(2003 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-122680601 / 500000000) (-245361201 / 1000000000) (Real.log (2003 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (361681919 / 1000000000) ≤ -Real.log (5120 / 7351) ∧
    -Real.log (5120 / 7351) ≤ (141282 / 390625) := by
  have h := checkLog_sound (w := (2231 / 12471)) (n := 12)
    (lo := (361681919 / 1000000000)) (hi := (141282 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7351 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7351 / 5120) = 1/(5120 / 7351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (361681919 / 1000000000) (141282 / 390625) (Real.log (7351 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7351 / 5120) = -Real.log (5120 / 7351) := by
    rw [show ((7351 / 5120) : ℝ) = ((5120 / 7351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (572244017 / 1000000000) ≤ -Real.log (2889 / 5120) ∧
    -Real.log (2889 / 5120) ≤ (286122009 / 500000000) := by
  have h := checkLog_sound (w := (2231 / 8009)) (n := 12)
    (lo := (572244017 / 1000000000)) (hi := (286122009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2889) = 1/(2889 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-286122009 / 500000000) (-572244017 / 1000000000) (Real.log (2889 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2822451 / 7812500) ≤ -Real.log (1280 / 1837) ∧
    -Real.log (1280 / 1837) ≤ (361273729 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 3117)) (n := 12)
    (lo := (2822451 / 7812500)) (hi := (361273729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1837 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1837 / 1280) = 1/(1280 / 1837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2822451 / 7812500) (361273729 / 1000000000) (Real.log (1837 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1837 / 1280) = -Real.log (1280 / 1837) := by
    rw [show ((1837 / 1280) : ℝ) = ((1280 / 1837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (285603067 / 500000000) ≤ -Real.log (723 / 1280) ∧
    -Real.log (723 / 1280) ≤ (114241227 / 200000000) := by
  have h := checkLog_sound (w := (557 / 2003)) (n := 12)
    (lo := (285603067 / 500000000)) (hi := (114241227 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 723) = 1/(723 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-114241227 / 200000000) (-285603067 / 500000000) (Real.log (723 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (270288171 / 1000000000) ≤ -Real.log (500000 / 655171) ∧
    -Real.log (500000 / 655171) ≤ (67572043 / 250000000) := by
  have h := checkLog_sound (w := (155171 / 1155171)) (n := 12)
    (lo := (270288171 / 1000000000)) (hi := (67572043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655171 / 500000) = 1/(500000 / 655171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (270288171 / 1000000000) (67572043 / 250000000) (Real.log (655171 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (655171 / 500000) = -Real.log (500000 / 655171) := by
    rw [show ((655171 / 500000) : ℝ) = ((500000 / 655171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (11611233 / 31250000) ≤ -Real.log (344829 / 500000) ∧
    -Real.log (344829 / 500000) ≤ (371559457 / 1000000000) := by
  have h := checkLog_sound (w := (155171 / 844829)) (n := 12)
    (lo := (11611233 / 31250000)) (hi := (371559457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 344829) = 1/(344829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-371559457 / 1000000000) (-11611233 / 31250000) (Real.log (344829 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33826653 / 125000000) ≤ -Real.log (62500 / 81923) ∧
    -Real.log (62500 / 81923) ≤ (10824529 / 40000000) := by
  have h := checkLog_sound (w := (19423 / 144423)) (n := 12)
    (lo := (33826653 / 125000000)) (hi := (10824529 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81923 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81923 / 62500) = 1/(62500 / 81923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33826653 / 125000000) (10824529 / 40000000) (Real.log (81923 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (81923 / 62500) = -Real.log (62500 / 81923) := by
    rw [show ((81923 / 62500) : ℝ) = ((62500 / 81923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (5815271 / 15625000) ≤ -Real.log (43077 / 62500) ∧
    -Real.log (43077 / 62500) ≤ (74435469 / 200000000) := by
  have h := checkLog_sound (w := (19423 / 105577)) (n := 12)
    (lo := (5815271 / 15625000)) (hi := (74435469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 43077) = 1/(43077 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-74435469 / 200000000) (-5815271 / 15625000) (Real.log (43077 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (203313019 / 1000000000) ≤ -Real.log (62500 / 76591) ∧
    -Real.log (62500 / 76591) ≤ (10165651 / 50000000) := by
  have h := checkLog_sound (w := (14091 / 139091)) (n := 12)
    (lo := (203313019 / 1000000000)) (hi := (10165651 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76591 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76591 / 62500) = 1/(62500 / 76591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (203313019 / 1000000000) (10165651 / 50000000) (Real.log (76591 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (76591 / 62500) = -Real.log (62500 / 76591) := by
    rw [show ((76591 / 62500) : ℝ) = ((62500 / 76591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (255480809 / 1000000000) ≤ -Real.log (48409 / 62500) ∧
    -Real.log (48409 / 62500) ≤ (25548081 / 100000000) := by
  have h := checkLog_sound (w := (14091 / 110909)) (n := 12)
    (lo := (255480809 / 1000000000)) (hi := (25548081 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48409) = 1/(48409 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-25548081 / 100000000) (-255480809 / 1000000000) (Real.log (48409 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (203579823 / 1000000000) ≤ -Real.log (1000000 / 1225783) ∧
    -Real.log (1000000 / 1225783) ≤ (12723739 / 62500000) := by
  have h := checkLog_sound (w := (225783 / 2225783)) (n := 12)
    (lo := (203579823 / 1000000000)) (hi := (12723739 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225783 / 1000000) = 1/(1000000 / 1225783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (203579823 / 1000000000) (12723739 / 62500000) (Real.log (1225783 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1225783 / 1000000) = -Real.log (1000000 / 1225783) := by
    rw [show ((1225783 / 1000000) : ℝ) = ((1000000 / 1225783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (127951541 / 500000000) ≤ -Real.log (774217 / 1000000) ∧
    -Real.log (774217 / 1000000) ≤ (255903083 / 1000000000) := by
  have h := checkLog_sound (w := (225783 / 1774217)) (n := 12)
    (lo := (127951541 / 500000000)) (hi := (255903083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774217) = 1/(774217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-255903083 / 1000000000) (-127951541 / 500000000) (Real.log (774217 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (160461907 / 250000000) ≤ -Real.log (31250000000 / 59374628439) ∧
    -Real.log (31250000000 / 59374628439) ≤ (641847629 / 1000000000) := by
  have h := checkLog_sound (w := (28124628439 / 90624628439)) (n := 12)
    (lo := (160461907 / 250000000)) (hi := (641847629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59374628439 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59374628439 / 31250000000) = 1/(31250000000 / 59374628439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (160461907 / 250000000) (641847629 / 1000000000) (Real.log (59374628439 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (59374628439 / 31250000000) = -Real.log (31250000000 / 59374628439) := by
    rw [show ((59374628439 / 31250000000) : ℝ) = ((31250000000 / 59374628439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (642790569 / 1000000000) ≤ -Real.log (125000000000 / 237722566567) ∧
    -Real.log (125000000000 / 237722566567) ≤ (64279057 / 100000000) := by
  have h := checkLog_sound (w := (112722566567 / 362722566567)) (n := 12)
    (lo := (642790569 / 1000000000)) (hi := (64279057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237722566567 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237722566567 / 125000000000) = 1/(125000000000 / 237722566567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (642790569 / 1000000000) (64279057 / 100000000) (Real.log (237722566567 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (237722566567 / 125000000000) = -Real.log (125000000000 / 237722566567) := by
    rw [show ((237722566567 / 125000000000) : ℝ) = ((125000000000 / 237722566567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (458793829 / 1000000000) ≤ -Real.log (250000000000 / 395541118387) ∧
    -Real.log (250000000000 / 395541118387) ≤ (45879383 / 100000000) := by
  have h := checkLog_sound (w := (145541118387 / 645541118387)) (n := 12)
    (lo := (458793829 / 1000000000)) (hi := (45879383 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395541118387 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395541118387 / 250000000000) = 1/(250000000000 / 395541118387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (458793829 / 1000000000) (45879383 / 100000000) (Real.log (395541118387 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (395541118387 / 250000000000) = -Real.log (250000000000 / 395541118387) := by
    rw [show ((395541118387 / 250000000000) : ℝ) = ((250000000000 / 395541118387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (229741453 / 500000000) ≤ -Real.log (125000000000 / 197906885279) ∧
    -Real.log (125000000000 / 197906885279) ≤ (459482907 / 1000000000) := by
  have h := checkLog_sound (w := (72906885279 / 322906885279)) (n := 12)
    (lo := (229741453 / 500000000)) (hi := (459482907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197906885279 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197906885279 / 125000000000) = 1/(125000000000 / 197906885279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (229741453 / 500000000) (459482907 / 1000000000) (Real.log (197906885279 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (197906885279 / 125000000000) = -Real.log (125000000000 / 197906885279) := by
    rw [show ((197906885279 / 125000000000) : ℝ) = ((125000000000 / 197906885279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0413

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0414Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0414
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

theorem reflection_log_1_neg : (98431871 / 500000000) ≤ -Real.log (2560 / 3117) ∧
    -Real.log (2560 / 3117) ≤ (196863743 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 5677)) (n := 12)
    (lo := (98431871 / 500000000)) (hi := (196863743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3117 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3117 / 2560) = 1/(2560 / 3117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (98431871 / 500000000) (196863743 / 1000000000) (Real.log (3117 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3117 / 2560) = -Real.log (2560 / 3117) := by
    rw [show ((3117 / 2560) : ℝ) = ((2560 / 3117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (245361201 / 1000000000) ≤ -Real.log (2003 / 2560) ∧
    -Real.log (2003 / 2560) ≤ (122680601 / 500000000) := by
  have h := checkLog_sound (w := (557 / 4563)) (n := 12)
    (lo := (245361201 / 1000000000)) (hi := (122680601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2003) = 1/(2003 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122680601 / 500000000) (-245361201 / 1000000000) (Real.log (2003 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (196623097 / 1000000000) ≤ -Real.log (2048 / 2493) ∧
    -Real.log (2048 / 2493) ≤ (98311549 / 500000000) := by
  have h := checkLog_sound (w := (445 / 4541)) (n := 12)
    (lo := (196623097 / 1000000000)) (hi := (98311549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2493 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2493 / 2048) = 1/(2048 / 2493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (196623097 / 1000000000) (98311549 / 500000000) (Real.log (2493 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2493 / 2048) = -Real.log (2048 / 2493) := by
    rw [show ((2493 / 2048) : ℝ) = ((2048 / 2493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (244986833 / 1000000000) ≤ -Real.log (1603 / 2048) ∧
    -Real.log (1603 / 2048) ≤ (122493417 / 500000000) := by
  have h := checkLog_sound (w := (445 / 3651)) (n := 12)
    (lo := (244986833 / 1000000000)) (hi := (122493417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1603) = 1/(1603 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-122493417 / 500000000) (-244986833 / 1000000000) (Real.log (1603 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2822451 / 7812500) ≤ -Real.log (1280 / 1837) ∧
    -Real.log (1280 / 1837) ≤ (361273729 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 3117)) (n := 12)
    (lo := (2822451 / 7812500)) (hi := (361273729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1837 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1837 / 1280) = 1/(1280 / 1837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2822451 / 7812500) (361273729 / 1000000000) (Real.log (1837 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1837 / 1280) = -Real.log (1280 / 1837) := by
    rw [show ((1837 / 1280) : ℝ) = ((1280 / 1837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (285603067 / 500000000) ≤ -Real.log (723 / 1280) ∧
    -Real.log (723 / 1280) ≤ (114241227 / 200000000) := by
  have h := checkLog_sound (w := (557 / 2003)) (n := 12)
    (lo := (285603067 / 500000000)) (hi := (114241227 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 723) = 1/(723 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-114241227 / 200000000) (-285603067 / 500000000) (Real.log (723 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (36086537 / 100000000) ≤ -Real.log (1024 / 1469) ∧
    -Real.log (1024 / 1469) ≤ (360865371 / 1000000000) := by
  have h := checkLog_sound (w := (445 / 2493)) (n := 12)
    (lo := (36086537 / 100000000)) (hi := (360865371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1469 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1469 / 1024) = 1/(1024 / 1469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (36086537 / 100000000) (360865371 / 1000000000) (Real.log (1469 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1469 / 1024) = -Real.log (1024 / 1469) := by
    rw [show ((1469 / 1024) : ℝ) = ((1024 / 1469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (35635583 / 62500000) ≤ -Real.log (579 / 1024) ∧
    -Real.log (579 / 1024) ≤ (570169329 / 1000000000) := by
  have h := checkLog_sound (w := (445 / 1603)) (n := 12)
    (lo := (35635583 / 62500000)) (hi := (570169329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 579) = 1/(579 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-570169329 / 1000000000) (-35635583 / 62500000) (Real.log (579 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (269963013 / 1000000000) ≤ -Real.log (250000 / 327479) ∧
    -Real.log (250000 / 327479) ≤ (134981507 / 500000000) := by
  have h := checkLog_sound (w := (77479 / 577479)) (n := 12)
    (lo := (269963013 / 1000000000)) (hi := (134981507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327479 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327479 / 250000) = 1/(250000 / 327479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (269963013 / 1000000000) (134981507 / 500000000) (Real.log (327479 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (327479 / 250000) = -Real.log (250000 / 327479) := by
    rw [show ((327479 / 250000) : ℝ) = ((250000 / 327479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (370941949 / 1000000000) ≤ -Real.log (172521 / 250000) ∧
    -Real.log (172521 / 250000) ≤ (7418839 / 20000000) := by
  have h := checkLog_sound (w := (77479 / 422521)) (n := 12)
    (lo := (370941949 / 1000000000)) (hi := (7418839 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 172521) = 1/(172521 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7418839 / 20000000) (-370941949 / 1000000000) (Real.log (172521 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (54057787 / 200000000) ≤ -Real.log (1000000 / 1310343) ∧
    -Real.log (1000000 / 1310343) ≤ (33786117 / 125000000) := by
  have h := checkLog_sound (w := (310343 / 2310343)) (n := 12)
    (lo := (54057787 / 200000000)) (hi := (33786117 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1310343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1310343 / 1000000) = 1/(1000000 / 1310343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (54057787 / 200000000) (33786117 / 125000000) (Real.log (1310343 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1310343 / 1000000) = -Real.log (1000000 / 1310343) := by
    rw [show ((1310343 / 1000000) : ℝ) = ((1000000 / 1310343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (185780453 / 500000000) ≤ -Real.log (689657 / 1000000) ∧
    -Real.log (689657 / 1000000) ≤ (371560907 / 1000000000) := by
  have h := checkLog_sound (w := (310343 / 1689657)) (n := 12)
    (lo := (185780453 / 500000000)) (hi := (371560907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 689657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 689657) = 1/(689657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-371560907 / 1000000000) (-185780453 / 500000000) (Real.log (689657 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2538087 / 12500000) ≤ -Real.log (100000 / 122513) ∧
    -Real.log (100000 / 122513) ≤ (203046961 / 1000000000) := by
  have h := checkLog_sound (w := (22513 / 222513)) (n := 12)
    (lo := (2538087 / 12500000)) (hi := (203046961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122513 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122513 / 100000) = 1/(100000 / 122513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2538087 / 12500000) (203046961 / 1000000000) (Real.log (122513 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (122513 / 100000) = -Real.log (100000 / 122513) := by
    rw [show ((122513 / 100000) : ℝ) = ((100000 / 122513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (51012001 / 200000000) ≤ -Real.log (77487 / 100000) ∧
    -Real.log (77487 / 100000) ≤ (127530003 / 500000000) := by
  have h := checkLog_sound (w := (22513 / 177487)) (n := 12)
    (lo := (51012001 / 200000000)) (hi := (127530003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 77487) = 1/(77487 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-127530003 / 500000000) (-51012001 / 200000000) (Real.log (77487 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (40662767 / 200000000) ≤ -Real.log (1000000 / 1225457) ∧
    -Real.log (1000000 / 1225457) ≤ (50828459 / 250000000) := by
  have h := checkLog_sound (w := (225457 / 2225457)) (n := 12)
    (lo := (40662767 / 200000000)) (hi := (50828459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225457 / 1000000) = 1/(1000000 / 1225457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (40662767 / 200000000) (50828459 / 250000000) (Real.log (1225457 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1225457 / 1000000) = -Real.log (1000000 / 1225457) := by
    rw [show ((1225457 / 1000000) : ℝ) = ((1000000 / 1225457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2554821 / 10000000) ≤ -Real.log (774543 / 1000000) ∧
    -Real.log (774543 / 1000000) ≤ (255482101 / 1000000000) := by
  have h := checkLog_sound (w := (225457 / 1774543)) (n := 12)
    (lo := (2554821 / 10000000)) (hi := (255482101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774543) = 1/(774543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-255482101 / 1000000000) (-2554821 / 10000000) (Real.log (774543 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (320452481 / 500000000) ≤ -Real.log (3906250000 / 7414835549) ∧
    -Real.log (3906250000 / 7414835549) ≤ (640904963 / 1000000000) := by
  have h := checkLog_sound (w := (3508585549 / 11321085549)) (n := 12)
    (lo := (320452481 / 500000000)) (hi := (640904963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7414835549 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7414835549 / 3906250000) = 1/(3906250000 / 7414835549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (320452481 / 500000000) (640904963 / 1000000000) (Real.log (7414835549 / 3906250000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7414835549 / 3906250000) = -Real.log (3906250000 / 7414835549) := by
    rw [show ((7414835549 / 3906250000) : ℝ) = ((3906250000 / 7414835549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (641849841 / 1000000000) ≤ -Real.log (500000000000 / 949996157511) ∧
    -Real.log (500000000000 / 949996157511) ≤ (320924921 / 500000000) := by
  have h := checkLog_sound (w := (449996157511 / 1449996157511)) (n := 12)
    (lo := (641849841 / 1000000000)) (hi := (320924921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((949996157511 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(949996157511 / 500000000000) = 1/(500000000000 / 949996157511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (641849841 / 1000000000) (320924921 / 500000000) (Real.log (949996157511 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (949996157511 / 500000000000) = -Real.log (500000000000 / 949996157511) := by
    rw [show ((949996157511 / 500000000000) : ℝ) = ((500000000000 / 949996157511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (229053483 / 500000000) ≤ -Real.log (125000000000 / 197634764541) ∧
    -Real.log (125000000000 / 197634764541) ≤ (458106967 / 1000000000) := by
  have h := checkLog_sound (w := (72634764541 / 322634764541)) (n := 12)
    (lo := (229053483 / 500000000)) (hi := (458106967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197634764541 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197634764541 / 125000000000) = 1/(125000000000 / 197634764541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (229053483 / 500000000) (458106967 / 1000000000) (Real.log (197634764541 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (197634764541 / 125000000000) = -Real.log (125000000000 / 197634764541) := by
    rw [show ((197634764541 / 125000000000) : ℝ) = ((125000000000 / 197634764541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (14337373 / 31250000) ≤ -Real.log (50000000000 / 79108390367) ∧
    -Real.log (50000000000 / 79108390367) ≤ (458795937 / 1000000000) := by
  have h := checkLog_sound (w := (29108390367 / 129108390367)) (n := 12)
    (lo := (14337373 / 31250000)) (hi := (458795937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79108390367 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79108390367 / 50000000000) = 1/(50000000000 / 79108390367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (14337373 / 31250000) (458795937 / 1000000000) (Real.log (79108390367 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (79108390367 / 50000000000) = -Real.log (50000000000 / 79108390367) := by
    rw [show ((79108390367 / 50000000000) : ℝ) = ((50000000000 / 79108390367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0414

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0415Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0415
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

theorem reflection_log_1_neg : (196623097 / 1000000000) ≤ -Real.log (2048 / 2493) ∧
    -Real.log (2048 / 2493) ≤ (98311549 / 500000000) := by
  have h := checkLog_sound (w := (445 / 4541)) (n := 12)
    (lo := (196623097 / 1000000000)) (hi := (98311549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2493 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2493 / 2048) = 1/(2048 / 2493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (196623097 / 1000000000) (98311549 / 500000000) (Real.log (2493 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2493 / 2048) = -Real.log (2048 / 2493) := by
    rw [show ((2493 / 2048) : ℝ) = ((2048 / 2493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (244986833 / 1000000000) ≤ -Real.log (1603 / 2048) ∧
    -Real.log (1603 / 2048) ≤ (122493417 / 500000000) := by
  have h := checkLog_sound (w := (445 / 3651)) (n := 12)
    (lo := (244986833 / 1000000000)) (hi := (122493417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1603) = 1/(1603 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122493417 / 500000000) (-244986833 / 1000000000) (Real.log (1603 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (98191197 / 500000000) ≤ -Real.log (5120 / 6231) ∧
    -Real.log (5120 / 6231) ≤ (39276479 / 200000000) := by
  have h := checkLog_sound (w := (1111 / 11351)) (n := 12)
    (lo := (98191197 / 500000000)) (hi := (39276479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6231 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6231 / 5120) = 1/(5120 / 6231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (98191197 / 500000000) (39276479 / 200000000) (Real.log (6231 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6231 / 5120) = -Real.log (5120 / 6231) := by
    rw [show ((6231 / 5120) : ℝ) = ((5120 / 6231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (48922521 / 200000000) ≤ -Real.log (4009 / 5120) ∧
    -Real.log (4009 / 5120) ≤ (122306303 / 500000000) := by
  have h := checkLog_sound (w := (1111 / 9129)) (n := 12)
    (lo := (48922521 / 200000000)) (hi := (122306303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4009) = 1/(4009 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-122306303 / 500000000) (-48922521 / 200000000) (Real.log (4009 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (36086537 / 100000000) ≤ -Real.log (1024 / 1469) ∧
    -Real.log (1024 / 1469) ≤ (360865371 / 1000000000) := by
  have h := checkLog_sound (w := (445 / 2493)) (n := 12)
    (lo := (36086537 / 100000000)) (hi := (360865371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1469 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1469 / 1024) = 1/(1024 / 1469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (36086537 / 100000000) (360865371 / 1000000000) (Real.log (1469 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1469 / 1024) = -Real.log (1024 / 1469) := by
    rw [show ((1469 / 1024) : ℝ) = ((1024 / 1469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (35635583 / 62500000) ≤ -Real.log (579 / 1024) ∧
    -Real.log (579 / 1024) ≤ (570169329 / 1000000000) := by
  have h := checkLog_sound (w := (445 / 1603)) (n := 12)
    (lo := (35635583 / 62500000)) (hi := (570169329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 579) = 1/(579 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-570169329 / 1000000000) (-35635583 / 62500000) (Real.log (579 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (180228423 / 500000000) ≤ -Real.log (2560 / 3671) ∧
    -Real.log (2560 / 3671) ≤ (360456847 / 1000000000) := by
  have h := checkLog_sound (w := (1111 / 6231)) (n := 12)
    (lo := (180228423 / 500000000)) (hi := (360456847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3671 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3671 / 2560) = 1/(2560 / 3671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (180228423 / 500000000) (360456847 / 1000000000) (Real.log (3671 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3671 / 2560) = -Real.log (2560 / 3671) := by
    rw [show ((3671 / 2560) : ℝ) = ((2560 / 3671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (113826719 / 200000000) ≤ -Real.log (1449 / 2560) ∧
    -Real.log (1449 / 2560) ≤ (142283399 / 250000000) := by
  have h := checkLog_sound (w := (1111 / 4009)) (n := 12)
    (lo := (113826719 / 200000000)) (hi := (142283399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1449) = 1/(1449 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-142283399 / 250000000) (-113826719 / 200000000) (Real.log (1449 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67409437 / 250000000) ≤ -Real.log (100000 / 130949) ∧
    -Real.log (100000 / 130949) ≤ (269637749 / 1000000000) := by
  have h := checkLog_sound (w := (30949 / 230949)) (n := 12)
    (lo := (67409437 / 250000000)) (hi := (269637749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130949 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(130949 / 100000) = 1/(100000 / 130949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67409437 / 250000000) (269637749 / 1000000000) (Real.log (130949 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (130949 / 100000) = -Real.log (100000 / 130949) := by
    rw [show ((130949 / 100000) : ℝ) = ((100000 / 130949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (370324823 / 1000000000) ≤ -Real.log (69051 / 100000) ∧
    -Real.log (69051 / 100000) ≤ (46290603 / 125000000) := by
  have h := checkLog_sound (w := (30949 / 169051)) (n := 12)
    (lo := (370324823 / 1000000000)) (hi := (46290603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 69051) = 1/(69051 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-46290603 / 125000000) (-370324823 / 1000000000) (Real.log (69051 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (527273 / 1953125) ≤ -Real.log (1000000 / 1309917) ∧
    -Real.log (1000000 / 1309917) ≤ (269963777 / 1000000000) := by
  have h := checkLog_sound (w := (309917 / 2309917)) (n := 12)
    (lo := (527273 / 1953125)) (hi := (269963777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1309917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1309917 / 1000000) = 1/(1000000 / 1309917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (527273 / 1953125) (269963777 / 1000000000) (Real.log (1309917 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1309917 / 1000000) = -Real.log (1000000 / 1309917) := by
    rw [show ((1309917 / 1000000) : ℝ) = ((1000000 / 1309917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (185471699 / 500000000) ≤ -Real.log (690083 / 1000000) ∧
    -Real.log (690083 / 1000000) ≤ (370943399 / 1000000000) := by
  have h := checkLog_sound (w := (309917 / 1690083)) (n := 12)
    (lo := (185471699 / 500000000)) (hi := (370943399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 690083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 690083) = 1/(690083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-370943399 / 1000000000) (-185471699 / 500000000) (Real.log (690083 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (202780831 / 1000000000) ≤ -Real.log (250000 / 306201) ∧
    -Real.log (250000 / 306201) ≤ (6336901 / 31250000) := by
  have h := checkLog_sound (w := (56201 / 556201)) (n := 12)
    (lo := (202780831 / 1000000000)) (hi := (6336901 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306201 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306201 / 250000) = 1/(250000 / 306201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (202780831 / 1000000000) (6336901 / 31250000) (Real.log (306201 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (306201 / 250000) = -Real.log (250000 / 306201) := by
    rw [show ((306201 / 250000) : ℝ) = ((250000 / 306201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (127319689 / 500000000) ≤ -Real.log (193799 / 250000) ∧
    -Real.log (193799 / 250000) ≤ (254639379 / 1000000000) := by
  have h := checkLog_sound (w := (56201 / 443799)) (n := 12)
    (lo := (127319689 / 500000000)) (hi := (254639379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193799) = 1/(193799 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-254639379 / 1000000000) (-127319689 / 500000000) (Real.log (193799 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (203047777 / 1000000000) ≤ -Real.log (1000000 / 1225131) ∧
    -Real.log (1000000 / 1225131) ≤ (101523889 / 500000000) := by
  have h := checkLog_sound (w := (225131 / 2225131)) (n := 12)
    (lo := (203047777 / 1000000000)) (hi := (101523889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225131 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225131 / 1000000) = 1/(1000000 / 1225131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (203047777 / 1000000000) (101523889 / 500000000) (Real.log (1225131 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1225131 / 1000000) = -Real.log (1000000 / 1225131) := by
    rw [show ((1225131 / 1000000) : ℝ) = ((1000000 / 1225131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (15941331 / 62500000) ≤ -Real.log (774869 / 1000000) ∧
    -Real.log (774869 / 1000000) ≤ (255061297 / 1000000000) := by
  have h := checkLog_sound (w := (225131 / 1774869)) (n := 12)
    (lo := (15941331 / 62500000)) (hi := (255061297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774869) = 1/(774869 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-255061297 / 1000000000) (-15941331 / 62500000) (Real.log (774869 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (159990643 / 250000000) ≤ -Real.log (125000000000 / 237051237491) ∧
    -Real.log (125000000000 / 237051237491) ≤ (639962573 / 1000000000) := by
  have h := checkLog_sound (w := (112051237491 / 362051237491)) (n := 12)
    (lo := (159990643 / 250000000)) (hi := (639962573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237051237491 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237051237491 / 125000000000) = 1/(125000000000 / 237051237491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (159990643 / 250000000) (639962573 / 1000000000) (Real.log (237051237491 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (237051237491 / 125000000000) = -Real.log (125000000000 / 237051237491) := by
    rw [show ((237051237491 / 125000000000) : ℝ) = ((125000000000 / 237051237491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (25636287 / 40000000) ≤ -Real.log (125000000000 / 237275262541) ∧
    -Real.log (125000000000 / 237275262541) ≤ (80113397 / 125000000) := by
  have h := checkLog_sound (w := (112275262541 / 362275262541)) (n := 12)
    (lo := (25636287 / 40000000)) (hi := (80113397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237275262541 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237275262541 / 125000000000) = 1/(125000000000 / 237275262541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (25636287 / 40000000) (80113397 / 125000000) (Real.log (237275262541 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (237275262541 / 125000000000) = -Real.log (125000000000 / 237275262541) := by
    rw [show ((237275262541 / 125000000000) : ℝ) = ((125000000000 / 237275262541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (457420209 / 1000000000) ≤ -Real.log (50000000000 / 78999633641) ∧
    -Real.log (50000000000 / 78999633641) ≤ (45742021 / 100000000) := by
  have h := checkLog_sound (w := (28999633641 / 128999633641)) (n := 12)
    (lo := (457420209 / 1000000000)) (hi := (45742021 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78999633641 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78999633641 / 50000000000) = 1/(50000000000 / 78999633641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (457420209 / 1000000000) (45742021 / 100000000) (Real.log (78999633641 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (78999633641 / 50000000000) = -Real.log (50000000000 / 78999633641) := by
    rw [show ((78999633641 / 50000000000) : ℝ) = ((50000000000 / 78999633641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (458109073 / 1000000000) ≤ -Real.log (250000000000 / 395270361829) ∧
    -Real.log (250000000000 / 395270361829) ≤ (229054537 / 500000000) := by
  have h := checkLog_sound (w := (145270361829 / 645270361829)) (n := 12)
    (lo := (458109073 / 1000000000)) (hi := (229054537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395270361829 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395270361829 / 250000000000) = 1/(250000000000 / 395270361829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (458109073 / 1000000000) (229054537 / 500000000) (Real.log (395270361829 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (395270361829 / 250000000000) = -Real.log (250000000000 / 395270361829) := by
    rw [show ((395270361829 / 250000000000) : ℝ) = ((250000000000 / 395270361829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0415

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0416Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0416
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

theorem reflection_log_1_neg : (98191197 / 500000000) ≤ -Real.log (5120 / 6231) ∧
    -Real.log (5120 / 6231) ≤ (39276479 / 200000000) := by
  have h := checkLog_sound (w := (1111 / 11351)) (n := 12)
    (lo := (98191197 / 500000000)) (hi := (39276479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6231 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6231 / 5120) = 1/(5120 / 6231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (98191197 / 500000000) (39276479 / 200000000) (Real.log (6231 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6231 / 5120) = -Real.log (5120 / 6231) := by
    rw [show ((6231 / 5120) : ℝ) = ((5120 / 6231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (48922521 / 200000000) ≤ -Real.log (4009 / 5120) ∧
    -Real.log (4009 / 5120) ≤ (122306303 / 500000000) := by
  have h := checkLog_sound (w := (1111 / 9129)) (n := 12)
    (lo := (48922521 / 200000000)) (hi := (122306303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4009) = 1/(4009 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122306303 / 500000000) (-48922521 / 200000000) (Real.log (4009 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (196141633 / 1000000000) ≤ -Real.log (10240 / 12459) ∧
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


theorem reflection_log_3 : Bounds (196141633 / 1000000000) (98070817 / 500000000) (Real.log (12459 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12459 / 10240) = -Real.log (10240 / 12459) := by
    rw [show ((12459 / 10240) : ℝ) = ((10240 / 12459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (244238517 / 1000000000) ≤ -Real.log (8021 / 10240) ∧
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


theorem reflection_log_4 : Bounds (-122119259 / 500000000) (-244238517 / 1000000000) (Real.log (8021 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (180228423 / 500000000) ≤ -Real.log (2560 / 3671) ∧
    -Real.log (2560 / 3671) ≤ (360456847 / 1000000000) := by
  have h := checkLog_sound (w := (1111 / 6231)) (n := 12)
    (lo := (180228423 / 500000000)) (hi := (360456847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3671 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3671 / 2560) = 1/(2560 / 3671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (180228423 / 500000000) (360456847 / 1000000000) (Real.log (3671 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3671 / 2560) = -Real.log (2560 / 3671) := by
    rw [show ((3671 / 2560) : ℝ) = ((2560 / 3671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (113826719 / 200000000) ≤ -Real.log (1449 / 2560) ∧
    -Real.log (1449 / 2560) ≤ (142283399 / 250000000) := by
  have h := checkLog_sound (w := (1111 / 4009)) (n := 12)
    (lo := (113826719 / 200000000)) (hi := (142283399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1449) = 1/(1449 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-142283399 / 250000000) (-113826719 / 200000000) (Real.log (1449 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (180024077 / 500000000) ≤ -Real.log (5120 / 7339) ∧
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


theorem reflection_log_7 : Bounds (180024077 / 500000000) (72009631 / 200000000) (Real.log (7339 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7339 / 5120) = -Real.log (5120 / 7339) := by
    rw [show ((7339 / 5120) : ℝ) = ((5120 / 7339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (568098933 / 1000000000) ≤ -Real.log (2901 / 5120) ∧
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


theorem reflection_log_8 : Bounds (-284049467 / 500000000) (-568098933 / 1000000000) (Real.log (2901 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (269313141 / 1000000000) ≤ -Real.log (200000 / 261813) ∧
    -Real.log (200000 / 261813) ≤ (134656571 / 500000000) := by
  have h := checkLog_sound (w := (61813 / 461813)) (n := 12)
    (lo := (269313141 / 1000000000)) (hi := (134656571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261813 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261813 / 200000) = 1/(200000 / 261813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (269313141 / 1000000000) (134656571 / 500000000) (Real.log (261813 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (261813 / 200000) = -Real.log (200000 / 261813) := by
    rw [show ((261813 / 200000) : ℝ) = ((200000 / 261813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (184854763 / 500000000) ≤ -Real.log (138187 / 200000) ∧
    -Real.log (138187 / 200000) ≤ (369709527 / 1000000000) := by
  have h := checkLog_sound (w := (61813 / 338187)) (n := 12)
    (lo := (184854763 / 500000000)) (hi := (369709527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 138187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 138187) = 1/(138187 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-369709527 / 1000000000) (-184854763 / 500000000) (Real.log (138187 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16852407 / 62500000) ≤ -Real.log (1000000 / 1309491) ∧
    -Real.log (1000000 / 1309491) ≤ (269638513 / 1000000000) := by
  have h := checkLog_sound (w := (309491 / 2309491)) (n := 12)
    (lo := (16852407 / 62500000)) (hi := (269638513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1309491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1309491 / 1000000) = 1/(1000000 / 1309491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16852407 / 62500000) (269638513 / 1000000000) (Real.log (1309491 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1309491 / 1000000) = -Real.log (1000000 / 1309491) := by
    rw [show ((1309491 / 1000000) : ℝ) = ((1000000 / 1309491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1446587 / 3906250) ≤ -Real.log (690509 / 1000000) ∧
    -Real.log (690509 / 1000000) ≤ (370326273 / 1000000000) := by
  have h := checkLog_sound (w := (309491 / 1690509)) (n := 12)
    (lo := (1446587 / 3906250)) (hi := (370326273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 690509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 690509) = 1/(690509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-370326273 / 1000000000) (-1446587 / 3906250) (Real.log (690509 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (20251463 / 100000000) ≤ -Real.log (500000 / 612239) ∧
    -Real.log (500000 / 612239) ≤ (202514631 / 1000000000) := by
  have h := checkLog_sound (w := (112239 / 1112239)) (n := 12)
    (lo := (20251463 / 100000000)) (hi := (202514631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612239 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612239 / 500000) = 1/(500000 / 612239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (20251463 / 100000000) (202514631 / 1000000000) (Real.log (612239 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (612239 / 500000) = -Real.log (500000 / 612239) := by
    rw [show ((612239 / 500000) : ℝ) = ((500000 / 612239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (254218927 / 1000000000) ≤ -Real.log (387761 / 500000) ∧
    -Real.log (387761 / 500000) ≤ (15888683 / 62500000) := by
  have h := checkLog_sound (w := (112239 / 887761)) (n := 12)
    (lo := (254218927 / 1000000000)) (hi := (15888683 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387761) = 1/(387761 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-15888683 / 62500000) (-254218927 / 1000000000) (Real.log (387761 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (202781647 / 1000000000) ≤ -Real.log (200000 / 244961) ∧
    -Real.log (200000 / 244961) ≤ (12673853 / 62500000) := by
  have h := checkLog_sound (w := (44961 / 444961)) (n := 12)
    (lo := (202781647 / 1000000000)) (hi := (12673853 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244961 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244961 / 200000) = 1/(200000 / 244961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (202781647 / 1000000000) (12673853 / 62500000) (Real.log (244961 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (244961 / 200000) = -Real.log (200000 / 244961) := by
    rw [show ((244961 / 200000) : ℝ) = ((200000 / 244961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (63660167 / 250000000) ≤ -Real.log (155039 / 200000) ∧
    -Real.log (155039 / 200000) ≤ (254640669 / 1000000000) := by
  have h := checkLog_sound (w := (44961 / 355039)) (n := 12)
    (lo := (63660167 / 250000000)) (hi := (254640669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 155039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 155039) = 1/(155039 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-254640669 / 1000000000) (-63660167 / 250000000) (Real.log (155039 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (159755667 / 250000000) ≤ -Real.log (125000000000 / 236828536693) ∧
    -Real.log (125000000000 / 236828536693) ≤ (639022669 / 1000000000) := by
  have h := checkLog_sound (w := (111828536693 / 361828536693)) (n := 12)
    (lo := (159755667 / 250000000)) (hi := (639022669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236828536693 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236828536693 / 125000000000) = 1/(125000000000 / 236828536693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (159755667 / 250000000) (639022669 / 1000000000) (Real.log (236828536693 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (236828536693 / 125000000000) = -Real.log (125000000000 / 236828536693) := by
    rw [show ((236828536693 / 125000000000) : ℝ) = ((125000000000 / 236828536693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (39997799 / 62500000) ≤ -Real.log (250000000000 / 474103523633) ∧
    -Real.log (250000000000 / 474103523633) ≤ (127992957 / 200000000) := by
  have h := checkLog_sound (w := (224103523633 / 724103523633)) (n := 12)
    (lo := (39997799 / 62500000)) (hi := (127992957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((474103523633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(474103523633 / 250000000000) = 1/(250000000000 / 474103523633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (39997799 / 62500000) (127992957 / 200000000) (Real.log (474103523633 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (474103523633 / 250000000000) = -Real.log (250000000000 / 474103523633) := by
    rw [show ((474103523633 / 250000000000) : ℝ) = ((250000000000 / 474103523633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (228366779 / 500000000) ≤ -Real.log (100000000000 / 157890814187) ∧
    -Real.log (100000000000 / 157890814187) ≤ (456733559 / 1000000000) := by
  have h := checkLog_sound (w := (57890814187 / 257890814187)) (n := 12)
    (lo := (228366779 / 500000000)) (hi := (456733559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157890814187 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157890814187 / 100000000000) = 1/(100000000000 / 157890814187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (228366779 / 500000000) (456733559 / 1000000000) (Real.log (157890814187 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (157890814187 / 100000000000) = -Real.log (100000000000 / 157890814187) := by
    rw [show ((157890814187 / 100000000000) : ℝ) = ((100000000000 / 157890814187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (114355579 / 250000000) ≤ -Real.log (62500000000 / 98749750063) ∧
    -Real.log (62500000000 / 98749750063) ≤ (457422317 / 1000000000) := by
  have h := checkLog_sound (w := (36249750063 / 161249750063)) (n := 12)
    (lo := (114355579 / 250000000)) (hi := (457422317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98749750063 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98749750063 / 62500000000) = 1/(62500000000 / 98749750063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (114355579 / 250000000) (457422317 / 1000000000) (Real.log (98749750063 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (98749750063 / 62500000000) = -Real.log (62500000000 / 98749750063) := by
    rw [show ((98749750063 / 62500000000) : ℝ) = ((62500000000 / 98749750063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0416

end


