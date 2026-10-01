-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0079Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0079Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:17:35.355217+00:00
-- url     : https://prove2.me/theorems/6f1b8a81-c306-449a-a20a-dc55867e5a12
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0079Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0080Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0079Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0080Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0081Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0082Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0083Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0084Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0085Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0086Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0079Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0080Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0081Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0082Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0083Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0084Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0085Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0086Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0079Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0080Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0081Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0082Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0083Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0084Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0085Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0086Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0079Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0080Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0081Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0082Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0083Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0084Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0085Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0086Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0079Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0079
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

theorem reflection_log_1_neg : (350876917 / 1000000000) ≤ -Real.log (640 / 909) ∧
    -Real.log (640 / 909) ≤ (175438459 / 500000000) := by
  have h := checkLog_sound (w := (269 / 1549)) (n := 12)
    (lo := (350876917 / 1000000000)) (hi := (175438459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909 / 640) = 1/(640 / 909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (350876917 / 1000000000) (175438459 / 500000000) (Real.log (909 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (909 / 640) = -Real.log (640 / 909) := by
    rw [show ((909 / 640) : ℝ) = ((640 / 909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (545266113 / 1000000000) ≤ -Real.log (371 / 640) ∧
    -Real.log (371 / 640) ≤ (272633057 / 500000000) := by
  have h := checkLog_sound (w := (269 / 1011)) (n := 12)
    (lo := (545266113 / 1000000000)) (hi := (272633057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 371) = 1/(371 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-272633057 / 500000000) (-545266113 / 1000000000) (Real.log (371 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (175025747 / 500000000) ≤ -Real.log (2560 / 3633) ∧
    -Real.log (2560 / 3633) ≤ (70010299 / 200000000) := by
  have h := checkLog_sound (w := (1073 / 6193)) (n := 12)
    (lo := (175025747 / 500000000)) (hi := (70010299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3633 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3633 / 2560) = 1/(2560 / 3633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (175025747 / 500000000) (70010299 / 200000000) (Real.log (3633 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3633 / 2560) = -Real.log (2560 / 3633) := by
    rw [show ((3633 / 2560) : ℝ) = ((2560 / 3633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (543246591 / 1000000000) ≤ -Real.log (1487 / 2560) ∧
    -Real.log (1487 / 2560) ≤ (2122057 / 3906250) := by
  have h := checkLog_sound (w := (1073 / 4047)) (n := 12)
    (lo := (543246591 / 1000000000)) (hi := (2122057 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1487) = 1/(1487 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2122057 / 3906250) (-543246591 / 1000000000) (Real.log (1487 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (610105187 / 1000000000) ≤ -Real.log (320 / 589) ∧
    -Real.log (320 / 589) ≤ (152526297 / 250000000) := by
  have h := checkLog_sound (w := (269 / 909)) (n := 12)
    (lo := (610105187 / 1000000000)) (hi := (152526297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589 / 320) = 1/(320 / 589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (610105187 / 1000000000) (152526297 / 250000000) (Real.log (589 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (589 / 320) = -Real.log (320 / 589) := by
    rw [show ((589 / 320) : ℝ) = ((320 / 589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1836495361 / 1000000000) ≤ -Real.log (51 / 320) ∧
    -Real.log (51 / 320) ≤ (459123841 / 250000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 51) = 1/(51 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-459123841 / 250000000) (-1836495361 / 1000000000) (Real.log (51 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (608831031 / 1000000000) ≤ -Real.log (1280 / 2353) ∧
    -Real.log (1280 / 2353) ≤ (76103879 / 125000000) := by
  have h := checkLog_sound (w := (1073 / 3633)) (n := 12)
    (lo := (608831031 / 1000000000)) (hi := (76103879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2353 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2353 / 1280) = 1/(1280 / 2353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (608831031 / 1000000000) (76103879 / 125000000) (Real.log (2353 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2353 / 1280) = -Real.log (1280 / 2353) := by
    rw [show ((2353 / 1280) : ℝ) = ((1280 / 2353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (910948281 / 500000000) ≤ -Real.log (207 / 1280) ∧
    -Real.log (207 / 1280) ≤ (364379313 / 200000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 207) = 1/(207 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-364379313 / 200000000) (-910948281 / 500000000) (Real.log (207 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (240879321 / 500000000) ≤ -Real.log (1000000 / 1618919) ∧
    -Real.log (1000000 / 1618919) ≤ (481758643 / 1000000000) := by
  have h := checkLog_sound (w := (618919 / 2618919)) (n := 12)
    (lo := (240879321 / 500000000)) (hi := (481758643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1618919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1618919 / 1000000) = 1/(1000000 / 1618919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (240879321 / 500000000) (481758643 / 1000000000) (Real.log (1618919 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1618919 / 1000000) = -Real.log (1000000 / 1618919) := by
    rw [show ((1618919 / 1000000) : ℝ) = ((1000000 / 1618919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (964743327 / 1000000000) ≤ -Real.log (381081 / 1000000) ∧
    -Real.log (381081 / 1000000) ≤ (964743329 / 1000000000) := by
  have h := checkLog_sound (w := (118919 / 881081)) (n := 12)
    (lo := (271596147 / 1000000000)) (hi := (67899037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381081) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 381081) = 1/(381081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-964743329 / 1000000000) (-964743327 / 1000000000) (Real.log (381081 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (241488307 / 500000000) ≤ -Real.log (250000 / 405223) ∧
    -Real.log (250000 / 405223) ≤ (96595323 / 200000000) := by
  have h := checkLog_sound (w := (155223 / 655223)) (n := 12)
    (lo := (241488307 / 500000000)) (hi := (96595323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405223 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(405223 / 250000) = 1/(250000 / 405223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (241488307 / 500000000) (96595323 / 200000000) (Real.log (405223 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (405223 / 250000) = -Real.log (250000 / 405223) := by
    rw [show ((405223 / 250000) : ℝ) = ((250000 / 405223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (969934153 / 1000000000) ≤ -Real.log (94777 / 250000) ∧
    -Real.log (94777 / 250000) ≤ (193986831 / 200000000) := by
  have h := checkLog_sound (w := (30223 / 219777)) (n := 12)
    (lo := (276786973 / 1000000000)) (hi := (138393487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94777) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 94777) = 1/(94777 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-193986831 / 200000000) (-969934153 / 1000000000) (Real.log (94777 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (79630487 / 200000000) ≤ -Real.log (1000000 / 1489071) ∧
    -Real.log (1000000 / 1489071) ≤ (99538109 / 250000000) := by
  have h := checkLog_sound (w := (489071 / 2489071)) (n := 12)
    (lo := (79630487 / 200000000)) (hi := (99538109 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489071 / 1000000) = 1/(1000000 / 1489071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (79630487 / 200000000) (99538109 / 250000000) (Real.log (1489071 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1489071 / 1000000) = -Real.log (1000000 / 1489071) := by
    rw [show ((1489071 / 1000000) : ℝ) = ((1000000 / 1489071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (671524641 / 1000000000) ≤ -Real.log (510929 / 1000000) ∧
    -Real.log (510929 / 1000000) ≤ (335762321 / 500000000) := by
  have h := checkLog_sound (w := (489071 / 1510929)) (n := 12)
    (lo := (671524641 / 1000000000)) (hi := (335762321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 510929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 510929) = 1/(510929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-335762321 / 500000000) (-671524641 / 1000000000) (Real.log (510929 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (39944167 / 100000000) ≤ -Real.log (62500 / 93187) ∧
    -Real.log (62500 / 93187) ≤ (399441671 / 1000000000) := by
  have h := checkLog_sound (w := (30687 / 155687)) (n := 12)
    (lo := (39944167 / 100000000)) (hi := (399441671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93187 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93187 / 62500) = 1/(62500 / 93187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (39944167 / 100000000) (399441671 / 1000000000) (Real.log (93187 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (93187 / 62500) = -Real.log (62500 / 93187) := by
    rw [show ((93187 / 62500) : ℝ) = ((62500 / 93187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (135058309 / 200000000) ≤ -Real.log (31813 / 62500) ∧
    -Real.log (31813 / 62500) ≤ (337645773 / 500000000) := by
  have h := checkLog_sound (w := (30687 / 94313)) (n := 12)
    (lo := (135058309 / 200000000)) (hi := (337645773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 31813) = 1/(31813 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-337645773 / 500000000) (-135058309 / 200000000) (Real.log (31813 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1446501969 / 1000000000) ≤ -Real.log (500000000000 / 2124114033499) ∧
    -Real.log (500000000000 / 2124114033499) ≤ (361625493 / 250000000) := by
  have h := checkLog_sound (w := (124114033499 / 4124114033499)) (n := 12)
    (lo := (60207609 / 1000000000)) (hi := (6020761 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2124114033499 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2124114033499 / 2000000000000) = 1/(500000000000 / 2124114033499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1446501969 / 1000000000) (361625493 / 250000000) (Real.log (2124114033499 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2124114033499 / 500000000000) = -Real.log (500000000000 / 2124114033499) := by
    rw [show ((2124114033499 / 500000000000) : ℝ) = ((500000000000 / 2124114033499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1452910767 / 1000000000) ≤ -Real.log (50000000000 / 213777076717) ∧
    -Real.log (50000000000 / 213777076717) ≤ (145291077 / 100000000) := by
  have h := checkLog_sound (w := (13777076717 / 413777076717)) (n := 12)
    (lo := (66616407 / 1000000000)) (hi := (8327051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213777076717 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(213777076717 / 200000000000) = 1/(50000000000 / 213777076717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1452910767 / 1000000000) (145291077 / 100000000) (Real.log (213777076717 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (213777076717 / 50000000000) = -Real.log (50000000000 / 213777076717) := by
    rw [show ((213777076717 / 50000000000) : ℝ) = ((50000000000 / 213777076717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (267419269 / 250000000) ≤ -Real.log (500000000000 / 1457219104807) ∧
    -Real.log (500000000000 / 1457219104807) ≤ (534838539 / 500000000) := by
  have h := checkLog_sound (w := (457219104807 / 2457219104807)) (n := 12)
    (lo := (47066237 / 125000000)) (hi := (376529897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457219104807 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1457219104807 / 1000000000000) = 1/(500000000000 / 1457219104807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (267419269 / 250000000) (534838539 / 500000000) (Real.log (1457219104807 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1457219104807 / 500000000000) = -Real.log (500000000000 / 1457219104807) := by
    rw [show ((1457219104807 / 500000000000) : ℝ) = ((500000000000 / 1457219104807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (214946643 / 200000000) ≤ -Real.log (15625000000 / 45768927011) ∧
    -Real.log (15625000000 / 45768927011) ≤ (1074733217 / 1000000000) := by
  have h := checkLog_sound (w := (14518927011 / 77018927011)) (n := 12)
    (lo := (76317207 / 200000000)) (hi := (95396509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45768927011 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(45768927011 / 31250000000) = 1/(15625000000 / 45768927011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (214946643 / 200000000) (1074733217 / 1000000000) (Real.log (45768927011 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (45768927011 / 15625000000) = -Real.log (15625000000 / 45768927011) := by
    rw [show ((45768927011 / 15625000000) : ℝ) = ((15625000000 / 45768927011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0079

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0080Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0080
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

theorem reflection_log_1_neg : (175025747 / 500000000) ≤ -Real.log (2560 / 3633) ∧
    -Real.log (2560 / 3633) ≤ (70010299 / 200000000) := by
  have h := checkLog_sound (w := (1073 / 6193)) (n := 12)
    (lo := (175025747 / 500000000)) (hi := (70010299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3633 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3633 / 2560) = 1/(2560 / 3633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (175025747 / 500000000) (70010299 / 200000000) (Real.log (3633 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3633 / 2560) = -Real.log (2560 / 3633) := by
    rw [show ((3633 / 2560) : ℝ) = ((2560 / 3633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (543246591 / 1000000000) ≤ -Real.log (1487 / 2560) ∧
    -Real.log (1487 / 2560) ≤ (2122057 / 3906250) := by
  have h := checkLog_sound (w := (1073 / 4047)) (n := 12)
    (lo := (543246591 / 1000000000)) (hi := (2122057 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1487) = 1/(1487 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2122057 / 3906250) (-543246591 / 1000000000) (Real.log (1487 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (349225389 / 1000000000) ≤ -Real.log (256 / 363) ∧
    -Real.log (256 / 363) ≤ (34922539 / 100000000) := by
  have h := checkLog_sound (w := (107 / 619)) (n := 12)
    (lo := (349225389 / 1000000000)) (hi := (34922539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363 / 256) = 1/(256 / 363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (349225389 / 1000000000) (34922539 / 100000000) (Real.log (363 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (363 / 256) = -Real.log (256 / 363) := by
    rw [show ((363 / 256) : ℝ) = ((256 / 363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (270615569 / 500000000) ≤ -Real.log (149 / 256) ∧
    -Real.log (149 / 256) ≤ (541231139 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 405)) (n := 12)
    (lo := (270615569 / 500000000)) (hi := (541231139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 149) = 1/(149 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-541231139 / 1000000000) (-270615569 / 500000000) (Real.log (149 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (608831031 / 1000000000) ≤ -Real.log (1280 / 2353) ∧
    -Real.log (1280 / 2353) ≤ (76103879 / 125000000) := by
  have h := checkLog_sound (w := (1073 / 3633)) (n := 12)
    (lo := (608831031 / 1000000000)) (hi := (76103879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2353 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2353 / 1280) = 1/(1280 / 2353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (608831031 / 1000000000) (76103879 / 125000000) (Real.log (2353 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2353 / 1280) = -Real.log (1280 / 2353) := by
    rw [show ((2353 / 1280) : ℝ) = ((1280 / 2353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (910948281 / 500000000) ≤ -Real.log (207 / 1280) ∧
    -Real.log (207 / 1280) ≤ (364379313 / 200000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 207) = 1/(207 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-364379313 / 200000000) (-910948281 / 500000000) (Real.log (207 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2430221 / 4000000) ≤ -Real.log (128 / 235) ∧
    -Real.log (128 / 235) ≤ (607555251 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 363)) (n := 12)
    (lo := (2430221 / 4000000)) (hi := (607555251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235 / 128) = 1/(128 / 235) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2430221 / 4000000) (607555251 / 1000000000) (Real.log (235 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (235 / 128) = -Real.log (128 / 235) := by
    rw [show ((235 / 128) : ℝ) = ((128 / 235) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (72300313 / 40000000) ≤ -Real.log (21 / 128) ∧
    -Real.log (21 / 128) ≤ (451876957 / 250000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 21) = 1/(21 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-451876957 / 250000000) (-72300313 / 40000000) (Real.log (21 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (96108579 / 200000000) ≤ -Real.log (125000 / 202119) ∧
    -Real.log (125000 / 202119) ≤ (30033931 / 62500000) := by
  have h := checkLog_sound (w := (77119 / 327119)) (n := 12)
    (lo := (96108579 / 200000000)) (hi := (30033931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202119 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202119 / 125000) = 1/(125000 / 202119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (96108579 / 200000000) (30033931 / 62500000) (Real.log (202119 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (202119 / 125000) = -Real.log (125000 / 202119) := by
    rw [show ((202119 / 125000) : ℝ) = ((125000 / 202119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (95959497 / 100000000) ≤ -Real.log (47881 / 125000) ∧
    -Real.log (47881 / 125000) ≤ (239898743 / 250000000) := by
  have h := checkLog_sound (w := (14619 / 110381)) (n := 12)
    (lo := (26644779 / 100000000)) (hi := (266447791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47881) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 47881) = 1/(47881 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-239898743 / 250000000) (-95959497 / 100000000) (Real.log (47881 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (24087963 / 50000000) ≤ -Real.log (25000 / 40473) ∧
    -Real.log (25000 / 40473) ≤ (481759261 / 1000000000) := by
  have h := checkLog_sound (w := (15473 / 65473)) (n := 12)
    (lo := (24087963 / 50000000)) (hi := (481759261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40473 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40473 / 25000) = 1/(25000 / 40473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (24087963 / 50000000) (481759261 / 1000000000) (Real.log (40473 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (40473 / 25000) = -Real.log (25000 / 40473) := by
    rw [show ((40473 / 25000) : ℝ) = ((25000 / 40473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (964745951 / 1000000000) ≤ -Real.log (9527 / 25000) ∧
    -Real.log (9527 / 25000) ≤ (964745953 / 1000000000) := by
  have h := checkLog_sound (w := (2973 / 22027)) (n := 12)
    (lo := (271598771 / 1000000000)) (hi := (67899693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9527) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 9527) = 1/(9527 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-964745953 / 1000000000) (-964745951 / 1000000000) (Real.log (9527 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (99216897 / 250000000) ≤ -Real.log (1000000 / 1487159) ∧
    -Real.log (1000000 / 1487159) ≤ (396867589 / 1000000000) := by
  have h := checkLog_sound (w := (487159 / 2487159)) (n := 12)
    (lo := (99216897 / 250000000)) (hi := (396867589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1487159 / 1000000) = 1/(1000000 / 1487159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (99216897 / 250000000) (396867589 / 1000000000) (Real.log (1487159 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1487159 / 1000000) = -Real.log (1000000 / 1487159) := by
    rw [show ((1487159 / 1000000) : ℝ) = ((1000000 / 1487159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (667789423 / 1000000000) ≤ -Real.log (512841 / 1000000) ∧
    -Real.log (512841 / 1000000) ≤ (41736839 / 62500000) := by
  have h := checkLog_sound (w := (487159 / 1512841)) (n := 12)
    (lo := (667789423 / 1000000000)) (hi := (41736839 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 512841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 512841) = 1/(512841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-41736839 / 62500000) (-667789423 / 1000000000) (Real.log (512841 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (398153107 / 1000000000) ≤ -Real.log (62500 / 93067) ∧
    -Real.log (62500 / 93067) ≤ (99538277 / 250000000) := by
  have h := checkLog_sound (w := (30567 / 155567)) (n := 12)
    (lo := (398153107 / 1000000000)) (hi := (99538277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93067 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93067 / 62500) = 1/(62500 / 93067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (398153107 / 1000000000) (99538277 / 250000000) (Real.log (93067 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (93067 / 62500) = -Real.log (62500 / 93067) := by
    rw [show ((93067 / 62500) : ℝ) = ((62500 / 93067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (335763299 / 500000000) ≤ -Real.log (31933 / 62500) ∧
    -Real.log (31933 / 62500) ≤ (671526599 / 1000000000) := by
  have h := checkLog_sound (w := (30567 / 94433)) (n := 12)
    (lo := (335763299 / 500000000)) (hi := (671526599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 31933) = 1/(31933 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-671526599 / 1000000000) (-335763299 / 500000000) (Real.log (31933 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (288027573 / 200000000) ≤ -Real.log (100000000000 / 422127775109) ∧
    -Real.log (100000000000 / 422127775109) ≤ (360034467 / 250000000) := by
  have h := checkLog_sound (w := (22127775109 / 822127775109)) (n := 12)
    (lo := (10768701 / 200000000)) (hi := (26921753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422127775109 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(422127775109 / 400000000000) = 1/(100000000000 / 422127775109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (288027573 / 200000000) (360034467 / 250000000) (Real.log (422127775109 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (422127775109 / 100000000000) = -Real.log (100000000000 / 422127775109) := by
    rw [show ((422127775109 / 100000000000) : ℝ) = ((100000000000 / 422127775109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1446505211 / 1000000000) ≤ -Real.log (125000000000 / 531030229873) ∧
    -Real.log (125000000000 / 531030229873) ≤ (723252607 / 500000000) := by
  have h := checkLog_sound (w := (31030229873 / 1031030229873)) (n := 12)
    (lo := (60210851 / 1000000000)) (hi := (15052713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((531030229873 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(531030229873 / 500000000000) = 1/(125000000000 / 531030229873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1446505211 / 1000000000) (723252607 / 500000000) (Real.log (531030229873 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (531030229873 / 125000000000) = -Real.log (125000000000 / 531030229873) := by
    rw [show ((531030229873 / 125000000000) : ℝ) = ((125000000000 / 531030229873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1064657011 / 1000000000) ≤ -Real.log (125000000000 / 362480525153) ∧
    -Real.log (125000000000 / 362480525153) ≤ (1064657013 / 1000000000) := by
  have h := checkLog_sound (w := (112480525153 / 612480525153)) (n := 12)
    (lo := (371509831 / 1000000000)) (hi := (46438729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362480525153 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(362480525153 / 250000000000) = 1/(125000000000 / 362480525153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1064657011 / 1000000000) (1064657013 / 1000000000) (Real.log (362480525153 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (362480525153 / 125000000000) = -Real.log (125000000000 / 362480525153) := by
    rw [show ((362480525153 / 125000000000) : ℝ) = ((125000000000 / 362480525153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (213935941 / 200000000) ≤ -Real.log (250000000000 / 728611467761) ∧
    -Real.log (250000000000 / 728611467761) ≤ (1069679707 / 1000000000) := by
  have h := checkLog_sound (w := (228611467761 / 1228611467761)) (n := 12)
    (lo := (15061301 / 40000000)) (hi := (188266263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728611467761 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(728611467761 / 500000000000) = 1/(250000000000 / 728611467761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (213935941 / 200000000) (1069679707 / 1000000000) (Real.log (728611467761 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (728611467761 / 250000000000) = -Real.log (250000000000 / 728611467761) := by
    rw [show ((728611467761 / 250000000000) : ℝ) = ((250000000000 / 728611467761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0080

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0081Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0081
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

theorem reflection_log_1_neg : (349225389 / 1000000000) ≤ -Real.log (256 / 363) ∧
    -Real.log (256 / 363) ≤ (34922539 / 100000000) := by
  have h := checkLog_sound (w := (107 / 619)) (n := 12)
    (lo := (349225389 / 1000000000)) (hi := (34922539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363 / 256) = 1/(256 / 363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (349225389 / 1000000000) (34922539 / 100000000) (Real.log (363 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (363 / 256) = -Real.log (256 / 363) := by
    rw [show ((363 / 256) : ℝ) = ((256 / 363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (270615569 / 500000000) ≤ -Real.log (149 / 256) ∧
    -Real.log (149 / 256) ≤ (541231139 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 405)) (n := 12)
    (lo := (270615569 / 500000000)) (hi := (541231139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 149) = 1/(149 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-541231139 / 1000000000) (-270615569 / 500000000) (Real.log (149 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (348398601 / 1000000000) ≤ -Real.log (2560 / 3627) ∧
    -Real.log (2560 / 3627) ≤ (174199301 / 500000000) := by
  have h := checkLog_sound (w := (1067 / 6187)) (n := 12)
    (lo := (348398601 / 1000000000)) (hi := (174199301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3627 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3627 / 2560) = 1/(2560 / 3627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (348398601 / 1000000000) (174199301 / 500000000) (Real.log (3627 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3627 / 2560) = -Real.log (2560 / 3627) := by
    rw [show ((3627 / 2560) : ℝ) = ((2560 / 3627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (539219739 / 1000000000) ≤ -Real.log (1493 / 2560) ∧
    -Real.log (1493 / 2560) ≤ (26960987 / 50000000) := by
  have h := checkLog_sound (w := (1067 / 4053)) (n := 12)
    (lo := (539219739 / 1000000000)) (hi := (26960987 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1493) = 1/(1493 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-26960987 / 50000000) (-539219739 / 1000000000) (Real.log (1493 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2430221 / 4000000) ≤ -Real.log (128 / 235) ∧
    -Real.log (128 / 235) ≤ (607555251 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 363)) (n := 12)
    (lo := (2430221 / 4000000)) (hi := (607555251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235 / 128) = 1/(128 / 235) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2430221 / 4000000) (607555251 / 1000000000) (Real.log (235 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (235 / 128) = -Real.log (128 / 235) := by
    rw [show ((235 / 128) : ℝ) = ((128 / 235) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (72300313 / 40000000) ≤ -Real.log (21 / 128) ∧
    -Real.log (21 / 128) ≤ (451876957 / 250000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 21) = 1/(21 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-451876957 / 250000000) (-72300313 / 40000000) (Real.log (21 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (303138919 / 500000000) ≤ -Real.log (1280 / 2347) ∧
    -Real.log (1280 / 2347) ≤ (606277839 / 1000000000) := by
  have h := checkLog_sound (w := (1067 / 3627)) (n := 12)
    (lo := (303138919 / 500000000)) (hi := (606277839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2347 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2347 / 1280) = 1/(1280 / 2347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (303138919 / 500000000) (606277839 / 1000000000) (Real.log (2347 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2347 / 1280) = -Real.log (1280 / 2347) := by
    rw [show ((2347 / 1280) : ℝ) = ((1280 / 2347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (179332319 / 100000000) ≤ -Real.log (213 / 1280) ∧
    -Real.log (213 / 1280) ≤ (1793323193 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 213) = 1/(213 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1793323193 / 1000000000) (-179332319 / 100000000) (Real.log (213 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (95865629 / 200000000) ≤ -Real.log (1000000 / 1614989) ∧
    -Real.log (1000000 / 1614989) ≤ (239664073 / 500000000) := by
  have h := checkLog_sound (w := (614989 / 2614989)) (n := 12)
    (lo := (95865629 / 200000000)) (hi := (239664073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1614989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1614989 / 1000000) = 1/(1000000 / 1614989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (95865629 / 200000000) (239664073 / 500000000) (Real.log (1614989 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1614989 / 1000000) = -Real.log (1000000 / 1614989) := by
    rw [show ((1614989 / 1000000) : ℝ) = ((1000000 / 1614989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (954483373 / 1000000000) ≤ -Real.log (385011 / 1000000) ∧
    -Real.log (385011 / 1000000) ≤ (7635867 / 8000000) := by
  have h := checkLog_sound (w := (114989 / 885011)) (n := 12)
    (lo := (261336193 / 1000000000)) (hi := (130668097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 385011) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 385011) = 1/(385011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7635867 / 8000000) (-954483373 / 1000000000) (Real.log (385011 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (240271757 / 500000000) ≤ -Real.log (1000000 / 1616953) ∧
    -Real.log (1000000 / 1616953) ≤ (96108703 / 200000000) := by
  have h := checkLog_sound (w := (616953 / 2616953)) (n := 12)
    (lo := (240271757 / 500000000)) (hi := (96108703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1616953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1616953 / 1000000) = 1/(1000000 / 1616953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (240271757 / 500000000) (96108703 / 200000000) (Real.log (1616953 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1616953 / 1000000) = -Real.log (1000000 / 1616953) := by
    rw [show ((1616953 / 1000000) : ℝ) = ((1000000 / 1616953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (959597581 / 1000000000) ≤ -Real.log (383047 / 1000000) ∧
    -Real.log (383047 / 1000000) ≤ (959597583 / 1000000000) := by
  have h := checkLog_sound (w := (116953 / 883047)) (n := 12)
    (lo := (266450401 / 1000000000)) (hi := (133225201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383047) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 383047) = 1/(383047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-959597583 / 1000000000) (-959597581 / 1000000000) (Real.log (383047 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (197793237 / 500000000) ≤ -Real.log (200000 / 297051) ∧
    -Real.log (200000 / 297051) ≤ (15823459 / 40000000) := by
  have h := checkLog_sound (w := (97051 / 497051)) (n := 12)
    (lo := (197793237 / 500000000)) (hi := (15823459 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297051 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297051 / 200000) = 1/(200000 / 297051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (197793237 / 500000000) (15823459 / 40000000) (Real.log (297051 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (297051 / 200000) = -Real.log (200000 / 297051) := by
    rw [show ((297051 / 200000) : ℝ) = ((200000 / 297051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (332041823 / 500000000) ≤ -Real.log (102949 / 200000) ∧
    -Real.log (102949 / 200000) ≤ (664083647 / 1000000000) := by
  have h := checkLog_sound (w := (97051 / 302949)) (n := 12)
    (lo := (332041823 / 500000000)) (hi := (664083647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 102949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 102949) = 1/(102949 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-664083647 / 1000000000) (-332041823 / 500000000) (Real.log (102949 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19843413 / 50000000) ≤ -Real.log (25000 / 37179) ∧
    -Real.log (25000 / 37179) ≤ (396868261 / 1000000000) := by
  have h := checkLog_sound (w := (12179 / 62179)) (n := 12)
    (lo := (19843413 / 50000000)) (hi := (396868261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37179 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37179 / 25000) = 1/(25000 / 37179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19843413 / 50000000) (396868261 / 1000000000) (Real.log (37179 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (37179 / 25000) = -Real.log (25000 / 37179) := by
    rw [show ((37179 / 25000) : ℝ) = ((25000 / 37179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (667791373 / 1000000000) ≤ -Real.log (12821 / 25000) ∧
    -Real.log (12821 / 25000) ≤ (333895687 / 500000000) := by
  have h := checkLog_sound (w := (12179 / 37821)) (n := 12)
    (lo := (667791373 / 1000000000)) (hi := (333895687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 12821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 12821) = 1/(12821 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-333895687 / 500000000) (-667791373 / 1000000000) (Real.log (12821 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (716905759 / 500000000) ≤ -Real.log (25000000000 / 104866419401) ∧
    -Real.log (25000000000 / 104866419401) ≤ (1433811521 / 1000000000) := by
  have h := checkLog_sound (w := (4866419401 / 204866419401)) (n := 12)
    (lo := (23758579 / 500000000)) (hi := (47517159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104866419401 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(104866419401 / 100000000000) = 1/(25000000000 / 104866419401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (716905759 / 500000000) (1433811521 / 1000000000) (Real.log (104866419401 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (104866419401 / 25000000000) = -Real.log (25000000000 / 104866419401) := by
    rw [show ((104866419401 / 25000000000) : ℝ) = ((25000000000 / 104866419401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (720070547 / 500000000) ≤ -Real.log (500000000000 / 2110645690999) ∧
    -Real.log (500000000000 / 2110645690999) ≤ (1440141097 / 1000000000) := by
  have h := checkLog_sound (w := (110645690999 / 4110645690999)) (n := 12)
    (lo := (26923367 / 500000000)) (hi := (10769347 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2110645690999 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2110645690999 / 2000000000000) = 1/(500000000000 / 2110645690999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (720070547 / 500000000) (1440141097 / 1000000000) (Real.log (2110645690999 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2110645690999 / 500000000000) = -Real.log (500000000000 / 2110645690999) := by
    rw [show ((2110645690999 / 500000000000) : ℝ) = ((500000000000 / 2110645690999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (26491753 / 25000000) ≤ -Real.log (100000000000 / 288541899387) ∧
    -Real.log (100000000000 / 288541899387) ≤ (529835061 / 500000000) := by
  have h := checkLog_sound (w := (88541899387 / 488541899387)) (n := 12)
    (lo := (18326147 / 50000000)) (hi := (366522941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288541899387 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(288541899387 / 200000000000) = 1/(100000000000 / 288541899387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (26491753 / 25000000) (529835061 / 500000000) (Real.log (288541899387 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (288541899387 / 100000000000) = -Real.log (100000000000 / 288541899387) := by
    rw [show ((288541899387 / 100000000000) : ℝ) = ((100000000000 / 288541899387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1064659633 / 1000000000) ≤ -Real.log (15625000000 / 45310184463) ∧
    -Real.log (15625000000 / 45310184463) ≤ (212931927 / 200000000) := by
  have h := checkLog_sound (w := (14060184463 / 76560184463)) (n := 12)
    (lo := (371512453 / 1000000000)) (hi := (185756227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45310184463 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(45310184463 / 31250000000) = 1/(15625000000 / 45310184463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1064659633 / 1000000000) (212931927 / 200000000) (Real.log (45310184463 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (45310184463 / 15625000000) = -Real.log (15625000000 / 45310184463) := by
    rw [show ((45310184463 / 15625000000) : ℝ) = ((15625000000 / 45310184463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0081

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0082Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0082
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

theorem reflection_log_1_neg : (348398601 / 1000000000) ≤ -Real.log (2560 / 3627) ∧
    -Real.log (2560 / 3627) ≤ (174199301 / 500000000) := by
  have h := checkLog_sound (w := (1067 / 6187)) (n := 12)
    (lo := (348398601 / 1000000000)) (hi := (174199301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3627 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3627 / 2560) = 1/(2560 / 3627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (348398601 / 1000000000) (174199301 / 500000000) (Real.log (3627 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3627 / 2560) = -Real.log (2560 / 3627) := by
    rw [show ((3627 / 2560) : ℝ) = ((2560 / 3627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (539219739 / 1000000000) ≤ -Real.log (1493 / 2560) ∧
    -Real.log (1493 / 2560) ≤ (26960987 / 50000000) := by
  have h := checkLog_sound (w := (1067 / 4053)) (n := 12)
    (lo := (539219739 / 1000000000)) (hi := (26960987 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1493) = 1/(1493 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-26960987 / 50000000) (-539219739 / 1000000000) (Real.log (1493 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (347571129 / 1000000000) ≤ -Real.log (320 / 453) ∧
    -Real.log (320 / 453) ≤ (34757113 / 100000000) := by
  have h := checkLog_sound (w := (133 / 773)) (n := 12)
    (lo := (347571129 / 1000000000)) (hi := (34757113 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((453 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(453 / 320) = 1/(320 / 453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (347571129 / 1000000000) (34757113 / 100000000) (Real.log (453 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (453 / 320) = -Real.log (320 / 453) := by
    rw [show ((453 / 320) : ℝ) = ((320 / 453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (268606189 / 500000000) ≤ -Real.log (187 / 320) ∧
    -Real.log (187 / 320) ≤ (537212379 / 1000000000) := by
  have h := checkLog_sound (w := (133 / 507)) (n := 12)
    (lo := (268606189 / 500000000)) (hi := (537212379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 187) = 1/(187 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-537212379 / 1000000000) (-268606189 / 500000000) (Real.log (187 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (303138919 / 500000000) ≤ -Real.log (1280 / 2347) ∧
    -Real.log (1280 / 2347) ≤ (606277839 / 1000000000) := by
  have h := checkLog_sound (w := (1067 / 3627)) (n := 12)
    (lo := (303138919 / 500000000)) (hi := (606277839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2347 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2347 / 1280) = 1/(1280 / 2347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (303138919 / 500000000) (606277839 / 1000000000) (Real.log (2347 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2347 / 1280) = -Real.log (1280 / 2347) := by
    rw [show ((2347 / 1280) : ℝ) = ((1280 / 2347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (179332319 / 100000000) ≤ -Real.log (213 / 1280) ∧
    -Real.log (213 / 1280) ≤ (1793323193 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 213) = 1/(213 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1793323193 / 1000000000) (-179332319 / 100000000) (Real.log (213 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (604998793 / 1000000000) ≤ -Real.log (160 / 293) ∧
    -Real.log (160 / 293) ≤ (302499397 / 500000000) := by
  have h := checkLog_sound (w := (133 / 453)) (n := 12)
    (lo := (604998793 / 1000000000)) (hi := (302499397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293 / 160) = 1/(160 / 293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (604998793 / 1000000000) (302499397 / 500000000) (Real.log (293 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (293 / 160) = -Real.log (160 / 293) := by
    rw [show ((293 / 160) : ℝ) = ((160 / 293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (444834237 / 250000000) ≤ -Real.log (27 / 160) ∧
    -Real.log (27 / 160) ≤ (1779336951 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 27) = 1/(27 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1779336951 / 1000000000) (-444834237 / 250000000) (Real.log (27 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (478114397 / 1000000000) ≤ -Real.log (100000 / 161303) ∧
    -Real.log (100000 / 161303) ≤ (239057199 / 500000000) := by
  have h := checkLog_sound (w := (61303 / 261303)) (n := 12)
    (lo := (478114397 / 1000000000)) (hi := (239057199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161303 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161303 / 100000) = 1/(100000 / 161303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (478114397 / 1000000000) (239057199 / 500000000) (Real.log (161303 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (161303 / 100000) = -Real.log (100000 / 161303) := by
    rw [show ((161303 / 100000) : ℝ) = ((100000 / 161303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (949408107 / 1000000000) ≤ -Real.log (38697 / 100000) ∧
    -Real.log (38697 / 100000) ≤ (949408109 / 1000000000) := by
  have h := checkLog_sound (w := (11303 / 88697)) (n := 12)
    (lo := (256260927 / 1000000000)) (hi := (4004077 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38697) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 38697) = 1/(38697 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-949408109 / 1000000000) (-949408107 / 1000000000) (Real.log (38697 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (119832191 / 250000000) ≤ -Real.log (100000 / 161499) ∧
    -Real.log (100000 / 161499) ≤ (95865753 / 200000000) := by
  have h := checkLog_sound (w := (61499 / 261499)) (n := 12)
    (lo := (119832191 / 250000000)) (hi := (95865753 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161499 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161499 / 100000) = 1/(100000 / 161499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (119832191 / 250000000) (95865753 / 200000000) (Real.log (161499 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (161499 / 100000) = -Real.log (100000 / 161499) := by
    rw [show ((161499 / 100000) : ℝ) = ((100000 / 161499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (95448597 / 100000000) ≤ -Real.log (38501 / 100000) ∧
    -Real.log (38501 / 100000) ≤ (238621493 / 250000000) := by
  have h := checkLog_sound (w := (11499 / 88501)) (n := 12)
    (lo := (26133879 / 100000000)) (hi := (261338791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 38501) = 1/(38501 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-238621493 / 250000000) (-95448597 / 100000000) (Real.log (38501 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (98577109 / 250000000) ≤ -Real.log (500000 / 741679) ∧
    -Real.log (500000 / 741679) ≤ (394308437 / 1000000000) := by
  have h := checkLog_sound (w := (241679 / 1241679)) (n := 12)
    (lo := (98577109 / 250000000)) (hi := (394308437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741679 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741679 / 500000) = 1/(500000 / 741679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (98577109 / 250000000) (394308437 / 1000000000) (Real.log (741679 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (741679 / 500000) = -Real.log (500000 / 741679) := by
    rw [show ((741679 / 500000) : ℝ) = ((500000 / 741679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (6604051 / 10000000) ≤ -Real.log (258321 / 500000) ∧
    -Real.log (258321 / 500000) ≤ (660405101 / 1000000000) := by
  have h := checkLog_sound (w := (241679 / 758321)) (n := 12)
    (lo := (6604051 / 10000000)) (hi := (660405101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 258321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 258321) = 1/(258321 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-660405101 / 1000000000) (-6604051 / 10000000) (Real.log (258321 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (395587147 / 1000000000) ≤ -Real.log (125000 / 185657) ∧
    -Real.log (125000 / 185657) ≤ (98896787 / 250000000) := by
  have h := checkLog_sound (w := (60657 / 310657)) (n := 12)
    (lo := (395587147 / 1000000000)) (hi := (98896787 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185657 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185657 / 125000) = 1/(125000 / 185657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (395587147 / 1000000000) (98896787 / 250000000) (Real.log (185657 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (185657 / 125000) = -Real.log (125000 / 185657) := by
    rw [show ((185657 / 125000) : ℝ) = ((125000 / 185657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (664085589 / 1000000000) ≤ -Real.log (64343 / 125000) ∧
    -Real.log (64343 / 125000) ≤ (66408559 / 100000000) := by
  have h := checkLog_sound (w := (60657 / 189343)) (n := 12)
    (lo := (664085589 / 1000000000)) (hi := (66408559 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 64343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 64343) = 1/(64343 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-66408559 / 100000000) (-664085589 / 1000000000) (Real.log (64343 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (285504501 / 200000000) ≤ -Real.log (500000000000 / 2084179652169) ∧
    -Real.log (500000000000 / 2084179652169) ≤ (356880627 / 250000000) := by
  have h := checkLog_sound (w := (84179652169 / 4084179652169)) (n := 12)
    (lo := (8245629 / 200000000)) (hi := (20614073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2084179652169 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2084179652169 / 2000000000000) = 1/(500000000000 / 2084179652169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (285504501 / 200000000) (356880627 / 250000000) (Real.log (2084179652169 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2084179652169 / 500000000000) = -Real.log (500000000000 / 2084179652169) := by
    rw [show ((2084179652169 / 500000000000) : ℝ) = ((500000000000 / 2084179652169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (716907367 / 500000000) ≤ -Real.log (500000000000 / 2097335134153) ∧
    -Real.log (500000000000 / 2097335134153) ≤ (1433814737 / 1000000000) := by
  have h := checkLog_sound (w := (97335134153 / 4097335134153)) (n := 12)
    (lo := (23760187 / 500000000)) (hi := (380163 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2097335134153 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2097335134153 / 2000000000000) = 1/(500000000000 / 2097335134153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (716907367 / 500000000) (1433814737 / 1000000000) (Real.log (2097335134153 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2097335134153 / 500000000000) = -Real.log (500000000000 / 2097335134153) := by
    rw [show ((2097335134153 / 500000000000) : ℝ) = ((500000000000 / 2097335134153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16479899 / 15625000) ≤ -Real.log (4000000000 / 11484610233) ∧
    -Real.log (4000000000 / 11484610233) ≤ (527356769 / 500000000) := by
  have h := checkLog_sound (w := (3484610233 / 19484610233)) (n := 12)
    (lo := (90391589 / 250000000)) (hi := (361566357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11484610233 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11484610233 / 8000000000) = 1/(4000000000 / 11484610233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (16479899 / 15625000) (527356769 / 500000000) (Real.log (11484610233 / 4000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11484610233 / 4000000000) = -Real.log (4000000000 / 11484610233) := by
    rw [show ((11484610233 / 4000000000) : ℝ) = ((4000000000 / 11484610233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (33114773 / 31250000) ≤ -Real.log (500000000000 / 1442713271063) ∧
    -Real.log (500000000000 / 1442713271063) ≤ (529836369 / 500000000) := by
  have h := checkLog_sound (w := (442713271063 / 2442713271063)) (n := 12)
    (lo := (91631389 / 250000000)) (hi := (366525557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1442713271063 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1442713271063 / 1000000000000) = 1/(500000000000 / 1442713271063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (33114773 / 31250000) (529836369 / 500000000) (Real.log (1442713271063 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1442713271063 / 500000000000) = -Real.log (500000000000 / 1442713271063) := by
    rw [show ((1442713271063 / 500000000000) : ℝ) = ((500000000000 / 1442713271063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0082

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0083Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0083
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

theorem reflection_log_1_neg : (347571129 / 1000000000) ≤ -Real.log (320 / 453) ∧
    -Real.log (320 / 453) ≤ (34757113 / 100000000) := by
  have h := checkLog_sound (w := (133 / 773)) (n := 12)
    (lo := (347571129 / 1000000000)) (hi := (34757113 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((453 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(453 / 320) = 1/(320 / 453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (347571129 / 1000000000) (34757113 / 100000000) (Real.log (453 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (453 / 320) = -Real.log (320 / 453) := by
    rw [show ((453 / 320) : ℝ) = ((320 / 453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (268606189 / 500000000) ≤ -Real.log (187 / 320) ∧
    -Real.log (187 / 320) ≤ (537212379 / 1000000000) := by
  have h := checkLog_sound (w := (133 / 507)) (n := 12)
    (lo := (268606189 / 500000000)) (hi := (537212379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 187) = 1/(187 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-537212379 / 1000000000) (-268606189 / 500000000) (Real.log (187 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (86685743 / 250000000) ≤ -Real.log (2560 / 3621) ∧
    -Real.log (2560 / 3621) ≤ (346742973 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 6181)) (n := 12)
    (lo := (86685743 / 250000000)) (hi := (346742973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3621 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3621 / 2560) = 1/(2560 / 3621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (86685743 / 250000000) (346742973 / 1000000000) (Real.log (3621 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3621 / 2560) = -Real.log (2560 / 3621) := by
    rw [show ((3621 / 2560) : ℝ) = ((2560 / 3621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (535209039 / 1000000000) ≤ -Real.log (1499 / 2560) ∧
    -Real.log (1499 / 2560) ≤ (6690113 / 12500000) := by
  have h := checkLog_sound (w := (1061 / 4059)) (n := 12)
    (lo := (535209039 / 1000000000)) (hi := (6690113 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1499) = 1/(1499 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6690113 / 12500000) (-535209039 / 1000000000) (Real.log (1499 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (604998793 / 1000000000) ≤ -Real.log (160 / 293) ∧
    -Real.log (160 / 293) ≤ (302499397 / 500000000) := by
  have h := checkLog_sound (w := (133 / 453)) (n := 12)
    (lo := (604998793 / 1000000000)) (hi := (302499397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293 / 160) = 1/(160 / 293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (604998793 / 1000000000) (302499397 / 500000000) (Real.log (293 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (293 / 160) = -Real.log (160 / 293) := by
    rw [show ((293 / 160) : ℝ) = ((160 / 293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (444834237 / 250000000) ≤ -Real.log (27 / 160) ∧
    -Real.log (27 / 160) ≤ (1779336951 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 27) = 1/(27 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1779336951 / 1000000000) (-444834237 / 250000000) (Real.log (27 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (60371811 / 100000000) ≤ -Real.log (1280 / 2341) ∧
    -Real.log (1280 / 2341) ≤ (603718111 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 3621)) (n := 12)
    (lo := (60371811 / 100000000)) (hi := (603718111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2341 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2341 / 1280) = 1/(1280 / 2341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (60371811 / 100000000) (603718111 / 1000000000) (Real.log (2341 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2341 / 1280) = -Real.log (1280 / 2341) := by
    rw [show ((2341 / 1280) : ℝ) = ((1280 / 2341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (14124349 / 8000000) ≤ -Real.log (219 / 1280) ∧
    -Real.log (219 / 1280) ≤ (441385907 / 250000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 219) = 1/(219 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-441385907 / 250000000) (-14124349 / 8000000) (Real.log (219 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (476901037 / 1000000000) ≤ -Real.log (500000 / 805537) ∧
    -Real.log (500000 / 805537) ≤ (238450519 / 500000000) := by
  have h := checkLog_sound (w := (305537 / 1305537)) (n := 12)
    (lo := (476901037 / 1000000000)) (hi := (238450519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805537 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805537 / 500000) = 1/(500000 / 805537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (476901037 / 1000000000) (238450519 / 500000000) (Real.log (805537 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (805537 / 500000) = -Real.log (500000 / 805537) := by
    rw [show ((805537 / 500000) : ℝ) = ((500000 / 805537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (118045773 / 125000000) ≤ -Real.log (194463 / 500000) ∧
    -Real.log (194463 / 500000) ≤ (472183093 / 500000000) := by
  have h := checkLog_sound (w := (55537 / 444463)) (n := 12)
    (lo := (62804751 / 250000000)) (hi := (50243801 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 194463) = 1/(194463 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-472183093 / 500000000) (-118045773 / 125000000) (Real.log (194463 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (478115017 / 1000000000) ≤ -Real.log (1000000 / 1613031) ∧
    -Real.log (1000000 / 1613031) ≤ (239057509 / 500000000) := by
  have h := checkLog_sound (w := (613031 / 2613031)) (n := 12)
    (lo := (478115017 / 1000000000)) (hi := (239057509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1613031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1613031 / 1000000) = 1/(1000000 / 1613031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (478115017 / 1000000000) (239057509 / 500000000) (Real.log (1613031 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1613031 / 1000000) = -Real.log (1000000 / 1613031) := by
    rw [show ((1613031 / 1000000) : ℝ) = ((1000000 / 1613031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (949410691 / 1000000000) ≤ -Real.log (386969 / 1000000) ∧
    -Real.log (386969 / 1000000) ≤ (949410693 / 1000000000) := by
  have h := checkLog_sound (w := (113031 / 886969)) (n := 12)
    (lo := (256263511 / 1000000000)) (hi := (32032939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386969) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 386969) = 1/(386969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-949410693 / 1000000000) (-949410691 / 1000000000) (Real.log (386969 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (393034163 / 1000000000) ≤ -Real.log (1000000 / 1481469) ∧
    -Real.log (1000000 / 1481469) ≤ (98258541 / 250000000) := by
  have h := checkLog_sound (w := (481469 / 2481469)) (n := 12)
    (lo := (393034163 / 1000000000)) (hi := (98258541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1481469 / 1000000) = 1/(1000000 / 1481469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (393034163 / 1000000000) (98258541 / 250000000) (Real.log (1481469 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1481469 / 1000000) = -Real.log (1000000 / 1481469) := by
    rw [show ((1481469 / 1000000) : ℝ) = ((1000000 / 1481469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (131351093 / 200000000) ≤ -Real.log (518531 / 1000000) ∧
    -Real.log (518531 / 1000000) ≤ (328377733 / 500000000) := by
  have h := checkLog_sound (w := (481469 / 1518531)) (n := 12)
    (lo := (131351093 / 200000000)) (hi := (328377733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 518531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 518531) = 1/(518531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-328377733 / 500000000) (-131351093 / 200000000) (Real.log (518531 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (39430911 / 100000000) ≤ -Real.log (1000000 / 1483359) ∧
    -Real.log (1000000 / 1483359) ≤ (394309111 / 1000000000) := by
  have h := checkLog_sound (w := (483359 / 2483359)) (n := 12)
    (lo := (39430911 / 100000000)) (hi := (394309111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1483359 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1483359 / 1000000) = 1/(1000000 / 1483359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (39430911 / 100000000) (394309111 / 1000000000) (Real.log (1483359 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1483359 / 1000000) = -Real.log (1000000 / 1483359) := by
    rw [show ((1483359 / 1000000) : ℝ) = ((1000000 / 1483359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (165101759 / 250000000) ≤ -Real.log (516641 / 1000000) ∧
    -Real.log (516641 / 1000000) ≤ (660407037 / 1000000000) := by
  have h := checkLog_sound (w := (483359 / 1516641)) (n := 12)
    (lo := (165101759 / 250000000)) (hi := (660407037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 516641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 516641) = 1/(516641 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-660407037 / 1000000000) (-165101759 / 250000000) (Real.log (516641 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1421267221 / 1000000000) ≤ -Real.log (31250000000 / 129448950443) ∧
    -Real.log (31250000000 / 129448950443) ≤ (177658403 / 125000000) := by
  have h := checkLog_sound (w := (4448950443 / 254448950443)) (n := 12)
    (lo := (34972861 / 1000000000)) (hi := (17486431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129448950443 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(129448950443 / 125000000000) = 1/(31250000000 / 129448950443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1421267221 / 1000000000) (177658403 / 125000000) (Real.log (129448950443 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (129448950443 / 31250000000) = -Real.log (31250000000 / 129448950443) := by
    rw [show ((129448950443 / 31250000000) : ℝ) = ((31250000000 / 129448950443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1427525709 / 1000000000) ≤ -Real.log (125000000000 / 521046582543) ∧
    -Real.log (125000000000 / 521046582543) ≤ (89220357 / 62500000) := by
  have h := checkLog_sound (w := (21046582543 / 1021046582543)) (n := 12)
    (lo := (41231349 / 1000000000)) (hi := (824627 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((521046582543 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(521046582543 / 500000000000) = 1/(125000000000 / 521046582543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1427525709 / 1000000000) (89220357 / 62500000) (Real.log (521046582543 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (521046582543 / 125000000000) = -Real.log (125000000000 / 521046582543) := by
    rw [show ((521046582543 / 125000000000) : ℝ) = ((125000000000 / 521046582543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1049789627 / 1000000000) ≤ -Real.log (500000000000 / 1428525006219) ∧
    -Real.log (500000000000 / 1428525006219) ≤ (1049789629 / 1000000000) := by
  have h := checkLog_sound (w := (428525006219 / 2428525006219)) (n := 12)
    (lo := (356642447 / 1000000000)) (hi := (22290153 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1428525006219 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1428525006219 / 1000000000000) = 1/(500000000000 / 1428525006219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1049789627 / 1000000000) (1049789629 / 1000000000) (Real.log (1428525006219 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1428525006219 / 500000000000) = -Real.log (500000000000 / 1428525006219) := by
    rw [show ((1428525006219 / 500000000000) : ℝ) = ((500000000000 / 1428525006219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (527358073 / 500000000) ≤ -Real.log (500000000000 / 1435580025589) ∧
    -Real.log (500000000000 / 1435580025589) ≤ (263679037 / 250000000) := by
  have h := checkLog_sound (w := (435580025589 / 2435580025589)) (n := 12)
    (lo := (180784483 / 500000000)) (hi := (361568967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1435580025589 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1435580025589 / 1000000000000) = 1/(500000000000 / 1435580025589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (527358073 / 500000000) (263679037 / 250000000) (Real.log (1435580025589 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1435580025589 / 500000000000) = -Real.log (500000000000 / 1435580025589) := by
    rw [show ((1435580025589 / 500000000000) : ℝ) = ((500000000000 / 1435580025589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0083

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0084Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0084
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

theorem reflection_log_1_neg : (86685743 / 250000000) ≤ -Real.log (2560 / 3621) ∧
    -Real.log (2560 / 3621) ≤ (346742973 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 6181)) (n := 12)
    (lo := (86685743 / 250000000)) (hi := (346742973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3621 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3621 / 2560) = 1/(2560 / 3621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (86685743 / 250000000) (346742973 / 1000000000) (Real.log (3621 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3621 / 2560) = -Real.log (2560 / 3621) := by
    rw [show ((3621 / 2560) : ℝ) = ((2560 / 3621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (535209039 / 1000000000) ≤ -Real.log (1499 / 2560) ∧
    -Real.log (1499 / 2560) ≤ (6690113 / 12500000) := by
  have h := checkLog_sound (w := (1061 / 4059)) (n := 12)
    (lo := (535209039 / 1000000000)) (hi := (6690113 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1499) = 1/(1499 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6690113 / 12500000) (-535209039 / 1000000000) (Real.log (1499 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (21619633 / 62500000) ≤ -Real.log (1280 / 1809) ∧
    -Real.log (1280 / 1809) ≤ (345914129 / 1000000000) := by
  have h := checkLog_sound (w := (529 / 3089)) (n := 12)
    (lo := (21619633 / 62500000)) (hi := (345914129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1809 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1809 / 1280) = 1/(1280 / 1809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (21619633 / 62500000) (345914129 / 1000000000) (Real.log (1809 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1809 / 1280) = -Real.log (1280 / 1809) := by
    rw [show ((1809 / 1280) : ℝ) = ((1280 / 1809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (106641941 / 200000000) ≤ -Real.log (751 / 1280) ∧
    -Real.log (751 / 1280) ≤ (266604853 / 500000000) := by
  have h := checkLog_sound (w := (529 / 2031)) (n := 12)
    (lo := (106641941 / 200000000)) (hi := (266604853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 751) = 1/(751 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-266604853 / 500000000) (-106641941 / 200000000) (Real.log (751 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (60371811 / 100000000) ≤ -Real.log (1280 / 2341) ∧
    -Real.log (1280 / 2341) ≤ (603718111 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 3621)) (n := 12)
    (lo := (60371811 / 100000000)) (hi := (603718111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2341 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2341 / 1280) = 1/(1280 / 2341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (60371811 / 100000000) (603718111 / 1000000000) (Real.log (2341 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2341 / 1280) = -Real.log (1280 / 2341) := by
    rw [show ((2341 / 1280) : ℝ) = ((1280 / 2341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (14124349 / 8000000) ≤ -Real.log (219 / 1280) ∧
    -Real.log (219 / 1280) ≤ (441385907 / 250000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 219) = 1/(219 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-441385907 / 250000000) (-14124349 / 8000000) (Real.log (219 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (120487157 / 200000000) ≤ -Real.log (640 / 1169) ∧
    -Real.log (640 / 1169) ≤ (301217893 / 500000000) := by
  have h := checkLog_sound (w := (529 / 1809)) (n := 12)
    (lo := (120487157 / 200000000)) (hi := (301217893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169 / 640) = 1/(640 / 1169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (120487157 / 200000000) (301217893 / 500000000) (Real.log (1169 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1169 / 640) = -Real.log (640 / 1169) := by
    rw [show ((1169 / 640) : ℝ) = ((640 / 1169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1751937973 / 1000000000) ≤ -Real.log (111 / 640) ∧
    -Real.log (111 / 640) ≤ (218992247 / 125000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 111) = 1/(111 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-218992247 / 125000000) (-1751937973 / 1000000000) (Real.log (111 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29730543 / 62500000) ≤ -Real.log (500000 / 804561) ∧
    -Real.log (500000 / 804561) ≤ (475688689 / 1000000000) := by
  have h := checkLog_sound (w := (304561 / 1304561)) (n := 12)
    (lo := (29730543 / 62500000)) (hi := (475688689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804561 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804561 / 500000) = 1/(500000 / 804561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29730543 / 62500000) (475688689 / 1000000000) (Real.log (804561 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (804561 / 500000) = -Real.log (500000 / 804561) := by
    rw [show ((804561 / 500000) : ℝ) = ((500000 / 804561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (939359787 / 1000000000) ≤ -Real.log (195439 / 500000) ∧
    -Real.log (195439 / 500000) ≤ (939359789 / 1000000000) := by
  have h := checkLog_sound (w := (54561 / 445439)) (n := 12)
    (lo := (246212607 / 1000000000)) (hi := (480884 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195439) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 195439) = 1/(195439 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-939359789 / 1000000000) (-939359787 / 1000000000) (Real.log (195439 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (238450829 / 500000000) ≤ -Real.log (40000 / 64443) ∧
    -Real.log (40000 / 64443) ≤ (476901659 / 1000000000) := by
  have h := checkLog_sound (w := (24443 / 104443)) (n := 12)
    (lo := (238450829 / 500000000)) (hi := (476901659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64443 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64443 / 40000) = 1/(40000 / 64443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (238450829 / 500000000) (476901659 / 1000000000) (Real.log (64443 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (64443 / 40000) = -Real.log (40000 / 64443) := by
    rw [show ((64443 / 40000) : ℝ) = ((40000 / 64443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (188873751 / 200000000) ≤ -Real.log (15557 / 40000) ∧
    -Real.log (15557 / 40000) ≤ (944368757 / 1000000000) := by
  have h := checkLog_sound (w := (4443 / 35557)) (n := 12)
    (lo := (10048863 / 40000000)) (hi := (31402697 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15557) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 15557) = 1/(15557 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-944368757 / 1000000000) (-188873751 / 200000000) (Real.log (15557 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (195881497 / 500000000) ≤ -Real.log (1000000 / 1479587) ∧
    -Real.log (1000000 / 1479587) ≤ (78352599 / 200000000) := by
  have h := checkLog_sound (w := (479587 / 2479587)) (n := 12)
    (lo := (195881497 / 500000000)) (hi := (78352599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1479587 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1479587 / 1000000) = 1/(1000000 / 1479587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (195881497 / 500000000) (78352599 / 200000000) (Real.log (1479587 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1479587 / 1000000) = -Real.log (1000000 / 1479587) := by
    rw [show ((1479587 / 1000000) : ℝ) = ((1000000 / 1479587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (653132551 / 1000000000) ≤ -Real.log (520413 / 1000000) ∧
    -Real.log (520413 / 1000000) ≤ (81641569 / 125000000) := by
  have h := checkLog_sound (w := (479587 / 1520413)) (n := 12)
    (lo := (653132551 / 1000000000)) (hi := (81641569 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 520413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 520413) = 1/(520413 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-81641569 / 125000000) (-653132551 / 1000000000) (Real.log (520413 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (196517419 / 500000000) ≤ -Real.log (100000 / 148147) ∧
    -Real.log (100000 / 148147) ≤ (393034839 / 1000000000) := by
  have h := checkLog_sound (w := (48147 / 248147)) (n := 12)
    (lo := (196517419 / 500000000)) (hi := (393034839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148147 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148147 / 100000) = 1/(100000 / 148147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (196517419 / 500000000) (393034839 / 1000000000) (Real.log (148147 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (148147 / 100000) = -Real.log (100000 / 148147) := by
    rw [show ((148147 / 100000) : ℝ) = ((100000 / 148147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (656757393 / 1000000000) ≤ -Real.log (51853 / 100000) ∧
    -Real.log (51853 / 100000) ≤ (328378697 / 500000000) := by
  have h := checkLog_sound (w := (48147 / 151853)) (n := 12)
    (lo := (656757393 / 1000000000)) (hi := (328378697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 51853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 51853) = 1/(51853 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-328378697 / 500000000) (-656757393 / 1000000000) (Real.log (51853 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (56601939 / 40000000) ≤ -Real.log (500000000000 / 2058343012397) ∧
    -Real.log (500000000000 / 2058343012397) ≤ (707524239 / 500000000) := by
  have h := checkLog_sound (w := (58343012397 / 4058343012397)) (n := 12)
    (lo := (5750823 / 200000000)) (hi := (7188529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2058343012397 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2058343012397 / 2000000000000) = 1/(500000000000 / 2058343012397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (56601939 / 40000000) (707524239 / 500000000) (Real.log (2058343012397 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2058343012397 / 500000000000) = -Real.log (500000000000 / 2058343012397) := by
    rw [show ((2058343012397 / 500000000000) : ℝ) = ((500000000000 / 2058343012397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (355317603 / 250000000) ≤ -Real.log (500000000000 / 2071189818089) ∧
    -Real.log (500000000000 / 2071189818089) ≤ (284254083 / 200000000) := by
  have h := checkLog_sound (w := (71189818089 / 4071189818089)) (n := 12)
    (lo := (8744013 / 250000000)) (hi := (34976053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2071189818089 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2071189818089 / 2000000000000) = 1/(500000000000 / 2071189818089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (355317603 / 250000000) (284254083 / 200000000) (Real.log (2071189818089 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2071189818089 / 500000000000) = -Real.log (500000000000 / 2071189818089) := by
    rw [show ((2071189818089 / 500000000000) : ℝ) = ((500000000000 / 2071189818089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (522447773 / 500000000) ≤ -Real.log (125000000000 / 355387692083) ∧
    -Real.log (125000000000 / 355387692083) ≤ (261223887 / 250000000) := by
  have h := checkLog_sound (w := (105387692083 / 605387692083)) (n := 12)
    (lo := (175874183 / 500000000)) (hi := (351748367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355387692083 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(355387692083 / 250000000000) = 1/(125000000000 / 355387692083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (522447773 / 500000000) (261223887 / 250000000) (Real.log (355387692083 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (355387692083 / 125000000000) = -Real.log (125000000000 / 355387692083) := by
    rw [show ((355387692083 / 125000000000) : ℝ) = ((125000000000 / 355387692083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1049792231 / 1000000000) ≤ -Real.log (125000000000 / 357132181359) ∧
    -Real.log (125000000000 / 357132181359) ≤ (1049792233 / 1000000000) := by
  have h := checkLog_sound (w := (107132181359 / 607132181359)) (n := 12)
    (lo := (356645051 / 1000000000)) (hi := (89161263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357132181359 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(357132181359 / 250000000000) = 1/(125000000000 / 357132181359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1049792231 / 1000000000) (1049792233 / 1000000000) (Real.log (357132181359 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (357132181359 / 125000000000) = -Real.log (125000000000 / 357132181359) := by
    rw [show ((357132181359 / 125000000000) : ℝ) = ((125000000000 / 357132181359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0084

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0085Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0085
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

theorem reflection_log_1_neg : (21619633 / 62500000) ≤ -Real.log (1280 / 1809) ∧
    -Real.log (1280 / 1809) ≤ (345914129 / 1000000000) := by
  have h := checkLog_sound (w := (529 / 3089)) (n := 12)
    (lo := (21619633 / 62500000)) (hi := (345914129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1809 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1809 / 1280) = 1/(1280 / 1809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (21619633 / 62500000) (345914129 / 1000000000) (Real.log (1809 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1809 / 1280) = -Real.log (1280 / 1809) := by
    rw [show ((1809 / 1280) : ℝ) = ((1280 / 1809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (106641941 / 200000000) ≤ -Real.log (751 / 1280) ∧
    -Real.log (751 / 1280) ≤ (266604853 / 500000000) := by
  have h := checkLog_sound (w := (529 / 2031)) (n := 12)
    (lo := (106641941 / 200000000)) (hi := (266604853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 751) = 1/(751 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-266604853 / 500000000) (-106641941 / 200000000) (Real.log (751 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (345084597 / 1000000000) ≤ -Real.log (512 / 723) ∧
    -Real.log (512 / 723) ≤ (172542299 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1235)) (n := 12)
    (lo := (345084597 / 1000000000)) (hi := (172542299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723 / 512) = 1/(512 / 723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (345084597 / 1000000000) (172542299 / 500000000) (Real.log (723 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (723 / 512) = -Real.log (512 / 723) := by
    rw [show ((723 / 512) : ℝ) = ((512 / 723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (13280359 / 25000000) ≤ -Real.log (301 / 512) ∧
    -Real.log (301 / 512) ≤ (531214361 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 813)) (n := 12)
    (lo := (13280359 / 25000000)) (hi := (531214361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 301) = 1/(301 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-531214361 / 1000000000) (-13280359 / 25000000) (Real.log (301 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (120487157 / 200000000) ≤ -Real.log (640 / 1169) ∧
    -Real.log (640 / 1169) ≤ (301217893 / 500000000) := by
  have h := checkLog_sound (w := (529 / 1809)) (n := 12)
    (lo := (120487157 / 200000000)) (hi := (301217893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169 / 640) = 1/(640 / 1169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (120487157 / 200000000) (301217893 / 500000000) (Real.log (1169 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1169 / 640) = -Real.log (640 / 1169) := by
    rw [show ((1169 / 640) : ℝ) = ((640 / 1169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1751937973 / 1000000000) ≤ -Real.log (111 / 640) ∧
    -Real.log (111 / 640) ≤ (218992247 / 125000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 111) = 1/(111 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-218992247 / 125000000) (-1751937973 / 1000000000) (Real.log (111 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (601151813 / 1000000000) ≤ -Real.log (256 / 467) ∧
    -Real.log (256 / 467) ≤ (300575907 / 500000000) := by
  have h := checkLog_sound (w := (211 / 723)) (n := 12)
    (lo := (601151813 / 1000000000)) (hi := (300575907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((467 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(467 / 256) = 1/(256 / 467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (601151813 / 1000000000) (300575907 / 500000000) (Real.log (467 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (467 / 256) = -Real.log (256 / 467) := by
    rw [show ((467 / 256) : ℝ) = ((256 / 467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1738514953 / 1000000000) ≤ -Real.log (45 / 256) ∧
    -Real.log (45 / 256) ≤ (434628739 / 250000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 45) = 1/(45 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-434628739 / 250000000) (-1738514953 / 1000000000) (Real.log (45 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (474477979 / 1000000000) ≤ -Real.log (40000 / 64287) ∧
    -Real.log (40000 / 64287) ≤ (23723899 / 50000000) := by
  have h := checkLog_sound (w := (24287 / 104287)) (n := 12)
    (lo := (474477979 / 1000000000)) (hi := (23723899 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64287 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64287 / 40000) = 1/(40000 / 64287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (474477979 / 1000000000) (23723899 / 50000000) (Real.log (64287 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (64287 / 40000) = -Real.log (40000 / 64287) := by
    rw [show ((64287 / 40000) : ℝ) = ((40000 / 64287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (467195529 / 500000000) ≤ -Real.log (15713 / 40000) ∧
    -Real.log (15713 / 40000) ≤ (46719553 / 50000000) := by
  have h := checkLog_sound (w := (4287 / 35713)) (n := 12)
    (lo := (120621939 / 500000000)) (hi := (241243879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15713) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 15713) = 1/(15713 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-46719553 / 50000000) (-467195529 / 500000000) (Real.log (15713 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (47568931 / 100000000) ≤ -Real.log (1000000 / 1609123) ∧
    -Real.log (1000000 / 1609123) ≤ (475689311 / 1000000000) := by
  have h := checkLog_sound (w := (609123 / 2609123)) (n := 12)
    (lo := (47568931 / 100000000)) (hi := (475689311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1609123 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1609123 / 1000000) = 1/(1000000 / 1609123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (47568931 / 100000000) (475689311 / 1000000000) (Real.log (1609123 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1609123 / 1000000) = -Real.log (1000000 / 1609123) := by
    rw [show ((1609123 / 1000000) : ℝ) = ((1000000 / 1609123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (187872469 / 200000000) ≤ -Real.log (390877 / 1000000) ∧
    -Real.log (390877 / 1000000) ≤ (939362347 / 1000000000) := by
  have h := checkLog_sound (w := (109123 / 890877)) (n := 12)
    (lo := (49243033 / 200000000)) (hi := (123107583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390877) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 390877) = 1/(390877 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-939362347 / 1000000000) (-187872469 / 200000000) (Real.log (390877 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (78098989 / 200000000) ≤ -Real.log (62500 / 92357) ∧
    -Real.log (62500 / 92357) ≤ (195247473 / 500000000) := by
  have h := checkLog_sound (w := (29857 / 154857)) (n := 12)
    (lo := (78098989 / 200000000)) (hi := (195247473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92357 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92357 / 62500) = 1/(62500 / 92357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (78098989 / 200000000) (195247473 / 500000000) (Real.log (92357 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (92357 / 62500) = -Real.log (62500 / 92357) := by
    rw [show ((92357 / 62500) : ℝ) = ((62500 / 92357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (649536119 / 1000000000) ≤ -Real.log (32643 / 62500) ∧
    -Real.log (32643 / 62500) ≤ (16238403 / 25000000) := by
  have h := checkLog_sound (w := (29857 / 95143)) (n := 12)
    (lo := (649536119 / 1000000000)) (hi := (16238403 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 32643) = 1/(32643 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-16238403 / 25000000) (-649536119 / 1000000000) (Real.log (32643 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (39176367 / 100000000) ≤ -Real.log (250000 / 369897) ∧
    -Real.log (250000 / 369897) ≤ (391763671 / 1000000000) := by
  have h := checkLog_sound (w := (119897 / 619897)) (n := 12)
    (lo := (39176367 / 100000000)) (hi := (391763671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369897 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369897 / 250000) = 1/(250000 / 369897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (39176367 / 100000000) (391763671 / 1000000000) (Real.log (369897 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (369897 / 250000) = -Real.log (250000 / 369897) := by
    rw [show ((369897 / 250000) : ℝ) = ((250000 / 369897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (653134473 / 1000000000) ≤ -Real.log (130103 / 250000) ∧
    -Real.log (130103 / 250000) ≤ (326567237 / 500000000) := by
  have h := checkLog_sound (w := (119897 / 380103)) (n := 12)
    (lo := (653134473 / 1000000000)) (hi := (326567237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 130103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 130103) = 1/(130103 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-326567237 / 500000000) (-653134473 / 1000000000) (Real.log (130103 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1408869037 / 1000000000) ≤ -Real.log (250000000000 / 1022831413479) ∧
    -Real.log (250000000000 / 1022831413479) ≤ (17610863 / 12500000) := by
  have h := checkLog_sound (w := (22831413479 / 2022831413479)) (n := 12)
    (lo := (22574677 / 1000000000)) (hi := (11287339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1022831413479 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1022831413479 / 1000000000000) = 1/(250000000000 / 1022831413479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1408869037 / 1000000000) (17610863 / 12500000) (Real.log (1022831413479 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1022831413479 / 250000000000) = -Real.log (250000000000 / 1022831413479) := by
    rw [show ((1022831413479 / 250000000000) : ℝ) = ((250000000000 / 1022831413479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (283010331 / 200000000) ≤ -Real.log (250000000000 / 1029174778767) ∧
    -Real.log (250000000000 / 1029174778767) ≤ (707525829 / 500000000) := by
  have h := checkLog_sound (w := (29174778767 / 2029174778767)) (n := 12)
    (lo := (5751459 / 200000000)) (hi := (1797331 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1029174778767 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1029174778767 / 1000000000000) = 1/(250000000000 / 1029174778767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (283010331 / 200000000) (707525829 / 500000000) (Real.log (1029174778767 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1029174778767 / 250000000000) = -Real.log (250000000000 / 1029174778767) := by
    rw [show ((1029174778767 / 250000000000) : ℝ) = ((250000000000 / 1029174778767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (130003883 / 125000000) ≤ -Real.log (250000000000 / 707326226143) ∧
    -Real.log (250000000000 / 707326226143) ≤ (520015533 / 500000000) := by
  have h := checkLog_sound (w := (207326226143 / 1207326226143)) (n := 12)
    (lo := (86720971 / 250000000)) (hi := (69376777 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707326226143 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(707326226143 / 500000000000) = 1/(250000000000 / 707326226143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (130003883 / 125000000) (520015533 / 500000000) (Real.log (707326226143 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (707326226143 / 250000000000) = -Real.log (250000000000 / 707326226143) := by
    rw [show ((707326226143 / 250000000000) : ℝ) = ((250000000000 / 707326226143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1044898143 / 1000000000) ≤ -Real.log (500000000000 / 1421554460697) ∧
    -Real.log (500000000000 / 1421554460697) ≤ (208979629 / 200000000) := by
  have h := checkLog_sound (w := (421554460697 / 2421554460697)) (n := 12)
    (lo := (351750963 / 1000000000)) (hi := (87937741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421554460697 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1421554460697 / 1000000000000) = 1/(500000000000 / 1421554460697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1044898143 / 1000000000) (208979629 / 200000000) (Real.log (1421554460697 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1421554460697 / 500000000000) = -Real.log (500000000000 / 1421554460697) := by
    rw [show ((1421554460697 / 500000000000) : ℝ) = ((500000000000 / 1421554460697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0085

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0086Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0086
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

theorem reflection_log_1_neg : (345084597 / 1000000000) ≤ -Real.log (512 / 723) ∧
    -Real.log (512 / 723) ≤ (172542299 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1235)) (n := 12)
    (lo := (345084597 / 1000000000)) (hi := (172542299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723 / 512) = 1/(512 / 723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (345084597 / 1000000000) (172542299 / 500000000) (Real.log (723 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (723 / 512) = -Real.log (512 / 723) := by
    rw [show ((723 / 512) : ℝ) = ((512 / 723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (13280359 / 25000000) ≤ -Real.log (301 / 512) ∧
    -Real.log (301 / 512) ≤ (531214361 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 813)) (n := 12)
    (lo := (13280359 / 25000000)) (hi := (531214361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 301) = 1/(301 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-531214361 / 1000000000) (-13280359 / 25000000) (Real.log (301 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (344254377 / 1000000000) ≤ -Real.log (640 / 903) ∧
    -Real.log (640 / 903) ≤ (172127189 / 500000000) := by
  have h := checkLog_sound (w := (263 / 1543)) (n := 12)
    (lo := (344254377 / 1000000000)) (hi := (172127189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903 / 640) = 1/(640 / 903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (344254377 / 1000000000) (172127189 / 500000000) (Real.log (903 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (903 / 640) = -Real.log (640 / 903) := by
    rw [show ((903 / 640) : ℝ) = ((640 / 903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (132305747 / 250000000) ≤ -Real.log (377 / 640) ∧
    -Real.log (377 / 640) ≤ (529222989 / 1000000000) := by
  have h := checkLog_sound (w := (263 / 1017)) (n := 12)
    (lo := (132305747 / 250000000)) (hi := (529222989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 377) = 1/(377 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-529222989 / 1000000000) (-132305747 / 250000000) (Real.log (377 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (601151813 / 1000000000) ≤ -Real.log (256 / 467) ∧
    -Real.log (256 / 467) ≤ (300575907 / 500000000) := by
  have h := checkLog_sound (w := (211 / 723)) (n := 12)
    (lo := (601151813 / 1000000000)) (hi := (300575907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((467 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(467 / 256) = 1/(256 / 467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (601151813 / 1000000000) (300575907 / 500000000) (Real.log (467 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (467 / 256) = -Real.log (256 / 467) := by
    rw [show ((467 / 256) : ℝ) = ((256 / 467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1738514953 / 1000000000) ≤ -Real.log (45 / 256) ∧
    -Real.log (45 / 256) ≤ (434628739 / 250000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 45) = 1/(45 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-434628739 / 250000000) (-1738514953 / 1000000000) (Real.log (45 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (59986619 / 100000000) ≤ -Real.log (320 / 583) ∧
    -Real.log (320 / 583) ≤ (599866191 / 1000000000) := by
  have h := checkLog_sound (w := (263 / 903)) (n := 12)
    (lo := (59986619 / 100000000)) (hi := (599866191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583 / 320) = 1/(320 / 583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (59986619 / 100000000) (599866191 / 1000000000) (Real.log (583 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (583 / 320) = -Real.log (320 / 583) := by
    rw [show ((583 / 320) : ℝ) = ((320 / 583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (862634863 / 500000000) ≤ -Real.log (57 / 320) ∧
    -Real.log (57 / 320) ≤ (1725269729 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 57) = 1/(57 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1725269729 / 1000000000) (-862634863 / 500000000) (Real.log (57 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (59158381 / 125000000) ≤ -Real.log (100000 / 160523) ∧
    -Real.log (100000 / 160523) ≤ (473267049 / 1000000000) := by
  have h := checkLog_sound (w := (60523 / 260523)) (n := 12)
    (lo := (59158381 / 125000000)) (hi := (473267049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160523 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160523 / 100000) = 1/(100000 / 160523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (59158381 / 125000000) (473267049 / 1000000000) (Real.log (160523 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (160523 / 100000) = -Real.log (100000 / 160523) := by
    rw [show ((160523 / 100000) : ℝ) = ((100000 / 160523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (929451961 / 1000000000) ≤ -Real.log (39477 / 100000) ∧
    -Real.log (39477 / 100000) ≤ (929451963 / 1000000000) := by
  have h := checkLog_sound (w := (10523 / 89477)) (n := 12)
    (lo := (236304781 / 1000000000)) (hi := (118152391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 39477) = 1/(39477 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-929451963 / 1000000000) (-929451961 / 1000000000) (Real.log (39477 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (474478601 / 1000000000) ≤ -Real.log (125000 / 200897) ∧
    -Real.log (125000 / 200897) ≤ (237239301 / 500000000) := by
  have h := checkLog_sound (w := (75897 / 325897)) (n := 12)
    (lo := (474478601 / 1000000000)) (hi := (237239301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200897 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200897 / 125000) = 1/(125000 / 200897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (474478601 / 1000000000) (237239301 / 500000000) (Real.log (200897 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (200897 / 125000) = -Real.log (125000 / 200897) := by
    rw [show ((200897 / 125000) : ℝ) = ((125000 / 200897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (233598401 / 250000000) ≤ -Real.log (49103 / 125000) ∧
    -Real.log (49103 / 125000) ≤ (467196803 / 500000000) := by
  have h := checkLog_sound (w := (13397 / 111603)) (n := 12)
    (lo := (30155803 / 125000000)) (hi := (9649857 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 49103) = 1/(49103 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-467196803 / 500000000) (-233598401 / 250000000) (Real.log (49103 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (389230707 / 1000000000) ≤ -Real.log (200000 / 295169) ∧
    -Real.log (200000 / 295169) ≤ (97307677 / 250000000) := by
  have h := checkLog_sound (w := (95169 / 495169)) (n := 12)
    (lo := (389230707 / 1000000000)) (hi := (97307677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295169 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295169 / 200000) = 1/(200000 / 295169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (389230707 / 1000000000) (97307677 / 250000000) (Real.log (295169 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (295169 / 200000) = -Real.log (200000 / 295169) := by
    rw [show ((295169 / 200000) : ℝ) = ((200000 / 295169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (161491959 / 250000000) ≤ -Real.log (104831 / 200000) ∧
    -Real.log (104831 / 200000) ≤ (645967837 / 1000000000) := by
  have h := checkLog_sound (w := (95169 / 304831)) (n := 12)
    (lo := (161491959 / 250000000)) (hi := (645967837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 104831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 104831) = 1/(104831 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-645967837 / 1000000000) (-161491959 / 250000000) (Real.log (104831 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (390496299 / 1000000000) ≤ -Real.log (500000 / 738857) ∧
    -Real.log (500000 / 738857) ≤ (3904963 / 10000000) := by
  have h := checkLog_sound (w := (238857 / 1238857)) (n := 12)
    (lo := (390496299 / 1000000000)) (hi := (3904963 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738857 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738857 / 500000) = 1/(500000 / 738857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (390496299 / 1000000000) (3904963 / 10000000) (Real.log (738857 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (738857 / 500000) = -Real.log (500000 / 738857) := by
    rw [show ((738857 / 500000) : ℝ) = ((500000 / 738857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (162384987 / 250000000) ≤ -Real.log (261143 / 500000) ∧
    -Real.log (261143 / 500000) ≤ (649539949 / 1000000000) := by
  have h := checkLog_sound (w := (238857 / 761143)) (n := 12)
    (lo := (162384987 / 250000000)) (hi := (649539949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 261143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 261143) = 1/(261143 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-649539949 / 1000000000) (-162384987 / 250000000) (Real.log (261143 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1402719009 / 1000000000) ≤ -Real.log (500000000000 / 2033120551207) ∧
    -Real.log (500000000000 / 2033120551207) ≤ (350679753 / 250000000) := by
  have h := checkLog_sound (w := (33120551207 / 4033120551207)) (n := 12)
    (lo := (16424649 / 1000000000)) (hi := (328493 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2033120551207 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2033120551207 / 2000000000000) = 1/(500000000000 / 2033120551207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1402719009 / 1000000000) (350679753 / 250000000) (Real.log (2033120551207 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2033120551207 / 500000000000) = -Real.log (500000000000 / 2033120551207) := by
    rw [show ((2033120551207 / 500000000000) : ℝ) = ((500000000000 / 2033120551207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (281774441 / 200000000) ≤ -Real.log (4000000000 / 16365354459) ∧
    -Real.log (4000000000 / 16365354459) ≤ (88054513 / 62500000) := by
  have h := checkLog_sound (w := (365354459 / 32365354459)) (n := 12)
    (lo := (4515569 / 200000000)) (hi := (11288923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16365354459 / 16000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16365354459 / 16000000000) = 1/(4000000000 / 16365354459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (281774441 / 200000000) (88054513 / 62500000) (Real.log (16365354459 / 4000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (16365354459 / 4000000000) = -Real.log (4000000000 / 16365354459) := by
    rw [show ((16365354459 / 4000000000) : ℝ) = ((4000000000 / 16365354459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1035198543 / 1000000000) ≤ -Real.log (500000000000 / 1407832606767) ∧
    -Real.log (500000000000 / 1407832606767) ≤ (207039709 / 200000000) := by
  have h := checkLog_sound (w := (407832606767 / 2407832606767)) (n := 12)
    (lo := (342051363 / 1000000000)) (hi := (85512841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1407832606767 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1407832606767 / 1000000000000) = 1/(500000000000 / 1407832606767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1035198543 / 1000000000) (207039709 / 200000000) (Real.log (1407832606767 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1407832606767 / 500000000000) = -Real.log (500000000000 / 1407832606767) := by
    rw [show ((1407832606767 / 500000000000) : ℝ) = ((500000000000 / 1407832606767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (520018123 / 500000000) ≤ -Real.log (500000000000 / 1414659784103) ∧
    -Real.log (500000000000 / 1414659784103) ≤ (130004531 / 125000000) := by
  have h := checkLog_sound (w := (414659784103 / 2414659784103)) (n := 12)
    (lo := (173444533 / 500000000)) (hi := (346889067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1414659784103 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1414659784103 / 1000000000000) = 1/(500000000000 / 1414659784103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (520018123 / 500000000) (130004531 / 125000000) (Real.log (1414659784103 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1414659784103 / 500000000000) = -Real.log (500000000000 / 1414659784103) := by
    rw [show ((1414659784103 / 500000000000) : ℝ) = ((500000000000 / 1414659784103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0086

end


