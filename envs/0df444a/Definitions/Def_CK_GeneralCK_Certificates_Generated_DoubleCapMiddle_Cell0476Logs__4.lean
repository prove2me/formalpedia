-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0476Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0476Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:38:34.356986+00:00
-- url     : https://prove2.me/theorems/8a9195a3-d1ba-47a4-ae8d-c499696f0881
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0476Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0477Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0476Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0477Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0478Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0479Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0476Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0477Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0478Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0479Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0476Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0477Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0478Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0479Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0476Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0477Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0478Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0479Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0476Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0476
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

theorem reflection_log_1_neg : (91404859 / 500000000) ≤ -Real.log (5120 / 6147) ∧
    -Real.log (5120 / 6147) ≤ (182809719 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 11267)) (n := 12)
    (lo := (91404859 / 500000000)) (hi := (182809719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6147 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6147 / 5120) = 1/(5120 / 6147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (91404859 / 500000000) (182809719 / 1000000000) (Real.log (6147 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6147 / 5120) = -Real.log (5120 / 6147) := by
    rw [show ((6147 / 5120) : ℝ) = ((5120 / 6147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (223876241 / 1000000000) ≤ -Real.log (4093 / 5120) ∧
    -Real.log (4093 / 5120) ≤ (111938121 / 500000000) := by
  have h := checkLog_sound (w := (1027 / 9213)) (n := 12)
    (lo := (223876241 / 1000000000)) (hi := (111938121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4093) = 1/(4093 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-111938121 / 500000000) (-223876241 / 1000000000) (Real.log (4093 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (1826877 / 10000000) ≤ -Real.log (4096 / 4917) ∧
    -Real.log (4096 / 4917) ≤ (182687701 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 9013)) (n := 12)
    (lo := (1826877 / 10000000)) (hi := (182687701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4917 / 4096) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4917 / 4096) = 1/(4096 / 4917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (1826877 / 10000000) (182687701 / 1000000000) (Real.log (4917 / 4096)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4917 / 4096) = -Real.log (4096 / 4917) := by
    rw [show ((4917 / 4096) : ℝ) = ((4096 / 4917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (111846509 / 500000000) ≤ -Real.log (3275 / 4096) ∧
    -Real.log (3275 / 4096) ≤ (223693019 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 7371)) (n := 12)
    (lo := (111846509 / 500000000)) (hi := (223693019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4096 / 3275) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4096 / 3275) = 1/(3275 / 4096) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-223693019 / 1000000000) (-111846509 / 500000000) (Real.log (3275 / 4096)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (16865447 / 50000000) ≤ -Real.log (2560 / 3587) ∧
    -Real.log (2560 / 3587) ≤ (337308941 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 6147)) (n := 12)
    (lo := (16865447 / 50000000)) (hi := (337308941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3587 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3587 / 2560) = 1/(2560 / 3587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (16865447 / 50000000) (337308941 / 1000000000) (Real.log (3587 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3587 / 2560) = -Real.log (2560 / 3587) := by
    rw [show ((3587 / 2560) : ℝ) = ((2560 / 3587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (256390329 / 500000000) ≤ -Real.log (1533 / 2560) ∧
    -Real.log (1533 / 2560) ≤ (512780659 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 4093)) (n := 12)
    (lo := (256390329 / 500000000)) (hi := (512780659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1533) = 1/(1533 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-512780659 / 1000000000) (-256390329 / 500000000) (Real.log (1533 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (337099829 / 1000000000) ≤ -Real.log (2048 / 2869) ∧
    -Real.log (2048 / 2869) ≤ (33709983 / 100000000) := by
  have h := checkLog_sound (w := (821 / 4917)) (n := 12)
    (lo := (337099829 / 1000000000)) (hi := (33709983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2869 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2869 / 2048) = 1/(2048 / 2869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (337099829 / 1000000000) (33709983 / 100000000) (Real.log (2869 / 2048)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2869 / 2048) = -Real.log (2048 / 2869) := by
    rw [show ((2869 / 2048) : ℝ) = ((2048 / 2869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (512291541 / 1000000000) ≤ -Real.log (1227 / 2048) ∧
    -Real.log (1227 / 2048) ≤ (256145771 / 500000000) := by
  have h := checkLog_sound (w := (821 / 3275)) (n := 12)
    (lo := (512291541 / 1000000000)) (hi := (256145771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1227) = 1/(1227 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-256145771 / 500000000) (-512291541 / 1000000000) (Real.log (1227 / 2048)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (251147747 / 1000000000) ≤ -Real.log (2000 / 2571) ∧
    -Real.log (2000 / 2571) ≤ (62786937 / 250000000) := by
  have h := checkLog_sound (w := (571 / 4571)) (n := 12)
    (lo := (251147747 / 1000000000)) (hi := (62786937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2571 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2571 / 2000) = 1/(2000 / 2571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (251147747 / 1000000000) (62786937 / 250000000) (Real.log (2571 / 2000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (2571 / 2000) = -Real.log (2000 / 2571) := by
    rw [show ((2571 / 2000) : ℝ) = ((2000 / 2571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (336172281 / 1000000000) ≤ -Real.log (1429 / 2000) ∧
    -Real.log (1429 / 2000) ≤ (168086141 / 500000000) := by
  have h := checkLog_sound (w := (571 / 3429)) (n := 12)
    (lo := (336172281 / 1000000000)) (hi := (168086141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1429) = 1/(1429 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-168086141 / 500000000) (-336172281 / 1000000000) (Real.log (1429 / 2000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (62828357 / 250000000) ≤ -Real.log (1000000 / 1285713) ∧
    -Real.log (1000000 / 1285713) ≤ (251313429 / 1000000000) := by
  have h := checkLog_sound (w := (285713 / 2285713)) (n := 12)
    (lo := (62828357 / 250000000)) (hi := (251313429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285713 / 1000000) = 1/(1000000 / 1285713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (62828357 / 250000000) (251313429 / 1000000000) (Real.log (1285713 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1285713 / 1000000) = -Real.log (1000000 / 1285713) := by
    rw [show ((1285713 / 1000000) : ℝ) = ((1000000 / 1285713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (84117609 / 250000000) ≤ -Real.log (714287 / 1000000) ∧
    -Real.log (714287 / 1000000) ≤ (336470437 / 1000000000) := by
  have h := checkLog_sound (w := (285713 / 1714287)) (n := 12)
    (lo := (84117609 / 250000000)) (hi := (336470437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714287) = 1/(714287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-336470437 / 1000000000) (-84117609 / 250000000) (Real.log (714287 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (46939397 / 250000000) ≤ -Real.log (1000000 / 1206541) ∧
    -Real.log (1000000 / 1206541) ≤ (187757589 / 1000000000) := by
  have h := checkLog_sound (w := (206541 / 2206541)) (n := 12)
    (lo := (46939397 / 250000000)) (hi := (187757589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206541 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206541 / 1000000) = 1/(1000000 / 1206541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (46939397 / 250000000) (187757589 / 1000000000) (Real.log (1206541 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1206541 / 1000000) = -Real.log (1000000 / 1206541) := by
    rw [show ((1206541 / 1000000) : ℝ) = ((1000000 / 1206541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (23135341 / 100000000) ≤ -Real.log (793459 / 1000000) ∧
    -Real.log (793459 / 1000000) ≤ (231353411 / 1000000000) := by
  have h := checkLog_sound (w := (206541 / 1793459)) (n := 12)
    (lo := (23135341 / 100000000)) (hi := (231353411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793459) = 1/(793459 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-231353411 / 1000000000) (-23135341 / 100000000) (Real.log (793459 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (93945509 / 500000000) ≤ -Real.log (500000 / 603351) ∧
    -Real.log (500000 / 603351) ≤ (187891019 / 1000000000) := by
  have h := checkLog_sound (w := (103351 / 1103351)) (n := 12)
    (lo := (93945509 / 500000000)) (hi := (187891019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603351 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603351 / 500000) = 1/(500000 / 603351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (93945509 / 500000000) (187891019 / 1000000000) (Real.log (603351 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (603351 / 500000) = -Real.log (500000 / 603351) := by
    rw [show ((603351 / 500000) : ℝ) = ((500000 / 603351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (231556339 / 1000000000) ≤ -Real.log (396649 / 500000) ∧
    -Real.log (396649 / 500000) ≤ (11577817 / 50000000) := by
  have h := checkLog_sound (w := (103351 / 896649)) (n := 12)
    (lo := (231556339 / 1000000000)) (hi := (11577817 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396649) = 1/(396649 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-11577817 / 50000000) (-231556339 / 1000000000) (Real.log (396649 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (587320029 / 1000000000) ≤ -Real.log (250000000000 / 449790062981) ∧
    -Real.log (250000000000 / 449790062981) ≤ (58732003 / 100000000) := by
  have h := checkLog_sound (w := (199790062981 / 699790062981)) (n := 12)
    (lo := (587320029 / 1000000000)) (hi := (58732003 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449790062981 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449790062981 / 250000000000) = 1/(250000000000 / 449790062981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (587320029 / 1000000000) (58732003 / 100000000) (Real.log (449790062981 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (449790062981 / 250000000000) = -Real.log (250000000000 / 449790062981) := by
    rw [show ((449790062981 / 250000000000) : ℝ) = ((250000000000 / 449790062981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (73472983 / 125000000) ≤ -Real.log (100000000000 / 179999496001) ∧
    -Real.log (100000000000 / 179999496001) ≤ (117556773 / 200000000) := by
  have h := checkLog_sound (w := (79999496001 / 279999496001)) (n := 12)
    (lo := (73472983 / 125000000)) (hi := (117556773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179999496001 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179999496001 / 100000000000) = 1/(100000000000 / 179999496001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (73472983 / 125000000) (117556773 / 200000000) (Real.log (179999496001 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (179999496001 / 100000000000) = -Real.log (100000000000 / 179999496001) := by
    rw [show ((179999496001 / 100000000000) : ℝ) = ((100000000000 / 179999496001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (209555499 / 500000000) ≤ -Real.log (500000000000 / 760304565201) ∧
    -Real.log (500000000000 / 760304565201) ≤ (419110999 / 1000000000) := by
  have h := checkLog_sound (w := (260304565201 / 1260304565201)) (n := 12)
    (lo := (209555499 / 500000000)) (hi := (419110999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760304565201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760304565201 / 500000000000) = 1/(500000000000 / 760304565201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (209555499 / 500000000) (419110999 / 1000000000) (Real.log (760304565201 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (760304565201 / 500000000000) = -Real.log (500000000000 / 760304565201) := by
    rw [show ((760304565201 / 500000000000) : ℝ) = ((500000000000 / 760304565201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (209723679 / 500000000) ≤ -Real.log (100000000000 / 152112068857) ∧
    -Real.log (100000000000 / 152112068857) ≤ (419447359 / 1000000000) := by
  have h := checkLog_sound (w := (52112068857 / 252112068857)) (n := 12)
    (lo := (209723679 / 500000000)) (hi := (419447359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152112068857 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152112068857 / 100000000000) = 1/(100000000000 / 152112068857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (209723679 / 500000000) (419447359 / 1000000000) (Real.log (152112068857 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (152112068857 / 100000000000) = -Real.log (100000000000 / 152112068857) := by
    rw [show ((152112068857 / 100000000000) : ℝ) = ((100000000000 / 152112068857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0476

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0477Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0477
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

theorem reflection_log_1_neg : (1826877 / 10000000) ≤ -Real.log (4096 / 4917) ∧
    -Real.log (4096 / 4917) ≤ (182687701 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 9013)) (n := 12)
    (lo := (1826877 / 10000000)) (hi := (182687701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4917 / 4096) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4917 / 4096) = 1/(4096 / 4917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (1826877 / 10000000) (182687701 / 1000000000) (Real.log (4917 / 4096)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4917 / 4096) = -Real.log (4096 / 4917) := by
    rw [show ((4917 / 4096) : ℝ) = ((4096 / 4917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (111846509 / 500000000) ≤ -Real.log (3275 / 4096) ∧
    -Real.log (3275 / 4096) ≤ (223693019 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 7371)) (n := 12)
    (lo := (111846509 / 500000000)) (hi := (223693019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4096 / 3275) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4096 / 3275) = 1/(3275 / 4096) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-223693019 / 1000000000) (-111846509 / 500000000) (Real.log (3275 / 4096)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (182565667 / 1000000000) ≤ -Real.log (10240 / 12291) ∧
    -Real.log (10240 / 12291) ≤ (45641417 / 250000000) := by
  have h := checkLog_sound (w := (2051 / 22531)) (n := 12)
    (lo := (182565667 / 1000000000)) (hi := (45641417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12291 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12291 / 10240) = 1/(10240 / 12291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (182565667 / 1000000000) (45641417 / 250000000) (Real.log (12291 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12291 / 10240) = -Real.log (10240 / 12291) := by
    rw [show ((12291 / 10240) : ℝ) = ((10240 / 12291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (223509829 / 1000000000) ≤ -Real.log (8189 / 10240) ∧
    -Real.log (8189 / 10240) ≤ (22350983 / 100000000) := by
  have h := checkLog_sound (w := (2051 / 18429)) (n := 12)
    (lo := (223509829 / 1000000000)) (hi := (22350983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8189) = 1/(8189 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22350983 / 100000000) (-223509829 / 1000000000) (Real.log (8189 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (337099829 / 1000000000) ≤ -Real.log (2048 / 2869) ∧
    -Real.log (2048 / 2869) ≤ (33709983 / 100000000) := by
  have h := checkLog_sound (w := (821 / 4917)) (n := 12)
    (lo := (337099829 / 1000000000)) (hi := (33709983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2869 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2869 / 2048) = 1/(2048 / 2869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (337099829 / 1000000000) (33709983 / 100000000) (Real.log (2869 / 2048)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2869 / 2048) = -Real.log (2048 / 2869) := by
    rw [show ((2869 / 2048) : ℝ) = ((2048 / 2869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (512291541 / 1000000000) ≤ -Real.log (1227 / 2048) ∧
    -Real.log (1227 / 2048) ≤ (256145771 / 500000000) := by
  have h := checkLog_sound (w := (821 / 3275)) (n := 12)
    (lo := (512291541 / 1000000000)) (hi := (256145771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1227) = 1/(1227 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-256145771 / 500000000) (-512291541 / 1000000000) (Real.log (1227 / 2048)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13475627 / 40000000) ≤ -Real.log (5120 / 7171) ∧
    -Real.log (5120 / 7171) ≤ (84222669 / 250000000) := by
  have h := checkLog_sound (w := (2051 / 12291)) (n := 12)
    (lo := (13475627 / 40000000)) (hi := (84222669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7171 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7171 / 5120) = 1/(5120 / 7171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13475627 / 40000000) (84222669 / 250000000) (Real.log (7171 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7171 / 5120) = -Real.log (5120 / 7171) := by
    rw [show ((7171 / 5120) : ℝ) = ((5120 / 7171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (511802663 / 1000000000) ≤ -Real.log (3069 / 5120) ∧
    -Real.log (3069 / 5120) ≤ (63975333 / 125000000) := by
  have h := checkLog_sound (w := (2051 / 8189)) (n := 12)
    (lo := (511802663 / 1000000000)) (hi := (63975333 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3069) = 1/(3069 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-63975333 / 125000000) (-511802663 / 1000000000) (Real.log (3069 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (250982817 / 1000000000) ≤ -Real.log (125000 / 160661) ∧
    -Real.log (125000 / 160661) ≤ (125491409 / 500000000) := by
  have h := checkLog_sound (w := (35661 / 285661)) (n := 12)
    (lo := (250982817 / 1000000000)) (hi := (125491409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160661 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160661 / 125000) = 1/(125000 / 160661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (250982817 / 1000000000) (125491409 / 500000000) (Real.log (160661 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (160661 / 125000) = -Real.log (125000 / 160661) := by
    rw [show ((160661 / 125000) : ℝ) = ((125000 / 160661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (167937807 / 500000000) ≤ -Real.log (89339 / 125000) ∧
    -Real.log (89339 / 125000) ≤ (67175123 / 200000000) := by
  have h := checkLog_sound (w := (35661 / 214339)) (n := 12)
    (lo := (167937807 / 500000000)) (hi := (67175123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89339) = 1/(89339 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-67175123 / 200000000) (-167937807 / 500000000) (Real.log (89339 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (10045941 / 40000000) ≤ -Real.log (1000000 / 1285501) ∧
    -Real.log (1000000 / 1285501) ≤ (125574263 / 500000000) := by
  have h := checkLog_sound (w := (285501 / 2285501)) (n := 12)
    (lo := (10045941 / 40000000)) (hi := (125574263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285501 / 1000000) = 1/(1000000 / 1285501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (10045941 / 40000000) (125574263 / 500000000) (Real.log (1285501 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1285501 / 1000000) = -Real.log (1000000 / 1285501) := by
    rw [show ((1285501 / 1000000) : ℝ) = ((1000000 / 1285501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (336173681 / 1000000000) ≤ -Real.log (714499 / 1000000) ∧
    -Real.log (714499 / 1000000) ≤ (168086841 / 500000000) := by
  have h := checkLog_sound (w := (285501 / 1714499)) (n := 12)
    (lo := (336173681 / 1000000000)) (hi := (168086841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714499) = 1/(714499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-168086841 / 500000000) (-336173681 / 1000000000) (Real.log (714499 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23453121 / 125000000) ≤ -Real.log (1000000 / 1206381) ∧
    -Real.log (1000000 / 1206381) ≤ (187624969 / 1000000000) := by
  have h := checkLog_sound (w := (206381 / 2206381)) (n := 12)
    (lo := (23453121 / 125000000)) (hi := (187624969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206381 / 1000000) = 1/(1000000 / 1206381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23453121 / 125000000) (187624969 / 1000000000) (Real.log (1206381 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1206381 / 1000000) = -Real.log (1000000 / 1206381) := by
    rw [show ((1206381 / 1000000) : ℝ) = ((1000000 / 1206381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (231151781 / 1000000000) ≤ -Real.log (793619 / 1000000) ∧
    -Real.log (793619 / 1000000) ≤ (115575891 / 500000000) := by
  have h := checkLog_sound (w := (206381 / 1793619)) (n := 12)
    (lo := (231151781 / 1000000000)) (hi := (115575891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793619) = 1/(793619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-115575891 / 500000000) (-231151781 / 1000000000) (Real.log (793619 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (11734901 / 62500000) ≤ -Real.log (500000 / 603271) ∧
    -Real.log (500000 / 603271) ≤ (187758417 / 1000000000) := by
  have h := checkLog_sound (w := (103271 / 1103271)) (n := 12)
    (lo := (11734901 / 62500000)) (hi := (187758417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603271 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603271 / 500000) = 1/(500000 / 603271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (11734901 / 62500000) (187758417 / 1000000000) (Real.log (603271 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (603271 / 500000) = -Real.log (500000 / 603271) := by
    rw [show ((603271 / 500000) : ℝ) = ((500000 / 603271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23135467 / 100000000) ≤ -Real.log (396729 / 500000) ∧
    -Real.log (396729 / 500000) ≤ (231354671 / 1000000000) := by
  have h := checkLog_sound (w := (103271 / 896729)) (n := 12)
    (lo := (23135467 / 100000000)) (hi := (231354671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396729) = 1/(396729 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-231354671 / 1000000000) (-23135467 / 100000000) (Real.log (396729 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (9169663 / 15625000) ≤ -Real.log (25000000000 / 44958248917) ∧
    -Real.log (25000000000 / 44958248917) ≤ (586858433 / 1000000000) := by
  have h := checkLog_sound (w := (19958248917 / 69958248917)) (n := 12)
    (lo := (9169663 / 15625000)) (hi := (586858433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44958248917 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44958248917 / 25000000000) = 1/(25000000000 / 44958248917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9169663 / 15625000) (586858433 / 1000000000) (Real.log (44958248917 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (44958248917 / 25000000000) = -Real.log (25000000000 / 44958248917) := by
    rw [show ((44958248917 / 25000000000) : ℝ) = ((25000000000 / 44958248917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (293661103 / 500000000) ≤ -Real.log (50000000000 / 89958208479) ∧
    -Real.log (50000000000 / 89958208479) ≤ (587322207 / 1000000000) := by
  have h := checkLog_sound (w := (39958208479 / 139958208479)) (n := 12)
    (lo := (293661103 / 500000000)) (hi := (587322207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89958208479 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89958208479 / 50000000000) = 1/(50000000000 / 89958208479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (293661103 / 500000000) (587322207 / 1000000000) (Real.log (89958208479 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (89958208479 / 50000000000) = -Real.log (50000000000 / 89958208479) := by
    rw [show ((89958208479 / 50000000000) : ℝ) = ((50000000000 / 89958208479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1675107 / 4000000) ≤ -Real.log (250000000000 / 380025238811) ∧
    -Real.log (250000000000 / 380025238811) ≤ (418776751 / 1000000000) := by
  have h := checkLog_sound (w := (130025238811 / 630025238811)) (n := 12)
    (lo := (1675107 / 4000000)) (hi := (418776751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380025238811 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380025238811 / 250000000000) = 1/(250000000000 / 380025238811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1675107 / 4000000) (418776751 / 1000000000) (Real.log (380025238811 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (380025238811 / 250000000000) = -Real.log (250000000000 / 380025238811) := by
    rw [show ((380025238811 / 250000000000) : ℝ) = ((250000000000 / 380025238811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (419113087 / 1000000000) ≤ -Real.log (500000000000 / 760306153571) ∧
    -Real.log (500000000000 / 760306153571) ≤ (3274321 / 7812500) := by
  have h := checkLog_sound (w := (260306153571 / 1260306153571)) (n := 12)
    (lo := (419113087 / 1000000000)) (hi := (3274321 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760306153571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760306153571 / 500000000000) = 1/(500000000000 / 760306153571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (419113087 / 1000000000) (3274321 / 7812500) (Real.log (760306153571 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (760306153571 / 500000000000) = -Real.log (500000000000 / 760306153571) := by
    rw [show ((760306153571 / 500000000000) : ℝ) = ((500000000000 / 760306153571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0477

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0478Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0478
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

theorem reflection_log_1_neg : (182565667 / 1000000000) ≤ -Real.log (10240 / 12291) ∧
    -Real.log (10240 / 12291) ≤ (45641417 / 250000000) := by
  have h := checkLog_sound (w := (2051 / 22531)) (n := 12)
    (lo := (182565667 / 1000000000)) (hi := (45641417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12291 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12291 / 10240) = 1/(10240 / 12291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (182565667 / 1000000000) (45641417 / 250000000) (Real.log (12291 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12291 / 10240) = -Real.log (10240 / 12291) := by
    rw [show ((12291 / 10240) : ℝ) = ((10240 / 12291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (223509829 / 1000000000) ≤ -Real.log (8189 / 10240) ∧
    -Real.log (8189 / 10240) ≤ (22350983 / 100000000) := by
  have h := checkLog_sound (w := (2051 / 18429)) (n := 12)
    (lo := (223509829 / 1000000000)) (hi := (22350983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8189) = 1/(8189 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22350983 / 100000000) (-223509829 / 1000000000) (Real.log (8189 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (182443619 / 1000000000) ≤ -Real.log (20480 / 24579) ∧
    -Real.log (20480 / 24579) ≤ (9122181 / 50000000) := by
  have h := checkLog_sound (w := (4099 / 45059)) (n := 12)
    (lo := (182443619 / 1000000000)) (hi := (9122181 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24579 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24579 / 20480) = 1/(20480 / 24579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (182443619 / 1000000000) (9122181 / 50000000) (Real.log (24579 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24579 / 20480) = -Real.log (20480 / 24579) := by
    rw [show ((24579 / 20480) : ℝ) = ((20480 / 24579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (223326673 / 1000000000) ≤ -Real.log (16381 / 20480) ∧
    -Real.log (16381 / 20480) ≤ (111663337 / 500000000) := by
  have h := checkLog_sound (w := (4099 / 36861)) (n := 12)
    (lo := (223326673 / 1000000000)) (hi := (111663337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16381) = 1/(16381 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-111663337 / 500000000) (-223326673 / 1000000000) (Real.log (16381 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (13475627 / 40000000) ≤ -Real.log (5120 / 7171) ∧
    -Real.log (5120 / 7171) ≤ (84222669 / 250000000) := by
  have h := checkLog_sound (w := (2051 / 12291)) (n := 12)
    (lo := (13475627 / 40000000)) (hi := (84222669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7171 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7171 / 5120) = 1/(5120 / 7171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (13475627 / 40000000) (84222669 / 250000000) (Real.log (7171 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7171 / 5120) = -Real.log (5120 / 7171) := by
    rw [show ((7171 / 5120) : ℝ) = ((5120 / 7171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (511802663 / 1000000000) ≤ -Real.log (3069 / 5120) ∧
    -Real.log (3069 / 5120) ≤ (63975333 / 125000000) := by
  have h := checkLog_sound (w := (2051 / 8189)) (n := 12)
    (lo := (511802663 / 1000000000)) (hi := (63975333 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3069) = 1/(3069 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-63975333 / 125000000) (-511802663 / 1000000000) (Real.log (3069 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (168340739 / 500000000) ≤ -Real.log (10240 / 14339) ∧
    -Real.log (10240 / 14339) ≤ (336681479 / 1000000000) := by
  have h := checkLog_sound (w := (4099 / 24579)) (n := 12)
    (lo := (168340739 / 500000000)) (hi := (336681479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14339 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14339 / 10240) = 1/(10240 / 14339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (168340739 / 500000000) (336681479 / 1000000000) (Real.log (14339 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14339 / 10240) = -Real.log (10240 / 14339) := by
    rw [show ((14339 / 10240) : ℝ) = ((10240 / 14339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (63914253 / 125000000) ≤ -Real.log (6141 / 10240) ∧
    -Real.log (6141 / 10240) ≤ (20452561 / 40000000) := by
  have h := checkLog_sound (w := (4099 / 16381)) (n := 12)
    (lo := (63914253 / 125000000)) (hi := (20452561 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6141) = 1/(6141 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20452561 / 40000000) (-63914253 / 125000000) (Real.log (6141 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12540893 / 50000000) ≤ -Real.log (250000 / 321269) ∧
    -Real.log (250000 / 321269) ≤ (250817861 / 1000000000) := by
  have h := checkLog_sound (w := (71269 / 571269)) (n := 12)
    (lo := (12540893 / 50000000)) (hi := (250817861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321269 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321269 / 250000) = 1/(250000 / 321269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12540893 / 50000000) (250817861 / 1000000000) (Real.log (321269 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (321269 / 250000) = -Real.log (250000 / 321269) := by
    rw [show ((321269 / 250000) : ℝ) = ((250000 / 321269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (67115807 / 200000000) ≤ -Real.log (178731 / 250000) ∧
    -Real.log (178731 / 250000) ≤ (83894759 / 250000000) := by
  have h := checkLog_sound (w := (71269 / 428731)) (n := 12)
    (lo := (67115807 / 200000000)) (hi := (83894759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178731) = 1/(178731 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-83894759 / 250000000) (-67115807 / 200000000) (Real.log (178731 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (50196719 / 200000000) ≤ -Real.log (1000000 / 1285289) ∧
    -Real.log (1000000 / 1285289) ≤ (62745899 / 250000000) := by
  have h := checkLog_sound (w := (285289 / 2285289)) (n := 12)
    (lo := (50196719 / 200000000)) (hi := (62745899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285289 / 1000000) = 1/(1000000 / 1285289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (50196719 / 200000000) (62745899 / 250000000) (Real.log (1285289 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1285289 / 1000000) = -Real.log (1000000 / 1285289) := by
    rw [show ((1285289 / 1000000) : ℝ) = ((1000000 / 1285289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (335877013 / 1000000000) ≤ -Real.log (714711 / 1000000) ∧
    -Real.log (714711 / 1000000) ≤ (167938507 / 500000000) := by
  have h := checkLog_sound (w := (285289 / 1714711)) (n := 12)
    (lo := (335877013 / 1000000000)) (hi := (167938507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714711) = 1/(714711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-167938507 / 500000000) (-335877013 / 1000000000) (Real.log (714711 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (93745751 / 500000000) ≤ -Real.log (50000 / 60311) ∧
    -Real.log (50000 / 60311) ≤ (187491503 / 1000000000) := by
  have h := checkLog_sound (w := (10311 / 110311)) (n := 12)
    (lo := (93745751 / 500000000)) (hi := (187491503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60311 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60311 / 50000) = 1/(50000 / 60311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (93745751 / 500000000) (187491503 / 1000000000) (Real.log (60311 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (60311 / 50000) = -Real.log (50000 / 60311) := by
    rw [show ((60311 / 50000) : ℝ) = ((50000 / 60311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (115474467 / 500000000) ≤ -Real.log (39689 / 50000) ∧
    -Real.log (39689 / 50000) ≤ (46189787 / 200000000) := by
  have h := checkLog_sound (w := (10311 / 89689)) (n := 12)
    (lo := (115474467 / 500000000)) (hi := (46189787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39689) = 1/(39689 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-46189787 / 200000000) (-115474467 / 500000000) (Real.log (39689 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (187625797 / 1000000000) ≤ -Real.log (500000 / 603191) ∧
    -Real.log (500000 / 603191) ≤ (93812899 / 500000000) := by
  have h := checkLog_sound (w := (103191 / 1103191)) (n := 12)
    (lo := (187625797 / 1000000000)) (hi := (93812899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603191 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603191 / 500000) = 1/(500000 / 603191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (187625797 / 1000000000) (93812899 / 500000000) (Real.log (603191 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (603191 / 500000) = -Real.log (500000 / 603191) := by
    rw [show ((603191 / 500000) : ℝ) = ((500000 / 603191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (231153041 / 1000000000) ≤ -Real.log (396809 / 500000) ∧
    -Real.log (396809 / 500000) ≤ (115576521 / 500000000) := by
  have h := checkLog_sound (w := (103191 / 896809)) (n := 12)
    (lo := (231153041 / 1000000000)) (hi := (115576521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396809) = 1/(396809 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-115576521 / 500000000) (-231153041 / 1000000000) (Real.log (396809 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (18324903 / 31250000) ≤ -Real.log (500000000000 / 898750076931) ∧
    -Real.log (500000000000 / 898750076931) ≤ (586396897 / 1000000000) := by
  have h := checkLog_sound (w := (398750076931 / 1398750076931)) (n := 12)
    (lo := (18324903 / 31250000)) (hi := (586396897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((898750076931 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(898750076931 / 500000000000) = 1/(500000000000 / 898750076931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (18324903 / 31250000) (586396897 / 1000000000) (Real.log (898750076931 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (898750076931 / 500000000000) = -Real.log (500000000000 / 898750076931) := by
    rw [show ((898750076931 / 500000000000) : ℝ) = ((500000000000 / 898750076931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (586860609 / 1000000000) ≤ -Real.log (500000000000 / 899166936007) ∧
    -Real.log (500000000000 / 899166936007) ≤ (58686061 / 100000000) := by
  have h := checkLog_sound (w := (399166936007 / 1399166936007)) (n := 12)
    (lo := (586860609 / 1000000000)) (hi := (58686061 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899166936007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899166936007 / 500000000000) = 1/(500000000000 / 899166936007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (586860609 / 1000000000) (58686061 / 100000000) (Real.log (899166936007 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (899166936007 / 500000000000) = -Real.log (500000000000 / 899166936007) := by
    rw [show ((899166936007 / 500000000000) : ℝ) = ((500000000000 / 899166936007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (418440437 / 1000000000) ≤ -Real.log (500000000000 / 759794905389) ∧
    -Real.log (500000000000 / 759794905389) ≤ (209220219 / 500000000) := by
  have h := checkLog_sound (w := (259794905389 / 1259794905389)) (n := 12)
    (lo := (418440437 / 1000000000)) (hi := (209220219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759794905389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759794905389 / 500000000000) = 1/(500000000000 / 759794905389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (418440437 / 1000000000) (209220219 / 500000000) (Real.log (759794905389 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (759794905389 / 500000000000) = -Real.log (500000000000 / 759794905389) := by
    rw [show ((759794905389 / 500000000000) : ℝ) = ((500000000000 / 759794905389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (418778839 / 1000000000) ≤ -Real.log (62500000000 / 95006508169) ∧
    -Real.log (62500000000 / 95006508169) ≤ (10469471 / 25000000) := by
  have h := checkLog_sound (w := (32506508169 / 157506508169)) (n := 12)
    (lo := (418778839 / 1000000000)) (hi := (10469471 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95006508169 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95006508169 / 62500000000) = 1/(62500000000 / 95006508169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (418778839 / 1000000000) (10469471 / 25000000) (Real.log (95006508169 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (95006508169 / 62500000000) = -Real.log (62500000000 / 95006508169) := by
    rw [show ((95006508169 / 62500000000) : ℝ) = ((62500000000 / 95006508169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0478

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0479Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0479
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

theorem reflection_log_1_neg : (182443619 / 1000000000) ≤ -Real.log (20480 / 24579) ∧
    -Real.log (20480 / 24579) ≤ (9122181 / 50000000) := by
  have h := checkLog_sound (w := (4099 / 45059)) (n := 12)
    (lo := (182443619 / 1000000000)) (hi := (9122181 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24579 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24579 / 20480) = 1/(20480 / 24579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (182443619 / 1000000000) (9122181 / 50000000) (Real.log (24579 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24579 / 20480) = -Real.log (20480 / 24579) := by
    rw [show ((24579 / 20480) : ℝ) = ((20480 / 24579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (223326673 / 1000000000) ≤ -Real.log (16381 / 20480) ∧
    -Real.log (16381 / 20480) ≤ (111663337 / 500000000) := by
  have h := checkLog_sound (w := (4099 / 36861)) (n := 12)
    (lo := (223326673 / 1000000000)) (hi := (111663337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16381) = 1/(16381 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-111663337 / 500000000) (-223326673 / 1000000000) (Real.log (16381 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (45580389 / 250000000) ≤ -Real.log (5 / 6) ∧
    -Real.log (5 / 6) ≤ (182321557 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6 / 5) = 1/(5 / 6) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (45580389 / 250000000) (182321557 / 1000000000) (Real.log (6 / 5)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6 / 5) = -Real.log (5 / 6) := by
    rw [show ((6 / 5) : ℝ) = ((5 / 6) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
    -Real.log (4 / 5) ≤ (1743309 / 7812500) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 4) = 1/(4 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1743309 / 7812500) (-223143551 / 1000000000) (Real.log (4 / 5)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168340739 / 500000000) ≤ -Real.log (10240 / 14339) ∧
    -Real.log (10240 / 14339) ≤ (336681479 / 1000000000) := by
  have h := checkLog_sound (w := (4099 / 24579)) (n := 12)
    (lo := (168340739 / 500000000)) (hi := (336681479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14339 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14339 / 10240) = 1/(10240 / 14339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168340739 / 500000000) (336681479 / 1000000000) (Real.log (14339 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (14339 / 10240) = -Real.log (10240 / 14339) := by
    rw [show ((14339 / 10240) : ℝ) = ((10240 / 14339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (63914253 / 125000000) ≤ -Real.log (6141 / 10240) ∧
    -Real.log (6141 / 10240) ≤ (20452561 / 40000000) := by
  have h := checkLog_sound (w := (4099 / 16381)) (n := 12)
    (lo := (63914253 / 125000000)) (hi := (20452561 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6141) = 1/(6141 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-20452561 / 40000000) (-63914253 / 125000000) (Real.log (6141 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (84118059 / 250000000) ≤ -Real.log (5 / 7) ∧
    -Real.log (5 / 7) ≤ (336472237 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 6)) (n := 12)
    (lo := (84118059 / 250000000)) (hi := (336472237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7 / 5) = 1/(5 / 7) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (84118059 / 250000000) (336472237 / 1000000000) (Real.log (7 / 5)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7 / 5) = -Real.log (5 / 7) := by
    rw [show ((7 / 5) : ℝ) = ((5 / 7) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (510825623 / 1000000000) ≤ -Real.log (3 / 5) ∧
    -Real.log (3 / 5) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 3) = 1/(3 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-63853203 / 125000000) (-510825623 / 1000000000) (Real.log (3 / 5)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125326827 / 500000000) ≤ -Real.log (200000 / 256973) ∧
    -Real.log (200000 / 256973) ≤ (50130731 / 200000000) := by
  have h := checkLog_sound (w := (56973 / 456973)) (n := 12)
    (lo := (125326827 / 500000000)) (hi := (50130731 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256973 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256973 / 200000) = 1/(200000 / 256973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125326827 / 500000000) (50130731 / 200000000) (Real.log (256973 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (256973 / 200000) = -Real.log (200000 / 256973) := by
    rw [show ((256973 / 200000) : ℝ) = ((200000 / 256973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (167641971 / 500000000) ≤ -Real.log (143027 / 200000) ∧
    -Real.log (143027 / 200000) ≤ (335283943 / 1000000000) := by
  have h := checkLog_sound (w := (56973 / 343027)) (n := 12)
    (lo := (167641971 / 500000000)) (hi := (335283943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 143027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 143027) = 1/(143027 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-335283943 / 1000000000) (-167641971 / 500000000) (Real.log (143027 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (125409319 / 500000000) ≤ -Real.log (1000000 / 1285077) ∧
    -Real.log (1000000 / 1285077) ≤ (250818639 / 1000000000) := by
  have h := checkLog_sound (w := (285077 / 2285077)) (n := 12)
    (lo := (125409319 / 500000000)) (hi := (250818639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285077 / 1000000) = 1/(1000000 / 1285077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (125409319 / 500000000) (250818639 / 1000000000) (Real.log (1285077 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1285077 / 1000000) = -Real.log (1000000 / 1285077) := by
    rw [show ((1285077 / 1000000) : ℝ) = ((1000000 / 1285077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (167790217 / 500000000) ≤ -Real.log (714923 / 1000000) ∧
    -Real.log (714923 / 1000000) ≤ (67116087 / 200000000) := by
  have h := checkLog_sound (w := (285077 / 1714923)) (n := 12)
    (lo := (167790217 / 500000000)) (hi := (67116087 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714923) = 1/(714923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-67116087 / 200000000) (-167790217 / 500000000) (Real.log (714923 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1463741 / 7812500) ≤ -Real.log (50000 / 60303) ∧
    -Real.log (50000 / 60303) ≤ (187358849 / 1000000000) := by
  have h := checkLog_sound (w := (10303 / 110303)) (n := 12)
    (lo := (1463741 / 7812500)) (hi := (187358849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60303 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60303 / 50000) = 1/(50000 / 60303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1463741 / 7812500) (187358849 / 1000000000) (Real.log (60303 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (60303 / 50000) = -Real.log (50000 / 60303) := by
    rw [show ((60303 / 50000) : ℝ) = ((50000 / 60303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (230747387 / 1000000000) ≤ -Real.log (39697 / 50000) ∧
    -Real.log (39697 / 50000) ≤ (57686847 / 250000000) := by
  have h := checkLog_sound (w := (10303 / 89697)) (n := 12)
    (lo := (230747387 / 1000000000)) (hi := (57686847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39697) = 1/(39697 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-57686847 / 250000000) (-230747387 / 1000000000) (Real.log (39697 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (187492331 / 1000000000) ≤ -Real.log (1000000 / 1206221) ∧
    -Real.log (1000000 / 1206221) ≤ (46873083 / 250000000) := by
  have h := checkLog_sound (w := (206221 / 2206221)) (n := 12)
    (lo := (187492331 / 1000000000)) (hi := (46873083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206221 / 1000000) = 1/(1000000 / 1206221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (187492331 / 1000000000) (46873083 / 250000000) (Real.log (1206221 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1206221 / 1000000) = -Real.log (1000000 / 1206221) := by
    rw [show ((1206221 / 1000000) : ℝ) = ((1000000 / 1206221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (115475097 / 500000000) ≤ -Real.log (793779 / 1000000) ∧
    -Real.log (793779 / 1000000) ≤ (46190039 / 200000000) := by
  have h := checkLog_sound (w := (206221 / 1793779)) (n := 12)
    (lo := (115475097 / 500000000)) (hi := (46190039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793779) = 1/(793779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-46190039 / 200000000) (-115475097 / 500000000) (Real.log (793779 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (585937597 / 1000000000) ≤ -Real.log (250000000000 / 449168688429) ∧
    -Real.log (250000000000 / 449168688429) ≤ (292968799 / 500000000) := by
  have h := checkLog_sound (w := (199168688429 / 699168688429)) (n := 12)
    (lo := (585937597 / 1000000000)) (hi := (292968799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449168688429 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449168688429 / 250000000000) = 1/(250000000000 / 449168688429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (585937597 / 1000000000) (292968799 / 500000000) (Real.log (449168688429 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (449168688429 / 250000000000) = -Real.log (250000000000 / 449168688429) := by
    rw [show ((449168688429 / 250000000000) : ℝ) = ((250000000000 / 449168688429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (586399073 / 1000000000) ≤ -Real.log (125000000000 / 224688008359) ∧
    -Real.log (125000000000 / 224688008359) ≤ (293199537 / 500000000) := by
  have h := checkLog_sound (w := (99688008359 / 349688008359)) (n := 12)
    (lo := (586399073 / 1000000000)) (hi := (293199537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((224688008359 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(224688008359 / 125000000000) = 1/(125000000000 / 224688008359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (586399073 / 1000000000) (293199537 / 500000000) (Real.log (224688008359 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (224688008359 / 125000000000) = -Real.log (125000000000 / 224688008359) := by
    rw [show ((224688008359 / 125000000000) : ℝ) = ((125000000000 / 224688008359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (83621247 / 200000000) ≤ -Real.log (500000000000 / 759541023251) ∧
    -Real.log (500000000000 / 759541023251) ≤ (104526559 / 250000000) := by
  have h := checkLog_sound (w := (259541023251 / 1259541023251)) (n := 12)
    (lo := (83621247 / 200000000)) (hi := (104526559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759541023251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759541023251 / 500000000000) = 1/(500000000000 / 759541023251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (83621247 / 200000000) (104526559 / 250000000) (Real.log (759541023251 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (759541023251 / 500000000000) = -Real.log (500000000000 / 759541023251) := by
    rw [show ((759541023251 / 500000000000) : ℝ) = ((500000000000 / 759541023251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (16737701 / 40000000) ≤ -Real.log (20000000000 / 30391859699) ∧
    -Real.log (20000000000 / 30391859699) ≤ (209221263 / 500000000) := by
  have h := checkLog_sound (w := (10391859699 / 50391859699)) (n := 12)
    (lo := (16737701 / 40000000)) (hi := (209221263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30391859699 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30391859699 / 20000000000) = 1/(20000000000 / 30391859699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (16737701 / 40000000) (209221263 / 500000000) (Real.log (30391859699 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (30391859699 / 20000000000) = -Real.log (20000000000 / 30391859699) := by
    rw [show ((30391859699 / 20000000000) : ℝ) = ((20000000000 / 30391859699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0479

end


