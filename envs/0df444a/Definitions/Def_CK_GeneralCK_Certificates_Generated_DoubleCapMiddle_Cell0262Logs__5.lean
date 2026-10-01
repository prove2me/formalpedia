-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0262Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0262Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:17:30.840337+00:00
-- url     : https://prove2.me/theorems/62efdb5a-21a2-4ac5-81b9-aaaaf4dfcaae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0262Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0263Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0262Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0263Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0264Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0265Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0266Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0262Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0263Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0264Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0265Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0266Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0262Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0263Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0264Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0265Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0266Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0262Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0263Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0264Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0265Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0266Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0262Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0262
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

theorem reflection_log_1_neg : (23741621 / 100000000) ≤ -Real.log (1280 / 1623) ∧
    -Real.log (1280 / 1623) ≤ (237416211 / 1000000000) := by
  have h := checkLog_sound (w := (343 / 2903)) (n := 12)
    (lo := (23741621 / 100000000)) (hi := (237416211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1623 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1623 / 1280) = 1/(1280 / 1623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (23741621 / 100000000) (237416211 / 1000000000) (Real.log (1623 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1623 / 1280) = -Real.log (1280 / 1623) := by
    rw [show ((1623 / 1280) : ℝ) = ((1280 / 1623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (155966037 / 500000000) ≤ -Real.log (937 / 1280) ∧
    -Real.log (937 / 1280) ≤ (12477283 / 40000000) := by
  have h := checkLog_sound (w := (343 / 2217)) (n := 12)
    (lo := (155966037 / 500000000)) (hi := (12477283 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 937) = 1/(937 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12477283 / 40000000) (-155966037 / 500000000) (Real.log (937 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (59238499 / 250000000) ≤ -Real.log (5120 / 6489) ∧
    -Real.log (5120 / 6489) ≤ (236953997 / 1000000000) := by
  have h := checkLog_sound (w := (1369 / 11609)) (n := 12)
    (lo := (59238499 / 250000000)) (hi := (236953997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6489 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6489 / 5120) = 1/(5120 / 6489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (59238499 / 250000000) (236953997 / 1000000000) (Real.log (6489 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6489 / 5120) = -Real.log (5120 / 6489) := by
    rw [show ((6489 / 5120) : ℝ) = ((5120 / 6489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (311131967 / 1000000000) ≤ -Real.log (3751 / 5120) ∧
    -Real.log (3751 / 5120) ≤ (4861437 / 15625000) := by
  have h := checkLog_sound (w := (1369 / 8871)) (n := 12)
    (lo := (311131967 / 1000000000)) (hi := (4861437 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3751) = 1/(3751 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4861437 / 15625000) (-311131967 / 1000000000) (Real.log (3751 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (429140943 / 1000000000) ≤ -Real.log (640 / 983) ∧
    -Real.log (640 / 983) ≤ (26821309 / 62500000) := by
  have h := checkLog_sound (w := (343 / 1623)) (n := 12)
    (lo := (429140943 / 1000000000)) (hi := (26821309 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983 / 640) = 1/(640 / 983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (429140943 / 1000000000) (26821309 / 62500000) (Real.log (983 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (983 / 640) = -Real.log (640 / 983) := by
    rw [show ((983 / 640) : ℝ) = ((640 / 983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (191934009 / 250000000) ≤ -Real.log (297 / 640) ∧
    -Real.log (297 / 640) ≤ (383868019 / 500000000) := by
  have h := checkLog_sound (w := (23 / 617)) (n := 12)
    (lo := (9323607 / 125000000)) (hi := (74588857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 297) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 297) = 1/(297 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-383868019 / 500000000) (-191934009 / 250000000) (Real.log (297 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (214188841 / 500000000) ≤ -Real.log (2560 / 3929) ∧
    -Real.log (2560 / 3929) ≤ (428377683 / 1000000000) := by
  have h := checkLog_sound (w := (1369 / 6489)) (n := 12)
    (lo := (214188841 / 500000000)) (hi := (428377683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3929 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3929 / 2560) = 1/(2560 / 3929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (214188841 / 500000000) (428377683 / 1000000000) (Real.log (3929 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3929 / 2560) = -Real.log (2560 / 3929) := by
    rw [show ((3929 / 2560) : ℝ) = ((2560 / 3929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (765213967 / 1000000000) ≤ -Real.log (1191 / 2560) ∧
    -Real.log (1191 / 2560) ≤ (765213969 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 2471)) (n := 12)
    (lo := (72066787 / 1000000000)) (hi := (18016697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1191) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1191) = 1/(1191 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-765213969 / 1000000000) (-765213967 / 1000000000) (Real.log (1191 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (324455321 / 1000000000) ≤ -Real.log (1000000 / 1383277) ∧
    -Real.log (1000000 / 1383277) ≤ (162227661 / 500000000) := by
  have h := checkLog_sound (w := (383277 / 2383277)) (n := 12)
    (lo := (324455321 / 1000000000)) (hi := (162227661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1383277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1383277 / 1000000) = 1/(1000000 / 1383277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (324455321 / 1000000000) (162227661 / 500000000) (Real.log (1383277 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1383277 / 1000000) = -Real.log (1000000 / 1383277) := by
    rw [show ((1383277 / 1000000) : ℝ) = ((1000000 / 1383277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (241667651 / 500000000) ≤ -Real.log (616723 / 1000000) ∧
    -Real.log (616723 / 1000000) ≤ (483335303 / 1000000000) := by
  have h := checkLog_sound (w := (383277 / 1616723)) (n := 12)
    (lo := (241667651 / 500000000)) (hi := (483335303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 616723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 616723) = 1/(616723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-483335303 / 1000000000) (-241667651 / 500000000) (Real.log (616723 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (162540949 / 500000000) ≤ -Real.log (62500 / 86509) ∧
    -Real.log (62500 / 86509) ≤ (325081899 / 1000000000) := by
  have h := checkLog_sound (w := (24009 / 149009)) (n := 12)
    (lo := (162540949 / 500000000)) (hi := (325081899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86509 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86509 / 62500) = 1/(62500 / 86509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (162540949 / 500000000) (325081899 / 1000000000) (Real.log (86509 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (86509 / 62500) = -Real.log (62500 / 86509) := by
    rw [show ((86509 / 62500) : ℝ) = ((62500 / 86509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (484742109 / 1000000000) ≤ -Real.log (38491 / 62500) ∧
    -Real.log (38491 / 62500) ≤ (48474211 / 100000000) := by
  have h := checkLog_sound (w := (24009 / 100991)) (n := 12)
    (lo := (484742109 / 1000000000)) (hi := (48474211 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 38491) = 1/(38491 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48474211 / 100000000) (-484742109 / 1000000000) (Real.log (38491 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (248805839 / 1000000000) ≤ -Real.log (1000000 / 1282493) ∧
    -Real.log (1000000 / 1282493) ≤ (3110073 / 12500000) := by
  have h := checkLog_sound (w := (282493 / 2282493)) (n := 12)
    (lo := (248805839 / 1000000000)) (hi := (3110073 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1282493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1282493 / 1000000) = 1/(1000000 / 1282493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (248805839 / 1000000000) (3110073 / 12500000) (Real.log (1282493 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1282493 / 1000000) = -Real.log (1000000 / 1282493) := by
    rw [show ((1282493 / 1000000) : ℝ) = ((1000000 / 1282493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (13278903 / 40000000) ≤ -Real.log (717507 / 1000000) ∧
    -Real.log (717507 / 1000000) ≤ (10374143 / 31250000) := by
  have h := checkLog_sound (w := (282493 / 1717507)) (n := 12)
    (lo := (13278903 / 40000000)) (hi := (10374143 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 717507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 717507) = 1/(717507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10374143 / 31250000) (-13278903 / 40000000) (Real.log (717507 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (249346827 / 1000000000) ≤ -Real.log (1000000 / 1283187) ∧
    -Real.log (1000000 / 1283187) ≤ (62336707 / 250000000) := by
  have h := checkLog_sound (w := (283187 / 2283187)) (n := 12)
    (lo := (249346827 / 1000000000)) (hi := (62336707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283187 / 1000000) = 1/(1000000 / 1283187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (249346827 / 1000000000) (62336707 / 250000000) (Real.log (1283187 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1283187 / 1000000) = -Real.log (1000000 / 1283187) := by
    rw [show ((1283187 / 1000000) : ℝ) = ((1000000 / 1283187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (332940281 / 1000000000) ≤ -Real.log (716813 / 1000000) ∧
    -Real.log (716813 / 1000000) ≤ (166470141 / 500000000) := by
  have h := checkLog_sound (w := (283187 / 1716813)) (n := 12)
    (lo := (332940281 / 1000000000)) (hi := (166470141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 716813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 716813) = 1/(716813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-166470141 / 500000000) (-332940281 / 1000000000) (Real.log (716813 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (807790623 / 1000000000) ≤ -Real.log (250000000000 / 560736748913) ∧
    -Real.log (250000000000 / 560736748913) ≤ (258493 / 320000) := by
  have h := checkLog_sound (w := (60736748913 / 1060736748913)) (n := 12)
    (lo := (114643443 / 1000000000)) (hi := (28660861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((560736748913 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(560736748913 / 500000000000) = 1/(250000000000 / 560736748913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (807790623 / 1000000000) (258493 / 320000) (Real.log (560736748913 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (560736748913 / 250000000000) = -Real.log (250000000000 / 560736748913) := by
    rw [show ((560736748913 / 250000000000) : ℝ) = ((250000000000 / 560736748913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (404912003 / 500000000) ≤ -Real.log (500000000000 / 1123756202749) ∧
    -Real.log (500000000000 / 1123756202749) ≤ (101228001 / 125000000) := by
  have h := checkLog_sound (w := (123756202749 / 2123756202749)) (n := 12)
    (lo := (58338413 / 500000000)) (hi := (116676827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1123756202749 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1123756202749 / 1000000000000) = 1/(500000000000 / 1123756202749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (404912003 / 500000000) (101228001 / 125000000) (Real.log (1123756202749 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1123756202749 / 500000000000) = -Real.log (500000000000 / 1123756202749) := by
    rw [show ((1123756202749 / 500000000000) : ℝ) = ((500000000000 / 1123756202749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (116155683 / 200000000) ≤ -Real.log (25000000000 / 44685731289) ∧
    -Real.log (25000000000 / 44685731289) ≤ (36298651 / 62500000) := by
  have h := checkLog_sound (w := (19685731289 / 69685731289)) (n := 12)
    (lo := (116155683 / 200000000)) (hi := (36298651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44685731289 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44685731289 / 25000000000) = 1/(25000000000 / 44685731289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (116155683 / 200000000) (36298651 / 62500000) (Real.log (44685731289 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (44685731289 / 25000000000) = -Real.log (25000000000 / 44685731289) := by
    rw [show ((44685731289 / 25000000000) : ℝ) = ((25000000000 / 44685731289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (145571777 / 250000000) ≤ -Real.log (50000000000 / 89506398461) ∧
    -Real.log (50000000000 / 89506398461) ≤ (582287109 / 1000000000) := by
  have h := checkLog_sound (w := (39506398461 / 139506398461)) (n := 12)
    (lo := (145571777 / 250000000)) (hi := (582287109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89506398461 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89506398461 / 50000000000) = 1/(50000000000 / 89506398461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (145571777 / 250000000) (582287109 / 1000000000) (Real.log (89506398461 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (89506398461 / 50000000000) = -Real.log (50000000000 / 89506398461) := by
    rw [show ((89506398461 / 50000000000) : ℝ) = ((50000000000 / 89506398461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0262

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0263Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0263
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

theorem reflection_log_1_neg : (59238499 / 250000000) ≤ -Real.log (5120 / 6489) ∧
    -Real.log (5120 / 6489) ≤ (236953997 / 1000000000) := by
  have h := checkLog_sound (w := (1369 / 11609)) (n := 12)
    (lo := (59238499 / 250000000)) (hi := (236953997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6489 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6489 / 5120) = 1/(5120 / 6489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (59238499 / 250000000) (236953997 / 1000000000) (Real.log (6489 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6489 / 5120) = -Real.log (5120 / 6489) := by
    rw [show ((6489 / 5120) : ℝ) = ((5120 / 6489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (311131967 / 1000000000) ≤ -Real.log (3751 / 5120) ∧
    -Real.log (3751 / 5120) ≤ (4861437 / 15625000) := by
  have h := checkLog_sound (w := (1369 / 8871)) (n := 12)
    (lo := (311131967 / 1000000000)) (hi := (4861437 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3751) = 1/(3751 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4861437 / 15625000) (-311131967 / 1000000000) (Real.log (3751 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (14780723 / 62500000) ≤ -Real.log (2560 / 3243) ∧
    -Real.log (2560 / 3243) ≤ (236491569 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 5803)) (n := 12)
    (lo := (14780723 / 62500000)) (hi := (236491569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3243 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3243 / 2560) = 1/(2560 / 3243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (14780723 / 62500000) (236491569 / 1000000000) (Real.log (3243 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3243 / 2560) = -Real.log (2560 / 3243) := by
    rw [show ((3243 / 2560) : ℝ) = ((2560 / 3243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (124133 / 400000) ≤ -Real.log (1877 / 2560) ∧
    -Real.log (1877 / 2560) ≤ (310332501 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 4437)) (n := 12)
    (lo := (124133 / 400000)) (hi := (310332501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1877) = 1/(1877 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-310332501 / 1000000000) (-124133 / 400000) (Real.log (1877 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (214188841 / 500000000) ≤ -Real.log (2560 / 3929) ∧
    -Real.log (2560 / 3929) ≤ (428377683 / 1000000000) := by
  have h := checkLog_sound (w := (1369 / 6489)) (n := 12)
    (lo := (214188841 / 500000000)) (hi := (428377683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3929 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3929 / 2560) = 1/(2560 / 3929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (214188841 / 500000000) (428377683 / 1000000000) (Real.log (3929 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3929 / 2560) = -Real.log (2560 / 3929) := by
    rw [show ((3929 / 2560) : ℝ) = ((2560 / 3929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (765213967 / 1000000000) ≤ -Real.log (1191 / 2560) ∧
    -Real.log (1191 / 2560) ≤ (765213969 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 2471)) (n := 12)
    (lo := (72066787 / 1000000000)) (hi := (18016697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1191) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1191) = 1/(1191 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-765213969 / 1000000000) (-765213967 / 1000000000) (Real.log (1191 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (427613837 / 1000000000) ≤ -Real.log (1280 / 1963) ∧
    -Real.log (1280 / 1963) ≤ (213806919 / 500000000) := by
  have h := checkLog_sound (w := (683 / 3243)) (n := 12)
    (lo := (427613837 / 1000000000)) (hi := (213806919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963 / 1280) = 1/(1280 / 1963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (427613837 / 1000000000) (213806919 / 500000000) (Real.log (1963 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1963 / 1280) = -Real.log (1280 / 1963) := by
    rw [show ((1963 / 1280) : ℝ) = ((1280 / 1963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (381349121 / 500000000) ≤ -Real.log (597 / 1280) ∧
    -Real.log (597 / 1280) ≤ (190674561 / 250000000) := by
  have h := checkLog_sound (w := (43 / 1237)) (n := 12)
    (lo := (34775531 / 500000000)) (hi := (69551063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 597) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 597) = 1/(597 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-190674561 / 250000000) (-381349121 / 500000000) (Real.log (597 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (80957269 / 250000000) ≤ -Real.log (1000000 / 1382411) ∧
    -Real.log (1000000 / 1382411) ≤ (323829077 / 1000000000) := by
  have h := checkLog_sound (w := (382411 / 2382411)) (n := 12)
    (lo := (80957269 / 250000000)) (hi := (323829077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1382411 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1382411 / 1000000) = 1/(1000000 / 1382411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (80957269 / 250000000) (323829077 / 1000000000) (Real.log (1382411 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1382411 / 1000000) = -Real.log (1000000 / 1382411) := by
    rw [show ((1382411 / 1000000) : ℝ) = ((1000000 / 1382411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (481932091 / 1000000000) ≤ -Real.log (617589 / 1000000) ∧
    -Real.log (617589 / 1000000) ≤ (120483023 / 250000000) := by
  have h := checkLog_sound (w := (382411 / 1617589)) (n := 12)
    (lo := (481932091 / 1000000000)) (hi := (120483023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 617589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 617589) = 1/(617589 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-120483023 / 250000000) (-481932091 / 1000000000) (Real.log (617589 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (81114011 / 250000000) ≤ -Real.log (500000 / 691639) ∧
    -Real.log (500000 / 691639) ≤ (64891209 / 200000000) := by
  have h := checkLog_sound (w := (191639 / 1191639)) (n := 12)
    (lo := (81114011 / 250000000)) (hi := (64891209 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691639 / 500000) = 1/(500000 / 691639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (81114011 / 250000000) (64891209 / 200000000) (Real.log (691639 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (691639 / 500000) = -Real.log (500000 / 691639) := by
    rw [show ((691639 / 500000) : ℝ) = ((500000 / 691639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (483336923 / 1000000000) ≤ -Real.log (308361 / 500000) ∧
    -Real.log (308361 / 500000) ≤ (120834231 / 250000000) := by
  have h := checkLog_sound (w := (191639 / 808361)) (n := 12)
    (lo := (483336923 / 1000000000)) (hi := (120834231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 308361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 308361) = 1/(308361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-120834231 / 250000000) (-483336923 / 1000000000) (Real.log (308361 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2482669 / 10000000) ≤ -Real.log (500000 / 640901) ∧
    -Real.log (500000 / 640901) ≤ (248266901 / 1000000000) := by
  have h := checkLog_sound (w := (140901 / 1140901)) (n := 12)
    (lo := (2482669 / 10000000)) (hi := (248266901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640901 / 500000) = 1/(500000 / 640901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2482669 / 10000000) (248266901 / 1000000000) (Real.log (640901 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (640901 / 500000) = -Real.log (500000 / 640901) := by
    rw [show ((640901 / 500000) : ℝ) = ((500000 / 640901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (331009981 / 1000000000) ≤ -Real.log (359099 / 500000) ∧
    -Real.log (359099 / 500000) ≤ (165504991 / 500000000) := by
  have h := checkLog_sound (w := (140901 / 859099)) (n := 12)
    (lo := (331009981 / 1000000000)) (hi := (165504991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 359099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 359099) = 1/(359099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-165504991 / 500000000) (-331009981 / 1000000000) (Real.log (359099 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (248806619 / 1000000000) ≤ -Real.log (500000 / 641247) ∧
    -Real.log (500000 / 641247) ≤ (12440331 / 50000000) := by
  have h := checkLog_sound (w := (141247 / 1141247)) (n := 12)
    (lo := (248806619 / 1000000000)) (hi := (12440331 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641247 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641247 / 500000) = 1/(500000 / 641247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (248806619 / 1000000000) (12440331 / 50000000) (Real.log (641247 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (641247 / 500000) = -Real.log (500000 / 641247) := by
    rw [show ((641247 / 500000) : ℝ) = ((500000 / 641247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (331973969 / 1000000000) ≤ -Real.log (358753 / 500000) ∧
    -Real.log (358753 / 500000) ≤ (33197397 / 100000000) := by
  have h := checkLog_sound (w := (141247 / 858753)) (n := 12)
    (lo := (331973969 / 1000000000)) (hi := (33197397 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 358753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 358753) = 1/(358753 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-33197397 / 100000000) (-331973969 / 1000000000) (Real.log (358753 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (402880583 / 500000000) ≤ -Real.log (500000000000 / 1119199823831) ∧
    -Real.log (500000000000 / 1119199823831) ≤ (50360073 / 62500000) := by
  have h := checkLog_sound (w := (119199823831 / 2119199823831)) (n := 12)
    (lo := (56306993 / 500000000)) (hi := (112613987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1119199823831 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1119199823831 / 1000000000000) = 1/(500000000000 / 1119199823831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (402880583 / 500000000) (50360073 / 62500000) (Real.log (1119199823831 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1119199823831 / 500000000000) = -Real.log (500000000000 / 1119199823831) := by
    rw [show ((1119199823831 / 500000000000) : ℝ) = ((500000000000 / 1119199823831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (100974121 / 125000000) ≤ -Real.log (500000000000 / 1121476127007) ∧
    -Real.log (500000000000 / 1121476127007) ≤ (80779297 / 100000000) := by
  have h := checkLog_sound (w := (121476127007 / 2121476127007)) (n := 12)
    (lo := (28661447 / 250000000)) (hi := (114645789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121476127007 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1121476127007 / 1000000000000) = 1/(500000000000 / 1121476127007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (100974121 / 125000000) (80779297 / 100000000) (Real.log (1121476127007 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1121476127007 / 500000000000) = -Real.log (500000000000 / 1121476127007) := by
    rw [show ((1121476127007 / 500000000000) : ℝ) = ((500000000000 / 1121476127007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (289638441 / 500000000) ≤ -Real.log (25000000000 / 44618684541) ∧
    -Real.log (25000000000 / 44618684541) ≤ (579276883 / 1000000000) := by
  have h := checkLog_sound (w := (19618684541 / 69618684541)) (n := 12)
    (lo := (289638441 / 500000000)) (hi := (579276883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44618684541 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44618684541 / 25000000000) = 1/(25000000000 / 44618684541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (289638441 / 500000000) (579276883 / 1000000000) (Real.log (44618684541 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (44618684541 / 25000000000) = -Real.log (25000000000 / 44618684541) := by
    rw [show ((44618684541 / 25000000000) : ℝ) = ((25000000000 / 44618684541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (145195147 / 250000000) ≤ -Real.log (15625000000 / 27928642757) ∧
    -Real.log (15625000000 / 27928642757) ≤ (580780589 / 1000000000) := by
  have h := checkLog_sound (w := (12303642757 / 43553642757)) (n := 12)
    (lo := (145195147 / 250000000)) (hi := (580780589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27928642757 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27928642757 / 15625000000) = 1/(15625000000 / 27928642757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (145195147 / 250000000) (580780589 / 1000000000) (Real.log (27928642757 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (27928642757 / 15625000000) = -Real.log (15625000000 / 27928642757) := by
    rw [show ((27928642757 / 15625000000) : ℝ) = ((15625000000 / 27928642757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0263

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0264Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0264
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

theorem reflection_log_1_neg : (14780723 / 62500000) ≤ -Real.log (2560 / 3243) ∧
    -Real.log (2560 / 3243) ≤ (236491569 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 5803)) (n := 12)
    (lo := (14780723 / 62500000)) (hi := (236491569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3243 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3243 / 2560) = 1/(2560 / 3243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (14780723 / 62500000) (236491569 / 1000000000) (Real.log (3243 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3243 / 2560) = -Real.log (2560 / 3243) := by
    rw [show ((3243 / 2560) : ℝ) = ((2560 / 3243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (124133 / 400000) ≤ -Real.log (1877 / 2560) ∧
    -Real.log (1877 / 2560) ≤ (310332501 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 4437)) (n := 12)
    (lo := (124133 / 400000)) (hi := (310332501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1877) = 1/(1877 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-310332501 / 1000000000) (-124133 / 400000) (Real.log (1877 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (236028927 / 1000000000) ≤ -Real.log (5120 / 6483) ∧
    -Real.log (5120 / 6483) ≤ (460994 / 1953125) := by
  have h := checkLog_sound (w := (1363 / 11603)) (n := 12)
    (lo := (236028927 / 1000000000)) (hi := (460994 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6483 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6483 / 5120) = 1/(5120 / 6483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (236028927 / 1000000000) (460994 / 1953125) (Real.log (6483 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6483 / 5120) = -Real.log (5120 / 6483) := by
    rw [show ((6483 / 5120) : ℝ) = ((5120 / 6483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (38691709 / 125000000) ≤ -Real.log (3757 / 5120) ∧
    -Real.log (3757 / 5120) ≤ (309533673 / 1000000000) := by
  have h := checkLog_sound (w := (1363 / 8877)) (n := 12)
    (lo := (38691709 / 125000000)) (hi := (309533673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3757) = 1/(3757 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-309533673 / 1000000000) (-38691709 / 125000000) (Real.log (3757 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (427613837 / 1000000000) ≤ -Real.log (1280 / 1963) ∧
    -Real.log (1280 / 1963) ≤ (213806919 / 500000000) := by
  have h := checkLog_sound (w := (683 / 3243)) (n := 12)
    (lo := (427613837 / 1000000000)) (hi := (213806919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963 / 1280) = 1/(1280 / 1963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (427613837 / 1000000000) (213806919 / 500000000) (Real.log (1963 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1963 / 1280) = -Real.log (1280 / 1963) := by
    rw [show ((1963 / 1280) : ℝ) = ((1280 / 1963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (381349121 / 500000000) ≤ -Real.log (597 / 1280) ∧
    -Real.log (597 / 1280) ≤ (190674561 / 250000000) := by
  have h := checkLog_sound (w := (43 / 1237)) (n := 12)
    (lo := (34775531 / 500000000)) (hi := (69551063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 597) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 597) = 1/(597 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-190674561 / 250000000) (-381349121 / 500000000) (Real.log (597 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (3334761 / 7812500) ≤ -Real.log (2560 / 3923) ∧
    -Real.log (2560 / 3923) ≤ (426849409 / 1000000000) := by
  have h := checkLog_sound (w := (1363 / 6483)) (n := 12)
    (lo := (3334761 / 7812500)) (hi := (426849409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3923 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3923 / 2560) = 1/(2560 / 3923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (3334761 / 7812500) (426849409 / 1000000000) (Real.log (3923 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3923 / 2560) = -Real.log (2560 / 3923) := by
    rw [show ((3923 / 2560) : ℝ) = ((2560 / 3923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (760188831 / 1000000000) ≤ -Real.log (1197 / 2560) ∧
    -Real.log (1197 / 2560) ≤ (760188833 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 2477)) (n := 12)
    (lo := (67041651 / 1000000000)) (hi := (16760413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1197) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1197) = 1/(1197 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-760188833 / 1000000000) (-760188831 / 1000000000) (Real.log (1197 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (323203161 / 1000000000) ≤ -Real.log (500000 / 690773) ∧
    -Real.log (500000 / 690773) ≤ (161601581 / 500000000) := by
  have h := checkLog_sound (w := (190773 / 1190773)) (n := 12)
    (lo := (323203161 / 1000000000)) (hi := (161601581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690773 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690773 / 500000) = 1/(500000 / 690773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (323203161 / 1000000000) (161601581 / 500000000) (Real.log (690773 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (690773 / 500000) = -Real.log (500000 / 690773) := by
    rw [show ((690773 / 500000) : ℝ) = ((500000 / 690773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (480532463 / 1000000000) ≤ -Real.log (309227 / 500000) ∧
    -Real.log (309227 / 500000) ≤ (30033279 / 62500000) := by
  have h := checkLog_sound (w := (190773 / 809227)) (n := 12)
    (lo := (480532463 / 1000000000)) (hi := (30033279 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 309227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 309227) = 1/(309227 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-30033279 / 62500000) (-480532463 / 1000000000) (Real.log (309227 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (323829799 / 1000000000) ≤ -Real.log (250000 / 345603) ∧
    -Real.log (250000 / 345603) ≤ (1619149 / 5000000) := by
  have h := checkLog_sound (w := (95603 / 595603)) (n := 12)
    (lo := (323829799 / 1000000000)) (hi := (1619149 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345603 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345603 / 250000) = 1/(250000 / 345603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (323829799 / 1000000000) (1619149 / 5000000) (Real.log (345603 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (345603 / 250000) = -Real.log (250000 / 345603) := by
    rw [show ((345603 / 250000) : ℝ) = ((250000 / 345603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (48193371 / 100000000) ≤ -Real.log (154397 / 250000) ∧
    -Real.log (154397 / 250000) ≤ (481933711 / 1000000000) := by
  have h := checkLog_sound (w := (95603 / 404397)) (n := 12)
    (lo := (48193371 / 100000000)) (hi := (481933711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 154397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 154397) = 1/(154397 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-481933711 / 1000000000) (-48193371 / 100000000) (Real.log (154397 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (24772767 / 100000000) ≤ -Real.log (1000000 / 1281111) ∧
    -Real.log (1000000 / 1281111) ≤ (247727671 / 1000000000) := by
  have h := checkLog_sound (w := (281111 / 2281111)) (n := 12)
    (lo := (24772767 / 100000000)) (hi := (247727671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281111 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281111 / 1000000) = 1/(1000000 / 1281111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (24772767 / 100000000) (247727671 / 1000000000) (Real.log (1281111 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1281111 / 1000000) = -Real.log (1000000 / 1281111) := by
    rw [show ((1281111 / 1000000) : ℝ) = ((1000000 / 1281111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (165024157 / 500000000) ≤ -Real.log (718889 / 1000000) ∧
    -Real.log (718889 / 1000000) ≤ (66009663 / 200000000) := by
  have h := checkLog_sound (w := (281111 / 1718889)) (n := 12)
    (lo := (165024157 / 500000000)) (hi := (66009663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718889) = 1/(718889 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-66009663 / 200000000) (-165024157 / 500000000) (Real.log (718889 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1551673 / 6250000) ≤ -Real.log (1000000 / 1281803) ∧
    -Real.log (1000000 / 1281803) ≤ (248267681 / 1000000000) := by
  have h := checkLog_sound (w := (281803 / 2281803)) (n := 12)
    (lo := (1551673 / 6250000)) (hi := (248267681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281803 / 1000000) = 1/(1000000 / 1281803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1551673 / 6250000) (248267681 / 1000000000) (Real.log (1281803 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1281803 / 1000000) = -Real.log (1000000 / 1281803) := by
    rw [show ((1281803 / 1000000) : ℝ) = ((1000000 / 1281803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (165505687 / 500000000) ≤ -Real.log (718197 / 1000000) ∧
    -Real.log (718197 / 1000000) ≤ (2648091 / 8000000) := by
  have h := checkLog_sound (w := (281803 / 1718197)) (n := 12)
    (lo := (165505687 / 500000000)) (hi := (2648091 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718197) = 1/(718197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2648091 / 8000000) (-165505687 / 500000000) (Real.log (718197 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (100466953 / 125000000) ≤ -Real.log (125000000000 / 279233782949) ∧
    -Real.log (125000000000 / 279233782949) ≤ (401867813 / 500000000) := by
  have h := checkLog_sound (w := (29233782949 / 529233782949)) (n := 12)
    (lo := (27647111 / 250000000)) (hi := (22117689 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279233782949 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(279233782949 / 250000000000) = 1/(125000000000 / 279233782949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (100466953 / 125000000) (401867813 / 500000000) (Real.log (279233782949 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (279233782949 / 125000000000) = -Real.log (125000000000 / 279233782949) := by
    rw [show ((279233782949 / 125000000000) : ℝ) = ((125000000000 / 279233782949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (805763509 / 1000000000) ≤ -Real.log (125000000000 / 279800611411) ∧
    -Real.log (125000000000 / 279800611411) ≤ (805763511 / 1000000000) := by
  have h := checkLog_sound (w := (29800611411 / 529800611411)) (n := 12)
    (lo := (112616329 / 1000000000)) (hi := (11261633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279800611411 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(279800611411 / 250000000000) = 1/(125000000000 / 279800611411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (805763509 / 1000000000) (805763511 / 1000000000) (Real.log (279800611411 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (279800611411 / 125000000000) = -Real.log (125000000000 / 279800611411) := by
    rw [show ((279800611411 / 125000000000) : ℝ) = ((125000000000 / 279800611411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (36110999 / 62500000) ≤ -Real.log (62500000000 / 111379416711) ∧
    -Real.log (62500000000 / 111379416711) ≤ (115555197 / 200000000) := by
  have h := checkLog_sound (w := (48879416711 / 173879416711)) (n := 12)
    (lo := (36110999 / 62500000)) (hi := (115555197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111379416711 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111379416711 / 62500000000) = 1/(62500000000 / 111379416711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (36110999 / 62500000) (115555197 / 200000000) (Real.log (111379416711 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (111379416711 / 62500000000) = -Real.log (62500000000 / 111379416711) := by
    rw [show ((111379416711 / 62500000000) : ℝ) = ((62500000000 / 111379416711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (289639527 / 500000000) ≤ -Real.log (62500000000 / 111546953691) ∧
    -Real.log (62500000000 / 111546953691) ≤ (115855811 / 200000000) := by
  have h := checkLog_sound (w := (49046953691 / 174046953691)) (n := 12)
    (lo := (289639527 / 500000000)) (hi := (115855811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111546953691 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111546953691 / 62500000000) = 1/(62500000000 / 111546953691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (289639527 / 500000000) (115855811 / 200000000) (Real.log (111546953691 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (111546953691 / 62500000000) = -Real.log (62500000000 / 111546953691) := by
    rw [show ((111546953691 / 62500000000) : ℝ) = ((62500000000 / 111546953691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0264

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0265Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0265
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

theorem reflection_log_1_neg : (236028927 / 1000000000) ≤ -Real.log (5120 / 6483) ∧
    -Real.log (5120 / 6483) ≤ (460994 / 1953125) := by
  have h := checkLog_sound (w := (1363 / 11603)) (n := 12)
    (lo := (236028927 / 1000000000)) (hi := (460994 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6483 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6483 / 5120) = 1/(5120 / 6483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (236028927 / 1000000000) (460994 / 1953125) (Real.log (6483 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6483 / 5120) = -Real.log (5120 / 6483) := by
    rw [show ((6483 / 5120) : ℝ) = ((5120 / 6483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (38691709 / 125000000) ≤ -Real.log (3757 / 5120) ∧
    -Real.log (3757 / 5120) ≤ (309533673 / 1000000000) := by
  have h := checkLog_sound (w := (1363 / 8877)) (n := 12)
    (lo := (38691709 / 125000000)) (hi := (309533673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3757) = 1/(3757 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-309533673 / 1000000000) (-38691709 / 125000000) (Real.log (3757 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (235566071 / 1000000000) ≤ -Real.log (64 / 81) ∧
    -Real.log (64 / 81) ≤ (29445759 / 125000000) := by
  have h := checkLog_sound (w := (17 / 145)) (n := 12)
    (lo := (235566071 / 1000000000)) (hi := (29445759 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81 / 64) = 1/(64 / 81) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (235566071 / 1000000000) (29445759 / 125000000) (Real.log (81 / 64)) := by
  have h := reflection_log_3_neg
  have he : Real.log (81 / 64) = -Real.log (64 / 81) := by
    rw [show ((81 / 64) : ℝ) = ((64 / 81) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (308735481 / 1000000000) ≤ -Real.log (47 / 64) ∧
    -Real.log (47 / 64) ≤ (154367741 / 500000000) := by
  have h := checkLog_sound (w := (17 / 111)) (n := 12)
    (lo := (308735481 / 1000000000)) (hi := (154367741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 47) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 47) = 1/(47 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-154367741 / 500000000) (-308735481 / 1000000000) (Real.log (47 / 64)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (3334761 / 7812500) ≤ -Real.log (2560 / 3923) ∧
    -Real.log (2560 / 3923) ≤ (426849409 / 1000000000) := by
  have h := checkLog_sound (w := (1363 / 6483)) (n := 12)
    (lo := (3334761 / 7812500)) (hi := (426849409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3923 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3923 / 2560) = 1/(2560 / 3923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (3334761 / 7812500) (426849409 / 1000000000) (Real.log (3923 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3923 / 2560) = -Real.log (2560 / 3923) := by
    rw [show ((3923 / 2560) : ℝ) = ((2560 / 3923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (760188831 / 1000000000) ≤ -Real.log (1197 / 2560) ∧
    -Real.log (1197 / 2560) ≤ (760188833 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 2477)) (n := 12)
    (lo := (67041651 / 1000000000)) (hi := (16760413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1197) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1197) = 1/(1197 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-760188833 / 1000000000) (-760188831 / 1000000000) (Real.log (1197 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (85216879 / 200000000) ≤ -Real.log (32 / 49) ∧
    -Real.log (32 / 49) ≤ (106521099 / 250000000) := by
  have h := checkLog_sound (w := (17 / 81)) (n := 12)
    (lo := (85216879 / 200000000)) (hi := (106521099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49 / 32) = 1/(32 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (85216879 / 200000000) (106521099 / 250000000) (Real.log (49 / 32)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49 / 32) = -Real.log (32 / 49) := by
    rw [show ((49 / 32) : ℝ) = ((32 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (757685701 / 1000000000) ≤ -Real.log (15 / 32) ∧
    -Real.log (15 / 32) ≤ (757685703 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 15) = 1/(15 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-757685703 / 1000000000) (-757685701 / 1000000000) (Real.log (15 / 32)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (322576131 / 1000000000) ≤ -Real.log (25000 / 34517) ∧
    -Real.log (25000 / 34517) ≤ (80644033 / 250000000) := by
  have h := checkLog_sound (w := (9517 / 59517)) (n := 12)
    (lo := (322576131 / 1000000000)) (hi := (80644033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34517 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34517 / 25000) = 1/(25000 / 34517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (322576131 / 1000000000) (80644033 / 250000000) (Real.log (34517 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (34517 / 25000) = -Real.log (25000 / 34517) := by
    rw [show ((34517 / 25000) : ℝ) = ((25000 / 34517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (479133177 / 1000000000) ≤ -Real.log (15483 / 25000) ∧
    -Real.log (15483 / 25000) ≤ (239566589 / 500000000) := by
  have h := checkLog_sound (w := (9517 / 40483)) (n := 12)
    (lo := (479133177 / 1000000000)) (hi := (239566589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 15483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 15483) = 1/(15483 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-239566589 / 500000000) (-479133177 / 1000000000) (Real.log (15483 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64640777 / 200000000) ≤ -Real.log (1000000 / 1381547) ∧
    -Real.log (1000000 / 1381547) ≤ (161601943 / 500000000) := by
  have h := checkLog_sound (w := (381547 / 2381547)) (n := 12)
    (lo := (64640777 / 200000000)) (hi := (161601943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1381547 / 1000000) = 1/(1000000 / 1381547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64640777 / 200000000) (161601943 / 500000000) (Real.log (1381547 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1381547 / 1000000) = -Real.log (1000000 / 1381547) := by
    rw [show ((1381547 / 1000000) : ℝ) = ((1000000 / 1381547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1501669 / 3125000) ≤ -Real.log (618453 / 1000000) ∧
    -Real.log (618453 / 1000000) ≤ (480534081 / 1000000000) := by
  have h := checkLog_sound (w := (381547 / 1618453)) (n := 12)
    (lo := (1501669 / 3125000)) (hi := (480534081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 618453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 618453) = 1/(618453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-480534081 / 1000000000) (-1501669 / 3125000) (Real.log (618453 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (247188149 / 1000000000) ≤ -Real.log (50000 / 64021) ∧
    -Real.log (50000 / 64021) ≤ (4943763 / 20000000) := by
  have h := checkLog_sound (w := (14021 / 114021)) (n := 12)
    (lo := (247188149 / 1000000000)) (hi := (4943763 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64021 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64021 / 50000) = 1/(50000 / 64021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (247188149 / 1000000000) (4943763 / 20000000) (Real.log (64021 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (64021 / 50000) = -Real.log (50000 / 64021) := by
    rw [show ((64021 / 50000) : ℝ) = ((50000 / 64021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (32908757 / 100000000) ≤ -Real.log (35979 / 50000) ∧
    -Real.log (35979 / 50000) ≤ (329087571 / 1000000000) := by
  have h := checkLog_sound (w := (14021 / 85979)) (n := 12)
    (lo := (32908757 / 100000000)) (hi := (329087571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 35979) = 1/(35979 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-329087571 / 1000000000) (-32908757 / 100000000) (Real.log (35979 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (4954569 / 20000000) ≤ -Real.log (125000 / 160139) ∧
    -Real.log (125000 / 160139) ≤ (247728451 / 1000000000) := by
  have h := checkLog_sound (w := (35139 / 285139)) (n := 12)
    (lo := (4954569 / 20000000)) (hi := (247728451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160139 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160139 / 125000) = 1/(125000 / 160139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4954569 / 20000000) (247728451 / 1000000000) (Real.log (160139 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (160139 / 125000) = -Real.log (125000 / 160139) := by
    rw [show ((160139 / 125000) : ℝ) = ((125000 / 160139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (66009941 / 200000000) ≤ -Real.log (89861 / 125000) ∧
    -Real.log (89861 / 125000) ≤ (165024853 / 500000000) := by
  have h := checkLog_sound (w := (35139 / 214861)) (n := 12)
    (lo := (66009941 / 200000000)) (hi := (165024853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89861) = 1/(89861 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-165024853 / 500000000) (-66009941 / 200000000) (Real.log (89861 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (801709307 / 1000000000) ≤ -Real.log (250000000000 / 557337079377) ∧
    -Real.log (250000000000 / 557337079377) ≤ (801709309 / 1000000000) := by
  have h := checkLog_sound (w := (57337079377 / 1057337079377)) (n := 12)
    (lo := (108562127 / 1000000000)) (hi := (6785133 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557337079377 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(557337079377 / 500000000000) = 1/(250000000000 / 557337079377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (801709307 / 1000000000) (801709309 / 1000000000) (Real.log (557337079377 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (557337079377 / 250000000000) = -Real.log (250000000000 / 557337079377) := by
    rw [show ((557337079377 / 250000000000) : ℝ) = ((250000000000 / 557337079377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (160747593 / 200000000) ≤ -Real.log (12500000000 / 27923443657) ∧
    -Real.log (12500000000 / 27923443657) ≤ (803737967 / 1000000000) := by
  have h := checkLog_sound (w := (2923443657 / 52923443657)) (n := 12)
    (lo := (22118157 / 200000000)) (hi := (55295393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27923443657 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(27923443657 / 25000000000) = 1/(12500000000 / 27923443657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (160747593 / 200000000) (803737967 / 1000000000) (Real.log (27923443657 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (27923443657 / 12500000000) = -Real.log (12500000000 / 27923443657) := by
    rw [show ((27923443657 / 12500000000) : ℝ) = ((12500000000 / 27923443657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (576275719 / 1000000000) ≤ -Real.log (500000000000 / 889699546957) ∧
    -Real.log (500000000000 / 889699546957) ≤ (14406893 / 25000000) := by
  have h := checkLog_sound (w := (389699546957 / 1389699546957)) (n := 12)
    (lo := (576275719 / 1000000000)) (hi := (14406893 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((889699546957 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(889699546957 / 500000000000) = 1/(500000000000 / 889699546957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (576275719 / 1000000000) (14406893 / 25000000) (Real.log (889699546957 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (889699546957 / 500000000000) = -Real.log (500000000000 / 889699546957) := by
    rw [show ((889699546957 / 500000000000) : ℝ) = ((500000000000 / 889699546957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (144444539 / 250000000) ≤ -Real.log (500000000000 / 891037268671) ∧
    -Real.log (500000000000 / 891037268671) ≤ (577778157 / 1000000000) := by
  have h := checkLog_sound (w := (391037268671 / 1391037268671)) (n := 12)
    (lo := (144444539 / 250000000)) (hi := (577778157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891037268671 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891037268671 / 500000000000) = 1/(500000000000 / 891037268671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (144444539 / 250000000) (577778157 / 1000000000) (Real.log (891037268671 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (891037268671 / 500000000000) = -Real.log (500000000000 / 891037268671) := by
    rw [show ((891037268671 / 500000000000) : ℝ) = ((500000000000 / 891037268671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0265

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0266Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0266
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

theorem reflection_log_1_neg : (235566071 / 1000000000) ≤ -Real.log (64 / 81) ∧
    -Real.log (64 / 81) ≤ (29445759 / 125000000) := by
  have h := checkLog_sound (w := (17 / 145)) (n := 12)
    (lo := (235566071 / 1000000000)) (hi := (29445759 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81 / 64) = 1/(64 / 81) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (235566071 / 1000000000) (29445759 / 125000000) (Real.log (81 / 64)) := by
  have h := reflection_log_1_neg
  have he : Real.log (81 / 64) = -Real.log (64 / 81) := by
    rw [show ((81 / 64) : ℝ) = ((64 / 81) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (308735481 / 1000000000) ≤ -Real.log (47 / 64) ∧
    -Real.log (47 / 64) ≤ (154367741 / 500000000) := by
  have h := checkLog_sound (w := (17 / 111)) (n := 12)
    (lo := (308735481 / 1000000000)) (hi := (154367741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 47) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 47) = 1/(47 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-154367741 / 500000000) (-308735481 / 1000000000) (Real.log (47 / 64)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (235103001 / 1000000000) ≤ -Real.log (5120 / 6477) ∧
    -Real.log (5120 / 6477) ≤ (117551501 / 500000000) := by
  have h := checkLog_sound (w := (1357 / 11597)) (n := 12)
    (lo := (235103001 / 1000000000)) (hi := (117551501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6477 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6477 / 5120) = 1/(5120 / 6477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (235103001 / 1000000000) (117551501 / 500000000) (Real.log (6477 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6477 / 5120) = -Real.log (5120 / 6477) := by
    rw [show ((6477 / 5120) : ℝ) = ((5120 / 6477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (307937927 / 1000000000) ≤ -Real.log (3763 / 5120) ∧
    -Real.log (3763 / 5120) ≤ (38492241 / 125000000) := by
  have h := checkLog_sound (w := (1357 / 8883)) (n := 12)
    (lo := (307937927 / 1000000000)) (hi := (38492241 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3763) = 1/(3763 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-38492241 / 125000000) (-307937927 / 1000000000) (Real.log (3763 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (85216879 / 200000000) ≤ -Real.log (32 / 49) ∧
    -Real.log (32 / 49) ≤ (106521099 / 250000000) := by
  have h := checkLog_sound (w := (17 / 81)) (n := 12)
    (lo := (85216879 / 200000000)) (hi := (106521099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49 / 32) = 1/(32 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (85216879 / 200000000) (106521099 / 250000000) (Real.log (49 / 32)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49 / 32) = -Real.log (32 / 49) := by
    rw [show ((49 / 32) : ℝ) = ((32 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (757685701 / 1000000000) ≤ -Real.log (15 / 32) ∧
    -Real.log (15 / 32) ≤ (757685703 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 15) = 1/(15 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-757685703 / 1000000000) (-757685701 / 1000000000) (Real.log (15 / 32)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (106329699 / 250000000) ≤ -Real.log (2560 / 3917) ∧
    -Real.log (2560 / 3917) ≤ (425318797 / 1000000000) := by
  have h := checkLog_sound (w := (1357 / 6477)) (n := 12)
    (lo := (106329699 / 250000000)) (hi := (425318797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3917 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3917 / 2560) = 1/(2560 / 3917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (106329699 / 250000000) (425318797 / 1000000000) (Real.log (3917 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3917 / 2560) = -Real.log (2560 / 3917) := by
    rw [show ((3917 / 2560) : ℝ) = ((2560 / 3917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (37759441 / 50000000) ≤ -Real.log (1203 / 2560) ∧
    -Real.log (1203 / 2560) ≤ (377594411 / 500000000) := by
  have h := checkLog_sound (w := (77 / 2483)) (n := 12)
    (lo := (1551041 / 25000000)) (hi := (62041641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1203) = 1/(1203 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-377594411 / 500000000) (-37759441 / 50000000) (Real.log (1203 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40243679 / 125000000) ≤ -Real.log (200000 / 275963) ∧
    -Real.log (200000 / 275963) ≤ (321949433 / 1000000000) := by
  have h := checkLog_sound (w := (75963 / 475963)) (n := 12)
    (lo := (40243679 / 125000000)) (hi := (321949433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275963 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(275963 / 200000) = 1/(200000 / 275963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40243679 / 125000000) (321949433 / 1000000000) (Real.log (275963 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (275963 / 200000) = -Real.log (200000 / 275963) := by
    rw [show ((275963 / 200000) : ℝ) = ((200000 / 275963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (238868729 / 500000000) ≤ -Real.log (124037 / 200000) ∧
    -Real.log (124037 / 200000) ≤ (477737459 / 1000000000) := by
  have h := checkLog_sound (w := (75963 / 324037)) (n := 12)
    (lo := (238868729 / 500000000)) (hi := (477737459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 124037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 124037) = 1/(124037 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-477737459 / 1000000000) (-238868729 / 500000000) (Real.log (124037 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64515371 / 200000000) ≤ -Real.log (1000000 / 1380681) ∧
    -Real.log (1000000 / 1380681) ≤ (40322107 / 125000000) := by
  have h := checkLog_sound (w := (380681 / 2380681)) (n := 12)
    (lo := (64515371 / 200000000)) (hi := (40322107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1380681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1380681 / 1000000) = 1/(1000000 / 1380681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64515371 / 200000000) (40322107 / 125000000) (Real.log (1380681 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1380681 / 1000000) = -Real.log (1000000 / 1380681) := by
    rw [show ((1380681 / 1000000) : ℝ) = ((1000000 / 1380681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (479134791 / 1000000000) ≤ -Real.log (619319 / 1000000) ∧
    -Real.log (619319 / 1000000) ≤ (59891849 / 125000000) := by
  have h := checkLog_sound (w := (380681 / 1619319)) (n := 12)
    (lo := (479134791 / 1000000000)) (hi := (59891849 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 619319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 619319) = 1/(619319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-59891849 / 125000000) (-479134791 / 1000000000) (Real.log (619319 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (123324559 / 500000000) ≤ -Real.log (100000 / 127973) ∧
    -Real.log (100000 / 127973) ≤ (246649119 / 1000000000) := by
  have h := checkLog_sound (w := (27973 / 227973)) (n := 12)
    (lo := (123324559 / 500000000)) (hi := (246649119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127973 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127973 / 100000) = 1/(100000 / 127973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (123324559 / 500000000) (246649119 / 1000000000) (Real.log (127973 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (127973 / 100000) = -Real.log (100000 / 127973) := by
    rw [show ((127973 / 100000) : ℝ) = ((100000 / 127973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (328129137 / 1000000000) ≤ -Real.log (72027 / 100000) ∧
    -Real.log (72027 / 100000) ≤ (164064569 / 500000000) := by
  have h := checkLog_sound (w := (27973 / 172027)) (n := 12)
    (lo := (328129137 / 1000000000)) (hi := (164064569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72027) = 1/(72027 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-164064569 / 500000000) (-328129137 / 1000000000) (Real.log (72027 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (24718893 / 100000000) ≤ -Real.log (1000000 / 1280421) ∧
    -Real.log (1000000 / 1280421) ≤ (247188931 / 1000000000) := by
  have h := checkLog_sound (w := (280421 / 2280421)) (n := 12)
    (lo := (24718893 / 100000000)) (hi := (247188931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280421 / 1000000) = 1/(1000000 / 1280421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (24718893 / 100000000) (247188931 / 1000000000) (Real.log (1280421 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1280421 / 1000000) = -Real.log (1000000 / 1280421) := by
    rw [show ((1280421 / 1000000) : ℝ) = ((1000000 / 1280421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1028403 / 3125000) ≤ -Real.log (719579 / 1000000) ∧
    -Real.log (719579 / 1000000) ≤ (329088961 / 1000000000) := by
  have h := checkLog_sound (w := (280421 / 1719579)) (n := 12)
    (lo := (1028403 / 3125000)) (hi := (329088961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 719579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 719579) = 1/(719579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-329088961 / 1000000000) (-1028403 / 3125000) (Real.log (719579 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (79968689 / 100000000) ≤ -Real.log (500000000000 / 1112422099857) ∧
    -Real.log (500000000000 / 1112422099857) ≤ (199921723 / 250000000) := by
  have h := checkLog_sound (w := (112422099857 / 2112422099857)) (n := 12)
    (lo := (10653971 / 100000000)) (hi := (106539711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112422099857 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1112422099857 / 1000000000000) = 1/(500000000000 / 1112422099857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (79968689 / 100000000) (199921723 / 250000000) (Real.log (1112422099857 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1112422099857 / 500000000000) = -Real.log (500000000000 / 1112422099857) := by
    rw [show ((1112422099857 / 500000000000) : ℝ) = ((500000000000 / 1112422099857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (400855823 / 500000000) ≤ -Real.log (125000000000 / 278669191483) ∧
    -Real.log (125000000000 / 278669191483) ≤ (25053489 / 31250000) := by
  have h := checkLog_sound (w := (28669191483 / 528669191483)) (n := 12)
    (lo := (54282233 / 500000000)) (hi := (108564467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278669191483 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(278669191483 / 250000000000) = 1/(125000000000 / 278669191483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (400855823 / 500000000) (25053489 / 31250000) (Real.log (278669191483 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (278669191483 / 125000000000) = -Real.log (125000000000 / 278669191483) := by
    rw [show ((278669191483 / 125000000000) : ℝ) = ((125000000000 / 278669191483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (114955651 / 200000000) ≤ -Real.log (250000000000 / 444184125397) ∧
    -Real.log (250000000000 / 444184125397) ≤ (35923641 / 62500000) := by
  have h := checkLog_sound (w := (194184125397 / 694184125397)) (n := 12)
    (lo := (114955651 / 200000000)) (hi := (35923641 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444184125397 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444184125397 / 250000000000) = 1/(250000000000 / 444184125397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (114955651 / 200000000) (35923641 / 62500000) (Real.log (444184125397 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (444184125397 / 250000000000) = -Real.log (250000000000 / 444184125397) := by
    rw [show ((444184125397 / 250000000000) : ℝ) = ((250000000000 / 444184125397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (57627789 / 100000000) ≤ -Real.log (250000000000 / 444850739113) ∧
    -Real.log (250000000000 / 444850739113) ≤ (576277891 / 1000000000) := by
  have h := checkLog_sound (w := (194850739113 / 694850739113)) (n := 12)
    (lo := (57627789 / 100000000)) (hi := (576277891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444850739113 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444850739113 / 250000000000) = 1/(250000000000 / 444850739113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (57627789 / 100000000) (576277891 / 1000000000) (Real.log (444850739113 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (444850739113 / 250000000000) = -Real.log (250000000000 / 444850739113) := by
    rw [show ((444850739113 / 250000000000) : ℝ) = ((250000000000 / 444850739113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0266

end


