-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0274Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0274Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:05:11.829753+00:00
-- url     : https://prove2.me/theorems/9d7b4cfd-810d-4d09-8bfb-1b73907688fe
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0274Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0275Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0274Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0275Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0276Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0277Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0278Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0279Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0280Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0274Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0275Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0276Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0277Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0278Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0279Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0280Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0274Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0275Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0276Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0277Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0278Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0279Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0280Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0274Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0275Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0276Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0277Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0278Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0279Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0280Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0274Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0274
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

theorem reflection_log_1_neg : (231855491 / 1000000000) ≤ -Real.log (640 / 807) ∧
    -Real.log (640 / 807) ≤ (57963873 / 250000000) := by
  have h := checkLog_sound (w := (167 / 1447)) (n := 12)
    (lo := (231855491 / 1000000000)) (hi := (57963873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807 / 640) = 1/(640 / 807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (231855491 / 1000000000) (57963873 / 250000000) (Real.log (807 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (807 / 640) = -Real.log (640 / 807) := by
    rw [show ((807 / 640) : ℝ) = ((640 / 807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (302372787 / 1000000000) ≤ -Real.log (473 / 640) ∧
    -Real.log (473 / 640) ≤ (75593197 / 250000000) := by
  have h := checkLog_sound (w := (167 / 1113)) (n := 12)
    (lo := (302372787 / 1000000000)) (hi := (75593197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 473) = 1/(473 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-75593197 / 250000000) (-302372787 / 1000000000) (Real.log (473 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (231390699 / 1000000000) ≤ -Real.log (5120 / 6453) ∧
    -Real.log (5120 / 6453) ≤ (2313907 / 10000000) := by
  have h := checkLog_sound (w := (1333 / 11573)) (n := 12)
    (lo := (231390699 / 1000000000)) (hi := (2313907 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6453 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6453 / 5120) = 1/(5120 / 6453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (231390699 / 1000000000) (2313907 / 10000000) (Real.log (6453 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6453 / 5120) = -Real.log (5120 / 6453) := by
    rw [show ((6453 / 5120) : ℝ) = ((5120 / 6453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (30158029 / 100000000) ≤ -Real.log (3787 / 5120) ∧
    -Real.log (3787 / 5120) ≤ (301580291 / 1000000000) := by
  have h := checkLog_sound (w := (1333 / 8907)) (n := 12)
    (lo := (30158029 / 100000000)) (hi := (301580291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3787) = 1/(3787 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-301580291 / 1000000000) (-30158029 / 100000000) (Real.log (3787 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (419943127 / 1000000000) ≤ -Real.log (320 / 487) ∧
    -Real.log (320 / 487) ≤ (52492891 / 125000000) := by
  have h := checkLog_sound (w := (167 / 807)) (n := 12)
    (lo := (419943127 / 1000000000)) (hi := (52492891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487 / 320) = 1/(320 / 487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (419943127 / 1000000000) (52492891 / 125000000) (Real.log (487 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (487 / 320) = -Real.log (320 / 487) := by
    rw [show ((487 / 320) : ℝ) = ((320 / 487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (737883073 / 1000000000) ≤ -Real.log (153 / 320) ∧
    -Real.log (153 / 320) ≤ (29515323 / 40000000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 153) = 1/(153 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-29515323 / 40000000) (-737883073 / 1000000000) (Real.log (153 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41917281 / 100000000) ≤ -Real.log (2560 / 3893) ∧
    -Real.log (2560 / 3893) ≤ (419172811 / 1000000000) := by
  have h := checkLog_sound (w := (1333 / 6453)) (n := 12)
    (lo := (41917281 / 100000000)) (hi := (419172811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3893 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3893 / 2560) = 1/(2560 / 3893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41917281 / 100000000) (419172811 / 1000000000) (Real.log (3893 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3893 / 2560) = -Real.log (2560 / 3893) := by
    rw [show ((3893 / 2560) : ℝ) = ((2560 / 3893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (183858773 / 250000000) ≤ -Real.log (1227 / 2560) ∧
    -Real.log (1227 / 2560) ≤ (367717547 / 500000000) := by
  have h := checkLog_sound (w := (53 / 2507)) (n := 12)
    (lo := (5285989 / 125000000)) (hi := (42287913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1227) = 1/(1227 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-367717547 / 500000000) (-183858773 / 250000000) (Real.log (1227 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (316926747 / 1000000000) ≤ -Real.log (500000 / 686451) ∧
    -Real.log (500000 / 686451) ≤ (79231687 / 250000000) := by
  have h := checkLog_sound (w := (186451 / 1186451)) (n := 12)
    (lo := (316926747 / 1000000000)) (hi := (79231687 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686451 / 500000) = 1/(500000 / 686451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (316926747 / 1000000000) (79231687 / 250000000) (Real.log (686451 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (686451 / 500000) = -Real.log (500000 / 686451) := by
    rw [show ((686451 / 500000) : ℝ) = ((500000 / 686451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9333049 / 20000000) ≤ -Real.log (313549 / 500000) ∧
    -Real.log (313549 / 500000) ≤ (466652451 / 1000000000) := by
  have h := checkLog_sound (w := (186451 / 813549)) (n := 12)
    (lo := (9333049 / 20000000)) (hi := (466652451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 313549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 313549) = 1/(313549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-466652451 / 1000000000) (-9333049 / 20000000) (Real.log (313549 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (317555873 / 1000000000) ≤ -Real.log (500000 / 686883) ∧
    -Real.log (500000 / 686883) ≤ (158777937 / 500000000) := by
  have h := checkLog_sound (w := (186883 / 1186883)) (n := 12)
    (lo := (317555873 / 1000000000)) (hi := (158777937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686883 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686883 / 500000) = 1/(500000 / 686883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (317555873 / 1000000000) (158777937 / 500000000) (Real.log (686883 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (686883 / 500000) = -Real.log (500000 / 686883) := by
    rw [show ((686883 / 500000) : ℝ) = ((500000 / 686883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18721247 / 40000000) ≤ -Real.log (313117 / 500000) ∧
    -Real.log (313117 / 500000) ≤ (58503897 / 125000000) := by
  have h := checkLog_sound (w := (186883 / 813117)) (n := 12)
    (lo := (18721247 / 40000000)) (hi := (58503897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 313117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 313117) = 1/(313117 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-58503897 / 125000000) (-18721247 / 40000000) (Real.log (313117 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (242341289 / 1000000000) ≤ -Real.log (1000000 / 1274229) ∧
    -Real.log (1000000 / 1274229) ≤ (24234129 / 100000000) := by
  have h := checkLog_sound (w := (274229 / 2274229)) (n := 12)
    (lo := (242341289 / 1000000000)) (hi := (24234129 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274229 / 1000000) = 1/(1000000 / 1274229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (242341289 / 1000000000) (24234129 / 100000000) (Real.log (1274229 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1274229 / 1000000) = -Real.log (1000000 / 1274229) := by
    rw [show ((1274229 / 1000000) : ℝ) = ((1000000 / 1274229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16026037 / 50000000) ≤ -Real.log (725771 / 1000000) ∧
    -Real.log (725771 / 1000000) ≤ (320520741 / 1000000000) := by
  have h := checkLog_sound (w := (274229 / 1725771)) (n := 12)
    (lo := (16026037 / 50000000)) (hi := (320520741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 725771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 725771) = 1/(725771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-320520741 / 1000000000) (-16026037 / 50000000) (Real.log (725771 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (242879509 / 1000000000) ≤ -Real.log (200000 / 254983) ∧
    -Real.log (200000 / 254983) ≤ (24287951 / 100000000) := by
  have h := checkLog_sound (w := (54983 / 454983)) (n := 12)
    (lo := (242879509 / 1000000000)) (hi := (24287951 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254983 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(254983 / 200000) = 1/(200000 / 254983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (242879509 / 1000000000) (24287951 / 100000000) (Real.log (254983 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (254983 / 200000) = -Real.log (200000 / 254983) := by
    rw [show ((254983 / 200000) : ℝ) = ((200000 / 254983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (321466389 / 1000000000) ≤ -Real.log (145017 / 200000) ∧
    -Real.log (145017 / 200000) ≤ (32146639 / 100000000) := by
  have h := checkLog_sound (w := (54983 / 345017)) (n := 12)
    (lo := (321466389 / 1000000000)) (hi := (32146639 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 145017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 145017) = 1/(145017 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-32146639 / 100000000) (-321466389 / 1000000000) (Real.log (145017 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (783579197 / 1000000000) ≤ -Real.log (125000000000 / 273661772163) ∧
    -Real.log (125000000000 / 273661772163) ≤ (783579199 / 1000000000) := by
  have h := checkLog_sound (w := (23661772163 / 523661772163)) (n := 12)
    (lo := (90432017 / 1000000000)) (hi := (45216009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273661772163 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(273661772163 / 250000000000) = 1/(125000000000 / 273661772163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (783579197 / 1000000000) (783579199 / 1000000000) (Real.log (273661772163 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (273661772163 / 125000000000) = -Real.log (125000000000 / 273661772163) := by
    rw [show ((273661772163 / 125000000000) : ℝ) = ((125000000000 / 273661772163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (98198381 / 125000000) ≤ -Real.log (500000000000 / 1096847184919) ∧
    -Real.log (500000000000 / 1096847184919) ≤ (15711741 / 20000000) := by
  have h := checkLog_sound (w := (96847184919 / 2096847184919)) (n := 12)
    (lo := (23109967 / 250000000)) (hi := (92439869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096847184919 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1096847184919 / 1000000000000) = 1/(500000000000 / 1096847184919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (98198381 / 125000000) (15711741 / 20000000) (Real.log (1096847184919 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1096847184919 / 500000000000) = -Real.log (500000000000 / 1096847184919) := by
    rw [show ((1096847184919 / 500000000000) : ℝ) = ((500000000000 / 1096847184919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (56286203 / 100000000) ≤ -Real.log (100000000000 / 175569015571) ∧
    -Real.log (100000000000 / 175569015571) ≤ (562862031 / 1000000000) := by
  have h := checkLog_sound (w := (75569015571 / 275569015571)) (n := 12)
    (lo := (56286203 / 100000000)) (hi := (562862031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175569015571 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175569015571 / 100000000000) = 1/(100000000000 / 175569015571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (56286203 / 100000000) (562862031 / 1000000000) (Real.log (175569015571 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (175569015571 / 100000000000) = -Real.log (100000000000 / 175569015571) := by
    rw [show ((175569015571 / 100000000000) : ℝ) = ((100000000000 / 175569015571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (564345899 / 1000000000) ≤ -Real.log (250000000000 / 439574325769) ∧
    -Real.log (250000000000 / 439574325769) ≤ (5643459 / 10000000) := by
  have h := checkLog_sound (w := (189574325769 / 689574325769)) (n := 12)
    (lo := (564345899 / 1000000000)) (hi := (5643459 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((439574325769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(439574325769 / 250000000000) = 1/(250000000000 / 439574325769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (564345899 / 1000000000) (5643459 / 10000000) (Real.log (439574325769 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (439574325769 / 250000000000) = -Real.log (250000000000 / 439574325769) := by
    rw [show ((439574325769 / 250000000000) : ℝ) = ((250000000000 / 439574325769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0274

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0275Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0275
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

theorem reflection_log_1_neg : (231390699 / 1000000000) ≤ -Real.log (5120 / 6453) ∧
    -Real.log (5120 / 6453) ≤ (2313907 / 10000000) := by
  have h := checkLog_sound (w := (1333 / 11573)) (n := 12)
    (lo := (231390699 / 1000000000)) (hi := (2313907 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6453 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6453 / 5120) = 1/(5120 / 6453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (231390699 / 1000000000) (2313907 / 10000000) (Real.log (6453 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6453 / 5120) = -Real.log (5120 / 6453) := by
    rw [show ((6453 / 5120) : ℝ) = ((5120 / 6453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (30158029 / 100000000) ≤ -Real.log (3787 / 5120) ∧
    -Real.log (3787 / 5120) ≤ (301580291 / 1000000000) := by
  have h := checkLog_sound (w := (1333 / 8907)) (n := 12)
    (lo := (30158029 / 100000000)) (hi := (301580291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3787) = 1/(3787 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-301580291 / 1000000000) (-30158029 / 100000000) (Real.log (3787 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (230925691 / 1000000000) ≤ -Real.log (512 / 645) ∧
    -Real.log (512 / 645) ≤ (57731423 / 250000000) := by
  have h := checkLog_sound (w := (133 / 1157)) (n := 12)
    (lo := (230925691 / 1000000000)) (hi := (57731423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(645 / 512) = 1/(512 / 645) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (230925691 / 1000000000) (57731423 / 250000000) (Real.log (645 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (645 / 512) = -Real.log (512 / 645) := by
    rw [show ((645 / 512) : ℝ) = ((512 / 645) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (300788419 / 1000000000) ≤ -Real.log (379 / 512) ∧
    -Real.log (379 / 512) ≤ (15039421 / 50000000) := by
  have h := checkLog_sound (w := (133 / 891)) (n := 12)
    (lo := (300788419 / 1000000000)) (hi := (15039421 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 379) = 1/(379 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-15039421 / 50000000) (-300788419 / 1000000000) (Real.log (379 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41917281 / 100000000) ≤ -Real.log (2560 / 3893) ∧
    -Real.log (2560 / 3893) ≤ (419172811 / 1000000000) := by
  have h := checkLog_sound (w := (1333 / 6453)) (n := 12)
    (lo := (41917281 / 100000000)) (hi := (419172811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3893 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3893 / 2560) = 1/(2560 / 3893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41917281 / 100000000) (419172811 / 1000000000) (Real.log (3893 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3893 / 2560) = -Real.log (2560 / 3893) := by
    rw [show ((3893 / 2560) : ℝ) = ((2560 / 3893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (183858773 / 250000000) ≤ -Real.log (1227 / 2560) ∧
    -Real.log (1227 / 2560) ≤ (367717547 / 500000000) := by
  have h := checkLog_sound (w := (53 / 2507)) (n := 12)
    (lo := (5285989 / 125000000)) (hi := (42287913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1227) = 1/(1227 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-367717547 / 500000000) (-183858773 / 250000000) (Real.log (1227 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (418401899 / 1000000000) ≤ -Real.log (256 / 389) ∧
    -Real.log (256 / 389) ≤ (4184019 / 10000000) := by
  have h := checkLog_sound (w := (133 / 645)) (n := 12)
    (lo := (418401899 / 1000000000)) (hi := (4184019 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389 / 256) = 1/(256 / 389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (418401899 / 1000000000) (4184019 / 10000000) (Real.log (389 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (389 / 256) = -Real.log (256 / 389) := by
    rw [show ((389 / 256) : ℝ) = ((256 / 389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (11453017 / 15625000) ≤ -Real.log (123 / 256) ∧
    -Real.log (123 / 256) ≤ (73299309 / 100000000) := by
  have h := checkLog_sound (w := (5 / 251)) (n := 12)
    (lo := (9961477 / 250000000)) (hi := (39845909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 123) = 1/(123 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-73299309 / 100000000) (-11453017 / 15625000) (Real.log (123 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (158148977 / 500000000) ≤ -Real.log (1000000 / 1372039) ∧
    -Real.log (1000000 / 1372039) ≤ (63259591 / 200000000) := by
  have h := checkLog_sound (w := (372039 / 2372039)) (n := 12)
    (lo := (158148977 / 500000000)) (hi := (63259591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1372039 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1372039 / 1000000) = 1/(1000000 / 1372039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (158148977 / 500000000) (63259591 / 200000000) (Real.log (1372039 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1372039 / 1000000) = -Real.log (1000000 / 1372039) := by
    rw [show ((1372039 / 1000000) : ℝ) = ((1000000 / 1372039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (14539913 / 31250000) ≤ -Real.log (627961 / 1000000) ∧
    -Real.log (627961 / 1000000) ≤ (465277217 / 1000000000) := by
  have h := checkLog_sound (w := (372039 / 1627961)) (n := 12)
    (lo := (14539913 / 31250000)) (hi := (465277217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 627961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 627961) = 1/(627961 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-465277217 / 1000000000) (-14539913 / 31250000) (Real.log (627961 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (79231869 / 250000000) ≤ -Real.log (1000000 / 1372903) ∧
    -Real.log (1000000 / 1372903) ≤ (316927477 / 1000000000) := by
  have h := checkLog_sound (w := (372903 / 2372903)) (n := 12)
    (lo := (79231869 / 250000000)) (hi := (316927477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1372903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1372903 / 1000000) = 1/(1000000 / 1372903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (79231869 / 250000000) (316927477 / 1000000000) (Real.log (1372903 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1372903 / 1000000) = -Real.log (1000000 / 1372903) := by
    rw [show ((1372903 / 1000000) : ℝ) = ((1000000 / 1372903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93330809 / 200000000) ≤ -Real.log (627097 / 1000000) ∧
    -Real.log (627097 / 1000000) ≤ (233327023 / 500000000) := by
  have h := checkLog_sound (w := (372903 / 1627097)) (n := 12)
    (lo := (93330809 / 200000000)) (hi := (233327023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 627097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 627097) = 1/(627097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-233327023 / 500000000) (-93330809 / 200000000) (Real.log (627097 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (12090139 / 50000000) ≤ -Real.log (1000000 / 1273543) ∧
    -Real.log (1000000 / 1273543) ≤ (241802781 / 1000000000) := by
  have h := checkLog_sound (w := (273543 / 2273543)) (n := 12)
    (lo := (12090139 / 50000000)) (hi := (241802781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1273543 / 1000000) = 1/(1000000 / 1273543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (12090139 / 50000000) (241802781 / 1000000000) (Real.log (1273543 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1273543 / 1000000) = -Real.log (1000000 / 1273543) := by
    rw [show ((1273543 / 1000000) : ℝ) = ((1000000 / 1273543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (63915197 / 200000000) ≤ -Real.log (726457 / 1000000) ∧
    -Real.log (726457 / 1000000) ≤ (159787993 / 500000000) := by
  have h := checkLog_sound (w := (273543 / 1726457)) (n := 12)
    (lo := (63915197 / 200000000)) (hi := (159787993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 726457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 726457) = 1/(726457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-159787993 / 500000000) (-63915197 / 200000000) (Real.log (726457 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (121171037 / 500000000) ≤ -Real.log (100000 / 127423) ∧
    -Real.log (100000 / 127423) ≤ (9693683 / 40000000) := by
  have h := checkLog_sound (w := (27423 / 227423)) (n := 12)
    (lo := (121171037 / 500000000)) (hi := (9693683 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127423 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127423 / 100000) = 1/(100000 / 127423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (121171037 / 500000000) (9693683 / 40000000) (Real.log (127423 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (127423 / 100000) = -Real.log (100000 / 127423) := by
    rw [show ((127423 / 100000) : ℝ) = ((100000 / 127423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (160261059 / 500000000) ≤ -Real.log (72577 / 100000) ∧
    -Real.log (72577 / 100000) ≤ (320522119 / 1000000000) := by
  have h := checkLog_sound (w := (27423 / 172577)) (n := 12)
    (lo := (160261059 / 500000000)) (hi := (320522119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72577) = 1/(72577 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-320522119 / 1000000000) (-160261059 / 500000000) (Real.log (72577 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (78157517 / 100000000) ≤ -Real.log (15625000000 / 34139236951) ∧
    -Real.log (15625000000 / 34139236951) ≤ (195393793 / 250000000) := by
  have h := checkLog_sound (w := (2889236951 / 65389236951)) (n := 12)
    (lo := (8842799 / 100000000)) (hi := (88427991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34139236951 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(34139236951 / 31250000000) = 1/(15625000000 / 34139236951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (78157517 / 100000000) (195393793 / 250000000) (Real.log (34139236951 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (34139236951 / 15625000000) = -Real.log (15625000000 / 34139236951) := by
    rw [show ((34139236951 / 15625000000) : ℝ) = ((15625000000 / 34139236951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (9794769 / 12500000) ≤ -Real.log (500000000000 / 1094649631557) ∧
    -Real.log (500000000000 / 1094649631557) ≤ (391790761 / 500000000) := by
  have h := checkLog_sound (w := (94649631557 / 2094649631557)) (n := 12)
    (lo := (4521717 / 50000000)) (hi := (90434341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094649631557 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1094649631557 / 1000000000000) = 1/(500000000000 / 1094649631557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (9794769 / 12500000) (391790761 / 500000000) (Real.log (1094649631557 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1094649631557 / 500000000000) = -Real.log (500000000000 / 1094649631557) := by
    rw [show ((1094649631557 / 500000000000) : ℝ) = ((500000000000 / 1094649631557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (112275753 / 200000000) ≤ -Real.log (250000000000 / 438271983063) ∧
    -Real.log (250000000000 / 438271983063) ≤ (280689383 / 500000000) := by
  have h := checkLog_sound (w := (188271983063 / 688271983063)) (n := 12)
    (lo := (112275753 / 200000000)) (hi := (280689383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438271983063 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438271983063 / 250000000000) = 1/(250000000000 / 438271983063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (112275753 / 200000000) (280689383 / 500000000) (Real.log (438271983063 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (438271983063 / 250000000000) = -Real.log (250000000000 / 438271983063) := by
    rw [show ((438271983063 / 250000000000) : ℝ) = ((250000000000 / 438271983063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (562864193 / 1000000000) ≤ -Real.log (100000000000 / 175569395263) ∧
    -Real.log (100000000000 / 175569395263) ≤ (281432097 / 500000000) := by
  have h := checkLog_sound (w := (75569395263 / 275569395263)) (n := 12)
    (lo := (562864193 / 1000000000)) (hi := (281432097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175569395263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175569395263 / 100000000000) = 1/(100000000000 / 175569395263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (562864193 / 1000000000) (281432097 / 500000000) (Real.log (175569395263 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (175569395263 / 100000000000) = -Real.log (100000000000 / 175569395263) := by
    rw [show ((175569395263 / 100000000000) : ℝ) = ((100000000000 / 175569395263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0275

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0276Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0276
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

theorem reflection_log_1_neg : (230925691 / 1000000000) ≤ -Real.log (512 / 645) ∧
    -Real.log (512 / 645) ≤ (57731423 / 250000000) := by
  have h := checkLog_sound (w := (133 / 1157)) (n := 12)
    (lo := (230925691 / 1000000000)) (hi := (57731423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(645 / 512) = 1/(512 / 645) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (230925691 / 1000000000) (57731423 / 250000000) (Real.log (645 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (645 / 512) = -Real.log (512 / 645) := by
    rw [show ((645 / 512) : ℝ) = ((512 / 645) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (300788419 / 1000000000) ≤ -Real.log (379 / 512) ∧
    -Real.log (379 / 512) ≤ (15039421 / 50000000) := by
  have h := checkLog_sound (w := (133 / 891)) (n := 12)
    (lo := (300788419 / 1000000000)) (hi := (15039421 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 379) = 1/(379 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-15039421 / 50000000) (-300788419 / 1000000000) (Real.log (379 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (230460467 / 1000000000) ≤ -Real.log (5120 / 6447) ∧
    -Real.log (5120 / 6447) ≤ (57615117 / 250000000) := by
  have h := checkLog_sound (w := (1327 / 11567)) (n := 12)
    (lo := (230460467 / 1000000000)) (hi := (57615117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6447 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6447 / 5120) = 1/(5120 / 6447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (230460467 / 1000000000) (57615117 / 250000000) (Real.log (6447 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6447 / 5120) = -Real.log (5120 / 6447) := by
    rw [show ((6447 / 5120) : ℝ) = ((5120 / 6447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (37499647 / 125000000) ≤ -Real.log (3793 / 5120) ∧
    -Real.log (3793 / 5120) ≤ (299997177 / 1000000000) := by
  have h := checkLog_sound (w := (1327 / 8913)) (n := 12)
    (lo := (37499647 / 125000000)) (hi := (299997177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3793) = 1/(3793 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-299997177 / 1000000000) (-37499647 / 125000000) (Real.log (3793 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (418401899 / 1000000000) ≤ -Real.log (256 / 389) ∧
    -Real.log (256 / 389) ≤ (4184019 / 10000000) := by
  have h := checkLog_sound (w := (133 / 645)) (n := 12)
    (lo := (418401899 / 1000000000)) (hi := (4184019 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389 / 256) = 1/(256 / 389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (418401899 / 1000000000) (4184019 / 10000000) (Real.log (389 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (389 / 256) = -Real.log (256 / 389) := by
    rw [show ((389 / 256) : ℝ) = ((256 / 389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (11453017 / 15625000) ≤ -Real.log (123 / 256) ∧
    -Real.log (123 / 256) ≤ (73299309 / 100000000) := by
  have h := checkLog_sound (w := (5 / 251)) (n := 12)
    (lo := (9961477 / 250000000)) (hi := (39845909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 123) = 1/(123 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-73299309 / 100000000) (-11453017 / 15625000) (Real.log (123 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (417630393 / 1000000000) ≤ -Real.log (2560 / 3887) ∧
    -Real.log (2560 / 3887) ≤ (208815197 / 500000000) := by
  have h := checkLog_sound (w := (1327 / 6447)) (n := 12)
    (lo := (417630393 / 1000000000)) (hi := (208815197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3887 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3887 / 2560) = 1/(2560 / 3887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (417630393 / 1000000000) (208815197 / 500000000) (Real.log (3887 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3887 / 2560) = -Real.log (2560 / 3887) := by
    rw [show ((3887 / 2560) : ℝ) = ((2560 / 3887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (730557033 / 1000000000) ≤ -Real.log (1233 / 2560) ∧
    -Real.log (1233 / 2560) ≤ (146111407 / 200000000) := by
  have h := checkLog_sound (w := (47 / 2513)) (n := 12)
    (lo := (37409853 / 1000000000)) (hi := (18704927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1233) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1233) = 1/(1233 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-146111407 / 200000000) (-730557033 / 1000000000) (Real.log (1233 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (78917009 / 250000000) ≤ -Real.log (40000 / 54847) ∧
    -Real.log (40000 / 54847) ≤ (315668037 / 1000000000) := by
  have h := checkLog_sound (w := (14847 / 94847)) (n := 12)
    (lo := (78917009 / 250000000)) (hi := (315668037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54847 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54847 / 40000) = 1/(40000 / 54847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (78917009 / 250000000) (315668037 / 1000000000) (Real.log (54847 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (54847 / 40000) = -Real.log (40000 / 54847) := by
    rw [show ((54847 / 40000) : ℝ) = ((40000 / 54847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (11597557 / 25000000) ≤ -Real.log (25153 / 40000) ∧
    -Real.log (25153 / 40000) ≤ (463902281 / 1000000000) := by
  have h := checkLog_sound (w := (14847 / 65153)) (n := 12)
    (lo := (11597557 / 25000000)) (hi := (463902281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 25153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 25153) = 1/(25153 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-463902281 / 1000000000) (-11597557 / 25000000) (Real.log (25153 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (316298683 / 1000000000) ≤ -Real.log (25000 / 34301) ∧
    -Real.log (25000 / 34301) ≤ (79074671 / 250000000) := by
  have h := checkLog_sound (w := (9301 / 59301)) (n := 12)
    (lo := (316298683 / 1000000000)) (hi := (79074671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34301 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34301 / 25000) = 1/(25000 / 34301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (316298683 / 1000000000) (79074671 / 250000000) (Real.log (34301 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (34301 / 25000) = -Real.log (25000 / 34301) := by
    rw [show ((34301 / 25000) : ℝ) = ((25000 / 34301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (58159851 / 125000000) ≤ -Real.log (15699 / 25000) ∧
    -Real.log (15699 / 25000) ≤ (465278809 / 1000000000) := by
  have h := checkLog_sound (w := (9301 / 40699)) (n := 12)
    (lo := (58159851 / 125000000)) (hi := (465278809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 15699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 15699) = 1/(15699 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-465278809 / 1000000000) (-58159851 / 125000000) (Real.log (15699 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (48252953 / 200000000) ≤ -Real.log (500000 / 636429) ∧
    -Real.log (500000 / 636429) ≤ (120632383 / 500000000) := by
  have h := checkLog_sound (w := (136429 / 1136429)) (n := 12)
    (lo := (48252953 / 200000000)) (hi := (120632383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636429 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636429 / 500000) = 1/(500000 / 636429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (48252953 / 200000000) (120632383 / 500000000) (Real.log (636429 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (636429 / 500000) = -Real.log (500000 / 636429) := by
    rw [show ((636429 / 500000) : ℝ) = ((500000 / 636429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (318633497 / 1000000000) ≤ -Real.log (363571 / 500000) ∧
    -Real.log (363571 / 500000) ≤ (159316749 / 500000000) := by
  have h := checkLog_sound (w := (136429 / 863571)) (n := 12)
    (lo := (318633497 / 1000000000)) (hi := (159316749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 363571) = 1/(363571 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-159316749 / 500000000) (-318633497 / 1000000000) (Real.log (363571 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (48360713 / 200000000) ≤ -Real.log (125000 / 159193) ∧
    -Real.log (125000 / 159193) ≤ (120901783 / 500000000) := by
  have h := checkLog_sound (w := (34193 / 284193)) (n := 12)
    (lo := (48360713 / 200000000)) (hi := (120901783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159193 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159193 / 125000) = 1/(125000 / 159193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (48360713 / 200000000) (120901783 / 500000000) (Real.log (159193 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (159193 / 125000) = -Real.log (125000 / 159193) := by
    rw [show ((159193 / 125000) : ℝ) = ((125000 / 159193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (159788681 / 500000000) ≤ -Real.log (90807 / 125000) ∧
    -Real.log (90807 / 125000) ≤ (319577363 / 1000000000) := by
  have h := checkLog_sound (w := (34193 / 215807)) (n := 12)
    (lo := (159788681 / 500000000)) (hi := (319577363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 90807) = 1/(90807 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-319577363 / 1000000000) (-159788681 / 500000000) (Real.log (90807 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (194892579 / 250000000) ≤ -Real.log (500000000000 / 1090267562517) ∧
    -Real.log (500000000000 / 1090267562517) ≤ (389785159 / 500000000) := by
  have h := checkLog_sound (w := (90267562517 / 2090267562517)) (n := 12)
    (lo := (2700723 / 31250000)) (hi := (86423137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090267562517 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1090267562517 / 1000000000000) = 1/(500000000000 / 1090267562517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (194892579 / 250000000) (389785159 / 500000000) (Real.log (1090267562517 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1090267562517 / 500000000000) = -Real.log (500000000000 / 1090267562517) := by
    rw [show ((1090267562517 / 500000000000) : ℝ) = ((500000000000 / 1090267562517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (781577491 / 1000000000) ≤ -Real.log (31250000000 / 68278632397) ∧
    -Real.log (31250000000 / 68278632397) ≤ (781577493 / 1000000000) := by
  have h := checkLog_sound (w := (5778632397 / 130778632397)) (n := 12)
    (lo := (88430311 / 1000000000)) (hi := (11053789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68278632397 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68278632397 / 62500000000) = 1/(31250000000 / 68278632397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (781577491 / 1000000000) (781577493 / 1000000000) (Real.log (68278632397 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (68278632397 / 31250000000) = -Real.log (31250000000 / 68278632397) := by
    rw [show ((68278632397 / 31250000000) : ℝ) = ((31250000000 / 68278632397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (559898263 / 1000000000) ≤ -Real.log (125000000000 / 218811800171) ∧
    -Real.log (125000000000 / 218811800171) ≤ (69987283 / 125000000) := by
  have h := checkLog_sound (w := (93811800171 / 343811800171)) (n := 12)
    (lo := (559898263 / 1000000000)) (hi := (69987283 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218811800171 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218811800171 / 125000000000) = 1/(125000000000 / 218811800171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (559898263 / 1000000000) (69987283 / 125000000) (Real.log (218811800171 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (218811800171 / 125000000000) = -Real.log (125000000000 / 218811800171) := by
    rw [show ((218811800171 / 125000000000) : ℝ) = ((125000000000 / 218811800171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (561380927 / 1000000000) ≤ -Real.log (250000000000 / 438272930501) ∧
    -Real.log (250000000000 / 438272930501) ≤ (8771577 / 15625000) := by
  have h := checkLog_sound (w := (188272930501 / 688272930501)) (n := 12)
    (lo := (561380927 / 1000000000)) (hi := (8771577 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438272930501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438272930501 / 250000000000) = 1/(250000000000 / 438272930501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (561380927 / 1000000000) (8771577 / 15625000) (Real.log (438272930501 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (438272930501 / 250000000000) = -Real.log (250000000000 / 438272930501) := by
    rw [show ((438272930501 / 250000000000) : ℝ) = ((250000000000 / 438272930501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0276

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0277Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0277
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

theorem reflection_log_1_neg : (230460467 / 1000000000) ≤ -Real.log (5120 / 6447) ∧
    -Real.log (5120 / 6447) ≤ (57615117 / 250000000) := by
  have h := checkLog_sound (w := (1327 / 11567)) (n := 12)
    (lo := (230460467 / 1000000000)) (hi := (57615117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6447 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6447 / 5120) = 1/(5120 / 6447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (230460467 / 1000000000) (57615117 / 250000000) (Real.log (6447 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6447 / 5120) = -Real.log (5120 / 6447) := by
    rw [show ((6447 / 5120) : ℝ) = ((5120 / 6447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (37499647 / 125000000) ≤ -Real.log (3793 / 5120) ∧
    -Real.log (3793 / 5120) ≤ (299997177 / 1000000000) := by
  have h := checkLog_sound (w := (1327 / 8913)) (n := 12)
    (lo := (37499647 / 125000000)) (hi := (299997177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3793) = 1/(3793 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-299997177 / 1000000000) (-37499647 / 125000000) (Real.log (3793 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (114997513 / 500000000) ≤ -Real.log (1280 / 1611) ∧
    -Real.log (1280 / 1611) ≤ (229995027 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 2891)) (n := 12)
    (lo := (114997513 / 500000000)) (hi := (229995027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1611 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1611 / 1280) = 1/(1280 / 1611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (114997513 / 500000000) (229995027 / 1000000000) (Real.log (1611 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1611 / 1280) = -Real.log (1280 / 1611) := by
    rw [show ((1611 / 1280) : ℝ) = ((1280 / 1611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (149603279 / 500000000) ≤ -Real.log (949 / 1280) ∧
    -Real.log (949 / 1280) ≤ (299206559 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 2229)) (n := 12)
    (lo := (149603279 / 500000000)) (hi := (299206559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 949) = 1/(949 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-299206559 / 1000000000) (-149603279 / 500000000) (Real.log (949 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (417630393 / 1000000000) ≤ -Real.log (2560 / 3887) ∧
    -Real.log (2560 / 3887) ≤ (208815197 / 500000000) := by
  have h := checkLog_sound (w := (1327 / 6447)) (n := 12)
    (lo := (417630393 / 1000000000)) (hi := (208815197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3887 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3887 / 2560) = 1/(2560 / 3887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (417630393 / 1000000000) (208815197 / 500000000) (Real.log (3887 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3887 / 2560) = -Real.log (2560 / 3887) := by
    rw [show ((3887 / 2560) : ℝ) = ((2560 / 3887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (730557033 / 1000000000) ≤ -Real.log (1233 / 2560) ∧
    -Real.log (1233 / 2560) ≤ (146111407 / 200000000) := by
  have h := checkLog_sound (w := (47 / 2513)) (n := 12)
    (lo := (37409853 / 1000000000)) (hi := (18704927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1233) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1233) = 1/(1233 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-146111407 / 200000000) (-730557033 / 1000000000) (Real.log (1233 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (416858291 / 1000000000) ≤ -Real.log (640 / 971) ∧
    -Real.log (640 / 971) ≤ (104214573 / 250000000) := by
  have h := checkLog_sound (w := (331 / 1611)) (n := 12)
    (lo := (416858291 / 1000000000)) (hi := (104214573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971 / 640) = 1/(640 / 971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (416858291 / 1000000000) (104214573 / 250000000) (Real.log (971 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (971 / 640) = -Real.log (640 / 971) := by
    rw [show ((971 / 640) : ℝ) = ((640 / 971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (364063449 / 500000000) ≤ -Real.log (309 / 640) ∧
    -Real.log (309 / 640) ≤ (7281269 / 10000000) := by
  have h := checkLog_sound (w := (11 / 629)) (n := 12)
    (lo := (17489859 / 500000000)) (hi := (34979719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 309) = 1/(309 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-7281269 / 10000000) (-364063449 / 500000000) (Real.log (309 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15751959 / 50000000) ≤ -Real.log (1000000 / 1370313) ∧
    -Real.log (1000000 / 1370313) ≤ (315039181 / 1000000000) := by
  have h := checkLog_sound (w := (370313 / 2370313)) (n := 12)
    (lo := (15751959 / 50000000)) (hi := (315039181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1370313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1370313 / 1000000) = 1/(1000000 / 1370313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15751959 / 50000000) (315039181 / 1000000000) (Real.log (1370313 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1370313 / 1000000) = -Real.log (1000000 / 1370313) := by
    rw [show ((1370313 / 1000000) : ℝ) = ((1000000 / 1370313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (57816551 / 125000000) ≤ -Real.log (629687 / 1000000) ∧
    -Real.log (629687 / 1000000) ≤ (462532409 / 1000000000) := by
  have h := checkLog_sound (w := (370313 / 1629687)) (n := 12)
    (lo := (57816551 / 125000000)) (hi := (462532409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 629687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 629687) = 1/(629687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-462532409 / 1000000000) (-57816551 / 125000000) (Real.log (629687 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (63133899 / 200000000) ≤ -Real.log (1000000 / 1371177) ∧
    -Real.log (1000000 / 1371177) ≤ (39458687 / 125000000) := by
  have h := checkLog_sound (w := (371177 / 2371177)) (n := 12)
    (lo := (63133899 / 200000000)) (hi := (39458687 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1371177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1371177 / 1000000) = 1/(1000000 / 1371177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (63133899 / 200000000) (39458687 / 125000000) (Real.log (1371177 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1371177 / 1000000) = -Real.log (1000000 / 1371177) := by
    rw [show ((1371177 / 1000000) : ℝ) = ((1000000 / 1371177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (23195273 / 50000000) ≤ -Real.log (628823 / 1000000) ∧
    -Real.log (628823 / 1000000) ≤ (463905461 / 1000000000) := by
  have h := checkLog_sound (w := (371177 / 1628823)) (n := 12)
    (lo := (23195273 / 50000000)) (hi := (463905461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 628823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 628823) = 1/(628823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-463905461 / 1000000000) (-23195273 / 50000000) (Real.log (628823 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (15045453 / 62500000) ≤ -Real.log (500000 / 636087) ∧
    -Real.log (500000 / 636087) ≤ (240727249 / 1000000000) := by
  have h := checkLog_sound (w := (136087 / 1136087)) (n := 12)
    (lo := (15045453 / 62500000)) (hi := (240727249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636087 / 500000) = 1/(500000 / 636087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (15045453 / 62500000) (240727249 / 1000000000) (Real.log (636087 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (636087 / 500000) = -Real.log (500000 / 636087) := by
    rw [show ((636087 / 500000) : ℝ) = ((500000 / 636087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (31769327 / 100000000) ≤ -Real.log (363913 / 500000) ∧
    -Real.log (363913 / 500000) ≤ (317693271 / 1000000000) := by
  have h := checkLog_sound (w := (136087 / 863913)) (n := 12)
    (lo := (31769327 / 100000000)) (hi := (317693271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 363913) = 1/(363913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-317693271 / 1000000000) (-31769327 / 100000000) (Real.log (363913 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (241265551 / 1000000000) ≤ -Real.log (1000000 / 1272859) ∧
    -Real.log (1000000 / 1272859) ≤ (15079097 / 62500000) := by
  have h := checkLog_sound (w := (272859 / 2272859)) (n := 12)
    (lo := (241265551 / 1000000000)) (hi := (15079097 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1272859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1272859 / 1000000) = 1/(1000000 / 1272859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (241265551 / 1000000000) (15079097 / 62500000) (Real.log (1272859 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1272859 / 1000000) = -Real.log (1000000 / 1272859) := by
    rw [show ((1272859 / 1000000) : ℝ) = ((1000000 / 1272859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (39829359 / 125000000) ≤ -Real.log (727141 / 1000000) ∧
    -Real.log (727141 / 1000000) ≤ (318634873 / 1000000000) := by
  have h := checkLog_sound (w := (272859 / 1727141)) (n := 12)
    (lo := (39829359 / 125000000)) (hi := (318634873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 727141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 727141) = 1/(727141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-318634873 / 1000000000) (-39829359 / 125000000) (Real.log (727141 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (194392897 / 250000000) ≤ -Real.log (500000000000 / 1088090591039) ∧
    -Real.log (500000000000 / 1088090591039) ≤ (77757159 / 100000000) := by
  have h := checkLog_sound (w := (88090591039 / 2088090591039)) (n := 12)
    (lo := (10553051 / 125000000)) (hi := (84424409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088090591039 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1088090591039 / 1000000000000) = 1/(500000000000 / 1088090591039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (194392897 / 250000000) (77757159 / 100000000) (Real.log (1088090591039 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1088090591039 / 500000000000) = -Real.log (500000000000 / 1088090591039) := by
    rw [show ((1088090591039 / 500000000000) : ℝ) = ((500000000000 / 1088090591039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (155914991 / 200000000) ≤ -Real.log (125000000000 / 272568155109) ∧
    -Real.log (125000000000 / 272568155109) ≤ (779574957 / 1000000000) := by
  have h := checkLog_sound (w := (22568155109 / 522568155109)) (n := 12)
    (lo := (3457111 / 40000000)) (hi := (675217 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272568155109 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(272568155109 / 250000000000) = 1/(125000000000 / 272568155109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (155914991 / 200000000) (779574957 / 1000000000) (Real.log (272568155109 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (272568155109 / 125000000000) = -Real.log (125000000000 / 272568155109) := by
    rw [show ((272568155109 / 125000000000) : ℝ) = ((125000000000 / 272568155109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (279210259 / 500000000) ≤ -Real.log (500000000000 / 873954763913) ∧
    -Real.log (500000000000 / 873954763913) ≤ (558420519 / 1000000000) := by
  have h := checkLog_sound (w := (373954763913 / 1373954763913)) (n := 12)
    (lo := (279210259 / 500000000)) (hi := (558420519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873954763913 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873954763913 / 500000000000) = 1/(500000000000 / 873954763913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (279210259 / 500000000) (558420519 / 1000000000) (Real.log (873954763913 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (873954763913 / 500000000000) = -Real.log (500000000000 / 873954763913) := by
    rw [show ((873954763913 / 500000000000) : ℝ) = ((500000000000 / 873954763913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (559900423 / 1000000000) ≤ -Real.log (62500000000 / 109406136499) ∧
    -Real.log (62500000000 / 109406136499) ≤ (69987553 / 125000000) := by
  have h := checkLog_sound (w := (46906136499 / 171906136499)) (n := 12)
    (lo := (559900423 / 1000000000)) (hi := (69987553 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109406136499 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109406136499 / 62500000000) = 1/(62500000000 / 109406136499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (559900423 / 1000000000) (69987553 / 125000000) (Real.log (109406136499 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (109406136499 / 62500000000) = -Real.log (62500000000 / 109406136499) := by
    rw [show ((109406136499 / 62500000000) : ℝ) = ((62500000000 / 109406136499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0277

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0278Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0278
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

theorem reflection_log_1_neg : (114997513 / 500000000) ≤ -Real.log (1280 / 1611) ∧
    -Real.log (1280 / 1611) ≤ (229995027 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 2891)) (n := 12)
    (lo := (114997513 / 500000000)) (hi := (229995027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1611 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1611 / 1280) = 1/(1280 / 1611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (114997513 / 500000000) (229995027 / 1000000000) (Real.log (1611 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1611 / 1280) = -Real.log (1280 / 1611) := by
    rw [show ((1611 / 1280) : ℝ) = ((1280 / 1611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (149603279 / 500000000) ≤ -Real.log (949 / 1280) ∧
    -Real.log (949 / 1280) ≤ (299206559 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 2229)) (n := 12)
    (lo := (149603279 / 500000000)) (hi := (299206559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 949) = 1/(949 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-299206559 / 1000000000) (-149603279 / 500000000) (Real.log (949 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (28691171 / 125000000) ≤ -Real.log (5120 / 6441) ∧
    -Real.log (5120 / 6441) ≤ (229529369 / 1000000000) := by
  have h := checkLog_sound (w := (1321 / 11561)) (n := 12)
    (lo := (28691171 / 125000000)) (hi := (229529369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6441 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6441 / 5120) = 1/(5120 / 6441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (28691171 / 125000000) (229529369 / 1000000000) (Real.log (6441 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6441 / 5120) = -Real.log (5120 / 6441) := by
    rw [show ((6441 / 5120) : ℝ) = ((5120 / 6441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (74604141 / 250000000) ≤ -Real.log (3799 / 5120) ∧
    -Real.log (3799 / 5120) ≤ (59683313 / 200000000) := by
  have h := checkLog_sound (w := (1321 / 8919)) (n := 12)
    (lo := (74604141 / 250000000)) (hi := (59683313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3799) = 1/(3799 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59683313 / 200000000) (-74604141 / 250000000) (Real.log (3799 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (416858291 / 1000000000) ≤ -Real.log (640 / 971) ∧
    -Real.log (640 / 971) ≤ (104214573 / 250000000) := by
  have h := checkLog_sound (w := (331 / 1611)) (n := 12)
    (lo := (416858291 / 1000000000)) (hi := (104214573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971 / 640) = 1/(640 / 971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (416858291 / 1000000000) (104214573 / 250000000) (Real.log (971 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (971 / 640) = -Real.log (640 / 971) := by
    rw [show ((971 / 640) : ℝ) = ((640 / 971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (364063449 / 500000000) ≤ -Real.log (309 / 640) ∧
    -Real.log (309 / 640) ≤ (7281269 / 10000000) := by
  have h := checkLog_sound (w := (11 / 629)) (n := 12)
    (lo := (17489859 / 500000000)) (hi := (34979719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 309) = 1/(309 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-7281269 / 10000000) (-364063449 / 500000000) (Real.log (309 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (416085593 / 1000000000) ≤ -Real.log (2560 / 3881) ∧
    -Real.log (2560 / 3881) ≤ (208042797 / 500000000) := by
  have h := checkLog_sound (w := (1321 / 6441)) (n := 12)
    (lo := (416085593 / 1000000000)) (hi := (208042797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3881 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3881 / 2560) = 1/(2560 / 3881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (416085593 / 1000000000) (208042797 / 500000000) (Real.log (3881 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3881 / 2560) = -Real.log (2560 / 3881) := by
    rw [show ((3881 / 2560) : ℝ) = ((2560 / 3881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (145140531 / 200000000) ≤ -Real.log (1239 / 2560) ∧
    -Real.log (1239 / 2560) ≤ (725702657 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 2519)) (n := 12)
    (lo := (1302219 / 40000000)) (hi := (8138869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1239) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1239) = 1/(1239 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-725702657 / 1000000000) (-145140531 / 200000000) (Real.log (1239 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (314409199 / 1000000000) ≤ -Real.log (20000 / 27389) ∧
    -Real.log (20000 / 27389) ≤ (786023 / 2500000) := by
  have h := checkLog_sound (w := (7389 / 47389)) (n := 12)
    (lo := (314409199 / 1000000000)) (hi := (786023 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27389 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27389 / 20000) = 1/(20000 / 27389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (314409199 / 1000000000) (786023 / 2500000) (Real.log (27389 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (27389 / 20000) = -Real.log (20000 / 27389) := by
    rw [show ((27389 / 20000) : ℝ) = ((20000 / 27389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (57645353 / 125000000) ≤ -Real.log (12611 / 20000) ∧
    -Real.log (12611 / 20000) ≤ (18446513 / 40000000) := by
  have h := checkLog_sound (w := (7389 / 32611)) (n := 12)
    (lo := (57645353 / 125000000)) (hi := (18446513 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 12611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 12611) = 1/(12611 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18446513 / 40000000) (-57645353 / 125000000) (Real.log (12611 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31503991 / 100000000) ≤ -Real.log (500000 / 685157) ∧
    -Real.log (500000 / 685157) ≤ (315039911 / 1000000000) := by
  have h := checkLog_sound (w := (185157 / 1185157)) (n := 12)
    (lo := (31503991 / 100000000)) (hi := (315039911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685157 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685157 / 500000) = 1/(500000 / 685157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31503991 / 100000000) (315039911 / 1000000000) (Real.log (685157 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (685157 / 500000) = -Real.log (500000 / 685157) := by
    rw [show ((685157 / 500000) : ℝ) = ((500000 / 685157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (115633499 / 250000000) ≤ -Real.log (314843 / 500000) ∧
    -Real.log (314843 / 500000) ≤ (462533997 / 1000000000) := by
  have h := checkLog_sound (w := (185157 / 814843)) (n := 12)
    (lo := (115633499 / 250000000)) (hi := (462533997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 314843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 314843) = 1/(314843 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-462533997 / 1000000000) (-115633499 / 250000000) (Real.log (314843 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (240189441 / 1000000000) ≤ -Real.log (100000 / 127149) ∧
    -Real.log (100000 / 127149) ≤ (120094721 / 500000000) := by
  have h := checkLog_sound (w := (27149 / 227149)) (n := 12)
    (lo := (240189441 / 1000000000)) (hi := (120094721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127149 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127149 / 100000) = 1/(100000 / 127149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (240189441 / 1000000000) (120094721 / 500000000) (Real.log (127149 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (127149 / 100000) = -Real.log (100000 / 127149) := by
    rw [show ((127149 / 100000) : ℝ) = ((100000 / 127149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (158376963 / 500000000) ≤ -Real.log (72851 / 100000) ∧
    -Real.log (72851 / 100000) ≤ (316753927 / 1000000000) := by
  have h := checkLog_sound (w := (27149 / 172851)) (n := 12)
    (lo := (158376963 / 500000000)) (hi := (316753927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72851) = 1/(72851 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-316753927 / 1000000000) (-158376963 / 500000000) (Real.log (72851 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (120364017 / 500000000) ≤ -Real.log (40000 / 50887) ∧
    -Real.log (40000 / 50887) ≤ (48145607 / 200000000) := by
  have h := checkLog_sound (w := (10887 / 90887)) (n := 12)
    (lo := (120364017 / 500000000)) (hi := (48145607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50887 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50887 / 40000) = 1/(40000 / 50887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (120364017 / 500000000) (48145607 / 200000000) (Real.log (50887 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (50887 / 40000) = -Real.log (40000 / 50887) := by
    rw [show ((50887 / 40000) : ℝ) = ((40000 / 50887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (79423661 / 250000000) ≤ -Real.log (29113 / 40000) ∧
    -Real.log (29113 / 40000) ≤ (63538929 / 200000000) := by
  have h := checkLog_sound (w := (10887 / 69113)) (n := 12)
    (lo := (79423661 / 250000000)) (hi := (63538929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 29113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 29113) = 1/(29113 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-63538929 / 200000000) (-79423661 / 250000000) (Real.log (29113 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (775572023 / 1000000000) ≤ -Real.log (500000000000 / 1085917056537) ∧
    -Real.log (500000000000 / 1085917056537) ≤ (31022881 / 40000000) := by
  have h := checkLog_sound (w := (85917056537 / 2085917056537)) (n := 12)
    (lo := (82424843 / 1000000000)) (hi := (20606211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085917056537 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1085917056537 / 1000000000000) = 1/(500000000000 / 1085917056537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (775572023 / 1000000000) (31022881 / 40000000) (Real.log (1085917056537 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1085917056537 / 500000000000) = -Real.log (500000000000 / 1085917056537) := by
    rw [show ((1085917056537 / 500000000000) : ℝ) = ((500000000000 / 1085917056537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (388786953 / 500000000) ≤ -Real.log (125000000000 / 272023278269) ∧
    -Real.log (125000000000 / 272023278269) ≤ (194393477 / 250000000) := by
  have h := checkLog_sound (w := (22023278269 / 522023278269)) (n := 12)
    (lo := (42213363 / 500000000)) (hi := (84426727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272023278269 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(272023278269 / 250000000000) = 1/(125000000000 / 272023278269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (388786953 / 500000000) (194393477 / 250000000) (Real.log (272023278269 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (272023278269 / 125000000000) = -Real.log (125000000000 / 272023278269) := by
    rw [show ((272023278269 / 125000000000) : ℝ) = ((125000000000 / 272023278269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (556943367 / 1000000000) ≤ -Real.log (500000000000 / 872664754087) ∧
    -Real.log (500000000000 / 872664754087) ≤ (69617921 / 125000000) := by
  have h := checkLog_sound (w := (372664754087 / 1372664754087)) (n := 12)
    (lo := (556943367 / 1000000000)) (hi := (69617921 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((872664754087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(872664754087 / 500000000000) = 1/(500000000000 / 872664754087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (556943367 / 1000000000) (69617921 / 125000000) (Real.log (872664754087 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (872664754087 / 500000000000) = -Real.log (500000000000 / 872664754087) := by
    rw [show ((872664754087 / 500000000000) : ℝ) = ((500000000000 / 872664754087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (279211339 / 500000000) ≤ -Real.log (125000000000 / 218489162917) ∧
    -Real.log (125000000000 / 218489162917) ≤ (558422679 / 1000000000) := by
  have h := checkLog_sound (w := (93489162917 / 343489162917)) (n := 12)
    (lo := (279211339 / 500000000)) (hi := (558422679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218489162917 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218489162917 / 125000000000) = 1/(125000000000 / 218489162917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (279211339 / 500000000) (558422679 / 1000000000) (Real.log (218489162917 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (218489162917 / 125000000000) = -Real.log (125000000000 / 218489162917) := by
    rw [show ((218489162917 / 125000000000) : ℝ) = ((125000000000 / 218489162917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0278

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0279Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0279
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

theorem reflection_log_1_neg : (28691171 / 125000000) ≤ -Real.log (5120 / 6441) ∧
    -Real.log (5120 / 6441) ≤ (229529369 / 1000000000) := by
  have h := checkLog_sound (w := (1321 / 11561)) (n := 12)
    (lo := (28691171 / 125000000)) (hi := (229529369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6441 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6441 / 5120) = 1/(5120 / 6441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (28691171 / 125000000) (229529369 / 1000000000) (Real.log (6441 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6441 / 5120) = -Real.log (5120 / 6441) := by
    rw [show ((6441 / 5120) : ℝ) = ((5120 / 6441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (74604141 / 250000000) ≤ -Real.log (3799 / 5120) ∧
    -Real.log (3799 / 5120) ≤ (59683313 / 200000000) := by
  have h := checkLog_sound (w := (1321 / 8919)) (n := 12)
    (lo := (74604141 / 250000000)) (hi := (59683313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3799) = 1/(3799 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59683313 / 200000000) (-74604141 / 250000000) (Real.log (3799 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (229063493 / 1000000000) ≤ -Real.log (2560 / 3219) ∧
    -Real.log (2560 / 3219) ≤ (114531747 / 500000000) := by
  have h := checkLog_sound (w := (659 / 5779)) (n := 12)
    (lo := (229063493 / 1000000000)) (hi := (114531747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3219 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3219 / 2560) = 1/(2560 / 3219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (229063493 / 1000000000) (114531747 / 500000000) (Real.log (3219 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3219 / 2560) = -Real.log (2560 / 3219) := by
    rw [show ((3219 / 2560) : ℝ) = ((2560 / 3219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (148813597 / 500000000) ≤ -Real.log (1901 / 2560) ∧
    -Real.log (1901 / 2560) ≤ (59525439 / 200000000) := by
  have h := checkLog_sound (w := (659 / 4461)) (n := 12)
    (lo := (148813597 / 500000000)) (hi := (59525439 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1901) = 1/(1901 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59525439 / 200000000) (-148813597 / 500000000) (Real.log (1901 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (416085593 / 1000000000) ≤ -Real.log (2560 / 3881) ∧
    -Real.log (2560 / 3881) ≤ (208042797 / 500000000) := by
  have h := checkLog_sound (w := (1321 / 6441)) (n := 12)
    (lo := (416085593 / 1000000000)) (hi := (208042797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3881 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3881 / 2560) = 1/(2560 / 3881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (416085593 / 1000000000) (208042797 / 500000000) (Real.log (3881 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3881 / 2560) = -Real.log (2560 / 3881) := by
    rw [show ((3881 / 2560) : ℝ) = ((2560 / 3881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (145140531 / 200000000) ≤ -Real.log (1239 / 2560) ∧
    -Real.log (1239 / 2560) ≤ (725702657 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 2519)) (n := 12)
    (lo := (1302219 / 40000000)) (hi := (8138869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1239) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1239) = 1/(1239 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-725702657 / 1000000000) (-145140531 / 200000000) (Real.log (1239 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (207656149 / 500000000) ≤ -Real.log (1280 / 1939) ∧
    -Real.log (1280 / 1939) ≤ (415312299 / 1000000000) := by
  have h := checkLog_sound (w := (659 / 3219)) (n := 12)
    (lo := (207656149 / 500000000)) (hi := (415312299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1939 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1939 / 1280) = 1/(1280 / 1939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (207656149 / 500000000) (415312299 / 1000000000) (Real.log (1939 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1939 / 1280) = -Real.log (1280 / 1939) := by
    rw [show ((1939 / 1280) : ℝ) = ((1280 / 1939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (361642137 / 500000000) ≤ -Real.log (621 / 1280) ∧
    -Real.log (621 / 1280) ≤ (180821069 / 250000000) := by
  have h := checkLog_sound (w := (19 / 1261)) (n := 12)
    (lo := (15068547 / 500000000)) (hi := (6027419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 621) = 1/(621 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-180821069 / 250000000) (-361642137 / 500000000) (Real.log (621 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15688941 / 50000000) ≤ -Real.log (1000000 / 1368587) ∧
    -Real.log (1000000 / 1368587) ≤ (313778821 / 1000000000) := by
  have h := checkLog_sound (w := (368587 / 2368587)) (n := 12)
    (lo := (15688941 / 50000000)) (hi := (313778821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1368587 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1368587 / 1000000) = 1/(1000000 / 1368587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15688941 / 50000000) (313778821 / 1000000000) (Real.log (1368587 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1368587 / 1000000) = -Real.log (1000000 / 1368587) := by
    rw [show ((1368587 / 1000000) : ℝ) = ((1000000 / 1368587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (459795113 / 1000000000) ≤ -Real.log (631413 / 1000000) ∧
    -Real.log (631413 / 1000000) ≤ (229897557 / 500000000) := by
  have h := checkLog_sound (w := (368587 / 1631413)) (n := 12)
    (lo := (459795113 / 1000000000)) (hi := (229897557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 631413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 631413) = 1/(631413 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-229897557 / 500000000) (-459795113 / 1000000000) (Real.log (631413 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (314409929 / 1000000000) ≤ -Real.log (1000000 / 1369451) ∧
    -Real.log (1000000 / 1369451) ≤ (31440993 / 100000000) := by
  have h := checkLog_sound (w := (369451 / 2369451)) (n := 12)
    (lo := (314409929 / 1000000000)) (hi := (31440993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1369451 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1369451 / 1000000) = 1/(1000000 / 1369451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (314409929 / 1000000000) (31440993 / 100000000) (Real.log (1369451 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1369451 / 1000000) = -Real.log (1000000 / 1369451) := by
    rw [show ((1369451 / 1000000) : ℝ) = ((1000000 / 1369451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (46116441 / 100000000) ≤ -Real.log (630549 / 1000000) ∧
    -Real.log (630549 / 1000000) ≤ (461164411 / 1000000000) := by
  have h := checkLog_sound (w := (369451 / 1630549)) (n := 12)
    (lo := (46116441 / 100000000)) (hi := (461164411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 630549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 630549) = 1/(630549 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-461164411 / 1000000000) (-46116441 / 100000000) (Real.log (630549 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (239652131 / 1000000000) ≤ -Real.log (1000000 / 1270807) ∧
    -Real.log (1000000 / 1270807) ≤ (59913033 / 250000000) := by
  have h := checkLog_sound (w := (270807 / 2270807)) (n := 12)
    (lo := (239652131 / 1000000000)) (hi := (59913033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1270807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1270807 / 1000000) = 1/(1000000 / 1270807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (239652131 / 1000000000) (59913033 / 250000000) (Real.log (1270807 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1270807 / 1000000) = -Real.log (1000000 / 1270807) := by
    rw [show ((1270807 / 1000000) : ℝ) = ((1000000 / 1270807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (63163367 / 200000000) ≤ -Real.log (729193 / 1000000) ∧
    -Real.log (729193 / 1000000) ≤ (78954209 / 250000000) := by
  have h := checkLog_sound (w := (270807 / 1729193)) (n := 12)
    (lo := (63163367 / 200000000)) (hi := (78954209 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 729193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 729193) = 1/(729193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-78954209 / 250000000) (-63163367 / 200000000) (Real.log (729193 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (240190227 / 1000000000) ≤ -Real.log (1000000 / 1271491) ∧
    -Real.log (1000000 / 1271491) ≤ (60047557 / 250000000) := by
  have h := checkLog_sound (w := (271491 / 2271491)) (n := 12)
    (lo := (240190227 / 1000000000)) (hi := (60047557 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271491 / 1000000) = 1/(1000000 / 1271491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (240190227 / 1000000000) (60047557 / 250000000) (Real.log (1271491 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1271491 / 1000000) = -Real.log (1000000 / 1271491) := by
    rw [show ((1271491 / 1000000) : ℝ) = ((1000000 / 1271491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (316755299 / 1000000000) ≤ -Real.log (728509 / 1000000) ∧
    -Real.log (728509 / 1000000) ≤ (3167553 / 10000000) := by
  have h := checkLog_sound (w := (271491 / 1728509)) (n := 12)
    (lo := (316755299 / 1000000000)) (hi := (3167553 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 728509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 728509) = 1/(728509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3167553 / 10000000) (-316755299 / 1000000000) (Real.log (728509 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (386786967 / 500000000) ≤ -Real.log (31250000000 / 67734341469) ∧
    -Real.log (31250000000 / 67734341469) ≤ (48348371 / 62500000) := by
  have h := checkLog_sound (w := (5234341469 / 130234341469)) (n := 12)
    (lo := (40213377 / 500000000)) (hi := (16085351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67734341469 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(67734341469 / 62500000000) = 1/(31250000000 / 67734341469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (386786967 / 500000000) (48348371 / 62500000) (Real.log (67734341469 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (67734341469 / 31250000000) = -Real.log (31250000000 / 67734341469) := by
    rw [show ((67734341469 / 31250000000) : ℝ) = ((31250000000 / 67734341469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (775574339 / 1000000000) ≤ -Real.log (20000000000 / 43436782867) ∧
    -Real.log (20000000000 / 43436782867) ≤ (775574341 / 1000000000) := by
  have h := checkLog_sound (w := (3436782867 / 83436782867)) (n := 12)
    (lo := (82427159 / 1000000000)) (hi := (2060679 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43436782867 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(43436782867 / 40000000000) = 1/(20000000000 / 43436782867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (775574339 / 1000000000) (775574341 / 1000000000) (Real.log (43436782867 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (43436782867 / 20000000000) = -Real.log (20000000000 / 43436782867) := by
    rw [show ((43436782867 / 20000000000) : ℝ) = ((20000000000 / 43436782867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (555468967 / 1000000000) ≤ -Real.log (500000000000 / 871379045053) ∧
    -Real.log (500000000000 / 871379045053) ≤ (69433621 / 125000000) := by
  have h := checkLog_sound (w := (371379045053 / 1371379045053)) (n := 12)
    (lo := (555468967 / 1000000000)) (hi := (69433621 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871379045053 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871379045053 / 500000000000) = 1/(500000000000 / 871379045053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (555468967 / 1000000000) (69433621 / 125000000) (Real.log (871379045053 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (871379045053 / 500000000000) = -Real.log (500000000000 / 871379045053) := by
    rw [show ((871379045053 / 500000000000) : ℝ) = ((500000000000 / 871379045053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (278472763 / 500000000) ≤ -Real.log (500000000000 / 872666638299) ∧
    -Real.log (500000000000 / 872666638299) ≤ (556945527 / 1000000000) := by
  have h := checkLog_sound (w := (372666638299 / 1372666638299)) (n := 12)
    (lo := (278472763 / 500000000)) (hi := (556945527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((872666638299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(872666638299 / 500000000000) = 1/(500000000000 / 872666638299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (278472763 / 500000000) (556945527 / 1000000000) (Real.log (872666638299 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (872666638299 / 500000000000) = -Real.log (500000000000 / 872666638299) := by
    rw [show ((872666638299 / 500000000000) : ℝ) = ((500000000000 / 872666638299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0279

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0280Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0280
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

theorem reflection_log_1_neg : (229063493 / 1000000000) ≤ -Real.log (2560 / 3219) ∧
    -Real.log (2560 / 3219) ≤ (114531747 / 500000000) := by
  have h := checkLog_sound (w := (659 / 5779)) (n := 12)
    (lo := (229063493 / 1000000000)) (hi := (114531747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3219 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3219 / 2560) = 1/(2560 / 3219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (229063493 / 1000000000) (114531747 / 500000000) (Real.log (3219 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3219 / 2560) = -Real.log (2560 / 3219) := by
    rw [show ((3219 / 2560) : ℝ) = ((2560 / 3219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (148813597 / 500000000) ≤ -Real.log (1901 / 2560) ∧
    -Real.log (1901 / 2560) ≤ (59525439 / 200000000) := by
  have h := checkLog_sound (w := (659 / 4461)) (n := 12)
    (lo := (148813597 / 500000000)) (hi := (59525439 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1901) = 1/(1901 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59525439 / 200000000) (-148813597 / 500000000) (Real.log (1901 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (228597401 / 1000000000) ≤ -Real.log (1024 / 1287) ∧
    -Real.log (1024 / 1287) ≤ (114298701 / 500000000) := by
  have h := checkLog_sound (w := (263 / 2311)) (n := 12)
    (lo := (228597401 / 1000000000)) (hi := (114298701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287 / 1024) = 1/(1024 / 1287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (228597401 / 1000000000) (114298701 / 500000000) (Real.log (1287 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1287 / 1024) = -Real.log (1024 / 1287) := by
    rw [show ((1287 / 1024) : ℝ) = ((1024 / 1287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (296838447 / 1000000000) ≤ -Real.log (761 / 1024) ∧
    -Real.log (761 / 1024) ≤ (18552403 / 62500000) := by
  have h := checkLog_sound (w := (263 / 1785)) (n := 12)
    (lo := (296838447 / 1000000000)) (hi := (18552403 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 761) = 1/(761 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18552403 / 62500000) (-296838447 / 1000000000) (Real.log (761 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (207656149 / 500000000) ≤ -Real.log (1280 / 1939) ∧
    -Real.log (1280 / 1939) ≤ (415312299 / 1000000000) := by
  have h := checkLog_sound (w := (659 / 3219)) (n := 12)
    (lo := (207656149 / 500000000)) (hi := (415312299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1939 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1939 / 1280) = 1/(1280 / 1939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (207656149 / 500000000) (415312299 / 1000000000) (Real.log (1939 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1939 / 1280) = -Real.log (1280 / 1939) := by
    rw [show ((1939 / 1280) : ℝ) = ((1280 / 1939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (361642137 / 500000000) ≤ -Real.log (621 / 1280) ∧
    -Real.log (621 / 1280) ≤ (180821069 / 250000000) := by
  have h := checkLog_sound (w := (19 / 1261)) (n := 12)
    (lo := (15068547 / 500000000)) (hi := (6027419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 621) = 1/(621 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-180821069 / 250000000) (-361642137 / 500000000) (Real.log (621 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (103634601 / 250000000) ≤ -Real.log (512 / 775) ∧
    -Real.log (512 / 775) ≤ (82907681 / 200000000) := by
  have h := checkLog_sound (w := (263 / 1287)) (n := 12)
    (lo := (103634601 / 250000000)) (hi := (82907681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775 / 512) = 1/(512 / 775) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (103634601 / 250000000) (82907681 / 200000000) (Real.log (775 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (775 / 512) = -Real.log (512 / 775) := by
    rw [show ((775 / 512) : ℝ) = ((512 / 775) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (45054483 / 62500000) ≤ -Real.log (249 / 512) ∧
    -Real.log (249 / 512) ≤ (72087173 / 100000000) := by
  have h := checkLog_sound (w := (7 / 505)) (n := 12)
    (lo := (6931137 / 250000000)) (hi := (27724549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 249) = 1/(249 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-72087173 / 100000000) (-45054483 / 62500000) (Real.log (249 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12525951 / 40000000) ≤ -Real.log (40000 / 54709) ∧
    -Real.log (40000 / 54709) ≤ (39143597 / 125000000) := by
  have h := checkLog_sound (w := (14709 / 94709)) (n := 12)
    (lo := (12525951 / 40000000)) (hi := (39143597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54709 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54709 / 40000) = 1/(40000 / 54709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12525951 / 40000000) (39143597 / 125000000) (Real.log (54709 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (54709 / 40000) = -Real.log (40000 / 54709) := by
    rw [show ((54709 / 40000) : ℝ) = ((40000 / 54709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (114607713 / 250000000) ≤ -Real.log (25291 / 40000) ∧
    -Real.log (25291 / 40000) ≤ (458430853 / 1000000000) := by
  have h := checkLog_sound (w := (14709 / 65291)) (n := 12)
    (lo := (114607713 / 250000000)) (hi := (458430853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 25291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 25291) = 1/(25291 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-458430853 / 1000000000) (-114607713 / 250000000) (Real.log (25291 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (313779551 / 1000000000) ≤ -Real.log (250000 / 342147) ∧
    -Real.log (250000 / 342147) ≤ (9805611 / 31250000) := by
  have h := checkLog_sound (w := (92147 / 592147)) (n := 12)
    (lo := (313779551 / 1000000000)) (hi := (9805611 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342147 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342147 / 250000) = 1/(250000 / 342147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (313779551 / 1000000000) (9805611 / 31250000) (Real.log (342147 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (342147 / 250000) = -Real.log (250000 / 342147) := by
    rw [show ((342147 / 250000) : ℝ) = ((250000 / 342147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (459796697 / 1000000000) ≤ -Real.log (157853 / 250000) ∧
    -Real.log (157853 / 250000) ≤ (229898349 / 500000000) := by
  have h := checkLog_sound (w := (92147 / 407853)) (n := 12)
    (lo := (459796697 / 1000000000)) (hi := (229898349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 157853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 157853) = 1/(157853 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-229898349 / 500000000) (-459796697 / 1000000000) (Real.log (157853 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (5977883 / 25000000) ≤ -Real.log (8000 / 10161) ∧
    -Real.log (8000 / 10161) ≤ (239115321 / 1000000000) := by
  have h := checkLog_sound (w := (2161 / 18161)) (n := 12)
    (lo := (5977883 / 25000000)) (hi := (239115321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10161 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10161 / 8000) = 1/(8000 / 10161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (5977883 / 25000000) (239115321 / 1000000000) (Real.log (10161 / 8000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (10161 / 8000) = -Real.log (8000 / 10161) := by
    rw [show ((10161 / 8000) : ℝ) = ((8000 / 10161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (39360249 / 125000000) ≤ -Real.log (5839 / 8000) ∧
    -Real.log (5839 / 8000) ≤ (314881993 / 1000000000) := by
  have h := checkLog_sound (w := (2161 / 13839)) (n := 12)
    (lo := (39360249 / 125000000)) (hi := (314881993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5839) = 1/(5839 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-314881993 / 1000000000) (-39360249 / 125000000) (Real.log (5839 / 8000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (119826459 / 500000000) ≤ -Real.log (125000 / 158851) ∧
    -Real.log (125000 / 158851) ≤ (239652919 / 1000000000) := by
  have h := checkLog_sound (w := (33851 / 283851)) (n := 12)
    (lo := (119826459 / 500000000)) (hi := (239652919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158851 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158851 / 125000) = 1/(125000 / 158851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (119826459 / 500000000) (239652919 / 1000000000) (Real.log (158851 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (158851 / 125000) = -Real.log (125000 / 158851) := by
    rw [show ((158851 / 125000) : ℝ) = ((125000 / 158851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (315818207 / 1000000000) ≤ -Real.log (91149 / 125000) ∧
    -Real.log (91149 / 125000) ≤ (9869319 / 31250000) := by
  have h := checkLog_sound (w := (33851 / 216149)) (n := 12)
    (lo := (315818207 / 1000000000)) (hi := (9869319 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 91149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 91149) = 1/(91149 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-9869319 / 31250000) (-315818207 / 1000000000) (Real.log (91149 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (771579627 / 1000000000) ≤ -Real.log (100000000000 / 216318057807) ∧
    -Real.log (100000000000 / 216318057807) ≤ (771579629 / 1000000000) := by
  have h := checkLog_sound (w := (16318057807 / 416318057807)) (n := 12)
    (lo := (78432447 / 1000000000)) (hi := (1225507 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216318057807 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(216318057807 / 200000000000) = 1/(100000000000 / 216318057807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (771579627 / 1000000000) (771579629 / 1000000000) (Real.log (216318057807 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (216318057807 / 100000000000) = -Real.log (100000000000 / 216318057807) := by
    rw [show ((216318057807 / 100000000000) : ℝ) = ((100000000000 / 216318057807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (96697031 / 125000000) ≤ -Real.log (125000000000 / 270937992943) ∧
    -Real.log (125000000000 / 270937992943) ≤ (618861 / 800000) := by
  have h := checkLog_sound (w := (20937992943 / 520937992943)) (n := 12)
    (lo := (20107267 / 250000000)) (hi := (80429069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270937992943 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(270937992943 / 250000000000) = 1/(125000000000 / 270937992943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (96697031 / 125000000) (618861 / 800000) (Real.log (270937992943 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (270937992943 / 125000000000) = -Real.log (125000000000 / 270937992943) := by
    rw [show ((270937992943 / 125000000000) : ℝ) = ((125000000000 / 270937992943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (553997313 / 1000000000) ≤ -Real.log (100000000000 / 174019523891) ∧
    -Real.log (100000000000 / 174019523891) ≤ (276998657 / 500000000) := by
  have h := checkLog_sound (w := (74019523891 / 274019523891)) (n := 12)
    (lo := (553997313 / 1000000000)) (hi := (276998657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174019523891 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174019523891 / 100000000000) = 1/(100000000000 / 174019523891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (553997313 / 1000000000) (276998657 / 500000000) (Real.log (174019523891 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (174019523891 / 100000000000) = -Real.log (100000000000 / 174019523891) := by
    rw [show ((174019523891 / 100000000000) : ℝ) = ((100000000000 / 174019523891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4443769 / 8000000) ≤ -Real.log (500000000000 / 871380925737) ∧
    -Real.log (500000000000 / 871380925737) ≤ (277735563 / 500000000) := by
  have h := checkLog_sound (w := (371380925737 / 1371380925737)) (n := 12)
    (lo := (4443769 / 8000000)) (hi := (277735563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871380925737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871380925737 / 500000000000) = 1/(500000000000 / 871380925737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4443769 / 8000000) (277735563 / 500000000) (Real.log (871380925737 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (871380925737 / 500000000000) = -Real.log (500000000000 / 871380925737) := by
    rw [show ((871380925737 / 500000000000) : ℝ) = ((500000000000 / 871380925737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0280

end


