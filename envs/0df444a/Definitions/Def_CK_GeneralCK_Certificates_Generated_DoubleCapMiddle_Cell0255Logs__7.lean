-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0255Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0255Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:12:46.21663+00:00
-- url     : https://prove2.me/theorems/96a5e9aa-b567-4030-9b04-11bad63f2bae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0255Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0256Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0255Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0256Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0257Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0258Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0259Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0260Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0261Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0255Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0256Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0257Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0258Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0259Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0260Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0261Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0255Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0256Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0257Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0258Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0259Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0260Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0261Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0255Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0256Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0257Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0258Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0259Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0260Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0261Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0255Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0255
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

theorem reflection_log_1_neg : (12032287 / 50000000) ≤ -Real.log (5120 / 6513) ∧
    -Real.log (5120 / 6513) ≤ (240645741 / 1000000000) := by
  have h := checkLog_sound (w := (1393 / 11633)) (n := 12)
    (lo := (12032287 / 50000000)) (hi := (240645741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6513 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6513 / 5120) = 1/(5120 / 6513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12032287 / 50000000) (240645741 / 1000000000) (Real.log (6513 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6513 / 5120) = -Real.log (5120 / 6513) := by
    rw [show ((6513 / 5120) : ℝ) = ((5120 / 6513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (158775409 / 500000000) ≤ -Real.log (3727 / 5120) ∧
    -Real.log (3727 / 5120) ≤ (317550819 / 1000000000) := by
  have h := checkLog_sound (w := (1393 / 8847)) (n := 12)
    (lo := (158775409 / 500000000)) (hi := (317550819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3727) = 1/(3727 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-317550819 / 1000000000) (-158775409 / 500000000) (Real.log (3727 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (240185017 / 1000000000) ≤ -Real.log (512 / 651) ∧
    -Real.log (512 / 651) ≤ (120092509 / 500000000) := by
  have h := checkLog_sound (w := (139 / 1163)) (n := 12)
    (lo := (240185017 / 1000000000)) (hi := (120092509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651 / 512) = 1/(512 / 651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (240185017 / 1000000000) (120092509 / 500000000) (Real.log (651 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (651 / 512) = -Real.log (512 / 651) := by
    rw [show ((651 / 512) : ℝ) = ((512 / 651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (63349241 / 200000000) ≤ -Real.log (373 / 512) ∧
    -Real.log (373 / 512) ≤ (158373103 / 500000000) := by
  have h := checkLog_sound (w := (139 / 885)) (n := 12)
    (lo := (63349241 / 200000000)) (hi := (158373103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 373) = 1/(373 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-158373103 / 500000000) (-63349241 / 200000000) (Real.log (373 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (17378701 / 40000000) ≤ -Real.log (2560 / 3953) ∧
    -Real.log (2560 / 3953) ≤ (217233763 / 500000000) := by
  have h := checkLog_sound (w := (1393 / 6513)) (n := 12)
    (lo := (17378701 / 40000000)) (hi := (217233763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3953 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3953 / 2560) = 1/(2560 / 3953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (17378701 / 40000000) (217233763 / 500000000) (Real.log (3953 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3953 / 2560) = -Real.log (2560 / 3953) := by
    rw [show ((3953 / 2560) : ℝ) = ((2560 / 3953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (98196363 / 125000000) ≤ -Real.log (1167 / 2560) ∧
    -Real.log (1167 / 2560) ≤ (392785453 / 500000000) := by
  have h := checkLog_sound (w := (113 / 2447)) (n := 12)
    (lo := (23105931 / 250000000)) (hi := (3696949 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1167) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1167) = 1/(1167 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-392785453 / 500000000) (-98196363 / 125000000) (Real.log (1167 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2710677 / 6250000) ≤ -Real.log (256 / 395) ∧
    -Real.log (256 / 395) ≤ (433708321 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 651)) (n := 12)
    (lo := (2710677 / 6250000)) (hi := (433708321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395 / 256) = 1/(256 / 395) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2710677 / 6250000) (433708321 / 1000000000) (Real.log (395 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (395 / 256) = -Real.log (256 / 395) := by
    rw [show ((395 / 256) : ℝ) = ((256 / 395) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (783003509 / 1000000000) ≤ -Real.log (117 / 256) ∧
    -Real.log (117 / 256) ≤ (783003511 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 245)) (n := 12)
    (lo := (89856329 / 1000000000)) (hi := (8985633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 117) = 1/(117 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-783003511 / 1000000000) (-783003509 / 1000000000) (Real.log (117 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (328830253 / 1000000000) ≤ -Real.log (500000 / 694671) ∧
    -Real.log (500000 / 694671) ≤ (164415127 / 500000000) := by
  have h := checkLog_sound (w := (194671 / 1194671)) (n := 12)
    (lo := (328830253 / 1000000000)) (hi := (164415127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694671 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694671 / 500000) = 1/(500000 / 694671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (328830253 / 1000000000) (164415127 / 500000000) (Real.log (694671 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (694671 / 500000) = -Real.log (500000 / 694671) := by
    rw [show ((694671 / 500000) : ℝ) = ((500000 / 694671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (246609107 / 500000000) ≤ -Real.log (305329 / 500000) ∧
    -Real.log (305329 / 500000) ≤ (98643643 / 200000000) := by
  have h := checkLog_sound (w := (194671 / 805329)) (n := 12)
    (lo := (246609107 / 500000000)) (hi := (98643643 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 305329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 305329) = 1/(305329 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-98643643 / 200000000) (-246609107 / 500000000) (Real.log (305329 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (164727767 / 500000000) ≤ -Real.log (1000000 / 1390211) ∧
    -Real.log (1000000 / 1390211) ≤ (65891107 / 200000000) := by
  have h := checkLog_sound (w := (390211 / 2390211)) (n := 12)
    (lo := (164727767 / 500000000)) (hi := (65891107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1390211 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1390211 / 1000000) = 1/(1000000 / 1390211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (164727767 / 500000000) (65891107 / 200000000) (Real.log (1390211 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1390211 / 1000000) = -Real.log (1000000 / 1390211) := by
    rw [show ((1390211 / 1000000) : ℝ) = ((1000000 / 1390211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (494642283 / 1000000000) ≤ -Real.log (609789 / 1000000) ∧
    -Real.log (609789 / 1000000) ≤ (123660571 / 250000000) := by
  have h := checkLog_sound (w := (390211 / 1609789)) (n := 12)
    (lo := (494642283 / 1000000000)) (hi := (123660571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 609789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 609789) = 1/(609789 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-123660571 / 250000000) (-494642283 / 1000000000) (Real.log (609789 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (126293309 / 500000000) ≤ -Real.log (1000000 / 1287351) ∧
    -Real.log (1000000 / 1287351) ≤ (252586619 / 1000000000) := by
  have h := checkLog_sound (w := (287351 / 2287351)) (n := 12)
    (lo := (126293309 / 500000000)) (hi := (252586619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287351 / 1000000) = 1/(1000000 / 1287351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (126293309 / 500000000) (252586619 / 1000000000) (Real.log (1287351 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1287351 / 1000000) = -Real.log (1000000 / 1287351) := by
    rw [show ((1287351 / 1000000) : ℝ) = ((1000000 / 1287351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (67753253 / 200000000) ≤ -Real.log (712649 / 1000000) ∧
    -Real.log (712649 / 1000000) ≤ (169383133 / 500000000) := by
  have h := checkLog_sound (w := (287351 / 1712649)) (n := 12)
    (lo := (67753253 / 200000000)) (hi := (169383133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 712649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 712649) = 1/(712649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-169383133 / 500000000) (-67753253 / 200000000) (Real.log (712649 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (126563947 / 500000000) ≤ -Real.log (62500 / 80503) ∧
    -Real.log (62500 / 80503) ≤ (50625579 / 200000000) := by
  have h := checkLog_sound (w := (18003 / 143003)) (n := 12)
    (lo := (126563947 / 500000000)) (hi := (50625579 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80503 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80503 / 62500) = 1/(62500 / 80503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (126563947 / 500000000) (50625579 / 200000000) (Real.log (80503 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (80503 / 62500) = -Real.log (62500 / 80503) := by
    rw [show ((80503 / 62500) : ℝ) = ((62500 / 80503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (67948957 / 200000000) ≤ -Real.log (44497 / 62500) ∧
    -Real.log (44497 / 62500) ≤ (169872393 / 500000000) := by
  have h := checkLog_sound (w := (18003 / 106997)) (n := 12)
    (lo := (67948957 / 200000000)) (hi := (169872393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44497) = 1/(44497 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-169872393 / 500000000) (-67948957 / 200000000) (Real.log (44497 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (822048467 / 1000000000) ≤ -Real.log (250000000000 / 568788912943) ∧
    -Real.log (250000000000 / 568788912943) ≤ (822048469 / 1000000000) := by
  have h := checkLog_sound (w := (68788912943 / 1068788912943)) (n := 12)
    (lo := (128901287 / 1000000000)) (hi := (16112661 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568788912943 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(568788912943 / 500000000000) = 1/(250000000000 / 568788912943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (822048467 / 1000000000) (822048469 / 1000000000) (Real.log (568788912943 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (568788912943 / 250000000000) = -Real.log (250000000000 / 568788912943) := by
    rw [show ((568788912943 / 250000000000) : ℝ) = ((250000000000 / 568788912943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (103012227 / 125000000) ≤ -Real.log (4000000000 / 9119292083) ∧
    -Real.log (4000000000 / 9119292083) ≤ (412048909 / 500000000) := by
  have h := checkLog_sound (w := (1119292083 / 17119292083)) (n := 12)
    (lo := (32737659 / 250000000)) (hi := (130950637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9119292083 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9119292083 / 8000000000) = 1/(4000000000 / 9119292083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (103012227 / 125000000) (412048909 / 500000000) (Real.log (9119292083 / 4000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9119292083 / 4000000000) = -Real.log (4000000000 / 9119292083) := by
    rw [show ((9119292083 / 4000000000) : ℝ) = ((4000000000 / 9119292083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (147838221 / 250000000) ≤ -Real.log (500000000000 / 903215327601) ∧
    -Real.log (500000000000 / 903215327601) ≤ (118270577 / 200000000) := by
  have h := checkLog_sound (w := (403215327601 / 1403215327601)) (n := 12)
    (lo := (147838221 / 250000000)) (hi := (118270577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903215327601 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903215327601 / 500000000000) = 1/(500000000000 / 903215327601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (147838221 / 250000000) (118270577 / 200000000) (Real.log (903215327601 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (903215327601 / 500000000000) = -Real.log (500000000000 / 903215327601) := by
    rw [show ((903215327601 / 500000000000) : ℝ) = ((500000000000 / 903215327601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (592872679 / 1000000000) ≤ -Real.log (500000000000 / 904589073421) ∧
    -Real.log (500000000000 / 904589073421) ≤ (14821817 / 25000000) := by
  have h := checkLog_sound (w := (404589073421 / 1404589073421)) (n := 12)
    (lo := (592872679 / 1000000000)) (hi := (14821817 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904589073421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904589073421 / 500000000000) = 1/(500000000000 / 904589073421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (592872679 / 1000000000) (14821817 / 25000000) (Real.log (904589073421 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (904589073421 / 500000000000) = -Real.log (500000000000 / 904589073421) := by
    rw [show ((904589073421 / 500000000000) : ℝ) = ((500000000000 / 904589073421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0255

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0256Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0256
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

theorem reflection_log_1_neg : (240185017 / 1000000000) ≤ -Real.log (512 / 651) ∧
    -Real.log (512 / 651) ≤ (120092509 / 500000000) := by
  have h := checkLog_sound (w := (139 / 1163)) (n := 12)
    (lo := (240185017 / 1000000000)) (hi := (120092509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651 / 512) = 1/(512 / 651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (240185017 / 1000000000) (120092509 / 500000000) (Real.log (651 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (651 / 512) = -Real.log (512 / 651) := by
    rw [show ((651 / 512) : ℝ) = ((512 / 651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (63349241 / 200000000) ≤ -Real.log (373 / 512) ∧
    -Real.log (373 / 512) ≤ (158373103 / 500000000) := by
  have h := checkLog_sound (w := (139 / 885)) (n := 12)
    (lo := (63349241 / 200000000)) (hi := (158373103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 373) = 1/(373 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-158373103 / 500000000) (-63349241 / 200000000) (Real.log (373 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (239724081 / 1000000000) ≤ -Real.log (5120 / 6507) ∧
    -Real.log (5120 / 6507) ≤ (119862041 / 500000000) := by
  have h := checkLog_sound (w := (1387 / 11627)) (n := 12)
    (lo := (239724081 / 1000000000)) (hi := (119862041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6507 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6507 / 5120) = 1/(5120 / 6507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (239724081 / 1000000000) (119862041 / 500000000) (Real.log (6507 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6507 / 5120) = -Real.log (5120 / 6507) := by
    rw [show ((6507 / 5120) : ℝ) = ((5120 / 6507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (315942239 / 1000000000) ≤ -Real.log (3733 / 5120) ∧
    -Real.log (3733 / 5120) ≤ (1974639 / 6250000) := by
  have h := checkLog_sound (w := (1387 / 8853)) (n := 12)
    (lo := (315942239 / 1000000000)) (hi := (1974639 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3733) = 1/(3733 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1974639 / 6250000) (-315942239 / 1000000000) (Real.log (3733 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2710677 / 6250000) ≤ -Real.log (256 / 395) ∧
    -Real.log (256 / 395) ≤ (433708321 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 651)) (n := 12)
    (lo := (2710677 / 6250000)) (hi := (433708321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395 / 256) = 1/(256 / 395) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2710677 / 6250000) (433708321 / 1000000000) (Real.log (395 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (395 / 256) = -Real.log (256 / 395) := by
    rw [show ((395 / 256) : ℝ) = ((256 / 395) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (783003509 / 1000000000) ≤ -Real.log (117 / 256) ∧
    -Real.log (117 / 256) ≤ (783003511 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 245)) (n := 12)
    (lo := (89856329 / 1000000000)) (hi := (8985633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 117) = 1/(117 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-783003511 / 1000000000) (-783003509 / 1000000000) (Real.log (117 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (216474269 / 500000000) ≤ -Real.log (2560 / 3947) ∧
    -Real.log (2560 / 3947) ≤ (432948539 / 1000000000) := by
  have h := checkLog_sound (w := (1387 / 6507)) (n := 12)
    (lo := (216474269 / 500000000)) (hi := (432948539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3947 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3947 / 2560) = 1/(2560 / 3947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (216474269 / 500000000) (432948539 / 1000000000) (Real.log (3947 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3947 / 2560) = -Real.log (2560 / 3947) := by
    rw [show ((3947 / 2560) : ℝ) = ((2560 / 3947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12194417 / 15625000) ≤ -Real.log (1173 / 2560) ∧
    -Real.log (1173 / 2560) ≤ (78044269 / 100000000) := by
  have h := checkLog_sound (w := (107 / 2453)) (n := 12)
    (lo := (21823877 / 250000000)) (hi := (87295509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1173) = 1/(1173 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-78044269 / 100000000) (-12194417 / 15625000) (Real.log (1173 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (164103011 / 500000000) ≤ -Real.log (40000 / 55539) ∧
    -Real.log (40000 / 55539) ≤ (328206023 / 1000000000) := by
  have h := checkLog_sound (w := (15539 / 95539)) (n := 12)
    (lo := (164103011 / 500000000)) (hi := (328206023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55539 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55539 / 40000) = 1/(40000 / 55539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (164103011 / 500000000) (328206023 / 1000000000) (Real.log (55539 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (55539 / 40000) = -Real.log (40000 / 55539) := by
    rw [show ((55539 / 40000) : ℝ) = ((40000 / 55539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (491799441 / 1000000000) ≤ -Real.log (24461 / 40000) ∧
    -Real.log (24461 / 40000) ≤ (245899721 / 500000000) := by
  have h := checkLog_sound (w := (15539 / 64461)) (n := 12)
    (lo := (491799441 / 1000000000)) (hi := (245899721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 24461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 24461) = 1/(24461 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-245899721 / 500000000) (-491799441 / 1000000000) (Real.log (24461 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (328830973 / 1000000000) ≤ -Real.log (1000000 / 1389343) ∧
    -Real.log (1000000 / 1389343) ≤ (164415487 / 500000000) := by
  have h := checkLog_sound (w := (389343 / 2389343)) (n := 12)
    (lo := (328830973 / 1000000000)) (hi := (164415487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1389343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1389343 / 1000000) = 1/(1000000 / 1389343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (328830973 / 1000000000) (164415487 / 500000000) (Real.log (1389343 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1389343 / 1000000) = -Real.log (1000000 / 1389343) := by
    rw [show ((1389343 / 1000000) : ℝ) = ((1000000 / 1389343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (123304963 / 250000000) ≤ -Real.log (610657 / 1000000) ∧
    -Real.log (610657 / 1000000) ≤ (493219853 / 1000000000) := by
  have h := checkLog_sound (w := (389343 / 1610657)) (n := 12)
    (lo := (123304963 / 250000000)) (hi := (493219853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 610657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 610657) = 1/(610657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-493219853 / 1000000000) (-123304963 / 250000000) (Real.log (610657 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (252045827 / 1000000000) ≤ -Real.log (200000 / 257331) ∧
    -Real.log (200000 / 257331) ≤ (63011457 / 250000000) := by
  have h := checkLog_sound (w := (57331 / 457331)) (n := 12)
    (lo := (252045827 / 1000000000)) (hi := (63011457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257331 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257331 / 200000) = 1/(200000 / 257331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (252045827 / 1000000000) (63011457 / 250000000) (Real.log (257331 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (257331 / 200000) = -Real.log (200000 / 257331) := by
    rw [show ((257331 / 200000) : ℝ) = ((200000 / 257331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (42223763 / 125000000) ≤ -Real.log (142669 / 200000) ∧
    -Real.log (142669 / 200000) ≤ (67558021 / 200000000) := by
  have h := checkLog_sound (w := (57331 / 342669)) (n := 12)
    (lo := (42223763 / 125000000)) (hi := (67558021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 142669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 142669) = 1/(142669 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-67558021 / 200000000) (-42223763 / 125000000) (Real.log (142669 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (50517479 / 200000000) ≤ -Real.log (125000 / 160919) ∧
    -Real.log (125000 / 160919) ≤ (63146849 / 250000000) := by
  have h := checkLog_sound (w := (35919 / 285919)) (n := 12)
    (lo := (50517479 / 200000000)) (hi := (63146849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160919 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160919 / 125000) = 1/(125000 / 160919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (50517479 / 200000000) (63146849 / 250000000) (Real.log (160919 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (160919 / 125000) = -Real.log (125000 / 160919) := by
    rw [show ((160919 / 125000) : ℝ) = ((125000 / 160919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (338767669 / 1000000000) ≤ -Real.log (89081 / 125000) ∧
    -Real.log (89081 / 125000) ≤ (33876767 / 100000000) := by
  have h := checkLog_sound (w := (35919 / 214081)) (n := 12)
    (lo := (338767669 / 1000000000)) (hi := (33876767 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89081) = 1/(89081 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-33876767 / 100000000) (-338767669 / 1000000000) (Real.log (89081 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (820005463 / 1000000000) ≤ -Real.log (50000000000 / 113525612199) ∧
    -Real.log (50000000000 / 113525612199) ≤ (164001093 / 200000000) := by
  have h := checkLog_sound (w := (13525612199 / 213525612199)) (n := 12)
    (lo := (126858283 / 1000000000)) (hi := (31714571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113525612199 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(113525612199 / 100000000000) = 1/(50000000000 / 113525612199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (820005463 / 1000000000) (164001093 / 200000000) (Real.log (113525612199 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (113525612199 / 50000000000) = -Real.log (50000000000 / 113525612199) := by
    rw [show ((113525612199 / 50000000000) : ℝ) = ((50000000000 / 113525612199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (32882033 / 40000000) ≤ -Real.log (15625000000 / 35549390861) ∧
    -Real.log (15625000000 / 35549390861) ≤ (822050827 / 1000000000) := by
  have h := checkLog_sound (w := (4299390861 / 66799390861)) (n := 12)
    (lo := (25780729 / 200000000)) (hi := (64451823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35549390861 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(35549390861 / 31250000000) = 1/(15625000000 / 35549390861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (32882033 / 40000000) (822050827 / 1000000000) (Real.log (35549390861 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (35549390861 / 15625000000) = -Real.log (15625000000 / 35549390861) := by
    rw [show ((35549390861 / 15625000000) : ℝ) = ((15625000000 / 35549390861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (147458983 / 250000000) ≤ -Real.log (250000000000 / 450923115743) ∧
    -Real.log (250000000000 / 450923115743) ≤ (589835933 / 1000000000) := by
  have h := checkLog_sound (w := (200923115743 / 700923115743)) (n := 12)
    (lo := (147458983 / 250000000)) (hi := (589835933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450923115743 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450923115743 / 250000000000) = 1/(250000000000 / 450923115743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (147458983 / 250000000) (589835933 / 1000000000) (Real.log (450923115743 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (450923115743 / 250000000000) = -Real.log (250000000000 / 450923115743) := by
    rw [show ((450923115743 / 250000000000) : ℝ) = ((250000000000 / 450923115743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (73919383 / 125000000) ≤ -Real.log (250000000000 / 451608648309) ∧
    -Real.log (250000000000 / 451608648309) ≤ (118271013 / 200000000) := by
  have h := checkLog_sound (w := (201608648309 / 701608648309)) (n := 12)
    (lo := (73919383 / 125000000)) (hi := (118271013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((451608648309 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(451608648309 / 250000000000) = 1/(250000000000 / 451608648309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (73919383 / 125000000) (118271013 / 200000000) (Real.log (451608648309 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (451608648309 / 250000000000) = -Real.log (250000000000 / 451608648309) := by
    rw [show ((451608648309 / 250000000000) : ℝ) = ((250000000000 / 451608648309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0256

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0257Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0257
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

theorem reflection_log_1_neg : (239724081 / 1000000000) ≤ -Real.log (5120 / 6507) ∧
    -Real.log (5120 / 6507) ≤ (119862041 / 500000000) := by
  have h := checkLog_sound (w := (1387 / 11627)) (n := 12)
    (lo := (239724081 / 1000000000)) (hi := (119862041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6507 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6507 / 5120) = 1/(5120 / 6507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (239724081 / 1000000000) (119862041 / 500000000) (Real.log (6507 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6507 / 5120) = -Real.log (5120 / 6507) := by
    rw [show ((6507 / 5120) : ℝ) = ((5120 / 6507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (315942239 / 1000000000) ≤ -Real.log (3733 / 5120) ∧
    -Real.log (3733 / 5120) ≤ (1974639 / 6250000) := by
  have h := checkLog_sound (w := (1387 / 8853)) (n := 12)
    (lo := (315942239 / 1000000000)) (hi := (1974639 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3733) = 1/(3733 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1974639 / 6250000) (-315942239 / 1000000000) (Real.log (3733 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (239262933 / 1000000000) ≤ -Real.log (640 / 813) ∧
    -Real.log (640 / 813) ≤ (119631467 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1453)) (n := 12)
    (lo := (239262933 / 1000000000)) (hi := (119631467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813 / 640) = 1/(640 / 813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (239262933 / 1000000000) (119631467 / 500000000) (Real.log (813 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (813 / 640) = -Real.log (640 / 813) := by
    rw [show ((813 / 640) : ℝ) = ((640 / 813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (157569459 / 500000000) ≤ -Real.log (467 / 640) ∧
    -Real.log (467 / 640) ≤ (315138919 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 467) = 1/(467 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-315138919 / 1000000000) (-157569459 / 500000000) (Real.log (467 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (216474269 / 500000000) ≤ -Real.log (2560 / 3947) ∧
    -Real.log (2560 / 3947) ≤ (432948539 / 1000000000) := by
  have h := checkLog_sound (w := (1387 / 6507)) (n := 12)
    (lo := (216474269 / 500000000)) (hi := (432948539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3947 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3947 / 2560) = 1/(2560 / 3947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (216474269 / 500000000) (432948539 / 1000000000) (Real.log (3947 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3947 / 2560) = -Real.log (2560 / 3947) := by
    rw [show ((3947 / 2560) : ℝ) = ((2560 / 3947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12194417 / 15625000) ≤ -Real.log (1173 / 2560) ∧
    -Real.log (1173 / 2560) ≤ (78044269 / 100000000) := by
  have h := checkLog_sound (w := (107 / 2453)) (n := 12)
    (lo := (21823877 / 250000000)) (hi := (87295509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1173) = 1/(1173 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-78044269 / 100000000) (-12194417 / 15625000) (Real.log (1173 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (216094089 / 500000000) ≤ -Real.log (320 / 493) ∧
    -Real.log (320 / 493) ≤ (432188179 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 813)) (n := 12)
    (lo := (216094089 / 500000000)) (hi := (432188179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493 / 320) = 1/(320 / 493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (216094089 / 500000000) (432188179 / 1000000000) (Real.log (493 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (493 / 320) = -Real.log (320 / 493) := by
    rw [show ((493 / 320) : ℝ) = ((320 / 493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (97236051 / 125000000) ≤ -Real.log (147 / 320) ∧
    -Real.log (147 / 320) ≤ (77788841 / 100000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 147) = 1/(147 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-77788841 / 100000000) (-97236051 / 125000000) (Real.log (147 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (327581401 / 1000000000) ≤ -Real.log (125000 / 173451) ∧
    -Real.log (125000 / 173451) ≤ (163790701 / 500000000) := by
  have h := checkLog_sound (w := (48451 / 298451)) (n := 12)
    (lo := (327581401 / 1000000000)) (hi := (163790701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173451 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173451 / 125000) = 1/(125000 / 173451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (327581401 / 1000000000) (163790701 / 500000000) (Real.log (173451 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (173451 / 125000) = -Real.log (125000 / 173451) := by
    rw [show ((173451 / 125000) : ℝ) = ((125000 / 173451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (245191339 / 500000000) ≤ -Real.log (76549 / 125000) ∧
    -Real.log (76549 / 125000) ≤ (490382679 / 1000000000) := by
  have h := checkLog_sound (w := (48451 / 201549)) (n := 12)
    (lo := (245191339 / 500000000)) (hi := (490382679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 76549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 76549) = 1/(76549 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-490382679 / 1000000000) (-245191339 / 500000000) (Real.log (76549 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (164103371 / 500000000) ≤ -Real.log (250000 / 347119) ∧
    -Real.log (250000 / 347119) ≤ (328206743 / 1000000000) := by
  have h := checkLog_sound (w := (97119 / 597119)) (n := 12)
    (lo := (164103371 / 500000000)) (hi := (328206743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347119 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347119 / 250000) = 1/(250000 / 347119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (164103371 / 500000000) (328206743 / 1000000000) (Real.log (347119 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (347119 / 250000) = -Real.log (250000 / 347119) := by
    rw [show ((347119 / 250000) : ℝ) = ((250000 / 347119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (122950269 / 250000000) ≤ -Real.log (152881 / 250000) ∧
    -Real.log (152881 / 250000) ≤ (491801077 / 1000000000) := by
  have h := checkLog_sound (w := (97119 / 402881)) (n := 12)
    (lo := (122950269 / 250000000)) (hi := (491801077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 152881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 152881) = 1/(152881 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-491801077 / 1000000000) (-122950269 / 250000000) (Real.log (152881 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (251505521 / 1000000000) ≤ -Real.log (25000 / 32149) ∧
    -Real.log (25000 / 32149) ≤ (125752761 / 500000000) := by
  have h := checkLog_sound (w := (7149 / 57149)) (n := 12)
    (lo := (251505521 / 1000000000)) (hi := (125752761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32149 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32149 / 25000) = 1/(25000 / 32149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (251505521 / 1000000000) (125752761 / 500000000) (Real.log (32149 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (32149 / 25000) = -Real.log (25000 / 32149) := by
    rw [show ((32149 / 25000) : ℝ) = ((25000 / 32149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (67363259 / 200000000) ≤ -Real.log (17851 / 25000) ∧
    -Real.log (17851 / 25000) ≤ (42102037 / 125000000) := by
  have h := checkLog_sound (w := (7149 / 42851)) (n := 12)
    (lo := (67363259 / 200000000)) (hi := (42102037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 17851) = 1/(17851 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-42102037 / 125000000) (-67363259 / 200000000) (Real.log (17851 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (63011651 / 250000000) ≤ -Real.log (15625 / 20104) ∧
    -Real.log (15625 / 20104) ≤ (50409321 / 200000000) := by
  have h := checkLog_sound (w := (4479 / 35729)) (n := 12)
    (lo := (63011651 / 250000000)) (hi := (50409321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20104 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20104 / 15625) = 1/(15625 / 20104) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (63011651 / 250000000) (50409321 / 200000000) (Real.log (20104 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (20104 / 15625) = -Real.log (15625 / 20104) := by
    rw [show ((20104 / 15625) : ℝ) = ((15625 / 20104) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (168895753 / 500000000) ≤ -Real.log (11146 / 15625) ∧
    -Real.log (11146 / 15625) ≤ (337791507 / 1000000000) := by
  have h := checkLog_sound (w := (4479 / 26771)) (n := 12)
    (lo := (168895753 / 500000000)) (hi := (337791507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11146) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11146) = 1/(11146 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-337791507 / 1000000000) (-168895753 / 500000000) (Real.log (11146 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (817964079 / 1000000000) ≤ -Real.log (125000000000 / 283235248011) ∧
    -Real.log (125000000000 / 283235248011) ≤ (817964081 / 1000000000) := by
  have h := checkLog_sound (w := (33235248011 / 533235248011)) (n := 12)
    (lo := (124816899 / 1000000000)) (hi := (1248169 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283235248011 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(283235248011 / 250000000000) = 1/(125000000000 / 283235248011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (817964079 / 1000000000) (817964081 / 1000000000) (Real.log (283235248011 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (283235248011 / 125000000000) = -Real.log (125000000000 / 283235248011) := by
    rw [show ((283235248011 / 125000000000) : ℝ) = ((125000000000 / 283235248011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (820007819 / 1000000000) ≤ -Real.log (250000000000 / 567629398029) ∧
    -Real.log (250000000000 / 567629398029) ≤ (820007821 / 1000000000) := by
  have h := checkLog_sound (w := (67629398029 / 1067629398029)) (n := 12)
    (lo := (126860639 / 1000000000)) (hi := (792879 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567629398029 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(567629398029 / 500000000000) = 1/(250000000000 / 567629398029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (820007819 / 1000000000) (820007821 / 1000000000) (Real.log (567629398029 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (567629398029 / 250000000000) = -Real.log (250000000000 / 567629398029) := by
    rw [show ((567629398029 / 250000000000) : ℝ) = ((250000000000 / 567629398029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (73540227 / 125000000) ≤ -Real.log (500000000000 / 900481765727) ∧
    -Real.log (500000000000 / 900481765727) ≤ (588321817 / 1000000000) := by
  have h := checkLog_sound (w := (400481765727 / 1400481765727)) (n := 12)
    (lo := (73540227 / 125000000)) (hi := (588321817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900481765727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900481765727 / 500000000000) = 1/(500000000000 / 900481765727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (73540227 / 125000000) (588321817 / 1000000000) (Real.log (900481765727 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (900481765727 / 500000000000) = -Real.log (500000000000 / 900481765727) := by
    rw [show ((900481765727 / 500000000000) : ℝ) = ((500000000000 / 900481765727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (589838111 / 1000000000) ≤ -Real.log (500000000000 / 901848196663) ∧
    -Real.log (500000000000 / 901848196663) ≤ (18432441 / 31250000) := by
  have h := checkLog_sound (w := (401848196663 / 1401848196663)) (n := 12)
    (lo := (589838111 / 1000000000)) (hi := (18432441 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((901848196663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(901848196663 / 500000000000) = 1/(500000000000 / 901848196663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (589838111 / 1000000000) (18432441 / 31250000) (Real.log (901848196663 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (901848196663 / 500000000000) = -Real.log (500000000000 / 901848196663) := by
    rw [show ((901848196663 / 500000000000) : ℝ) = ((500000000000 / 901848196663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0257

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0258Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0258
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

theorem reflection_log_1_neg : (239262933 / 1000000000) ≤ -Real.log (640 / 813) ∧
    -Real.log (640 / 813) ≤ (119631467 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1453)) (n := 12)
    (lo := (239262933 / 1000000000)) (hi := (119631467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813 / 640) = 1/(640 / 813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (239262933 / 1000000000) (119631467 / 500000000) (Real.log (813 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (813 / 640) = -Real.log (640 / 813) := by
    rw [show ((813 / 640) : ℝ) = ((640 / 813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (157569459 / 500000000) ≤ -Real.log (467 / 640) ∧
    -Real.log (467 / 640) ≤ (315138919 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 467) = 1/(467 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-315138919 / 1000000000) (-157569459 / 500000000) (Real.log (467 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (59700393 / 250000000) ≤ -Real.log (5120 / 6501) ∧
    -Real.log (5120 / 6501) ≤ (238801573 / 1000000000) := by
  have h := checkLog_sound (w := (1381 / 11621)) (n := 12)
    (lo := (59700393 / 250000000)) (hi := (238801573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6501 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6501 / 5120) = 1/(5120 / 6501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (59700393 / 250000000) (238801573 / 1000000000) (Real.log (6501 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6501 / 5120) = -Real.log (5120 / 6501) := by
    rw [show ((6501 / 5120) : ℝ) = ((5120 / 6501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (314336243 / 1000000000) ≤ -Real.log (3739 / 5120) ∧
    -Real.log (3739 / 5120) ≤ (78584061 / 250000000) := by
  have h := checkLog_sound (w := (1381 / 8859)) (n := 12)
    (lo := (314336243 / 1000000000)) (hi := (78584061 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3739) = 1/(3739 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-78584061 / 250000000) (-314336243 / 1000000000) (Real.log (3739 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (216094089 / 500000000) ≤ -Real.log (320 / 493) ∧
    -Real.log (320 / 493) ≤ (432188179 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 813)) (n := 12)
    (lo := (216094089 / 500000000)) (hi := (432188179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493 / 320) = 1/(320 / 493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (216094089 / 500000000) (432188179 / 1000000000) (Real.log (493 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (493 / 320) = -Real.log (320 / 493) := by
    rw [show ((493 / 320) : ℝ) = ((320 / 493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (97236051 / 125000000) ≤ -Real.log (147 / 320) ∧
    -Real.log (147 / 320) ≤ (77788841 / 100000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 147) = 1/(147 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-77788841 / 100000000) (-97236051 / 125000000) (Real.log (147 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (431427239 / 1000000000) ≤ -Real.log (2560 / 3941) ∧
    -Real.log (2560 / 3941) ≤ (10785681 / 25000000) := by
  have h := checkLog_sound (w := (1381 / 6501)) (n := 12)
    (lo := (431427239 / 1000000000)) (hi := (10785681 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3941 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3941 / 2560) = 1/(2560 / 3941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (431427239 / 1000000000) (10785681 / 25000000) (Real.log (3941 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3941 / 2560) = -Real.log (2560 / 3941) := by
    rw [show ((3941 / 2560) : ℝ) = ((2560 / 3941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (193835159 / 250000000) ≤ -Real.log (1179 / 2560) ∧
    -Real.log (1179 / 2560) ≤ (387670319 / 500000000) := by
  have h := checkLog_sound (w := (101 / 2459)) (n := 12)
    (lo := (5137091 / 62500000)) (hi := (82193457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1179) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1179) = 1/(1179 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-387670319 / 500000000) (-193835159 / 250000000) (Real.log (1179 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (326956389 / 1000000000) ≤ -Real.log (1000000 / 1386741) ∧
    -Real.log (1000000 / 1386741) ≤ (32695639 / 100000000) := by
  have h := checkLog_sound (w := (386741 / 2386741)) (n := 12)
    (lo := (326956389 / 1000000000)) (hi := (32695639 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1386741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1386741 / 1000000) = 1/(1000000 / 1386741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (326956389 / 1000000000) (32695639 / 100000000) (Real.log (1386741 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1386741 / 1000000) = -Real.log (1000000 / 1386741) := by
    rw [show ((1386741 / 1000000) : ℝ) = ((1000000 / 1386741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (6112099 / 12500000) ≤ -Real.log (613259 / 1000000) ∧
    -Real.log (613259 / 1000000) ≤ (488967921 / 1000000000) := by
  have h := checkLog_sound (w := (386741 / 1613259)) (n := 12)
    (lo := (6112099 / 12500000)) (hi := (488967921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 613259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 613259) = 1/(613259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-488967921 / 1000000000) (-6112099 / 12500000) (Real.log (613259 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (163791061 / 500000000) ≤ -Real.log (1000000 / 1387609) ∧
    -Real.log (1000000 / 1387609) ≤ (327582123 / 1000000000) := by
  have h := checkLog_sound (w := (387609 / 2387609)) (n := 12)
    (lo := (163791061 / 500000000)) (hi := (327582123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1387609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1387609 / 1000000) = 1/(1000000 / 1387609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (163791061 / 500000000) (327582123 / 1000000000) (Real.log (1387609 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1387609 / 1000000) = -Real.log (1000000 / 1387609) := by
    rw [show ((1387609 / 1000000) : ℝ) = ((1000000 / 1387609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (490384311 / 1000000000) ≤ -Real.log (612391 / 1000000) ∧
    -Real.log (612391 / 1000000) ≤ (61298039 / 125000000) := by
  have h := checkLog_sound (w := (387609 / 1612391)) (n := 12)
    (lo := (490384311 / 1000000000)) (hi := (61298039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 612391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 612391) = 1/(612391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-61298039 / 125000000) (-490384311 / 1000000000) (Real.log (612391 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2509657 / 10000000) ≤ -Real.log (500000 / 642633) ∧
    -Real.log (500000 / 642633) ≤ (250965701 / 1000000000) := by
  have h := checkLog_sound (w := (142633 / 1142633)) (n := 12)
    (lo := (2509657 / 10000000)) (hi := (250965701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642633 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642633 / 500000) = 1/(500000 / 642633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2509657 / 10000000) (250965701 / 1000000000) (Real.log (642633 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (642633 / 500000) = -Real.log (500000 / 642633) := by
    rw [show ((642633 / 500000) : ℝ) = ((500000 / 642633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (335844833 / 1000000000) ≤ -Real.log (357367 / 500000) ∧
    -Real.log (357367 / 500000) ≤ (167922417 / 500000000) := by
  have h := checkLog_sound (w := (142633 / 857367)) (n := 12)
    (lo := (335844833 / 1000000000)) (hi := (167922417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 357367) = 1/(357367 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-167922417 / 500000000) (-335844833 / 1000000000) (Real.log (357367 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (125753149 / 500000000) ≤ -Real.log (1000000 / 1285961) ∧
    -Real.log (1000000 / 1285961) ≤ (251506299 / 1000000000) := by
  have h := checkLog_sound (w := (285961 / 2285961)) (n := 12)
    (lo := (125753149 / 500000000)) (hi := (251506299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285961 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285961 / 1000000) = 1/(1000000 / 1285961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (125753149 / 500000000) (251506299 / 1000000000) (Real.log (1285961 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1285961 / 1000000) = -Real.log (1000000 / 1285961) := by
    rw [show ((1285961 / 1000000) : ℝ) = ((1000000 / 1285961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (10525553 / 31250000) ≤ -Real.log (714039 / 1000000) ∧
    -Real.log (714039 / 1000000) ≤ (336817697 / 1000000000) := by
  have h := checkLog_sound (w := (285961 / 1714039)) (n := 12)
    (lo := (10525553 / 31250000)) (hi := (336817697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714039) = 1/(714039 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-336817697 / 1000000000) (-10525553 / 31250000) (Real.log (714039 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (815924309 / 1000000000) ≤ -Real.log (250000000000 / 565316204083) ∧
    -Real.log (250000000000 / 565316204083) ≤ (815924311 / 1000000000) := by
  have h := checkLog_sound (w := (65316204083 / 1065316204083)) (n := 12)
    (lo := (122777129 / 1000000000)) (hi := (12277713 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565316204083 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(565316204083 / 500000000000) = 1/(250000000000 / 565316204083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (815924309 / 1000000000) (815924311 / 1000000000) (Real.log (565316204083 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (565316204083 / 250000000000) = -Real.log (250000000000 / 565316204083) := by
    rw [show ((565316204083 / 250000000000) : ℝ) = ((250000000000 / 565316204083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (817966433 / 1000000000) ≤ -Real.log (100000000000 / 226588731709) ∧
    -Real.log (100000000000 / 226588731709) ≤ (163593287 / 200000000) := by
  have h := checkLog_sound (w := (26588731709 / 426588731709)) (n := 12)
    (lo := (124819253 / 1000000000)) (hi := (62409627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226588731709 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(226588731709 / 200000000000) = 1/(100000000000 / 226588731709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (817966433 / 1000000000) (163593287 / 200000000) (Real.log (226588731709 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (226588731709 / 100000000000) = -Real.log (100000000000 / 226588731709) := by
    rw [show ((226588731709 / 100000000000) : ℝ) = ((100000000000 / 226588731709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (293405267 / 500000000) ≤ -Real.log (31250000000 / 56195119443) ∧
    -Real.log (31250000000 / 56195119443) ≤ (117362107 / 200000000) := by
  have h := checkLog_sound (w := (24945119443 / 87445119443)) (n := 12)
    (lo := (293405267 / 500000000)) (hi := (117362107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56195119443 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56195119443 / 31250000000) = 1/(31250000000 / 56195119443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (293405267 / 500000000) (117362107 / 200000000) (Real.log (56195119443 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (56195119443 / 31250000000) = -Real.log (31250000000 / 56195119443) := by
    rw [show ((56195119443 / 31250000000) : ℝ) = ((31250000000 / 56195119443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (117664799 / 200000000) ≤ -Real.log (12500000000 / 22512093177) ∧
    -Real.log (12500000000 / 22512093177) ≤ (147080999 / 250000000) := by
  have h := checkLog_sound (w := (10012093177 / 35012093177)) (n := 12)
    (lo := (117664799 / 200000000)) (hi := (147080999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22512093177 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22512093177 / 12500000000) = 1/(12500000000 / 22512093177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (117664799 / 200000000) (147080999 / 250000000) (Real.log (22512093177 / 12500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (22512093177 / 12500000000) = -Real.log (12500000000 / 22512093177) := by
    rw [show ((22512093177 / 12500000000) : ℝ) = ((12500000000 / 22512093177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0258

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0259Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0259
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

theorem reflection_log_1_neg : (59700393 / 250000000) ≤ -Real.log (5120 / 6501) ∧
    -Real.log (5120 / 6501) ≤ (238801573 / 1000000000) := by
  have h := checkLog_sound (w := (1381 / 11621)) (n := 12)
    (lo := (59700393 / 250000000)) (hi := (238801573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6501 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6501 / 5120) = 1/(5120 / 6501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (59700393 / 250000000) (238801573 / 1000000000) (Real.log (6501 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6501 / 5120) = -Real.log (5120 / 6501) := by
    rw [show ((6501 / 5120) : ℝ) = ((5120 / 6501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (314336243 / 1000000000) ≤ -Real.log (3739 / 5120) ∧
    -Real.log (3739 / 5120) ≤ (78584061 / 250000000) := by
  have h := checkLog_sound (w := (1381 / 8859)) (n := 12)
    (lo := (314336243 / 1000000000)) (hi := (78584061 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3739) = 1/(3739 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-78584061 / 250000000) (-314336243 / 1000000000) (Real.log (3739 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (119169999 / 500000000) ≤ -Real.log (2560 / 3249) ∧
    -Real.log (2560 / 3249) ≤ (238339999 / 1000000000) := by
  have h := checkLog_sound (w := (689 / 5809)) (n := 12)
    (lo := (119169999 / 500000000)) (hi := (238339999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3249 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3249 / 2560) = 1/(2560 / 3249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (119169999 / 500000000) (238339999 / 1000000000) (Real.log (3249 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3249 / 2560) = -Real.log (2560 / 3249) := by
    rw [show ((3249 / 2560) : ℝ) = ((2560 / 3249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (313534211 / 1000000000) ≤ -Real.log (1871 / 2560) ∧
    -Real.log (1871 / 2560) ≤ (78383553 / 250000000) := by
  have h := checkLog_sound (w := (689 / 4431)) (n := 12)
    (lo := (313534211 / 1000000000)) (hi := (78383553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1871) = 1/(1871 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-78383553 / 250000000) (-313534211 / 1000000000) (Real.log (1871 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (431427239 / 1000000000) ≤ -Real.log (2560 / 3941) ∧
    -Real.log (2560 / 3941) ≤ (10785681 / 25000000) := by
  have h := checkLog_sound (w := (1381 / 6501)) (n := 12)
    (lo := (431427239 / 1000000000)) (hi := (10785681 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3941 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3941 / 2560) = 1/(2560 / 3941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (431427239 / 1000000000) (10785681 / 25000000) (Real.log (3941 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3941 / 2560) = -Real.log (2560 / 3941) := by
    rw [show ((3941 / 2560) : ℝ) = ((2560 / 3941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (193835159 / 250000000) ≤ -Real.log (1179 / 2560) ∧
    -Real.log (1179 / 2560) ≤ (387670319 / 500000000) := by
  have h := checkLog_sound (w := (101 / 2459)) (n := 12)
    (lo := (5137091 / 62500000)) (hi := (82193457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1179) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1179) = 1/(1179 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-387670319 / 500000000) (-193835159 / 250000000) (Real.log (1179 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (430665721 / 1000000000) ≤ -Real.log (1280 / 1969) ∧
    -Real.log (1280 / 1969) ≤ (215332861 / 500000000) := by
  have h := checkLog_sound (w := (689 / 3249)) (n := 12)
    (lo := (430665721 / 1000000000)) (hi := (215332861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969 / 1280) = 1/(1280 / 1969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (430665721 / 1000000000) (215332861 / 500000000) (Real.log (1969 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1969 / 1280) = -Real.log (1280 / 1969) := by
    rw [show ((1969 / 1280) : ℝ) = ((1280 / 1969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (386399669 / 500000000) ≤ -Real.log (591 / 1280) ∧
    -Real.log (591 / 1280) ≤ (38639967 / 50000000) := by
  have h := checkLog_sound (w := (49 / 1231)) (n := 12)
    (lo := (39826079 / 500000000)) (hi := (79652159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 591) = 1/(591 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38639967 / 50000000) (-386399669 / 500000000) (Real.log (591 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (326331709 / 1000000000) ≤ -Real.log (8000 / 11087) ∧
    -Real.log (8000 / 11087) ≤ (32633171 / 100000000) := by
  have h := checkLog_sound (w := (3087 / 19087)) (n := 12)
    (lo := (326331709 / 1000000000)) (hi := (32633171 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11087 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11087 / 8000) = 1/(8000 / 11087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (326331709 / 1000000000) (32633171 / 100000000) (Real.log (11087 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (11087 / 8000) = -Real.log (8000 / 11087) := by
    rw [show ((11087 / 8000) : ℝ) = ((8000 / 11087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (121889197 / 250000000) ≤ -Real.log (4913 / 8000) ∧
    -Real.log (4913 / 8000) ≤ (487556789 / 1000000000) := by
  have h := checkLog_sound (w := (3087 / 12913)) (n := 12)
    (lo := (121889197 / 250000000)) (hi := (487556789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 4913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 4913) = 1/(4913 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-487556789 / 1000000000) (-121889197 / 250000000) (Real.log (4913 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (326957111 / 1000000000) ≤ -Real.log (500000 / 693371) ∧
    -Real.log (500000 / 693371) ≤ (40869639 / 125000000) := by
  have h := checkLog_sound (w := (193371 / 1193371)) (n := 12)
    (lo := (326957111 / 1000000000)) (hi := (40869639 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693371 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693371 / 500000) = 1/(500000 / 693371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (326957111 / 1000000000) (40869639 / 125000000) (Real.log (693371 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (693371 / 500000) = -Real.log (500000 / 693371) := by
    rw [show ((693371 / 500000) : ℝ) = ((500000 / 693371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (9779391 / 20000000) ≤ -Real.log (306629 / 500000) ∧
    -Real.log (306629 / 500000) ≤ (488969551 / 1000000000) := by
  have h := checkLog_sound (w := (193371 / 806629)) (n := 12)
    (lo := (9779391 / 20000000)) (hi := (488969551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 306629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 306629) = 1/(306629 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-488969551 / 1000000000) (-9779391 / 20000000) (Real.log (306629 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (62606397 / 250000000) ≤ -Real.log (250000 / 321143) ∧
    -Real.log (250000 / 321143) ≤ (250425589 / 1000000000) := by
  have h := checkLog_sound (w := (71143 / 571143)) (n := 12)
    (lo := (62606397 / 250000000)) (hi := (250425589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321143 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321143 / 250000) = 1/(250000 / 321143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (62606397 / 250000000) (250425589 / 1000000000) (Real.log (321143 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (321143 / 250000) = -Real.log (250000 / 321143) := by
    rw [show ((321143 / 250000) : ℝ) = ((250000 / 321143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (334874313 / 1000000000) ≤ -Real.log (178857 / 250000) ∧
    -Real.log (178857 / 250000) ≤ (167437157 / 500000000) := by
  have h := checkLog_sound (w := (71143 / 428857)) (n := 12)
    (lo := (334874313 / 1000000000)) (hi := (167437157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178857) = 1/(178857 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-167437157 / 500000000) (-334874313 / 1000000000) (Real.log (178857 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (125483239 / 500000000) ≤ -Real.log (1000000 / 1285267) ∧
    -Real.log (1000000 / 1285267) ≤ (250966479 / 1000000000) := by
  have h := checkLog_sound (w := (285267 / 2285267)) (n := 12)
    (lo := (125483239 / 500000000)) (hi := (250966479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285267 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285267 / 1000000) = 1/(1000000 / 1285267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (125483239 / 500000000) (250966479 / 1000000000) (Real.log (1285267 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1285267 / 1000000) = -Real.log (1000000 / 1285267) := by
    rw [show ((1285267 / 1000000) : ℝ) = ((1000000 / 1285267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (41980779 / 125000000) ≤ -Real.log (714733 / 1000000) ∧
    -Real.log (714733 / 1000000) ≤ (335846233 / 1000000000) := by
  have h := checkLog_sound (w := (285267 / 1714733)) (n := 12)
    (lo := (41980779 / 125000000)) (hi := (335846233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714733) = 1/(714733 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-335846233 / 1000000000) (-41980779 / 125000000) (Real.log (714733 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (813888497 / 1000000000) ≤ -Real.log (500000000000 / 1128332994097) ∧
    -Real.log (500000000000 / 1128332994097) ≤ (813888499 / 1000000000) := by
  have h := checkLog_sound (w := (128332994097 / 2128332994097)) (n := 12)
    (lo := (120741317 / 1000000000)) (hi := (60370659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128332994097 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1128332994097 / 1000000000000) = 1/(500000000000 / 1128332994097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (813888497 / 1000000000) (813888499 / 1000000000) (Real.log (1128332994097 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1128332994097 / 500000000000) = -Real.log (500000000000 / 1128332994097) := by
    rw [show ((1128332994097 / 500000000000) : ℝ) = ((500000000000 / 1128332994097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (815926661 / 1000000000) ≤ -Real.log (250000000000 / 565317533567) ∧
    -Real.log (250000000000 / 565317533567) ≤ (815926663 / 1000000000) := by
  have h := checkLog_sound (w := (65317533567 / 1065317533567)) (n := 12)
    (lo := (122779481 / 1000000000)) (hi := (61389741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565317533567 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(565317533567 / 500000000000) = 1/(250000000000 / 565317533567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (815926661 / 1000000000) (815926663 / 1000000000) (Real.log (565317533567 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (565317533567 / 250000000000) = -Real.log (250000000000 / 565317533567) := by
    rw [show ((565317533567 / 250000000000) : ℝ) = ((250000000000 / 565317533567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (292649951 / 500000000) ≤ -Real.log (5000000000 / 8977646947) ∧
    -Real.log (5000000000 / 8977646947) ≤ (585299903 / 1000000000) := by
  have h := checkLog_sound (w := (3977646947 / 13977646947)) (n := 12)
    (lo := (292649951 / 500000000)) (hi := (585299903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8977646947 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8977646947 / 5000000000) = 1/(5000000000 / 8977646947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (292649951 / 500000000) (585299903 / 1000000000) (Real.log (8977646947 / 5000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8977646947 / 5000000000) = -Real.log (5000000000 / 8977646947) := by
    rw [show ((8977646947 / 5000000000) : ℝ) = ((5000000000 / 8977646947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (586812711 / 1000000000) ≤ -Real.log (250000000000 / 449561934317) ∧
    -Real.log (250000000000 / 449561934317) ≤ (73351589 / 125000000) := by
  have h := checkLog_sound (w := (199561934317 / 699561934317)) (n := 12)
    (lo := (586812711 / 1000000000)) (hi := (73351589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449561934317 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449561934317 / 250000000000) = 1/(250000000000 / 449561934317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (586812711 / 1000000000) (73351589 / 125000000) (Real.log (449561934317 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (449561934317 / 250000000000) = -Real.log (250000000000 / 449561934317) := by
    rw [show ((449561934317 / 250000000000) : ℝ) = ((250000000000 / 449561934317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0259

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0260Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0260
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

theorem reflection_log_1_neg : (119169999 / 500000000) ≤ -Real.log (2560 / 3249) ∧
    -Real.log (2560 / 3249) ≤ (238339999 / 1000000000) := by
  have h := checkLog_sound (w := (689 / 5809)) (n := 12)
    (lo := (119169999 / 500000000)) (hi := (238339999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3249 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3249 / 2560) = 1/(2560 / 3249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (119169999 / 500000000) (238339999 / 1000000000) (Real.log (3249 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3249 / 2560) = -Real.log (2560 / 3249) := by
    rw [show ((3249 / 2560) : ℝ) = ((2560 / 3249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (313534211 / 1000000000) ≤ -Real.log (1871 / 2560) ∧
    -Real.log (1871 / 2560) ≤ (78383553 / 250000000) := by
  have h := checkLog_sound (w := (689 / 4431)) (n := 12)
    (lo := (313534211 / 1000000000)) (hi := (78383553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1871) = 1/(1871 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-78383553 / 250000000) (-313534211 / 1000000000) (Real.log (1871 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (237878211 / 1000000000) ≤ -Real.log (1024 / 1299) ∧
    -Real.log (1024 / 1299) ≤ (59469553 / 250000000) := by
  have h := checkLog_sound (w := (275 / 2323)) (n := 12)
    (lo := (237878211 / 1000000000)) (hi := (59469553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299 / 1024) = 1/(1024 / 1299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (237878211 / 1000000000) (59469553 / 250000000) (Real.log (1299 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1299 / 1024) = -Real.log (1024 / 1299) := by
    rw [show ((1299 / 1024) : ℝ) = ((1024 / 1299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (156366411 / 500000000) ≤ -Real.log (749 / 1024) ∧
    -Real.log (749 / 1024) ≤ (312732823 / 1000000000) := by
  have h := checkLog_sound (w := (275 / 1773)) (n := 12)
    (lo := (156366411 / 500000000)) (hi := (312732823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 749) = 1/(749 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-312732823 / 1000000000) (-156366411 / 500000000) (Real.log (749 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (430665721 / 1000000000) ≤ -Real.log (1280 / 1969) ∧
    -Real.log (1280 / 1969) ≤ (215332861 / 500000000) := by
  have h := checkLog_sound (w := (689 / 3249)) (n := 12)
    (lo := (430665721 / 1000000000)) (hi := (215332861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969 / 1280) = 1/(1280 / 1969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (430665721 / 1000000000) (215332861 / 500000000) (Real.log (1969 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1969 / 1280) = -Real.log (1280 / 1969) := by
    rw [show ((1969 / 1280) : ℝ) = ((1280 / 1969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (386399669 / 500000000) ≤ -Real.log (591 / 1280) ∧
    -Real.log (591 / 1280) ≤ (38639967 / 50000000) := by
  have h := checkLog_sound (w := (49 / 1231)) (n := 12)
    (lo := (39826079 / 500000000)) (hi := (79652159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 591) = 1/(591 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-38639967 / 50000000) (-386399669 / 500000000) (Real.log (591 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (429903623 / 1000000000) ≤ -Real.log (512 / 787) ∧
    -Real.log (512 / 787) ≤ (53737953 / 125000000) := by
  have h := checkLog_sound (w := (275 / 1299)) (n := 12)
    (lo := (429903623 / 1000000000)) (hi := (53737953 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787 / 512) = 1/(512 / 787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (429903623 / 1000000000) (53737953 / 125000000) (Real.log (787 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (787 / 512) = -Real.log (512 / 787) := by
    rw [show ((787 / 512) : ℝ) = ((512 / 787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (770264483 / 1000000000) ≤ -Real.log (237 / 512) ∧
    -Real.log (237 / 512) ≤ (154052897 / 200000000) := by
  have h := checkLog_sound (w := (19 / 493)) (n := 12)
    (lo := (77117303 / 1000000000)) (hi := (9639663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 237) = 1/(237 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-154052897 / 200000000) (-770264483 / 1000000000) (Real.log (237 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (325706637 / 1000000000) ≤ -Real.log (1000000 / 1385009) ∧
    -Real.log (1000000 / 1385009) ≤ (162853319 / 500000000) := by
  have h := checkLog_sound (w := (385009 / 2385009)) (n := 12)
    (lo := (325706637 / 1000000000)) (hi := (162853319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1385009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1385009 / 1000000) = 1/(1000000 / 1385009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (325706637 / 1000000000) (162853319 / 500000000) (Real.log (1385009 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1385009 / 1000000) = -Real.log (1000000 / 1385009) := by
    rw [show ((1385009 / 1000000) : ℝ) = ((1000000 / 1385009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (97229529 / 200000000) ≤ -Real.log (614991 / 1000000) ∧
    -Real.log (614991 / 1000000) ≤ (243073823 / 500000000) := by
  have h := checkLog_sound (w := (385009 / 1614991)) (n := 12)
    (lo := (97229529 / 200000000)) (hi := (243073823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 614991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 614991) = 1/(614991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-243073823 / 500000000) (-97229529 / 200000000) (Real.log (614991 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (32633243 / 100000000) ≤ -Real.log (250000 / 346469) ∧
    -Real.log (250000 / 346469) ≤ (326332431 / 1000000000) := by
  have h := checkLog_sound (w := (96469 / 596469)) (n := 12)
    (lo := (32633243 / 100000000)) (hi := (326332431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346469 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346469 / 250000) = 1/(250000 / 346469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (32633243 / 100000000) (326332431 / 1000000000) (Real.log (346469 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (346469 / 250000) = -Real.log (250000 / 346469) := by
    rw [show ((346469 / 250000) : ℝ) = ((250000 / 346469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (30472401 / 62500000) ≤ -Real.log (153531 / 250000) ∧
    -Real.log (153531 / 250000) ≤ (487558417 / 1000000000) := by
  have h := checkLog_sound (w := (96469 / 403531)) (n := 12)
    (lo := (30472401 / 62500000)) (hi := (487558417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 153531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 153531) = 1/(153531 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-487558417 / 1000000000) (-30472401 / 62500000) (Real.log (153531 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (62471491 / 250000000) ≤ -Real.log (1000000 / 1283879) ∧
    -Real.log (1000000 / 1283879) ≤ (49977193 / 200000000) := by
  have h := checkLog_sound (w := (283879 / 2283879)) (n := 12)
    (lo := (62471491 / 250000000)) (hi := (49977193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283879 / 1000000) = 1/(1000000 / 1283879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (62471491 / 250000000) (49977193 / 200000000) (Real.log (1283879 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1283879 / 1000000) = -Real.log (1000000 / 1283879) := by
    rw [show ((1283879 / 1000000) : ℝ) = ((1000000 / 1283879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (333906131 / 1000000000) ≤ -Real.log (716121 / 1000000) ∧
    -Real.log (716121 / 1000000) ≤ (83476533 / 250000000) := by
  have h := checkLog_sound (w := (283879 / 1716121)) (n := 12)
    (lo := (333906131 / 1000000000)) (hi := (83476533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 716121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 716121) = 1/(716121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-83476533 / 250000000) (-333906131 / 1000000000) (Real.log (716121 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (250426367 / 1000000000) ≤ -Real.log (1000000 / 1284573) ∧
    -Real.log (1000000 / 1284573) ≤ (489114 / 1953125) := by
  have h := checkLog_sound (w := (284573 / 2284573)) (n := 12)
    (lo := (250426367 / 1000000000)) (hi := (489114 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1284573 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1284573 / 1000000) = 1/(1000000 / 1284573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (250426367 / 1000000000) (489114 / 1953125) (Real.log (1284573 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1284573 / 1000000) = -Real.log (1000000 / 1284573) := by
    rw [show ((1284573 / 1000000) : ℝ) = ((1000000 / 1284573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (334875711 / 1000000000) ≤ -Real.log (715427 / 1000000) ∧
    -Real.log (715427 / 1000000) ≤ (5232433 / 15625000) := by
  have h := checkLog_sound (w := (284573 / 1715427)) (n := 12)
    (lo := (334875711 / 1000000000)) (hi := (5232433 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 715427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 715427) = 1/(715427 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-5232433 / 15625000) (-334875711 / 1000000000) (Real.log (715427 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (405927141 / 500000000) ≤ -Real.log (50000000000 / 112604005587) ∧
    -Real.log (50000000000 / 112604005587) ≤ (202963571 / 250000000) := by
  have h := checkLog_sound (w := (12604005587 / 212604005587)) (n := 12)
    (lo := (59353551 / 500000000)) (hi := (118707103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112604005587 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(112604005587 / 100000000000) = 1/(50000000000 / 112604005587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (405927141 / 500000000) (202963571 / 250000000) (Real.log (112604005587 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (112604005587 / 50000000000) = -Real.log (50000000000 / 112604005587) := by
    rw [show ((112604005587 / 50000000000) : ℝ) = ((50000000000 / 112604005587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (406945423 / 500000000) ≤ -Real.log (50000000000 / 112833564557) ∧
    -Real.log (50000000000 / 112833564557) ≤ (25434089 / 31250000) := by
  have h := checkLog_sound (w := (12833564557 / 212833564557)) (n := 12)
    (lo := (60371833 / 500000000)) (hi := (120743667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112833564557 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(112833564557 / 100000000000) = 1/(50000000000 / 112833564557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (406945423 / 500000000) (25434089 / 31250000) (Real.log (112833564557 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (112833564557 / 50000000000) = -Real.log (50000000000 / 112833564557) := by
    rw [show ((112833564557 / 50000000000) : ℝ) = ((50000000000 / 112833564557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (116758419 / 200000000) ≤ -Real.log (100000000000 / 179282411771) ∧
    -Real.log (100000000000 / 179282411771) ≤ (18243503 / 31250000) := by
  have h := checkLog_sound (w := (79282411771 / 279282411771)) (n := 12)
    (lo := (116758419 / 200000000)) (hi := (18243503 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179282411771 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179282411771 / 100000000000) = 1/(100000000000 / 179282411771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (116758419 / 200000000) (18243503 / 31250000) (Real.log (179282411771 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (179282411771 / 100000000000) = -Real.log (100000000000 / 179282411771) := by
    rw [show ((179282411771 / 100000000000) : ℝ) = ((100000000000 / 179282411771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (585302079 / 1000000000) ≤ -Real.log (10000000000 / 17955332969) ∧
    -Real.log (10000000000 / 17955332969) ≤ (1829069 / 3125000) := by
  have h := checkLog_sound (w := (7955332969 / 27955332969)) (n := 12)
    (lo := (585302079 / 1000000000)) (hi := (1829069 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17955332969 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17955332969 / 10000000000) = 1/(10000000000 / 17955332969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (585302079 / 1000000000) (1829069 / 3125000) (Real.log (17955332969 / 10000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17955332969 / 10000000000) = -Real.log (10000000000 / 17955332969) := by
    rw [show ((17955332969 / 10000000000) : ℝ) = ((10000000000 / 17955332969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0260

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0261Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0261
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

theorem reflection_log_1_neg : (237878211 / 1000000000) ≤ -Real.log (1024 / 1299) ∧
    -Real.log (1024 / 1299) ≤ (59469553 / 250000000) := by
  have h := checkLog_sound (w := (275 / 2323)) (n := 12)
    (lo := (237878211 / 1000000000)) (hi := (59469553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299 / 1024) = 1/(1024 / 1299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (237878211 / 1000000000) (59469553 / 250000000) (Real.log (1299 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1299 / 1024) = -Real.log (1024 / 1299) := by
    rw [show ((1299 / 1024) : ℝ) = ((1024 / 1299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (156366411 / 500000000) ≤ -Real.log (749 / 1024) ∧
    -Real.log (749 / 1024) ≤ (312732823 / 1000000000) := by
  have h := checkLog_sound (w := (275 / 1773)) (n := 12)
    (lo := (156366411 / 500000000)) (hi := (312732823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 749) = 1/(749 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-312732823 / 1000000000) (-156366411 / 500000000) (Real.log (749 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (23741621 / 100000000) ≤ -Real.log (1280 / 1623) ∧
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


theorem reflection_log_3 : Bounds (23741621 / 100000000) (237416211 / 1000000000) (Real.log (1623 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1623 / 1280) = -Real.log (1280 / 1623) := by
    rw [show ((1623 / 1280) : ℝ) = ((1280 / 1623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (155966037 / 500000000) ≤ -Real.log (937 / 1280) ∧
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


theorem reflection_log_4 : Bounds (-12477283 / 40000000) (-155966037 / 500000000) (Real.log (937 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (429903623 / 1000000000) ≤ -Real.log (512 / 787) ∧
    -Real.log (512 / 787) ≤ (53737953 / 125000000) := by
  have h := checkLog_sound (w := (275 / 1299)) (n := 12)
    (lo := (429903623 / 1000000000)) (hi := (53737953 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787 / 512) = 1/(512 / 787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (429903623 / 1000000000) (53737953 / 125000000) (Real.log (787 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (787 / 512) = -Real.log (512 / 787) := by
    rw [show ((787 / 512) : ℝ) = ((512 / 787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (770264483 / 1000000000) ≤ -Real.log (237 / 512) ∧
    -Real.log (237 / 512) ≤ (154052897 / 200000000) := by
  have h := checkLog_sound (w := (19 / 493)) (n := 12)
    (lo := (77117303 / 1000000000)) (hi := (9639663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 237) = 1/(237 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-154052897 / 200000000) (-770264483 / 1000000000) (Real.log (237 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (429140943 / 1000000000) ≤ -Real.log (640 / 983) ∧
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


theorem reflection_log_7 : Bounds (429140943 / 1000000000) (26821309 / 62500000) (Real.log (983 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (983 / 640) = -Real.log (640 / 983) := by
    rw [show ((983 / 640) : ℝ) = ((640 / 983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (191934009 / 250000000) ≤ -Real.log (297 / 640) ∧
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


theorem reflection_log_8 : Bounds (-383868019 / 500000000) (-191934009 / 250000000) (Real.log (297 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (13003247 / 40000000) ≤ -Real.log (1000000 / 1384143) ∧
    -Real.log (1000000 / 1384143) ≤ (40635147 / 125000000) := by
  have h := checkLog_sound (w := (384143 / 2384143)) (n := 12)
    (lo := (13003247 / 40000000)) (hi := (40635147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1384143 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1384143 / 1000000) = 1/(1000000 / 1384143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (13003247 / 40000000) (40635147 / 125000000) (Real.log (1384143 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1384143 / 1000000) = -Real.log (1000000 / 1384143) := by
    rw [show ((1384143 / 1000000) : ℝ) = ((1000000 / 1384143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (96948097 / 200000000) ≤ -Real.log (615857 / 1000000) ∧
    -Real.log (615857 / 1000000) ≤ (242370243 / 500000000) := by
  have h := checkLog_sound (w := (384143 / 1615857)) (n := 12)
    (lo := (96948097 / 200000000)) (hi := (242370243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 615857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 615857) = 1/(615857 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-242370243 / 500000000) (-96948097 / 200000000) (Real.log (615857 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (325707359 / 1000000000) ≤ -Real.log (100000 / 138501) ∧
    -Real.log (100000 / 138501) ≤ (2035671 / 6250000) := by
  have h := checkLog_sound (w := (38501 / 238501)) (n := 12)
    (lo := (325707359 / 1000000000)) (hi := (2035671 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138501 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138501 / 100000) = 1/(100000 / 138501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (325707359 / 1000000000) (2035671 / 6250000) (Real.log (138501 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (138501 / 100000) = -Real.log (100000 / 138501) := by
    rw [show ((138501 / 100000) : ℝ) = ((100000 / 138501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (486149271 / 1000000000) ≤ -Real.log (61499 / 100000) ∧
    -Real.log (61499 / 100000) ≤ (60768659 / 125000000) := by
  have h := checkLog_sound (w := (38501 / 161499)) (n := 12)
    (lo := (486149271 / 1000000000)) (hi := (60768659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 61499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 61499) = 1/(61499 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-60768659 / 125000000) (-486149271 / 1000000000) (Real.log (61499 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (249346047 / 1000000000) ≤ -Real.log (500000 / 641593) ∧
    -Real.log (500000 / 641593) ≤ (487004 / 1953125) := by
  have h := checkLog_sound (w := (141593 / 1141593)) (n := 12)
    (lo := (249346047 / 1000000000)) (hi := (487004 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641593 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641593 / 500000) = 1/(500000 / 641593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (249346047 / 1000000000) (487004 / 1953125) (Real.log (641593 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (641593 / 500000) = -Real.log (500000 / 641593) := by
    rw [show ((641593 / 500000) : ℝ) = ((500000 / 641593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (166469443 / 500000000) ≤ -Real.log (358407 / 500000) ∧
    -Real.log (358407 / 500000) ≤ (332938887 / 1000000000) := by
  have h := checkLog_sound (w := (141593 / 858407)) (n := 12)
    (lo := (166469443 / 500000000)) (hi := (332938887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 358407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 358407) = 1/(358407 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-332938887 / 1000000000) (-166469443 / 500000000) (Real.log (358407 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (124943371 / 500000000) ≤ -Real.log (25000 / 32097) ∧
    -Real.log (25000 / 32097) ≤ (249886743 / 1000000000) := by
  have h := checkLog_sound (w := (7097 / 57097)) (n := 12)
    (lo := (124943371 / 500000000)) (hi := (249886743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32097 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32097 / 25000) = 1/(25000 / 32097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (124943371 / 500000000) (249886743 / 1000000000) (Real.log (32097 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (32097 / 25000) = -Real.log (25000 / 32097) := by
    rw [show ((32097 / 25000) : ℝ) = ((25000 / 32097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (41738441 / 125000000) ≤ -Real.log (17903 / 25000) ∧
    -Real.log (17903 / 25000) ≤ (333907529 / 1000000000) := by
  have h := checkLog_sound (w := (7097 / 42903)) (n := 12)
    (lo := (41738441 / 125000000)) (hi := (333907529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 17903) = 1/(17903 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-333907529 / 1000000000) (-41738441 / 125000000) (Real.log (17903 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (40491083 / 50000000) ≤ -Real.log (62500000000 / 140469195771) ∧
    -Real.log (62500000000 / 140469195771) ≤ (404910831 / 500000000) := by
  have h := checkLog_sound (w := (15469195771 / 265469195771)) (n := 12)
    (lo := (1458431 / 12500000)) (hi := (116674481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140469195771 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(140469195771 / 125000000000) = 1/(62500000000 / 140469195771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (40491083 / 50000000) (404910831 / 500000000) (Real.log (140469195771 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (140469195771 / 62500000000) = -Real.log (62500000000 / 140469195771) := by
    rw [show ((140469195771 / 62500000000) : ℝ) = ((62500000000 / 140469195771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (81185663 / 100000000) ≤ -Real.log (250000000000 / 563021349941) ∧
    -Real.log (250000000000 / 563021349941) ≤ (101482079 / 125000000) := by
  have h := checkLog_sound (w := (63021349941 / 1063021349941)) (n := 12)
    (lo := (2374189 / 20000000)) (hi := (118709451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563021349941 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(563021349941 / 500000000000) = 1/(250000000000 / 563021349941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (81185663 / 100000000) (101482079 / 125000000) (Real.log (563021349941 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (563021349941 / 250000000000) = -Real.log (250000000000 / 563021349941) := by
    rw [show ((563021349941 / 250000000000) : ℝ) = ((250000000000 / 563021349941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (291142467 / 500000000) ≤ -Real.log (62500000000 / 111882754801) ∧
    -Real.log (62500000000 / 111882754801) ≤ (116456987 / 200000000) := by
  have h := checkLog_sound (w := (49382754801 / 174382754801)) (n := 12)
    (lo := (291142467 / 500000000)) (hi := (116456987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111882754801 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111882754801 / 62500000000) = 1/(62500000000 / 111882754801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (291142467 / 500000000) (116456987 / 200000000) (Real.log (111882754801 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (111882754801 / 62500000000) = -Real.log (62500000000 / 111882754801) := by
    rw [show ((111882754801 / 62500000000) : ℝ) = ((62500000000 / 111882754801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (583794271 / 1000000000) ≤ -Real.log (250000000000 / 448207004413) ∧
    -Real.log (250000000000 / 448207004413) ≤ (18243571 / 31250000) := by
  have h := checkLog_sound (w := (198207004413 / 698207004413)) (n := 12)
    (lo := (583794271 / 1000000000)) (hi := (18243571 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((448207004413 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(448207004413 / 250000000000) = 1/(250000000000 / 448207004413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (583794271 / 1000000000) (18243571 / 31250000) (Real.log (448207004413 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (448207004413 / 250000000000) = -Real.log (250000000000 / 448207004413) := by
    rw [show ((448207004413 / 250000000000) : ℝ) = ((250000000000 / 448207004413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0261

end


