-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0435Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0435Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:34:07.186041+00:00
-- url     : https://prove2.me/theorems/abb5dc55-dfa6-4b58-a146-a30295344b01
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0435Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0436Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0435Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0436Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0437Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0438Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0439Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0440Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0435Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0436Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0437Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0438Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0439Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0440Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0435Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0436Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0437Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0438Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0439Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0440Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0435Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0436Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0437Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0438Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0439Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0440Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0435Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0435
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

theorem reflection_log_1_neg : (191797997 / 1000000000) ≤ -Real.log (2048 / 2481) ∧
    -Real.log (2048 / 2481) ≤ (95898999 / 500000000) := by
  have h := checkLog_sound (w := (433 / 4529)) (n := 12)
    (lo := (191797997 / 1000000000)) (hi := (95898999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2481 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2481 / 2048) = 1/(2048 / 2481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (191797997 / 1000000000) (95898999 / 500000000) (Real.log (2481 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2481 / 2048) = -Real.log (2048 / 2481) := by
    rw [show ((2481 / 2048) : ℝ) = ((2048 / 2481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (190023 / 800000) ≤ -Real.log (1615 / 2048) ∧
    -Real.log (1615 / 2048) ≤ (237528751 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 3663)) (n := 12)
    (lo := (190023 / 800000)) (hi := (237528751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1615) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1615) = 1/(1615 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-237528751 / 1000000000) (-190023 / 800000) (Real.log (1615 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (19155613 / 100000000) ≤ -Real.log (5120 / 6201) ∧
    -Real.log (5120 / 6201) ≤ (191556131 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 11321)) (n := 12)
    (lo := (19155613 / 100000000)) (hi := (191556131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6201 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6201 / 5120) = 1/(5120 / 6201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (19155613 / 100000000) (191556131 / 1000000000) (Real.log (6201 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6201 / 5120) = -Real.log (5120 / 6201) := by
    rw [show ((6201 / 5120) : ℝ) = ((5120 / 6201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (118578651 / 500000000) ≤ -Real.log (4039 / 5120) ∧
    -Real.log (4039 / 5120) ≤ (237157303 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 9159)) (n := 12)
    (lo := (118578651 / 500000000)) (hi := (237157303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4039) = 1/(4039 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-237157303 / 1000000000) (-118578651 / 500000000) (Real.log (4039 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (352663 / 1000000) ≤ -Real.log (1024 / 1457) ∧
    -Real.log (1024 / 1457) ≤ (352663001 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2481)) (n := 12)
    (lo := (352663 / 1000000)) (hi := (352663001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1457 / 1024) = 1/(1024 / 1457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (352663 / 1000000) (352663001 / 1000000000) (Real.log (1457 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1457 / 1024) = -Real.log (1024 / 1457) := by
    rw [show ((1457 / 1024) : ℝ) = ((1024 / 1457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (137413947 / 250000000) ≤ -Real.log (591 / 1024) ∧
    -Real.log (591 / 1024) ≤ (549655789 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 1615)) (n := 12)
    (lo := (137413947 / 250000000)) (hi := (549655789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 591) = 1/(591 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-549655789 / 1000000000) (-137413947 / 250000000) (Real.log (591 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (35225111 / 100000000) ≤ -Real.log (2560 / 3641) ∧
    -Real.log (2560 / 3641) ≤ (352251111 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 6201)) (n := 12)
    (lo := (35225111 / 100000000)) (hi := (352251111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3641 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3641 / 2560) = 1/(2560 / 3641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (35225111 / 100000000) (352251111 / 1000000000) (Real.log (3641 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3641 / 2560) = -Real.log (2560 / 3641) := by
    rw [show ((3641 / 2560) : ℝ) = ((2560 / 3641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (274320537 / 500000000) ≤ -Real.log (1479 / 2560) ∧
    -Real.log (1479 / 2560) ≤ (21945643 / 40000000) := by
  have h := checkLog_sound (w := (1081 / 4039)) (n := 12)
    (lo := (274320537 / 500000000)) (hi := (21945643 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1479) = 1/(1479 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-21945643 / 40000000) (-274320537 / 500000000) (Real.log (1479 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131561219 / 500000000) ≤ -Real.log (500000 / 650493) ∧
    -Real.log (500000 / 650493) ≤ (263122439 / 1000000000) := by
  have h := checkLog_sound (w := (150493 / 1150493)) (n := 12)
    (lo := (131561219 / 500000000)) (hi := (263122439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650493 / 500000) = 1/(500000 / 650493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131561219 / 500000000) (263122439 / 1000000000) (Real.log (650493 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (650493 / 500000) = -Real.log (500000 / 650493) := by
    rw [show ((650493 / 500000) : ℝ) = ((500000 / 650493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89521127 / 250000000) ≤ -Real.log (349507 / 500000) ∧
    -Real.log (349507 / 500000) ≤ (358084509 / 1000000000) := by
  have h := checkLog_sound (w := (150493 / 849507)) (n := 12)
    (lo := (89521127 / 250000000)) (hi := (358084509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 349507) = 1/(349507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-358084509 / 1000000000) (-89521127 / 250000000) (Real.log (349507 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (65862457 / 250000000) ≤ -Real.log (250000 / 325353) ∧
    -Real.log (250000 / 325353) ≤ (263449829 / 1000000000) := by
  have h := checkLog_sound (w := (75353 / 575353)) (n := 12)
    (lo := (65862457 / 250000000)) (hi := (263449829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325353 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325353 / 250000) = 1/(250000 / 325353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (65862457 / 250000000) (263449829 / 1000000000) (Real.log (325353 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (325353 / 250000) = -Real.log (250000 / 325353) := by
    rw [show ((325353 / 250000) : ℝ) = ((250000 / 325353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (358694123 / 1000000000) ≤ -Real.log (174647 / 250000) ∧
    -Real.log (174647 / 250000) ≤ (89673531 / 250000000) := by
  have h := checkLog_sound (w := (75353 / 424647)) (n := 12)
    (lo := (358694123 / 1000000000)) (hi := (89673531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 174647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 174647) = 1/(174647 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89673531 / 250000000) (-358694123 / 1000000000) (Real.log (174647 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (49365137 / 250000000) ≤ -Real.log (200000 / 243661) ∧
    -Real.log (200000 / 243661) ≤ (197460549 / 1000000000) := by
  have h := checkLog_sound (w := (43661 / 443661)) (n := 12)
    (lo := (49365137 / 250000000)) (hi := (197460549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243661 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243661 / 200000) = 1/(200000 / 243661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (49365137 / 250000000) (197460549 / 1000000000) (Real.log (243661 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (243661 / 200000) = -Real.log (200000 / 243661) := by
    rw [show ((243661 / 200000) : ℝ) = ((200000 / 243661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3078633 / 12500000) ≤ -Real.log (156339 / 200000) ∧
    -Real.log (156339 / 200000) ≤ (246290641 / 1000000000) := by
  have h := checkLog_sound (w := (43661 / 356339)) (n := 12)
    (lo := (3078633 / 12500000)) (hi := (246290641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 156339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 156339) = 1/(156339 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-246290641 / 1000000000) (-3078633 / 12500000) (Real.log (156339 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (49431819 / 250000000) ≤ -Real.log (100000 / 121863) ∧
    -Real.log (100000 / 121863) ≤ (197727277 / 1000000000) := by
  have h := checkLog_sound (w := (21863 / 221863)) (n := 12)
    (lo := (49431819 / 250000000)) (hi := (197727277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121863 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121863 / 100000) = 1/(100000 / 121863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (49431819 / 250000000) (197727277 / 1000000000) (Real.log (121863 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (121863 / 100000) = -Real.log (100000 / 121863) := by
    rw [show ((121863 / 100000) : ℝ) = ((100000 / 121863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (246706489 / 1000000000) ≤ -Real.log (78137 / 100000) ∧
    -Real.log (78137 / 100000) ≤ (24670649 / 100000000) := by
  have h := checkLog_sound (w := (21863 / 178137)) (n := 12)
    (lo := (246706489 / 1000000000)) (hi := (24670649 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78137) = 1/(78137 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-24670649 / 100000000) (-246706489 / 1000000000) (Real.log (78137 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (310603473 / 500000000) ≤ -Real.log (250000000000 / 465293255929) ∧
    -Real.log (250000000000 / 465293255929) ≤ (621206947 / 1000000000) := by
  have h := checkLog_sound (w := (215293255929 / 715293255929)) (n := 12)
    (lo := (310603473 / 500000000)) (hi := (621206947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((465293255929 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(465293255929 / 250000000000) = 1/(250000000000 / 465293255929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (310603473 / 500000000) (621206947 / 1000000000) (Real.log (465293255929 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (465293255929 / 250000000000) = -Real.log (250000000000 / 465293255929) := by
    rw [show ((465293255929 / 250000000000) : ℝ) = ((250000000000 / 465293255929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (38883997 / 62500000) ≤ -Real.log (250000000000 / 465729442819) ∧
    -Real.log (250000000000 / 465729442819) ≤ (622143953 / 1000000000) := by
  have h := checkLog_sound (w := (215729442819 / 715729442819)) (n := 12)
    (lo := (38883997 / 62500000)) (hi := (622143953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((465729442819 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(465729442819 / 250000000000) = 1/(250000000000 / 465729442819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (38883997 / 62500000) (622143953 / 1000000000) (Real.log (465729442819 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (465729442819 / 250000000000) = -Real.log (250000000000 / 465729442819) := by
    rw [show ((465729442819 / 250000000000) : ℝ) = ((250000000000 / 465729442819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (110937797 / 250000000) ≤ -Real.log (125000000000 / 194817831763) ∧
    -Real.log (125000000000 / 194817831763) ≤ (443751189 / 1000000000) := by
  have h := checkLog_sound (w := (69817831763 / 319817831763)) (n := 12)
    (lo := (110937797 / 250000000)) (hi := (443751189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194817831763 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194817831763 / 125000000000) = 1/(125000000000 / 194817831763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (110937797 / 250000000) (443751189 / 1000000000) (Real.log (194817831763 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (194817831763 / 125000000000) = -Real.log (125000000000 / 194817831763) := by
    rw [show ((194817831763 / 125000000000) : ℝ) = ((125000000000 / 194817831763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (222216883 / 500000000) ≤ -Real.log (100000000000 / 155960684439) ∧
    -Real.log (100000000000 / 155960684439) ≤ (444433767 / 1000000000) := by
  have h := checkLog_sound (w := (55960684439 / 255960684439)) (n := 12)
    (lo := (222216883 / 500000000)) (hi := (444433767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155960684439 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155960684439 / 100000000000) = 1/(100000000000 / 155960684439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (222216883 / 500000000) (444433767 / 1000000000) (Real.log (155960684439 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (155960684439 / 100000000000) = -Real.log (100000000000 / 155960684439) := by
    rw [show ((155960684439 / 100000000000) : ℝ) = ((100000000000 / 155960684439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0435

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0436Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0436
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

theorem reflection_log_1_neg : (19155613 / 100000000) ≤ -Real.log (5120 / 6201) ∧
    -Real.log (5120 / 6201) ≤ (191556131 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 11321)) (n := 12)
    (lo := (19155613 / 100000000)) (hi := (191556131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6201 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6201 / 5120) = 1/(5120 / 6201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (19155613 / 100000000) (191556131 / 1000000000) (Real.log (6201 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6201 / 5120) = -Real.log (5120 / 6201) := by
    rw [show ((6201 / 5120) : ℝ) = ((5120 / 6201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (118578651 / 500000000) ≤ -Real.log (4039 / 5120) ∧
    -Real.log (4039 / 5120) ≤ (237157303 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 9159)) (n := 12)
    (lo := (118578651 / 500000000)) (hi := (237157303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4039) = 1/(4039 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-237157303 / 1000000000) (-118578651 / 500000000) (Real.log (4039 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (47828551 / 250000000) ≤ -Real.log (10240 / 12399) ∧
    -Real.log (10240 / 12399) ≤ (38262841 / 200000000) := by
  have h := checkLog_sound (w := (2159 / 22639)) (n := 12)
    (lo := (47828551 / 250000000)) (hi := (38262841 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12399 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12399 / 10240) = 1/(10240 / 12399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (47828551 / 250000000) (38262841 / 200000000) (Real.log (12399 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12399 / 10240) = -Real.log (10240 / 12399) := by
    rw [show ((12399 / 10240) : ℝ) = ((10240 / 12399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (29598249 / 125000000) ≤ -Real.log (8081 / 10240) ∧
    -Real.log (8081 / 10240) ≤ (236785993 / 1000000000) := by
  have h := checkLog_sound (w := (2159 / 18321)) (n := 12)
    (lo := (29598249 / 125000000)) (hi := (236785993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8081) = 1/(8081 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-236785993 / 1000000000) (-29598249 / 125000000) (Real.log (8081 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (35225111 / 100000000) ≤ -Real.log (2560 / 3641) ∧
    -Real.log (2560 / 3641) ≤ (352251111 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 6201)) (n := 12)
    (lo := (35225111 / 100000000)) (hi := (352251111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3641 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3641 / 2560) = 1/(2560 / 3641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (35225111 / 100000000) (352251111 / 1000000000) (Real.log (3641 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3641 / 2560) = -Real.log (2560 / 3641) := by
    rw [show ((3641 / 2560) : ℝ) = ((2560 / 3641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (274320537 / 500000000) ≤ -Real.log (1479 / 2560) ∧
    -Real.log (1479 / 2560) ≤ (21945643 / 40000000) := by
  have h := checkLog_sound (w := (1081 / 4039)) (n := 12)
    (lo := (274320537 / 500000000)) (hi := (21945643 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1479) = 1/(1479 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-21945643 / 40000000) (-274320537 / 500000000) (Real.log (1479 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (351839051 / 1000000000) ≤ -Real.log (5120 / 7279) ∧
    -Real.log (5120 / 7279) ≤ (87959763 / 250000000) := by
  have h := checkLog_sound (w := (2159 / 12399)) (n := 12)
    (lo := (351839051 / 1000000000)) (hi := (87959763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7279 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7279 / 5120) = 1/(5120 / 7279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (351839051 / 1000000000) (87959763 / 250000000) (Real.log (7279 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7279 / 5120) = -Real.log (5120 / 7279) := by
    rw [show ((7279 / 5120) : ℝ) = ((5120 / 7279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (547627389 / 1000000000) ≤ -Real.log (2961 / 5120) ∧
    -Real.log (2961 / 5120) ≤ (54762739 / 100000000) := by
  have h := checkLog_sound (w := (2159 / 8081)) (n := 12)
    (lo := (547627389 / 1000000000)) (hi := (54762739 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2961) = 1/(2961 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-54762739 / 100000000) (-547627389 / 1000000000) (Real.log (2961 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (262795709 / 1000000000) ≤ -Real.log (1000000 / 1300561) ∧
    -Real.log (1000000 / 1300561) ≤ (26279571 / 100000000) := by
  have h := checkLog_sound (w := (300561 / 2300561)) (n := 12)
    (lo := (262795709 / 1000000000)) (hi := (26279571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1300561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1300561 / 1000000) = 1/(1000000 / 1300561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (262795709 / 1000000000) (26279571 / 100000000) (Real.log (1300561 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1300561 / 1000000) = -Real.log (1000000 / 1300561) := by
    rw [show ((1300561 / 1000000) : ℝ) = ((1000000 / 1300561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (357476693 / 1000000000) ≤ -Real.log (699439 / 1000000) ∧
    -Real.log (699439 / 1000000) ≤ (178738347 / 500000000) := by
  have h := checkLog_sound (w := (300561 / 1699439)) (n := 12)
    (lo := (357476693 / 1000000000)) (hi := (178738347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 699439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 699439) = 1/(699439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-178738347 / 500000000) (-357476693 / 1000000000) (Real.log (699439 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (263123207 / 1000000000) ≤ -Real.log (1000000 / 1300987) ∧
    -Real.log (1000000 / 1300987) ≤ (32890401 / 125000000) := by
  have h := checkLog_sound (w := (300987 / 2300987)) (n := 12)
    (lo := (263123207 / 1000000000)) (hi := (32890401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1300987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1300987 / 1000000) = 1/(1000000 / 1300987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (263123207 / 1000000000) (32890401 / 125000000) (Real.log (1300987 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1300987 / 1000000) = -Real.log (1000000 / 1300987) := by
    rw [show ((1300987 / 1000000) : ℝ) = ((1000000 / 1300987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (179042969 / 500000000) ≤ -Real.log (699013 / 1000000) ∧
    -Real.log (699013 / 1000000) ≤ (358085939 / 1000000000) := by
  have h := checkLog_sound (w := (300987 / 1699013)) (n := 12)
    (lo := (179042969 / 500000000)) (hi := (358085939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 699013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 699013) = 1/(699013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-358085939 / 1000000000) (-179042969 / 500000000) (Real.log (699013 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (197194569 / 1000000000) ≤ -Real.log (1000000 / 1217981) ∧
    -Real.log (1000000 / 1217981) ≤ (19719457 / 100000000) := by
  have h := checkLog_sound (w := (217981 / 2217981)) (n := 12)
    (lo := (197194569 / 1000000000)) (hi := (19719457 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217981 / 1000000) = 1/(1000000 / 1217981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (197194569 / 1000000000) (19719457 / 100000000) (Real.log (1217981 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1217981 / 1000000) = -Real.log (1000000 / 1217981) := by
    rw [show ((1217981 / 1000000) : ℝ) = ((1000000 / 1217981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (122938121 / 500000000) ≤ -Real.log (782019 / 1000000) ∧
    -Real.log (782019 / 1000000) ≤ (245876243 / 1000000000) := by
  have h := checkLog_sound (w := (217981 / 1782019)) (n := 12)
    (lo := (122938121 / 500000000)) (hi := (245876243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782019) = 1/(782019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-245876243 / 1000000000) (-122938121 / 500000000) (Real.log (782019 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (197461369 / 1000000000) ≤ -Real.log (500000 / 609153) ∧
    -Real.log (500000 / 609153) ≤ (19746137 / 100000000) := by
  have h := checkLog_sound (w := (109153 / 1109153)) (n := 12)
    (lo := (197461369 / 1000000000)) (hi := (19746137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609153 / 500000) = 1/(500000 / 609153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (197461369 / 1000000000) (19746137 / 100000000) (Real.log (609153 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (609153 / 500000) = -Real.log (500000 / 609153) := by
    rw [show ((609153 / 500000) : ℝ) = ((500000 / 609153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (246291919 / 1000000000) ≤ -Real.log (390847 / 500000) ∧
    -Real.log (390847 / 500000) ≤ (3078649 / 12500000) := by
  have h := checkLog_sound (w := (109153 / 890847)) (n := 12)
    (lo := (246291919 / 1000000000)) (hi := (3078649 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 390847) = 1/(390847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3078649 / 12500000) (-246291919 / 1000000000) (Real.log (390847 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (620272403 / 1000000000) ≤ -Real.log (25000000000 / 46485862241) ∧
    -Real.log (25000000000 / 46485862241) ≤ (155068101 / 250000000) := by
  have h := checkLog_sound (w := (21485862241 / 71485862241)) (n := 12)
    (lo := (620272403 / 1000000000)) (hi := (155068101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46485862241 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46485862241 / 25000000000) = 1/(25000000000 / 46485862241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (620272403 / 1000000000) (155068101 / 250000000) (Real.log (46485862241 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (46485862241 / 25000000000) = -Real.log (25000000000 / 46485862241) := by
    rw [show ((46485862241 / 25000000000) : ℝ) = ((25000000000 / 46485862241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (310604573 / 500000000) ≤ -Real.log (500000000000 / 930588558439) ∧
    -Real.log (500000000000 / 930588558439) ≤ (621209147 / 1000000000) := by
  have h := checkLog_sound (w := (430588558439 / 1430588558439)) (n := 12)
    (lo := (310604573 / 500000000)) (hi := (621209147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((930588558439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(930588558439 / 500000000000) = 1/(500000000000 / 930588558439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (310604573 / 500000000) (621209147 / 1000000000) (Real.log (930588558439 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (930588558439 / 500000000000) = -Real.log (500000000000 / 930588558439) := by
    rw [show ((930588558439 / 500000000000) : ℝ) = ((500000000000 / 930588558439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (443070811 / 1000000000) ≤ -Real.log (250000000000 / 389370654677) ∧
    -Real.log (250000000000 / 389370654677) ≤ (110767703 / 250000000) := by
  have h := checkLog_sound (w := (139370654677 / 639370654677)) (n := 12)
    (lo := (443070811 / 1000000000)) (hi := (110767703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389370654677 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389370654677 / 250000000000) = 1/(250000000000 / 389370654677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (443070811 / 1000000000) (110767703 / 250000000) (Real.log (389370654677 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (389370654677 / 250000000000) = -Real.log (250000000000 / 389370654677) := by
    rw [show ((389370654677 / 250000000000) : ℝ) = ((250000000000 / 389370654677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (55469161 / 125000000) ≤ -Real.log (50000000000 / 77927296359) ∧
    -Real.log (50000000000 / 77927296359) ≤ (443753289 / 1000000000) := by
  have h := checkLog_sound (w := (27927296359 / 127927296359)) (n := 12)
    (lo := (55469161 / 125000000)) (hi := (443753289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77927296359 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77927296359 / 50000000000) = 1/(50000000000 / 77927296359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (55469161 / 125000000) (443753289 / 1000000000) (Real.log (77927296359 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (77927296359 / 50000000000) = -Real.log (50000000000 / 77927296359) := by
    rw [show ((77927296359 / 50000000000) : ℝ) = ((50000000000 / 77927296359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0436

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0437Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0437
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

theorem reflection_log_1_neg : (47828551 / 250000000) ≤ -Real.log (10240 / 12399) ∧
    -Real.log (10240 / 12399) ≤ (38262841 / 200000000) := by
  have h := checkLog_sound (w := (2159 / 22639)) (n := 12)
    (lo := (47828551 / 250000000)) (hi := (38262841 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12399 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12399 / 10240) = 1/(10240 / 12399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (47828551 / 250000000) (38262841 / 200000000) (Real.log (12399 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12399 / 10240) = -Real.log (10240 / 12399) := by
    rw [show ((12399 / 10240) : ℝ) = ((10240 / 12399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (29598249 / 125000000) ≤ -Real.log (8081 / 10240) ∧
    -Real.log (8081 / 10240) ≤ (236785993 / 1000000000) := by
  have h := checkLog_sound (w := (2159 / 18321)) (n := 12)
    (lo := (29598249 / 125000000)) (hi := (236785993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8081) = 1/(8081 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-236785993 / 1000000000) (-29598249 / 125000000) (Real.log (8081 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (9553611 / 50000000) ≤ -Real.log (2560 / 3099) ∧
    -Real.log (2560 / 3099) ≤ (191072221 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 5659)) (n := 12)
    (lo := (9553611 / 50000000)) (hi := (191072221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3099 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3099 / 2560) = 1/(2560 / 3099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (9553611 / 50000000) (191072221 / 1000000000) (Real.log (3099 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3099 / 2560) = -Real.log (2560 / 3099) := by
    rw [show ((3099 / 2560) : ℝ) = ((2560 / 3099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (11820741 / 50000000) ≤ -Real.log (2021 / 2560) ∧
    -Real.log (2021 / 2560) ≤ (236414821 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 4581)) (n := 12)
    (lo := (11820741 / 50000000)) (hi := (236414821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2021) = 1/(2021 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-236414821 / 1000000000) (-11820741 / 50000000) (Real.log (2021 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (351839051 / 1000000000) ≤ -Real.log (5120 / 7279) ∧
    -Real.log (5120 / 7279) ≤ (87959763 / 250000000) := by
  have h := checkLog_sound (w := (2159 / 12399)) (n := 12)
    (lo := (351839051 / 1000000000)) (hi := (87959763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7279 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7279 / 5120) = 1/(5120 / 7279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (351839051 / 1000000000) (87959763 / 250000000) (Real.log (7279 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7279 / 5120) = -Real.log (5120 / 7279) := by
    rw [show ((7279 / 5120) : ℝ) = ((5120 / 7279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (547627389 / 1000000000) ≤ -Real.log (2961 / 5120) ∧
    -Real.log (2961 / 5120) ≤ (54762739 / 100000000) := by
  have h := checkLog_sound (w := (2159 / 8081)) (n := 12)
    (lo := (547627389 / 1000000000)) (hi := (54762739 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2961) = 1/(2961 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-54762739 / 100000000) (-547627389 / 1000000000) (Real.log (2961 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (351426821 / 1000000000) ≤ -Real.log (1280 / 1819) ∧
    -Real.log (1280 / 1819) ≤ (175713411 / 500000000) := by
  have h := checkLog_sound (w := (539 / 3099)) (n := 12)
    (lo := (351426821 / 1000000000)) (hi := (175713411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1819 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1819 / 1280) = 1/(1280 / 1819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (351426821 / 1000000000) (175713411 / 500000000) (Real.log (1819 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1819 / 1280) = -Real.log (1280 / 1819) := by
    rw [show ((1819 / 1280) : ℝ) = ((1280 / 1819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (546614731 / 1000000000) ≤ -Real.log (741 / 1280) ∧
    -Real.log (741 / 1280) ≤ (136653683 / 250000000) := by
  have h := checkLog_sound (w := (539 / 2021)) (n := 12)
    (lo := (546614731 / 1000000000)) (hi := (136653683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 741) = 1/(741 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-136653683 / 250000000) (-546614731 / 1000000000) (Real.log (741 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131234437 / 500000000) ≤ -Real.log (125000 / 162517) ∧
    -Real.log (125000 / 162517) ≤ (2099751 / 8000000) := by
  have h := checkLog_sound (w := (37517 / 287517)) (n := 12)
    (lo := (131234437 / 500000000)) (hi := (2099751 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162517 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162517 / 125000) = 1/(125000 / 162517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131234437 / 500000000) (2099751 / 8000000) (Real.log (162517 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (162517 / 125000) = -Real.log (125000 / 162517) := by
    rw [show ((162517 / 125000) : ℝ) = ((125000 / 162517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2788041 / 7812500) ≤ -Real.log (87483 / 125000) ∧
    -Real.log (87483 / 125000) ≤ (356869249 / 1000000000) := by
  have h := checkLog_sound (w := (37517 / 212483)) (n := 12)
    (lo := (2788041 / 7812500)) (hi := (356869249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 87483) = 1/(87483 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-356869249 / 1000000000) (-2788041 / 7812500) (Real.log (87483 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (131398239 / 500000000) ≤ -Real.log (500000 / 650281) ∧
    -Real.log (500000 / 650281) ≤ (262796479 / 1000000000) := by
  have h := checkLog_sound (w := (150281 / 1150281)) (n := 12)
    (lo := (131398239 / 500000000)) (hi := (262796479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650281 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650281 / 500000) = 1/(500000 / 650281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (131398239 / 500000000) (262796479 / 1000000000) (Real.log (650281 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (650281 / 500000) = -Real.log (500000 / 650281) := by
    rw [show ((650281 / 500000) : ℝ) = ((500000 / 650281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (357478123 / 1000000000) ≤ -Real.log (349719 / 500000) ∧
    -Real.log (349719 / 500000) ≤ (89369531 / 250000000) := by
  have h := checkLog_sound (w := (150281 / 849719)) (n := 12)
    (lo := (357478123 / 1000000000)) (hi := (89369531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 349719) = 1/(349719 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89369531 / 250000000) (-357478123 / 1000000000) (Real.log (349719 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4923213 / 25000000) ≤ -Real.log (1000000 / 1217657) ∧
    -Real.log (1000000 / 1217657) ≤ (196928521 / 1000000000) := by
  have h := checkLog_sound (w := (217657 / 2217657)) (n := 12)
    (lo := (4923213 / 25000000)) (hi := (196928521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217657 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217657 / 1000000) = 1/(1000000 / 1217657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4923213 / 25000000) (196928521 / 1000000000) (Real.log (1217657 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1217657 / 1000000) = -Real.log (1000000 / 1217657) := by
    rw [show ((1217657 / 1000000) : ℝ) = ((1000000 / 1217657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49092403 / 200000000) ≤ -Real.log (782343 / 1000000) ∧
    -Real.log (782343 / 1000000) ≤ (479418 / 1953125) := by
  have h := checkLog_sound (w := (217657 / 1782343)) (n := 12)
    (lo := (49092403 / 200000000)) (hi := (479418 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782343) = 1/(782343 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-479418 / 1953125) (-49092403 / 200000000) (Real.log (782343 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19719539 / 100000000) ≤ -Real.log (500000 / 608991) ∧
    -Real.log (500000 / 608991) ≤ (197195391 / 1000000000) := by
  have h := checkLog_sound (w := (108991 / 1108991)) (n := 12)
    (lo := (19719539 / 100000000)) (hi := (197195391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608991 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608991 / 500000) = 1/(500000 / 608991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19719539 / 100000000) (197195391 / 1000000000) (Real.log (608991 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (608991 / 500000) = -Real.log (500000 / 608991) := by
    rw [show ((608991 / 500000) : ℝ) = ((500000 / 608991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3073469 / 12500000) ≤ -Real.log (391009 / 500000) ∧
    -Real.log (391009 / 500000) ≤ (245877521 / 1000000000) := by
  have h := checkLog_sound (w := (108991 / 891009)) (n := 12)
    (lo := (3073469 / 12500000)) (hi := (245877521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391009) = 1/(391009 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-245877521 / 1000000000) (-3073469 / 12500000) (Real.log (391009 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (309669061 / 500000000) ≤ -Real.log (250000000000 / 464424516763) ∧
    -Real.log (250000000000 / 464424516763) ≤ (619338123 / 1000000000) := by
  have h := checkLog_sound (w := (214424516763 / 714424516763)) (n := 12)
    (lo := (309669061 / 500000000)) (hi := (619338123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((464424516763 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(464424516763 / 250000000000) = 1/(250000000000 / 464424516763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (309669061 / 500000000) (619338123 / 1000000000) (Real.log (464424516763 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (464424516763 / 250000000000) = -Real.log (250000000000 / 464424516763) := by
    rw [show ((464424516763 / 250000000000) : ℝ) = ((250000000000 / 464424516763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (310137301 / 500000000) ≤ -Real.log (100000000000 / 185943857783) ∧
    -Real.log (100000000000 / 185943857783) ≤ (620274603 / 1000000000) := by
  have h := checkLog_sound (w := (85943857783 / 285943857783)) (n := 12)
    (lo := (310137301 / 500000000)) (hi := (620274603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185943857783 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185943857783 / 100000000000) = 1/(100000000000 / 185943857783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (310137301 / 500000000) (620274603 / 1000000000) (Real.log (185943857783 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (185943857783 / 100000000000) = -Real.log (100000000000 / 185943857783) := by
    rw [show ((185943857783 / 100000000000) : ℝ) = ((100000000000 / 185943857783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (55298817 / 125000000) ≤ -Real.log (25000000000 / 38910586533) ∧
    -Real.log (25000000000 / 38910586533) ≤ (442390537 / 1000000000) := by
  have h := checkLog_sound (w := (13910586533 / 63910586533)) (n := 12)
    (lo := (55298817 / 125000000)) (hi := (442390537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38910586533 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38910586533 / 25000000000) = 1/(25000000000 / 38910586533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (55298817 / 125000000) (442390537 / 1000000000) (Real.log (38910586533 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (38910586533 / 25000000000) = -Real.log (25000000000 / 38910586533) := by
    rw [show ((38910586533 / 25000000000) : ℝ) = ((25000000000 / 38910586533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (443072911 / 1000000000) ≤ -Real.log (62500000000 / 97342868067) ∧
    -Real.log (62500000000 / 97342868067) ≤ (27692057 / 62500000) := by
  have h := checkLog_sound (w := (34842868067 / 159842868067)) (n := 12)
    (lo := (443072911 / 1000000000)) (hi := (27692057 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97342868067 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97342868067 / 62500000000) = 1/(62500000000 / 97342868067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (443072911 / 1000000000) (27692057 / 62500000) (Real.log (97342868067 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (97342868067 / 62500000000) = -Real.log (62500000000 / 97342868067) := by
    rw [show ((97342868067 / 62500000000) : ℝ) = ((62500000000 / 97342868067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0437

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0438Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0438
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

theorem reflection_log_1_neg : (9553611 / 50000000) ≤ -Real.log (2560 / 3099) ∧
    -Real.log (2560 / 3099) ≤ (191072221 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 5659)) (n := 12)
    (lo := (9553611 / 50000000)) (hi := (191072221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3099 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3099 / 2560) = 1/(2560 / 3099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (9553611 / 50000000) (191072221 / 1000000000) (Real.log (3099 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3099 / 2560) = -Real.log (2560 / 3099) := by
    rw [show ((3099 / 2560) : ℝ) = ((2560 / 3099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (11820741 / 50000000) ≤ -Real.log (2021 / 2560) ∧
    -Real.log (2021 / 2560) ≤ (236414821 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 4581)) (n := 12)
    (lo := (11820741 / 50000000)) (hi := (236414821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2021) = 1/(2021 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-236414821 / 1000000000) (-11820741 / 50000000) (Real.log (2021 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (190830177 / 1000000000) ≤ -Real.log (10240 / 12393) ∧
    -Real.log (10240 / 12393) ≤ (95415089 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 22633)) (n := 12)
    (lo := (190830177 / 1000000000)) (hi := (95415089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12393 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12393 / 10240) = 1/(10240 / 12393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (190830177 / 1000000000) (95415089 / 500000000) (Real.log (12393 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12393 / 10240) = -Real.log (10240 / 12393) := by
    rw [show ((12393 / 10240) : ℝ) = ((10240 / 12393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (47208757 / 200000000) ≤ -Real.log (8087 / 10240) ∧
    -Real.log (8087 / 10240) ≤ (118021893 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 18327)) (n := 12)
    (lo := (47208757 / 200000000)) (hi := (118021893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8087) = 1/(8087 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-118021893 / 500000000) (-47208757 / 200000000) (Real.log (8087 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (351426821 / 1000000000) ≤ -Real.log (1280 / 1819) ∧
    -Real.log (1280 / 1819) ≤ (175713411 / 500000000) := by
  have h := checkLog_sound (w := (539 / 3099)) (n := 12)
    (lo := (351426821 / 1000000000)) (hi := (175713411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1819 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1819 / 1280) = 1/(1280 / 1819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (351426821 / 1000000000) (175713411 / 500000000) (Real.log (1819 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1819 / 1280) = -Real.log (1280 / 1819) := by
    rw [show ((1819 / 1280) : ℝ) = ((1280 / 1819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (546614731 / 1000000000) ≤ -Real.log (741 / 1280) ∧
    -Real.log (741 / 1280) ≤ (136653683 / 250000000) := by
  have h := checkLog_sound (w := (539 / 2021)) (n := 12)
    (lo := (546614731 / 1000000000)) (hi := (136653683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 741) = 1/(741 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-136653683 / 250000000) (-546614731 / 1000000000) (Real.log (741 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (175507211 / 500000000) ≤ -Real.log (5120 / 7273) ∧
    -Real.log (5120 / 7273) ≤ (351014423 / 1000000000) := by
  have h := checkLog_sound (w := (2153 / 12393)) (n := 12)
    (lo := (175507211 / 500000000)) (hi := (351014423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7273 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7273 / 5120) = 1/(5120 / 7273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (175507211 / 500000000) (351014423 / 1000000000) (Real.log (7273 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7273 / 5120) = -Real.log (5120 / 7273) := by
    rw [show ((7273 / 5120) : ℝ) = ((5120 / 7273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (545603097 / 1000000000) ≤ -Real.log (2967 / 5120) ∧
    -Real.log (2967 / 5120) ≤ (272801549 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 8087)) (n := 12)
    (lo := (545603097 / 1000000000)) (hi := (272801549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2967) = 1/(2967 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-272801549 / 500000000) (-545603097 / 1000000000) (Real.log (2967 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (262142701 / 1000000000) ≤ -Real.log (15625 / 20308) ∧
    -Real.log (15625 / 20308) ≤ (131071351 / 500000000) := by
  have h := checkLog_sound (w := (4683 / 35933)) (n := 12)
    (lo := (262142701 / 1000000000)) (hi := (131071351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20308 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20308 / 15625) = 1/(15625 / 20308) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (262142701 / 1000000000) (131071351 / 500000000) (Real.log (20308 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (20308 / 15625) = -Real.log (15625 / 20308) := by
    rw [show ((20308 / 15625) : ℝ) = ((15625 / 20308) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (356263599 / 1000000000) ≤ -Real.log (10942 / 15625) ∧
    -Real.log (10942 / 15625) ≤ (890659 / 2500000) := by
  have h := checkLog_sound (w := (4683 / 26567)) (n := 12)
    (lo := (356263599 / 1000000000)) (hi := (890659 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10942) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10942) = 1/(10942 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-890659 / 2500000) (-356263599 / 1000000000) (Real.log (10942 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (262469643 / 1000000000) ≤ -Real.log (1000000 / 1300137) ∧
    -Real.log (1000000 / 1300137) ≤ (65617411 / 250000000) := by
  have h := checkLog_sound (w := (300137 / 2300137)) (n := 12)
    (lo := (262469643 / 1000000000)) (hi := (65617411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1300137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1300137 / 1000000) = 1/(1000000 / 1300137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (262469643 / 1000000000) (65617411 / 250000000) (Real.log (1300137 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1300137 / 1000000) = -Real.log (1000000 / 1300137) := by
    rw [show ((1300137 / 1000000) : ℝ) = ((1000000 / 1300137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (356870677 / 1000000000) ≤ -Real.log (699863 / 1000000) ∧
    -Real.log (699863 / 1000000) ≤ (178435339 / 500000000) := by
  have h := checkLog_sound (w := (300137 / 1699863)) (n := 12)
    (lo := (356870677 / 1000000000)) (hi := (178435339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 699863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 699863) = 1/(699863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-178435339 / 500000000) (-356870677 / 1000000000) (Real.log (699863 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (61457 / 312500) ≤ -Real.log (1000000 / 1217333) ∧
    -Real.log (1000000 / 1217333) ≤ (196662401 / 1000000000) := by
  have h := checkLog_sound (w := (217333 / 2217333)) (n := 12)
    (lo := (61457 / 312500)) (hi := (196662401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217333 / 1000000) = 1/(1000000 / 1217333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (61457 / 312500) (196662401 / 1000000000) (Real.log (1217333 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1217333 / 1000000) = -Real.log (1000000 / 1217333) := by
    rw [show ((1217333 / 1000000) : ℝ) = ((1000000 / 1217333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (6126199 / 25000000) ≤ -Real.log (782667 / 1000000) ∧
    -Real.log (782667 / 1000000) ≤ (245047961 / 1000000000) := by
  have h := checkLog_sound (w := (217333 / 1782667)) (n := 12)
    (lo := (6126199 / 25000000)) (hi := (245047961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782667) = 1/(782667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-245047961 / 1000000000) (-6126199 / 25000000) (Real.log (782667 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (196929341 / 1000000000) ≤ -Real.log (500000 / 608829) ∧
    -Real.log (500000 / 608829) ≤ (98464671 / 500000000) := by
  have h := checkLog_sound (w := (108829 / 1108829)) (n := 12)
    (lo := (196929341 / 1000000000)) (hi := (98464671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608829 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608829 / 500000) = 1/(500000 / 608829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (196929341 / 1000000000) (98464671 / 500000000) (Real.log (608829 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (608829 / 500000) = -Real.log (500000 / 608829) := by
    rw [show ((608829 / 500000) : ℝ) = ((500000 / 608829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (245463293 / 1000000000) ≤ -Real.log (391171 / 500000) ∧
    -Real.log (391171 / 500000) ≤ (122731647 / 500000000) := by
  have h := checkLog_sound (w := (108829 / 891171)) (n := 12)
    (lo := (245463293 / 1000000000)) (hi := (122731647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391171) = 1/(391171 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-122731647 / 500000000) (-245463293 / 1000000000) (Real.log (391171 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (618406301 / 1000000000) ≤ -Real.log (500000000000 / 927983915189) ∧
    -Real.log (500000000000 / 927983915189) ≤ (309203151 / 500000000) := by
  have h := checkLog_sound (w := (427983915189 / 1427983915189)) (n := 12)
    (lo := (618406301 / 1000000000)) (hi := (309203151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927983915189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927983915189 / 500000000000) = 1/(500000000000 / 927983915189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (618406301 / 1000000000) (309203151 / 500000000) (Real.log (927983915189 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (927983915189 / 500000000000) = -Real.log (500000000000 / 927983915189) := by
    rw [show ((927983915189 / 500000000000) : ℝ) = ((500000000000 / 927983915189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3870877 / 6250000) ≤ -Real.log (500000000000 / 928851075139) ∧
    -Real.log (500000000000 / 928851075139) ≤ (619340321 / 1000000000) := by
  have h := checkLog_sound (w := (428851075139 / 1428851075139)) (n := 12)
    (lo := (3870877 / 6250000)) (hi := (619340321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((928851075139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(928851075139 / 500000000000) = 1/(500000000000 / 928851075139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3870877 / 6250000) (619340321 / 1000000000) (Real.log (928851075139 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (928851075139 / 500000000000) = -Real.log (500000000000 / 928851075139) := by
    rw [show ((928851075139 / 500000000000) : ℝ) = ((500000000000 / 928851075139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (441710361 / 1000000000) ≤ -Real.log (62500000000 / 97210323803) ∧
    -Real.log (62500000000 / 97210323803) ≤ (220855181 / 500000000) := by
  have h := checkLog_sound (w := (34710323803 / 159710323803)) (n := 12)
    (lo := (441710361 / 1000000000)) (hi := (220855181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97210323803 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97210323803 / 62500000000) = 1/(62500000000 / 97210323803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (441710361 / 1000000000) (220855181 / 500000000) (Real.log (97210323803 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (97210323803 / 62500000000) = -Real.log (62500000000 / 97210323803) := by
    rw [show ((97210323803 / 62500000000) : ℝ) = ((62500000000 / 97210323803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (88478527 / 200000000) ≤ -Real.log (62500000000 / 97276670561) ∧
    -Real.log (62500000000 / 97276670561) ≤ (110598159 / 250000000) := by
  have h := checkLog_sound (w := (34776670561 / 159776670561)) (n := 12)
    (lo := (88478527 / 200000000)) (hi := (110598159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97276670561 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97276670561 / 62500000000) = 1/(62500000000 / 97276670561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (88478527 / 200000000) (110598159 / 250000000) (Real.log (97276670561 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (97276670561 / 62500000000) = -Real.log (62500000000 / 97276670561) := by
    rw [show ((97276670561 / 62500000000) : ℝ) = ((62500000000 / 97276670561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0438

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0439Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0439
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

theorem reflection_log_1_neg : (190830177 / 1000000000) ≤ -Real.log (10240 / 12393) ∧
    -Real.log (10240 / 12393) ≤ (95415089 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 22633)) (n := 12)
    (lo := (190830177 / 1000000000)) (hi := (95415089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12393 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12393 / 10240) = 1/(10240 / 12393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (190830177 / 1000000000) (95415089 / 500000000) (Real.log (12393 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12393 / 10240) = -Real.log (10240 / 12393) := by
    rw [show ((12393 / 10240) : ℝ) = ((10240 / 12393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (47208757 / 200000000) ≤ -Real.log (8087 / 10240) ∧
    -Real.log (8087 / 10240) ≤ (118021893 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 18327)) (n := 12)
    (lo := (47208757 / 200000000)) (hi := (118021893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8087) = 1/(8087 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-118021893 / 500000000) (-47208757 / 200000000) (Real.log (8087 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (47647019 / 250000000) ≤ -Real.log (1024 / 1239) ∧
    -Real.log (1024 / 1239) ≤ (190588077 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 2263)) (n := 12)
    (lo := (47647019 / 250000000)) (hi := (190588077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239 / 1024) = 1/(1024 / 1239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (47647019 / 250000000) (190588077 / 1000000000) (Real.log (1239 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1239 / 1024) = -Real.log (1024 / 1239) := by
    rw [show ((1239 / 1024) : ℝ) = ((1024 / 1239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (29459111 / 125000000) ≤ -Real.log (809 / 1024) ∧
    -Real.log (809 / 1024) ≤ (235672889 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 1833)) (n := 12)
    (lo := (29459111 / 125000000)) (hi := (235672889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 809) = 1/(809 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-235672889 / 1000000000) (-29459111 / 125000000) (Real.log (809 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (175507211 / 500000000) ≤ -Real.log (5120 / 7273) ∧
    -Real.log (5120 / 7273) ≤ (351014423 / 1000000000) := by
  have h := checkLog_sound (w := (2153 / 12393)) (n := 12)
    (lo := (175507211 / 500000000)) (hi := (351014423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7273 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7273 / 5120) = 1/(5120 / 7273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (175507211 / 500000000) (351014423 / 1000000000) (Real.log (7273 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7273 / 5120) = -Real.log (5120 / 7273) := by
    rw [show ((7273 / 5120) : ℝ) = ((5120 / 7273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (545603097 / 1000000000) ≤ -Real.log (2967 / 5120) ∧
    -Real.log (2967 / 5120) ≤ (272801549 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 8087)) (n := 12)
    (lo := (545603097 / 1000000000)) (hi := (272801549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2967) = 1/(2967 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-272801549 / 500000000) (-545603097 / 1000000000) (Real.log (2967 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (87650463 / 250000000) ≤ -Real.log (512 / 727) ∧
    -Real.log (512 / 727) ≤ (350601853 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 1239)) (n := 12)
    (lo := (87650463 / 250000000)) (hi := (350601853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727 / 512) = 1/(512 / 727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (87650463 / 250000000) (350601853 / 1000000000) (Real.log (727 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (727 / 512) = -Real.log (512 / 727) := by
    rw [show ((727 / 512) : ℝ) = ((512 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (272296243 / 500000000) ≤ -Real.log (297 / 512) ∧
    -Real.log (297 / 512) ≤ (544592487 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 809)) (n := 12)
    (lo := (272296243 / 500000000)) (hi := (544592487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 297) = 1/(297 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-544592487 / 1000000000) (-272296243 / 500000000) (Real.log (297 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (65453913 / 250000000) ≤ -Real.log (1000000 / 1299287) ∧
    -Real.log (1000000 / 1299287) ≤ (261815653 / 1000000000) := by
  have h := checkLog_sound (w := (299287 / 2299287)) (n := 12)
    (lo := (65453913 / 250000000)) (hi := (261815653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299287 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299287 / 1000000) = 1/(1000000 / 1299287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (65453913 / 250000000) (261815653 / 1000000000) (Real.log (1299287 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1299287 / 1000000) = -Real.log (1000000 / 1299287) := by
    rw [show ((1299287 / 1000000) : ℝ) = ((1000000 / 1299287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (35565689 / 100000000) ≤ -Real.log (700713 / 1000000) ∧
    -Real.log (700713 / 1000000) ≤ (355656891 / 1000000000) := by
  have h := checkLog_sound (w := (299287 / 1700713)) (n := 12)
    (lo := (35565689 / 100000000)) (hi := (355656891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 700713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 700713) = 1/(700713 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-355656891 / 1000000000) (-35565689 / 100000000) (Real.log (700713 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (26214347 / 100000000) ≤ -Real.log (1000000 / 1299713) ∧
    -Real.log (1000000 / 1299713) ≤ (262143471 / 1000000000) := by
  have h := checkLog_sound (w := (299713 / 2299713)) (n := 12)
    (lo := (26214347 / 100000000)) (hi := (262143471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299713 / 1000000) = 1/(1000000 / 1299713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (26214347 / 100000000) (262143471 / 1000000000) (Real.log (1299713 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1299713 / 1000000) = -Real.log (1000000 / 1299713) := by
    rw [show ((1299713 / 1000000) : ℝ) = ((1000000 / 1299713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (356265027 / 1000000000) ≤ -Real.log (700287 / 1000000) ∧
    -Real.log (700287 / 1000000) ≤ (89066257 / 250000000) := by
  have h := checkLog_sound (w := (299713 / 1700287)) (n := 12)
    (lo := (356265027 / 1000000000)) (hi := (89066257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 700287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 700287) = 1/(700287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89066257 / 250000000) (-356265027 / 1000000000) (Real.log (700287 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (19639703 / 100000000) ≤ -Real.log (100000 / 121701) ∧
    -Real.log (100000 / 121701) ≤ (196397031 / 1000000000) := by
  have h := checkLog_sound (w := (21701 / 221701)) (n := 12)
    (lo := (19639703 / 100000000)) (hi := (196397031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121701 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121701 / 100000) = 1/(100000 / 121701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (19639703 / 100000000) (196397031 / 1000000000) (Real.log (121701 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (121701 / 100000) = -Real.log (100000 / 121701) := by
    rw [show ((121701 / 100000) : ℝ) = ((100000 / 121701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (122317677 / 500000000) ≤ -Real.log (78299 / 100000) ∧
    -Real.log (78299 / 100000) ≤ (48927071 / 200000000) := by
  have h := checkLog_sound (w := (21701 / 178299)) (n := 12)
    (lo := (122317677 / 500000000)) (hi := (48927071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78299) = 1/(78299 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-48927071 / 200000000) (-122317677 / 500000000) (Real.log (78299 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (196663221 / 1000000000) ≤ -Real.log (500000 / 608667) ∧
    -Real.log (500000 / 608667) ≤ (98331611 / 500000000) := by
  have h := checkLog_sound (w := (108667 / 1108667)) (n := 12)
    (lo := (196663221 / 1000000000)) (hi := (98331611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608667 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608667 / 500000) = 1/(500000 / 608667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (196663221 / 1000000000) (98331611 / 500000000) (Real.log (608667 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (608667 / 500000) = -Real.log (500000 / 608667) := by
    rw [show ((608667 / 500000) : ℝ) = ((500000 / 608667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (122524619 / 500000000) ≤ -Real.log (391333 / 500000) ∧
    -Real.log (391333 / 500000) ≤ (245049239 / 1000000000) := by
  have h := checkLog_sound (w := (108667 / 891333)) (n := 12)
    (lo := (122524619 / 500000000)) (hi := (245049239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391333) = 1/(391333 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-245049239 / 1000000000) (-122524619 / 500000000) (Real.log (391333 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (617472543 / 1000000000) ≤ -Real.log (500000000000 / 927117807147) ∧
    -Real.log (500000000000 / 927117807147) ≤ (19296017 / 31250000) := by
  have h := checkLog_sound (w := (427117807147 / 1427117807147)) (n := 12)
    (lo := (617472543 / 1000000000)) (hi := (19296017 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927117807147 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927117807147 / 500000000000) = 1/(500000000000 / 927117807147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (617472543 / 1000000000) (19296017 / 31250000) (Real.log (927117807147 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (927117807147 / 500000000000) = -Real.log (500000000000 / 927117807147) := by
    rw [show ((927117807147 / 500000000000) : ℝ) = ((500000000000 / 927117807147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (309204249 / 500000000) ≤ -Real.log (500000000000 / 927985954331) ∧
    -Real.log (500000000000 / 927985954331) ≤ (618408499 / 1000000000) := by
  have h := checkLog_sound (w := (427985954331 / 1427985954331)) (n := 12)
    (lo := (309204249 / 500000000)) (hi := (618408499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927985954331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927985954331 / 500000000000) = 1/(500000000000 / 927985954331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (309204249 / 500000000) (618408499 / 1000000000) (Real.log (927985954331 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (927985954331 / 500000000000) = -Real.log (500000000000 / 927985954331) := by
    rw [show ((927985954331 / 500000000000) : ℝ) = ((500000000000 / 927985954331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (88206477 / 200000000) ≤ -Real.log (500000000000 / 777155519227) ∧
    -Real.log (500000000000 / 777155519227) ≤ (220516193 / 500000000) := by
  have h := checkLog_sound (w := (277155519227 / 1277155519227)) (n := 12)
    (lo := (88206477 / 200000000)) (hi := (220516193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777155519227 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777155519227 / 500000000000) = 1/(500000000000 / 777155519227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (88206477 / 200000000) (220516193 / 500000000) (Real.log (777155519227 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (777155519227 / 500000000000) = -Real.log (500000000000 / 777155519227) := by
    rw [show ((777155519227 / 500000000000) : ℝ) = ((500000000000 / 777155519227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (22085623 / 50000000) ≤ -Real.log (5000000000 / 7776842229) ∧
    -Real.log (5000000000 / 7776842229) ≤ (441712461 / 1000000000) := by
  have h := checkLog_sound (w := (2776842229 / 12776842229)) (n := 12)
    (lo := (22085623 / 50000000)) (hi := (441712461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7776842229 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7776842229 / 5000000000) = 1/(5000000000 / 7776842229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (22085623 / 50000000) (441712461 / 1000000000) (Real.log (7776842229 / 5000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7776842229 / 5000000000) = -Real.log (5000000000 / 7776842229) := by
    rw [show ((7776842229 / 5000000000) : ℝ) = ((5000000000 / 7776842229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0439

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0440Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0440
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

theorem reflection_log_1_neg : (47647019 / 250000000) ≤ -Real.log (1024 / 1239) ∧
    -Real.log (1024 / 1239) ≤ (190588077 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 2263)) (n := 12)
    (lo := (47647019 / 250000000)) (hi := (190588077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239 / 1024) = 1/(1024 / 1239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (47647019 / 250000000) (190588077 / 1000000000) (Real.log (1239 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1239 / 1024) = -Real.log (1024 / 1239) := by
    rw [show ((1239 / 1024) : ℝ) = ((1024 / 1239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (29459111 / 125000000) ≤ -Real.log (809 / 1024) ∧
    -Real.log (809 / 1024) ≤ (235672889 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 1833)) (n := 12)
    (lo := (29459111 / 125000000)) (hi := (235672889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 809) = 1/(809 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-235672889 / 1000000000) (-29459111 / 125000000) (Real.log (809 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (38069183 / 200000000) ≤ -Real.log (10240 / 12387) ∧
    -Real.log (10240 / 12387) ≤ (47586479 / 250000000) := by
  have h := checkLog_sound (w := (2147 / 22627)) (n := 12)
    (lo := (38069183 / 200000000)) (hi := (47586479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12387 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12387 / 10240) = 1/(10240 / 12387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (38069183 / 200000000) (47586479 / 250000000) (Real.log (12387 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12387 / 10240) = -Real.log (10240 / 12387) := by
    rw [show ((12387 / 10240) : ℝ) = ((10240 / 12387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (235302129 / 1000000000) ≤ -Real.log (8093 / 10240) ∧
    -Real.log (8093 / 10240) ≤ (23530213 / 100000000) := by
  have h := checkLog_sound (w := (2147 / 18333)) (n := 12)
    (lo := (235302129 / 1000000000)) (hi := (23530213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8093) = 1/(8093 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-23530213 / 100000000) (-235302129 / 1000000000) (Real.log (8093 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (87650463 / 250000000) ≤ -Real.log (512 / 727) ∧
    -Real.log (512 / 727) ≤ (350601853 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 1239)) (n := 12)
    (lo := (87650463 / 250000000)) (hi := (350601853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727 / 512) = 1/(512 / 727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (87650463 / 250000000) (350601853 / 1000000000) (Real.log (727 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (727 / 512) = -Real.log (512 / 727) := by
    rw [show ((727 / 512) : ℝ) = ((512 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (272296243 / 500000000) ≤ -Real.log (297 / 512) ∧
    -Real.log (297 / 512) ≤ (544592487 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 809)) (n := 12)
    (lo := (272296243 / 500000000)) (hi := (544592487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 297) = 1/(297 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-544592487 / 1000000000) (-272296243 / 500000000) (Real.log (297 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (43773639 / 125000000) ≤ -Real.log (5120 / 7267) ∧
    -Real.log (5120 / 7267) ≤ (350189113 / 1000000000) := by
  have h := checkLog_sound (w := (2147 / 12387)) (n := 12)
    (lo := (43773639 / 125000000)) (hi := (350189113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7267 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7267 / 5120) = 1/(5120 / 7267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (43773639 / 125000000) (350189113 / 1000000000) (Real.log (7267 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7267 / 5120) = -Real.log (5120 / 7267) := by
    rw [show ((7267 / 5120) : ℝ) = ((5120 / 7267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (108716579 / 200000000) ≤ -Real.log (2973 / 5120) ∧
    -Real.log (2973 / 5120) ≤ (33973931 / 62500000) := by
  have h := checkLog_sound (w := (2147 / 8093)) (n := 12)
    (lo := (108716579 / 200000000)) (hi := (33973931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2973) = 1/(2973 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-33973931 / 62500000) (-108716579 / 200000000) (Real.log (2973 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16343031 / 62500000) ≤ -Real.log (500000 / 649431) ∧
    -Real.log (500000 / 649431) ≤ (261488497 / 1000000000) := by
  have h := checkLog_sound (w := (149431 / 1149431)) (n := 12)
    (lo := (16343031 / 62500000)) (hi := (261488497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649431 / 500000) = 1/(500000 / 649431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16343031 / 62500000) (261488497 / 1000000000) (Real.log (649431 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (649431 / 500000) = -Real.log (500000 / 649431) := by
    rw [show ((649431 / 500000) : ℝ) = ((500000 / 649431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (355050549 / 1000000000) ≤ -Real.log (350569 / 500000) ∧
    -Real.log (350569 / 500000) ≤ (7101011 / 20000000) := by
  have h := checkLog_sound (w := (149431 / 850569)) (n := 12)
    (lo := (355050549 / 1000000000)) (hi := (7101011 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 350569) = 1/(350569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7101011 / 20000000) (-355050549 / 1000000000) (Real.log (350569 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (130908211 / 500000000) ≤ -Real.log (125000 / 162411) ∧
    -Real.log (125000 / 162411) ≤ (261816423 / 1000000000) := by
  have h := checkLog_sound (w := (37411 / 287411)) (n := 12)
    (lo := (130908211 / 500000000)) (hi := (261816423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162411 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162411 / 125000) = 1/(125000 / 162411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (130908211 / 500000000) (261816423 / 1000000000) (Real.log (162411 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (162411 / 125000) = -Real.log (125000 / 162411) := by
    rw [show ((162411 / 125000) : ℝ) = ((125000 / 162411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (177829159 / 500000000) ≤ -Real.log (87589 / 125000) ∧
    -Real.log (87589 / 125000) ≤ (355658319 / 1000000000) := by
  have h := checkLog_sound (w := (37411 / 212589)) (n := 12)
    (lo := (177829159 / 500000000)) (hi := (355658319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 87589) = 1/(87589 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-355658319 / 1000000000) (-177829159 / 500000000) (Real.log (87589 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (196130769 / 1000000000) ≤ -Real.log (500000 / 608343) ∧
    -Real.log (500000 / 608343) ≤ (19613077 / 100000000) := by
  have h := checkLog_sound (w := (108343 / 1108343)) (n := 12)
    (lo := (196130769 / 1000000000)) (hi := (19613077 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608343 / 500000) = 1/(500000 / 608343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (196130769 / 1000000000) (19613077 / 100000000) (Real.log (608343 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (608343 / 500000) = -Real.log (500000 / 608343) := by
    rw [show ((608343 / 500000) : ℝ) = ((500000 / 608343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (244221641 / 1000000000) ≤ -Real.log (391657 / 500000) ∧
    -Real.log (391657 / 500000) ≤ (122110821 / 500000000) := by
  have h := checkLog_sound (w := (108343 / 891657)) (n := 12)
    (lo := (244221641 / 1000000000)) (hi := (122110821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391657) = 1/(391657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-122110821 / 500000000) (-244221641 / 1000000000) (Real.log (391657 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (49099463 / 250000000) ≤ -Real.log (1000000 / 1217011) ∧
    -Real.log (1000000 / 1217011) ≤ (196397853 / 1000000000) := by
  have h := checkLog_sound (w := (217011 / 2217011)) (n := 12)
    (lo := (49099463 / 250000000)) (hi := (196397853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217011 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217011 / 1000000) = 1/(1000000 / 1217011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (49099463 / 250000000) (196397853 / 1000000000) (Real.log (1217011 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1217011 / 1000000) = -Real.log (1000000 / 1217011) := by
    rw [show ((1217011 / 1000000) : ℝ) = ((1000000 / 1217011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (244636631 / 1000000000) ≤ -Real.log (782989 / 1000000) ∧
    -Real.log (782989 / 1000000) ≤ (30579579 / 125000000) := by
  have h := checkLog_sound (w := (217011 / 1782989)) (n := 12)
    (lo := (244636631 / 1000000000)) (hi := (30579579 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782989) = 1/(782989 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-30579579 / 125000000) (-244636631 / 1000000000) (Real.log (782989 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (308269523 / 500000000) ≤ -Real.log (250000000000 / 463126374551) ∧
    -Real.log (250000000000 / 463126374551) ≤ (616539047 / 1000000000) := by
  have h := checkLog_sound (w := (213126374551 / 713126374551)) (n := 12)
    (lo := (308269523 / 500000000)) (hi := (616539047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463126374551 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463126374551 / 250000000000) = 1/(250000000000 / 463126374551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (308269523 / 500000000) (616539047 / 1000000000) (Real.log (463126374551 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (463126374551 / 250000000000) = -Real.log (250000000000 / 463126374551) := by
    rw [show ((463126374551 / 250000000000) : ℝ) = ((250000000000 / 463126374551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (30873737 / 50000000) ≤ -Real.log (500000000000 / 927119843817) ∧
    -Real.log (500000000000 / 927119843817) ≤ (617474741 / 1000000000) := by
  have h := checkLog_sound (w := (427119843817 / 1427119843817)) (n := 12)
    (lo := (30873737 / 50000000)) (hi := (617474741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927119843817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927119843817 / 500000000000) = 1/(500000000000 / 927119843817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (30873737 / 50000000) (617474741 / 1000000000) (Real.log (927119843817 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (927119843817 / 500000000000) = -Real.log (500000000000 / 927119843817) := by
    rw [show ((927119843817 / 500000000000) : ℝ) = ((500000000000 / 927119843817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (44035241 / 100000000) ≤ -Real.log (500000000000 / 776627252927) ∧
    -Real.log (500000000000 / 776627252927) ≤ (440352411 / 1000000000) := by
  have h := checkLog_sound (w := (276627252927 / 1276627252927)) (n := 12)
    (lo := (44035241 / 100000000)) (hi := (440352411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776627252927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776627252927 / 500000000000) = 1/(500000000000 / 776627252927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (44035241 / 100000000) (440352411 / 1000000000) (Real.log (776627252927 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (776627252927 / 500000000000) = -Real.log (500000000000 / 776627252927) := by
    rw [show ((776627252927 / 500000000000) : ℝ) = ((500000000000 / 776627252927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (110258621 / 250000000) ≤ -Real.log (125000000000 / 194289287589) ∧
    -Real.log (125000000000 / 194289287589) ≤ (88206897 / 200000000) := by
  have h := checkLog_sound (w := (69289287589 / 319289287589)) (n := 12)
    (lo := (110258621 / 250000000)) (hi := (88206897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194289287589 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194289287589 / 125000000000) = 1/(125000000000 / 194289287589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (110258621 / 250000000) (88206897 / 200000000) (Real.log (194289287589 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (194289287589 / 125000000000) = -Real.log (125000000000 / 194289287589) := by
    rw [show ((194289287589 / 125000000000) : ℝ) = ((125000000000 / 194289287589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0440

end


