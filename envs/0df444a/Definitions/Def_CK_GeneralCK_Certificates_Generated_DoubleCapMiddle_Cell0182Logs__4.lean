-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0182Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0182Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:19:56.386734+00:00
-- url     : https://prove2.me/theorems/e05e5425-fa2d-4708-bd3d-a4f19e2c3a2a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0182Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0183Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0182Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0183Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0184Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0185Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0182Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0183Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0184Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0185Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0182Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0183Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0184Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0185Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0182Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0183Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0184Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0185Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0182Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0182
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

theorem reflection_log_1_neg : (273717837 / 1000000000) ≤ -Real.log (1280 / 1683) ∧
    -Real.log (1280 / 1683) ≤ (136858919 / 500000000) := by
  have h := checkLog_sound (w := (403 / 2963)) (n := 12)
    (lo := (273717837 / 1000000000)) (hi := (136858919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1683 / 1280) = 1/(1280 / 1683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (273717837 / 1000000000) (136858919 / 500000000) (Real.log (1683 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1683 / 1280) = -Real.log (1280 / 1683) := by
    rw [show ((1683 / 1280) : ℝ) = ((1280 / 1683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (94527091 / 250000000) ≤ -Real.log (877 / 1280) ∧
    -Real.log (877 / 1280) ≤ (75621673 / 200000000) := by
  have h := checkLog_sound (w := (403 / 2157)) (n := 12)
    (lo := (94527091 / 250000000)) (hi := (75621673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 877) = 1/(877 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-75621673 / 200000000) (-94527091 / 250000000) (Real.log (877 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (54654421 / 200000000) ≤ -Real.log (5120 / 6729) ∧
    -Real.log (5120 / 6729) ≤ (136636053 / 500000000) := by
  have h := checkLog_sound (w := (1609 / 11849)) (n := 12)
    (lo := (54654421 / 200000000)) (hi := (136636053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6729 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6729 / 5120) = 1/(5120 / 6729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (54654421 / 200000000) (136636053 / 500000000) (Real.log (6729 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6729 / 5120) = -Real.log (5120 / 6729) := by
    rw [show ((6729 / 5120) : ℝ) = ((5120 / 6729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (377253541 / 1000000000) ≤ -Real.log (3511 / 5120) ∧
    -Real.log (3511 / 5120) ≤ (188626771 / 500000000) := by
  have h := checkLog_sound (w := (1609 / 8631)) (n := 12)
    (lo := (377253541 / 1000000000)) (hi := (188626771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3511) = 1/(3511 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-188626771 / 500000000) (-377253541 / 1000000000) (Real.log (3511 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (244194139 / 500000000) ≤ -Real.log (640 / 1043) ∧
    -Real.log (640 / 1043) ≤ (488388279 / 1000000000) := by
  have h := checkLog_sound (w := (403 / 1683)) (n := 12)
    (lo := (244194139 / 500000000)) (hi := (488388279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1043 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1043 / 640) = 1/(640 / 1043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (244194139 / 500000000) (488388279 / 1000000000) (Real.log (1043 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1043 / 640) = -Real.log (640 / 1043) := by
    rw [show ((1043 / 640) : ℝ) = ((640 / 1043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (496704017 / 500000000) ≤ -Real.log (237 / 640) ∧
    -Real.log (237 / 640) ≤ (248352009 / 250000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 237) = 1/(237 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-248352009 / 250000000) (-496704017 / 500000000) (Real.log (237 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (24383447 / 50000000) ≤ -Real.log (2560 / 4169) ∧
    -Real.log (2560 / 4169) ≤ (487668941 / 1000000000) := by
  have h := checkLog_sound (w := (1609 / 6729)) (n := 12)
    (lo := (24383447 / 50000000)) (hi := (487668941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4169 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4169 / 2560) = 1/(2560 / 4169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (24383447 / 50000000) (487668941 / 1000000000) (Real.log (4169 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4169 / 2560) = -Real.log (2560 / 4169) := by
    rw [show ((4169 / 2560) : ℝ) = ((2560 / 4169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (495124237 / 500000000) ≤ -Real.log (951 / 2560) ∧
    -Real.log (951 / 2560) ≤ (247562119 / 250000000) := by
  have h := checkLog_sound (w := (329 / 2231)) (n := 12)
    (lo := (148550647 / 500000000)) (hi := (59420259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 951) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 951) = 1/(951 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-247562119 / 250000000) (-495124237 / 500000000) (Real.log (951 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (373827887 / 1000000000) ≤ -Real.log (1000000 / 1453287) ∧
    -Real.log (1000000 / 1453287) ≤ (23364243 / 62500000) := by
  have h := checkLog_sound (w := (453287 / 2453287)) (n := 12)
    (lo := (373827887 / 1000000000)) (hi := (23364243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1453287 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1453287 / 1000000) = 1/(1000000 / 1453287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (373827887 / 1000000000) (23364243 / 62500000) (Real.log (1453287 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1453287 / 1000000) = -Real.log (1000000 / 1453287) := by
    rw [show ((1453287 / 1000000) : ℝ) = ((1000000 / 1453287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (301915647 / 500000000) ≤ -Real.log (546713 / 1000000) ∧
    -Real.log (546713 / 1000000) ≤ (120766259 / 200000000) := by
  have h := checkLog_sound (w := (453287 / 1546713)) (n := 12)
    (lo := (301915647 / 500000000)) (hi := (120766259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 546713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 546713) = 1/(546713 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-120766259 / 200000000) (-301915647 / 500000000) (Real.log (546713 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (374438041 / 1000000000) ≤ -Real.log (500000 / 727087) ∧
    -Real.log (500000 / 727087) ≤ (187219021 / 500000000) := by
  have h := checkLog_sound (w := (227087 / 1227087)) (n := 12)
    (lo := (374438041 / 1000000000)) (hi := (187219021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727087 / 500000) = 1/(500000 / 727087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (374438041 / 1000000000) (187219021 / 500000000) (Real.log (727087 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (727087 / 500000) = -Real.log (500000 / 727087) := by
    rw [show ((727087 / 500000) : ℝ) = ((500000 / 727087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (121091007 / 200000000) ≤ -Real.log (272913 / 500000) ∧
    -Real.log (272913 / 500000) ≤ (151363759 / 250000000) := by
  have h := checkLog_sound (w := (227087 / 772913)) (n := 12)
    (lo := (121091007 / 200000000)) (hi := (151363759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 272913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 272913) = 1/(272913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-151363759 / 250000000) (-121091007 / 200000000) (Real.log (272913 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (292521841 / 1000000000) ≤ -Real.log (500000 / 669901) ∧
    -Real.log (500000 / 669901) ≤ (146260921 / 500000000) := by
  have h := checkLog_sound (w := (169901 / 1169901)) (n := 12)
    (lo := (292521841 / 1000000000)) (hi := (146260921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669901 / 500000) = 1/(500000 / 669901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (292521841 / 1000000000) (146260921 / 500000000) (Real.log (669901 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (669901 / 500000) = -Real.log (500000 / 669901) := by
    rw [show ((669901 / 500000) : ℝ) = ((500000 / 669901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3243871 / 7812500) ≤ -Real.log (330099 / 500000) ∧
    -Real.log (330099 / 500000) ≤ (415215489 / 1000000000) := by
  have h := checkLog_sound (w := (169901 / 830099)) (n := 12)
    (lo := (3243871 / 7812500)) (hi := (415215489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330099) = 1/(330099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-415215489 / 1000000000) (-3243871 / 7812500) (Real.log (330099 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (293077739 / 1000000000) ≤ -Real.log (1000000 / 1340547) ∧
    -Real.log (1000000 / 1340547) ≤ (14653887 / 50000000) := by
  have h := checkLog_sound (w := (340547 / 2340547)) (n := 12)
    (lo := (293077739 / 1000000000)) (hi := (14653887 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1340547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1340547 / 1000000) = 1/(1000000 / 1340547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (293077739 / 1000000000) (14653887 / 50000000) (Real.log (1340547 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1340547 / 1000000) = -Real.log (1000000 / 1340547) := by
    rw [show ((1340547 / 1000000) : ℝ) = ((1000000 / 1340547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16653783 / 40000000) ≤ -Real.log (659453 / 1000000) ∧
    -Real.log (659453 / 1000000) ≤ (813173 / 1953125) := by
  have h := checkLog_sound (w := (340547 / 1659453)) (n := 12)
    (lo := (16653783 / 40000000)) (hi := (813173 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 659453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 659453) = 1/(659453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-813173 / 1953125) (-16653783 / 40000000) (Real.log (659453 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (977659181 / 1000000000) ≤ -Real.log (25000000000 / 66455663209) ∧
    -Real.log (25000000000 / 66455663209) ≤ (977659183 / 1000000000) := by
  have h := checkLog_sound (w := (16455663209 / 116455663209)) (n := 12)
    (lo := (284512001 / 1000000000)) (hi := (142256001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66455663209 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(66455663209 / 50000000000) = 1/(25000000000 / 66455663209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (977659181 / 1000000000) (977659183 / 1000000000) (Real.log (66455663209 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (66455663209 / 25000000000) = -Real.log (25000000000 / 66455663209) := by
    rw [show ((66455663209 / 25000000000) : ℝ) = ((25000000000 / 66455663209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (244973269 / 250000000) ≤ -Real.log (62500000000 / 166510710373) ∧
    -Real.log (62500000000 / 166510710373) ≤ (489946539 / 500000000) := by
  have h := checkLog_sound (w := (41510710373 / 291510710373)) (n := 12)
    (lo := (35843237 / 125000000)) (hi := (286745897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166510710373 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(166510710373 / 125000000000) = 1/(62500000000 / 166510710373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (244973269 / 250000000) (489946539 / 500000000) (Real.log (166510710373 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (166510710373 / 62500000000) = -Real.log (62500000000 / 166510710373) := by
    rw [show ((166510710373 / 62500000000) : ℝ) = ((62500000000 / 166510710373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (70773733 / 100000000) ≤ -Real.log (500000000000 / 1014697106019) ∧
    -Real.log (500000000000 / 1014697106019) ≤ (176934333 / 250000000) := by
  have h := checkLog_sound (w := (14697106019 / 2014697106019)) (n := 12)
    (lo := (291803 / 20000000)) (hi := (14590151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1014697106019 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1014697106019 / 1000000000000) = 1/(500000000000 / 1014697106019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (70773733 / 100000000) (176934333 / 250000000) (Real.log (1014697106019 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1014697106019 / 500000000000) = -Real.log (500000000000 / 1014697106019) := by
    rw [show ((1014697106019 / 500000000000) : ℝ) = ((500000000000 / 1014697106019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (354711157 / 500000000) ≤ -Real.log (500000000000 / 1016408295967) ∧
    -Real.log (500000000000 / 1016408295967) ≤ (177355579 / 250000000) := by
  have h := checkLog_sound (w := (16408295967 / 2016408295967)) (n := 12)
    (lo := (8137567 / 500000000)) (hi := (3255027 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1016408295967 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1016408295967 / 1000000000000) = 1/(500000000000 / 1016408295967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (354711157 / 500000000) (177355579 / 250000000) (Real.log (1016408295967 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1016408295967 / 500000000000) = -Real.log (500000000000 / 1016408295967) := by
    rw [show ((1016408295967 / 500000000000) : ℝ) = ((500000000000 / 1016408295967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0182

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0183Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0183
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

theorem reflection_log_1_neg : (54654421 / 200000000) ≤ -Real.log (5120 / 6729) ∧
    -Real.log (5120 / 6729) ≤ (136636053 / 500000000) := by
  have h := checkLog_sound (w := (1609 / 11849)) (n := 12)
    (lo := (54654421 / 200000000)) (hi := (136636053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6729 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6729 / 5120) = 1/(5120 / 6729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (54654421 / 200000000) (136636053 / 500000000) (Real.log (6729 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6729 / 5120) = -Real.log (5120 / 6729) := by
    rw [show ((6729 / 5120) : ℝ) = ((5120 / 6729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (377253541 / 1000000000) ≤ -Real.log (3511 / 5120) ∧
    -Real.log (3511 / 5120) ≤ (188626771 / 500000000) := by
  have h := checkLog_sound (w := (1609 / 8631)) (n := 12)
    (lo := (377253541 / 1000000000)) (hi := (188626771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3511) = 1/(3511 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-188626771 / 500000000) (-377253541 / 1000000000) (Real.log (3511 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (136413087 / 500000000) ≤ -Real.log (2560 / 3363) ∧
    -Real.log (2560 / 3363) ≤ (10913047 / 40000000) := by
  have h := checkLog_sound (w := (803 / 5923)) (n := 12)
    (lo := (136413087 / 500000000)) (hi := (10913047 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3363 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3363 / 2560) = 1/(2560 / 3363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (136413087 / 500000000) (10913047 / 40000000) (Real.log (3363 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3363 / 2560) = -Real.log (2560 / 3363) := by
    rw [show ((3363 / 2560) : ℝ) = ((2560 / 3363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (376399449 / 1000000000) ≤ -Real.log (1757 / 2560) ∧
    -Real.log (1757 / 2560) ≤ (7527989 / 20000000) := by
  have h := checkLog_sound (w := (803 / 4317)) (n := 12)
    (lo := (376399449 / 1000000000)) (hi := (7527989 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1757) = 1/(1757 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7527989 / 20000000) (-376399449 / 1000000000) (Real.log (1757 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24383447 / 50000000) ≤ -Real.log (2560 / 4169) ∧
    -Real.log (2560 / 4169) ≤ (487668941 / 1000000000) := by
  have h := checkLog_sound (w := (1609 / 6729)) (n := 12)
    (lo := (24383447 / 50000000)) (hi := (487668941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4169 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4169 / 2560) = 1/(2560 / 4169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24383447 / 50000000) (487668941 / 1000000000) (Real.log (4169 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4169 / 2560) = -Real.log (2560 / 4169) := by
    rw [show ((4169 / 2560) : ℝ) = ((2560 / 4169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (495124237 / 500000000) ≤ -Real.log (951 / 2560) ∧
    -Real.log (951 / 2560) ≤ (247562119 / 250000000) := by
  have h := checkLog_sound (w := (329 / 2231)) (n := 12)
    (lo := (148550647 / 500000000)) (hi := (59420259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 951) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 951) = 1/(951 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-247562119 / 250000000) (-495124237 / 500000000) (Real.log (951 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (121737271 / 250000000) ≤ -Real.log (1280 / 2083) ∧
    -Real.log (1280 / 2083) ≤ (97389817 / 200000000) := by
  have h := checkLog_sound (w := (803 / 3363)) (n := 12)
    (lo := (121737271 / 250000000)) (hi := (97389817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2083 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2083 / 1280) = 1/(1280 / 2083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (121737271 / 250000000) (97389817 / 200000000) (Real.log (2083 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2083 / 1280) = -Real.log (1280 / 2083) := by
    rw [show ((2083 / 1280) : ℝ) = ((1280 / 2083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (197419773 / 200000000) ≤ -Real.log (477 / 1280) ∧
    -Real.log (477 / 1280) ≤ (987098867 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 1117)) (n := 12)
    (lo := (58790337 / 200000000)) (hi := (146975843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 477) = 1/(477 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-987098867 / 1000000000) (-197419773 / 200000000) (Real.log (477 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (373218049 / 1000000000) ≤ -Real.log (1000000 / 1452401) ∧
    -Real.log (1000000 / 1452401) ≤ (7464361 / 20000000) := by
  have h := checkLog_sound (w := (452401 / 2452401)) (n := 12)
    (lo := (373218049 / 1000000000)) (hi := (7464361 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1452401 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1452401 / 1000000) = 1/(1000000 / 1452401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (373218049 / 1000000000) (7464361 / 20000000) (Real.log (1452401 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1452401 / 1000000) = -Real.log (1000000 / 1452401) := by
    rw [show ((1452401 / 1000000) : ℝ) = ((1000000 / 1452401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (602212011 / 1000000000) ≤ -Real.log (547599 / 1000000) ∧
    -Real.log (547599 / 1000000) ≤ (150553003 / 250000000) := by
  have h := checkLog_sound (w := (452401 / 1547599)) (n := 12)
    (lo := (602212011 / 1000000000)) (hi := (150553003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 547599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 547599) = 1/(547599 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-150553003 / 250000000) (-602212011 / 1000000000) (Real.log (547599 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (14953143 / 40000000) ≤ -Real.log (125000 / 181661) ∧
    -Real.log (125000 / 181661) ≤ (11682143 / 31250000) := by
  have h := checkLog_sound (w := (56661 / 306661)) (n := 12)
    (lo := (14953143 / 40000000)) (hi := (11682143 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181661 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181661 / 125000) = 1/(125000 / 181661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (14953143 / 40000000) (11682143 / 31250000) (Real.log (181661 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (181661 / 125000) = -Real.log (125000 / 181661) := by
    rw [show ((181661 / 125000) : ℝ) = ((125000 / 181661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (603833123 / 1000000000) ≤ -Real.log (68339 / 125000) ∧
    -Real.log (68339 / 125000) ≤ (150958281 / 250000000) := by
  have h := checkLog_sound (w := (56661 / 193339)) (n := 12)
    (lo := (603833123 / 1000000000)) (hi := (150958281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 68339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 68339) = 1/(68339 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-150958281 / 250000000) (-603833123 / 1000000000) (Real.log (68339 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (36495891 / 125000000) ≤ -Real.log (1000000 / 1339059) ∧
    -Real.log (1000000 / 1339059) ≤ (291967129 / 1000000000) := by
  have h := checkLog_sound (w := (339059 / 2339059)) (n := 12)
    (lo := (36495891 / 125000000)) (hi := (291967129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1339059 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1339059 / 1000000) = 1/(1000000 / 1339059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (36495891 / 125000000) (291967129 / 1000000000) (Real.log (1339059 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1339059 / 1000000) = -Real.log (1000000 / 1339059) := by
    rw [show ((1339059 / 1000000) : ℝ) = ((1000000 / 1339059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (414090701 / 1000000000) ≤ -Real.log (660941 / 1000000) ∧
    -Real.log (660941 / 1000000) ≤ (207045351 / 500000000) := by
  have h := checkLog_sound (w := (339059 / 1660941)) (n := 12)
    (lo := (414090701 / 1000000000)) (hi := (207045351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 660941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 660941) = 1/(660941 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-207045351 / 500000000) (-414090701 / 1000000000) (Real.log (660941 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (73130647 / 250000000) ≤ -Real.log (1000000 / 1339803) ∧
    -Real.log (1000000 / 1339803) ≤ (292522589 / 1000000000) := by
  have h := checkLog_sound (w := (339803 / 2339803)) (n := 12)
    (lo := (73130647 / 250000000)) (hi := (292522589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1339803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1339803 / 1000000) = 1/(1000000 / 1339803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (73130647 / 250000000) (292522589 / 1000000000) (Real.log (1339803 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1339803 / 1000000) = -Real.log (1000000 / 1339803) := by
    rw [show ((1339803 / 1000000) : ℝ) = ((1000000 / 1339803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (415217003 / 1000000000) ≤ -Real.log (660197 / 1000000) ∧
    -Real.log (660197 / 1000000) ≤ (103804251 / 250000000) := by
  have h := checkLog_sound (w := (339803 / 1660197)) (n := 12)
    (lo := (415217003 / 1000000000)) (hi := (103804251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 660197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 660197) = 1/(660197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-103804251 / 250000000) (-415217003 / 1000000000) (Real.log (660197 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (48771503 / 50000000) ≤ -Real.log (50000000000 / 132615380963) ∧
    -Real.log (50000000000 / 132615380963) ≤ (487715031 / 500000000) := by
  have h := checkLog_sound (w := (32615380963 / 232615380963)) (n := 12)
    (lo := (441067 / 1562500)) (hi := (282282881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132615380963 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(132615380963 / 100000000000) = 1/(50000000000 / 132615380963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (48771503 / 50000000) (487715031 / 500000000) (Real.log (132615380963 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (132615380963 / 50000000000) = -Real.log (50000000000 / 132615380963) := by
    rw [show ((132615380963 / 50000000000) : ℝ) = ((50000000000 / 132615380963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (488830849 / 500000000) ≤ -Real.log (500000000000 / 1329116609843) ∧
    -Real.log (500000000000 / 1329116609843) ≤ (9776617 / 10000000) := by
  have h := checkLog_sound (w := (329116609843 / 2329116609843)) (n := 12)
    (lo := (142257259 / 500000000)) (hi := (284514519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329116609843 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1329116609843 / 1000000000000) = 1/(500000000000 / 1329116609843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (488830849 / 500000000) (9776617 / 10000000) (Real.log (1329116609843 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1329116609843 / 500000000000) = -Real.log (500000000000 / 1329116609843) := by
    rw [show ((1329116609843 / 500000000000) : ℝ) = ((500000000000 / 1329116609843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (706057829 / 1000000000) ≤ -Real.log (62500000000 / 126624293999) ∧
    -Real.log (62500000000 / 126624293999) ≤ (706057831 / 1000000000) := by
  have h := checkLog_sound (w := (1624293999 / 251624293999)) (n := 12)
    (lo := (12910649 / 1000000000)) (hi := (258213 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126624293999 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126624293999 / 125000000000) = 1/(62500000000 / 126624293999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (706057829 / 1000000000) (706057831 / 1000000000) (Real.log (126624293999 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (126624293999 / 62500000000) = -Real.log (62500000000 / 126624293999) := by
    rw [show ((126624293999 / 62500000000) : ℝ) = ((62500000000 / 126624293999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (707739591 / 1000000000) ≤ -Real.log (500000000000 / 1014699400331) ∧
    -Real.log (500000000000 / 1014699400331) ≤ (707739593 / 1000000000) := by
  have h := checkLog_sound (w := (14699400331 / 2014699400331)) (n := 12)
    (lo := (14592411 / 1000000000)) (hi := (3648103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1014699400331 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1014699400331 / 1000000000000) = 1/(500000000000 / 1014699400331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (707739591 / 1000000000) (707739593 / 1000000000) (Real.log (1014699400331 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1014699400331 / 500000000000) = -Real.log (500000000000 / 1014699400331) := by
    rw [show ((1014699400331 / 500000000000) : ℝ) = ((500000000000 / 1014699400331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0183

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0184Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0184
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

theorem reflection_log_1_neg : (136413087 / 500000000) ≤ -Real.log (2560 / 3363) ∧
    -Real.log (2560 / 3363) ≤ (10913047 / 40000000) := by
  have h := checkLog_sound (w := (803 / 5923)) (n := 12)
    (lo := (136413087 / 500000000)) (hi := (10913047 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3363 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3363 / 2560) = 1/(2560 / 3363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (136413087 / 500000000) (10913047 / 40000000) (Real.log (3363 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3363 / 2560) = -Real.log (2560 / 3363) := by
    rw [show ((3363 / 2560) : ℝ) = ((2560 / 3363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (376399449 / 1000000000) ≤ -Real.log (1757 / 2560) ∧
    -Real.log (1757 / 2560) ≤ (7527989 / 20000000) := by
  have h := checkLog_sound (w := (803 / 4317)) (n := 12)
    (lo := (376399449 / 1000000000)) (hi := (7527989 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1757) = 1/(1757 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7527989 / 20000000) (-376399449 / 1000000000) (Real.log (1757 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (68095011 / 250000000) ≤ -Real.log (5120 / 6723) ∧
    -Real.log (5120 / 6723) ≤ (54476009 / 200000000) := by
  have h := checkLog_sound (w := (1603 / 11843)) (n := 12)
    (lo := (68095011 / 250000000)) (hi := (54476009 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6723 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6723 / 5120) = 1/(5120 / 6723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (68095011 / 250000000) (54476009 / 200000000) (Real.log (6723 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6723 / 5120) = -Real.log (5120 / 6723) := by
    rw [show ((6723 / 5120) : ℝ) = ((5120 / 6723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (75109217 / 200000000) ≤ -Real.log (3517 / 5120) ∧
    -Real.log (3517 / 5120) ≤ (187773043 / 500000000) := by
  have h := checkLog_sound (w := (1603 / 8637)) (n := 12)
    (lo := (75109217 / 200000000)) (hi := (187773043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3517) = 1/(3517 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-187773043 / 500000000) (-75109217 / 200000000) (Real.log (3517 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (121737271 / 250000000) ≤ -Real.log (1280 / 2083) ∧
    -Real.log (1280 / 2083) ≤ (97389817 / 200000000) := by
  have h := checkLog_sound (w := (803 / 3363)) (n := 12)
    (lo := (121737271 / 250000000)) (hi := (97389817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2083 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2083 / 1280) = 1/(1280 / 2083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (121737271 / 250000000) (97389817 / 200000000) (Real.log (2083 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2083 / 1280) = -Real.log (1280 / 2083) := by
    rw [show ((2083 / 1280) : ℝ) = ((1280 / 2083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (197419773 / 200000000) ≤ -Real.log (477 / 1280) ∧
    -Real.log (477 / 1280) ≤ (987098867 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 1117)) (n := 12)
    (lo := (58790337 / 200000000)) (hi := (146975843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 477) = 1/(477 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-987098867 / 1000000000) (-197419773 / 200000000) (Real.log (477 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (486228709 / 1000000000) ≤ -Real.log (2560 / 4163) ∧
    -Real.log (2560 / 4163) ≤ (48622871 / 100000000) := by
  have h := checkLog_sound (w := (1603 / 6723)) (n := 12)
    (lo := (486228709 / 1000000000)) (hi := (48622871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4163 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4163 / 2560) = 1/(2560 / 4163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (486228709 / 1000000000) (48622871 / 100000000) (Real.log (4163 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4163 / 2560) = -Real.log (2560 / 4163) := by
    rw [show ((4163 / 2560) : ℝ) = ((2560 / 4163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (196791829 / 200000000) ≤ -Real.log (957 / 2560) ∧
    -Real.log (957 / 2560) ≤ (983959147 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 2237)) (n := 12)
    (lo := (58162393 / 200000000)) (hi := (145405983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 957) = 1/(957 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-983959147 / 1000000000) (-196791829 / 200000000) (Real.log (957 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (372608527 / 1000000000) ≤ -Real.log (250000 / 362879) ∧
    -Real.log (250000 / 362879) ≤ (23288033 / 62500000) := by
  have h := checkLog_sound (w := (112879 / 612879)) (n := 12)
    (lo := (372608527 / 1000000000)) (hi := (23288033 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362879 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362879 / 250000) = 1/(250000 / 362879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (372608527 / 1000000000) (23288033 / 62500000) (Real.log (362879 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (362879 / 250000) = -Real.log (250000 / 362879) := by
    rw [show ((362879 / 250000) : ℝ) = ((250000 / 362879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (60059717 / 100000000) ≤ -Real.log (137121 / 250000) ∧
    -Real.log (137121 / 250000) ≤ (600597171 / 1000000000) := by
  have h := checkLog_sound (w := (112879 / 387121)) (n := 12)
    (lo := (60059717 / 100000000)) (hi := (600597171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 137121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 137121) = 1/(137121 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-600597171 / 1000000000) (-60059717 / 100000000) (Real.log (137121 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (373218737 / 1000000000) ≤ -Real.log (500000 / 726201) ∧
    -Real.log (500000 / 726201) ≤ (186609369 / 500000000) := by
  have h := checkLog_sound (w := (226201 / 1226201)) (n := 12)
    (lo := (373218737 / 1000000000)) (hi := (186609369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726201 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726201 / 500000) = 1/(500000 / 726201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (373218737 / 1000000000) (186609369 / 500000000) (Real.log (726201 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (726201 / 500000) = -Real.log (500000 / 726201) := by
    rw [show ((726201 / 500000) : ℝ) = ((500000 / 726201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (602213837 / 1000000000) ≤ -Real.log (273799 / 500000) ∧
    -Real.log (273799 / 500000) ≤ (301106919 / 500000000) := by
  have h := checkLog_sound (w := (226201 / 773799)) (n := 12)
    (lo := (602213837 / 1000000000)) (hi := (301106919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 273799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 273799) = 1/(273799 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-301106919 / 500000000) (-602213837 / 1000000000) (Real.log (273799 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (145706427 / 500000000) ≤ -Real.log (1000000 / 1338317) ∧
    -Real.log (1000000 / 1338317) ≤ (58282571 / 200000000) := by
  have h := checkLog_sound (w := (338317 / 2338317)) (n := 12)
    (lo := (145706427 / 500000000)) (hi := (58282571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338317 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1338317 / 1000000) = 1/(1000000 / 1338317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (145706427 / 500000000) (58282571 / 200000000) (Real.log (1338317 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1338317 / 1000000) = -Real.log (1000000 / 1338317) := by
    rw [show ((1338317 / 1000000) : ℝ) = ((1000000 / 1338317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (412968689 / 1000000000) ≤ -Real.log (661683 / 1000000) ∧
    -Real.log (661683 / 1000000) ≤ (41296869 / 100000000) := by
  have h := checkLog_sound (w := (338317 / 1661683)) (n := 12)
    (lo := (412968689 / 1000000000)) (hi := (41296869 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 661683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 661683) = 1/(661683 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-41296869 / 100000000) (-412968689 / 1000000000) (Real.log (661683 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (2335743 / 8000000) ≤ -Real.log (50000 / 66953) ∧
    -Real.log (50000 / 66953) ≤ (72991969 / 250000000) := by
  have h := checkLog_sound (w := (16953 / 116953)) (n := 12)
    (lo := (2335743 / 8000000)) (hi := (72991969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66953 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66953 / 50000) = 1/(50000 / 66953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (2335743 / 8000000) (72991969 / 250000000) (Real.log (66953 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (66953 / 50000) = -Real.log (50000 / 66953) := by
    rw [show ((66953 / 50000) : ℝ) = ((50000 / 66953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (207046107 / 500000000) ≤ -Real.log (33047 / 50000) ∧
    -Real.log (33047 / 50000) ≤ (82818443 / 200000000) := by
  have h := checkLog_sound (w := (16953 / 83047)) (n := 12)
    (lo := (207046107 / 500000000)) (hi := (82818443 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33047) = 1/(33047 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-82818443 / 200000000) (-207046107 / 500000000) (Real.log (33047 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (973205697 / 1000000000) ≤ -Real.log (781250000 / 2067511313) ∧
    -Real.log (781250000 / 2067511313) ≤ (973205699 / 1000000000) := by
  have h := checkLog_sound (w := (505011313 / 3630011313)) (n := 12)
    (lo := (280058517 / 1000000000)) (hi := (140029259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2067511313 / 1562500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2067511313 / 1562500000) = 1/(781250000 / 2067511313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (973205697 / 1000000000) (973205699 / 1000000000) (Real.log (2067511313 / 781250000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2067511313 / 781250000) = -Real.log (781250000 / 2067511313) := by
    rw [show ((2067511313 / 781250000) : ℝ) = ((781250000 / 2067511313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (487716287 / 500000000) ≤ -Real.log (20000000000 / 53046285779) ∧
    -Real.log (20000000000 / 53046285779) ≤ (7620567 / 7812500) := by
  have h := checkLog_sound (w := (13046285779 / 93046285779)) (n := 12)
    (lo := (141142697 / 500000000)) (hi := (56457079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53046285779 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(53046285779 / 40000000000) = 1/(20000000000 / 53046285779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (487716287 / 500000000) (7620567 / 7812500) (Real.log (53046285779 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (53046285779 / 20000000000) = -Real.log (20000000000 / 53046285779) := by
    rw [show ((53046285779 / 20000000000) : ℝ) = ((20000000000 / 53046285779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (704381543 / 1000000000) ≤ -Real.log (500000000000 / 1011297706001) ∧
    -Real.log (500000000000 / 1011297706001) ≤ (140876309 / 200000000) := by
  have h := checkLog_sound (w := (11297706001 / 2011297706001)) (n := 12)
    (lo := (11234363 / 1000000000)) (hi := (2808591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1011297706001 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1011297706001 / 1000000000000) = 1/(500000000000 / 1011297706001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (704381543 / 1000000000) (140876309 / 200000000) (Real.log (1011297706001 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1011297706001 / 500000000000) = -Real.log (500000000000 / 1011297706001) := by
    rw [show ((1011297706001 / 500000000000) : ℝ) = ((500000000000 / 1011297706001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (706060089 / 1000000000) ≤ -Real.log (125000000000 / 253249160287) ∧
    -Real.log (125000000000 / 253249160287) ≤ (706060091 / 1000000000) := by
  have h := checkLog_sound (w := (3249160287 / 503249160287)) (n := 12)
    (lo := (12912909 / 1000000000)) (hi := (1291291 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253249160287 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(253249160287 / 250000000000) = 1/(125000000000 / 253249160287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (706060089 / 1000000000) (706060091 / 1000000000) (Real.log (253249160287 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (253249160287 / 125000000000) = -Real.log (125000000000 / 253249160287) := by
    rw [show ((253249160287 / 125000000000) : ℝ) = ((125000000000 / 253249160287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0184

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0185Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0185
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

theorem reflection_log_1_neg : (68095011 / 250000000) ≤ -Real.log (5120 / 6723) ∧
    -Real.log (5120 / 6723) ≤ (54476009 / 200000000) := by
  have h := checkLog_sound (w := (1603 / 11843)) (n := 12)
    (lo := (68095011 / 250000000)) (hi := (54476009 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6723 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6723 / 5120) = 1/(5120 / 6723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (68095011 / 250000000) (54476009 / 200000000) (Real.log (6723 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6723 / 5120) = -Real.log (5120 / 6723) := by
    rw [show ((6723 / 5120) : ℝ) = ((5120 / 6723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (75109217 / 200000000) ≤ -Real.log (3517 / 5120) ∧
    -Real.log (3517 / 5120) ≤ (187773043 / 500000000) := by
  have h := checkLog_sound (w := (1603 / 8637)) (n := 12)
    (lo := (75109217 / 200000000)) (hi := (187773043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3517) = 1/(3517 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-187773043 / 500000000) (-75109217 / 200000000) (Real.log (3517 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (54386743 / 200000000) ≤ -Real.log (16 / 21) ∧
    -Real.log (16 / 21) ≤ (67983429 / 250000000) := by
  have h := checkLog_sound (w := (5 / 37)) (n := 12)
    (lo := (54386743 / 200000000)) (hi := (67983429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21 / 16) = 1/(16 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (54386743 / 200000000) (67983429 / 250000000) (Real.log (21 / 16)) := by
  have h := reflection_log_3_neg
  have he : Real.log (21 / 16) = -Real.log (16 / 21) := by
    rw [show ((21 / 16) : ℝ) = ((16 / 21) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (374693449 / 1000000000) ≤ -Real.log (11 / 16) ∧
    -Real.log (11 / 16) ≤ (7493869 / 20000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 11) = 1/(11 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7493869 / 20000000) (-374693449 / 1000000000) (Real.log (11 / 16)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (486228709 / 1000000000) ≤ -Real.log (2560 / 4163) ∧
    -Real.log (2560 / 4163) ≤ (48622871 / 100000000) := by
  have h := checkLog_sound (w := (1603 / 6723)) (n := 12)
    (lo := (486228709 / 1000000000)) (hi := (48622871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4163 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4163 / 2560) = 1/(2560 / 4163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (486228709 / 1000000000) (48622871 / 100000000) (Real.log (4163 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4163 / 2560) = -Real.log (2560 / 4163) := by
    rw [show ((4163 / 2560) : ℝ) = ((2560 / 4163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (196791829 / 200000000) ≤ -Real.log (957 / 2560) ∧
    -Real.log (957 / 2560) ≤ (983959147 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 2237)) (n := 12)
    (lo := (58162393 / 200000000)) (hi := (145405983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 957) = 1/(957 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-983959147 / 1000000000) (-196791829 / 200000000) (Real.log (957 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97101563 / 200000000) ≤ -Real.log (8 / 13) ∧
    -Real.log (8 / 13) ≤ (60688477 / 125000000) := by
  have h := checkLog_sound (w := (5 / 21)) (n := 12)
    (lo := (97101563 / 200000000)) (hi := (60688477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13 / 8) = 1/(8 / 13) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97101563 / 200000000) (60688477 / 125000000) (Real.log (13 / 8)) := by
  have h := reflection_log_7_neg
  have he : Real.log (13 / 8) = -Real.log (8 / 13) := by
    rw [show ((13 / 8) : ℝ) = ((8 / 13) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (245207313 / 250000000) ≤ -Real.log (3 / 8) ∧
    -Real.log (3 / 8) ≤ (490414627 / 500000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4 / 3) = 1/(3 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-490414627 / 500000000) (-245207313 / 250000000) (Real.log (3 / 8)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (185999317 / 500000000) ≤ -Real.log (1000000 / 1450631) ∧
    -Real.log (1000000 / 1450631) ≤ (74399727 / 200000000) := by
  have h := checkLog_sound (w := (450631 / 2450631)) (n := 12)
    (lo := (185999317 / 500000000)) (hi := (74399727 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1450631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1450631 / 1000000) = 1/(1000000 / 1450631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (185999317 / 500000000) (74399727 / 200000000) (Real.log (1450631 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1450631 / 1000000) = -Real.log (1000000 / 1450631) := by
    rw [show ((1450631 / 1000000) : ℝ) = ((1000000 / 1450631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (149746233 / 250000000) ≤ -Real.log (549369 / 1000000) ∧
    -Real.log (549369 / 1000000) ≤ (598984933 / 1000000000) := by
  have h := checkLog_sound (w := (450631 / 1549369)) (n := 12)
    (lo := (149746233 / 250000000)) (hi := (598984933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 549369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 549369) = 1/(549369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-598984933 / 1000000000) (-149746233 / 250000000) (Real.log (549369 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (5822019 / 15625000) ≤ -Real.log (1000000 / 1451517) ∧
    -Real.log (1000000 / 1451517) ≤ (372609217 / 1000000000) := by
  have h := checkLog_sound (w := (451517 / 2451517)) (n := 12)
    (lo := (5822019 / 15625000)) (hi := (372609217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451517 / 1000000) = 1/(1000000 / 1451517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (5822019 / 15625000) (372609217 / 1000000000) (Real.log (1451517 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1451517 / 1000000) = -Real.log (1000000 / 1451517) := by
    rw [show ((1451517 / 1000000) : ℝ) = ((1000000 / 1451517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (600598993 / 1000000000) ≤ -Real.log (548483 / 1000000) ∧
    -Real.log (548483 / 1000000) ≤ (300299497 / 500000000) := by
  have h := checkLog_sound (w := (451517 / 1548483)) (n := 12)
    (lo := (600598993 / 1000000000)) (hi := (300299497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 548483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 548483) = 1/(548483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-300299497 / 500000000) (-600598993 / 1000000000) (Real.log (548483 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9089321 / 31250000) ≤ -Real.log (40000 / 53503) ∧
    -Real.log (40000 / 53503) ≤ (290858273 / 1000000000) := by
  have h := checkLog_sound (w := (13503 / 93503)) (n := 12)
    (lo := (9089321 / 31250000)) (hi := (290858273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53503 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53503 / 40000) = 1/(40000 / 53503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9089321 / 31250000) (290858273 / 1000000000) (Real.log (53503 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (53503 / 40000) = -Real.log (40000 / 53503) := by
    rw [show ((53503 / 40000) : ℝ) = ((40000 / 53503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (82369587 / 200000000) ≤ -Real.log (26497 / 40000) ∧
    -Real.log (26497 / 40000) ≤ (1608781 / 3906250) := by
  have h := checkLog_sound (w := (13503 / 66497)) (n := 12)
    (lo := (82369587 / 200000000)) (hi := (1608781 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26497) = 1/(26497 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1608781 / 3906250) (-82369587 / 200000000) (Real.log (26497 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (291413601 / 1000000000) ≤ -Real.log (500000 / 669159) ∧
    -Real.log (500000 / 669159) ≤ (145706801 / 500000000) := by
  have h := checkLog_sound (w := (169159 / 1169159)) (n := 12)
    (lo := (291413601 / 1000000000)) (hi := (145706801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669159 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669159 / 500000) = 1/(500000 / 669159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (291413601 / 1000000000) (145706801 / 500000000) (Real.log (669159 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (669159 / 500000) = -Real.log (500000 / 669159) := by
    rw [show ((669159 / 500000) : ℝ) = ((500000 / 669159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2064851 / 5000000) ≤ -Real.log (330841 / 500000) ∧
    -Real.log (330841 / 500000) ≤ (412970201 / 1000000000) := by
  have h := checkLog_sound (w := (169159 / 830841)) (n := 12)
    (lo := (2064851 / 5000000)) (hi := (412970201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330841) = 1/(330841 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-412970201 / 1000000000) (-2064851 / 5000000) (Real.log (330841 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (194196713 / 200000000) ≤ -Real.log (500000000000 / 1320270164497) ∧
    -Real.log (500000000000 / 1320270164497) ≤ (970983567 / 1000000000) := by
  have h := checkLog_sound (w := (320270164497 / 2320270164497)) (n := 12)
    (lo := (55567277 / 200000000)) (hi := (138918193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1320270164497 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1320270164497 / 1000000000000) = 1/(500000000000 / 1320270164497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (194196713 / 200000000) (970983567 / 1000000000) (Real.log (1320270164497 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1320270164497 / 500000000000) = -Real.log (500000000000 / 1320270164497) := by
    rw [show ((1320270164497 / 500000000000) : ℝ) = ((500000000000 / 1320270164497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (973208209 / 1000000000) ≤ -Real.log (125000000000 / 330802641103) ∧
    -Real.log (125000000000 / 330802641103) ≤ (973208211 / 1000000000) := by
  have h := checkLog_sound (w := (80802641103 / 580802641103)) (n := 12)
    (lo := (280061029 / 1000000000)) (hi := (28006103 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330802641103 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(330802641103 / 250000000000) = 1/(125000000000 / 330802641103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (973208209 / 1000000000) (973208211 / 1000000000) (Real.log (330802641103 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (330802641103 / 125000000000) = -Real.log (125000000000 / 330802641103) := by
    rw [show ((330802641103 / 125000000000) : ℝ) = ((125000000000 / 330802641103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (702706207 / 1000000000) ≤ -Real.log (500000000000 / 1009604860927) ∧
    -Real.log (500000000000 / 1009604860927) ≤ (702706209 / 1000000000) := by
  have h := checkLog_sound (w := (9604860927 / 2009604860927)) (n := 12)
    (lo := (9559027 / 1000000000)) (hi := (2389757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1009604860927 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1009604860927 / 1000000000000) = 1/(500000000000 / 1009604860927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (702706207 / 1000000000) (702706209 / 1000000000) (Real.log (1009604860927 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1009604860927 / 500000000000) = -Real.log (500000000000 / 1009604860927) := by
    rw [show ((1009604860927 / 500000000000) : ℝ) = ((500000000000 / 1009604860927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (352191901 / 500000000) ≤ -Real.log (250000000000 / 505649995013) ∧
    -Real.log (250000000000 / 505649995013) ≤ (176095951 / 250000000) := by
  have h := checkLog_sound (w := (5649995013 / 1005649995013)) (n := 12)
    (lo := (5618311 / 500000000)) (hi := (11236623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((505649995013 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(505649995013 / 500000000000) = 1/(250000000000 / 505649995013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (352191901 / 500000000) (176095951 / 250000000) (Real.log (505649995013 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (505649995013 / 250000000000) = -Real.log (250000000000 / 505649995013) := by
    rw [show ((505649995013 / 250000000000) : ℝ) = ((250000000000 / 505649995013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0185

end


