-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0178Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0178Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:27:57.023567+00:00
-- url     : https://prove2.me/theorems/874912be-0b73-4104-8133-c9d2a6ddf9cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0178Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0179Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0178Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0179Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0180Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0181Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0178Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0179Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0180Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0181Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0178Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0179Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0180Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0181Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0178Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0179Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0180Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0181Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0178Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0178
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

theorem reflection_log_1_neg : (275498781 / 1000000000) ≤ -Real.log (640 / 843) ∧
    -Real.log (640 / 843) ≤ (137749391 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1483)) (n := 12)
    (lo := (275498781 / 1000000000)) (hi := (137749391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843 / 640) = 1/(640 / 843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (275498781 / 1000000000) (137749391 / 500000000) (Real.log (843 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (843 / 640) = -Real.log (640 / 843) := by
    rw [show ((843 / 640) : ℝ) = ((640 / 843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (381534981 / 1000000000) ≤ -Real.log (437 / 640) ∧
    -Real.log (437 / 640) ≤ (190767491 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1077)) (n := 12)
    (lo := (381534981 / 1000000000)) (hi := (190767491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 437) = 1/(437 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-190767491 / 500000000) (-381534981 / 1000000000) (Real.log (437 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (137526921 / 500000000) ≤ -Real.log (5120 / 6741) ∧
    -Real.log (5120 / 6741) ≤ (275053843 / 1000000000) := by
  have h := checkLog_sound (w := (1621 / 11861)) (n := 12)
    (lo := (137526921 / 500000000)) (hi := (275053843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6741 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6741 / 5120) = 1/(5120 / 6741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (137526921 / 500000000) (275053843 / 1000000000) (Real.log (6741 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6741 / 5120) = -Real.log (5120 / 6741) := by
    rw [show ((6741 / 5120) : ℝ) = ((5120 / 6741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (15227089 / 40000000) ≤ -Real.log (3499 / 5120) ∧
    -Real.log (3499 / 5120) ≤ (190338613 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 8619)) (n := 12)
    (lo := (15227089 / 40000000)) (hi := (190338613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3499) = 1/(3499 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-190338613 / 500000000) (-15227089 / 40000000) (Real.log (3499 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (122815117 / 250000000) ≤ -Real.log (320 / 523) ∧
    -Real.log (320 / 523) ≤ (491260469 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 843)) (n := 12)
    (lo := (122815117 / 250000000)) (hi := (491260469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((523 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(523 / 320) = 1/(320 / 523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (122815117 / 250000000) (491260469 / 1000000000) (Real.log (523 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (523 / 320) = -Real.log (320 / 523) := by
    rw [show ((523 / 320) : ℝ) = ((320 / 523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (50307353 / 50000000) ≤ -Real.log (117 / 320) ∧
    -Real.log (117 / 320) ≤ (503073531 / 500000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 117) = 1/(117 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-503073531 / 500000000) (-50307353 / 50000000) (Real.log (117 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (490543193 / 1000000000) ≤ -Real.log (2560 / 4181) ∧
    -Real.log (2560 / 4181) ≤ (245271597 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 6741)) (n := 12)
    (lo := (490543193 / 1000000000)) (hi := (245271597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4181 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4181 / 2560) = 1/(2560 / 4181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (490543193 / 1000000000) (245271597 / 500000000) (Real.log (4181 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4181 / 2560) = -Real.log (2560 / 4181) := by
    rw [show ((4181 / 2560) : ℝ) = ((2560 / 4181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1002947057 / 1000000000) ≤ -Real.log (939 / 2560) ∧
    -Real.log (939 / 2560) ≤ (1002947059 / 1000000000) := by
  have h := checkLog_sound (w := (341 / 2219)) (n := 12)
    (lo := (309799877 / 1000000000)) (hi := (154899939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 939) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 939) = 1/(939 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1002947059 / 1000000000) (-1002947057 / 1000000000) (Real.log (939 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75252843 / 200000000) ≤ -Real.log (15625 / 22763) ∧
    -Real.log (15625 / 22763) ≤ (47033027 / 125000000) := by
  have h := checkLog_sound (w := (3569 / 19194)) (n := 12)
    (lo := (75252843 / 200000000)) (hi := (47033027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22763 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22763 / 15625) = 1/(15625 / 22763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75252843 / 200000000) (47033027 / 125000000) (Real.log (22763 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (22763 / 15625) = -Real.log (15625 / 22763) := by
    rw [show ((22763 / 15625) : ℝ) = ((15625 / 22763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (305168307 / 500000000) ≤ -Real.log (8487 / 15625) ∧
    -Real.log (8487 / 15625) ≤ (122067323 / 200000000) := by
  have h := checkLog_sound (w := (3569 / 12056)) (n := 12)
    (lo := (305168307 / 500000000)) (hi := (122067323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 8487) = 1/(8487 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-122067323 / 200000000) (-305168307 / 500000000) (Real.log (8487 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (376874257 / 1000000000) ≤ -Real.log (1000000 / 1457721) ∧
    -Real.log (1000000 / 1457721) ≤ (188437129 / 500000000) := by
  have h := checkLog_sound (w := (457721 / 2457721)) (n := 12)
    (lo := (376874257 / 1000000000)) (hi := (188437129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1457721 / 1000000) = 1/(1000000 / 1457721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (376874257 / 1000000000) (188437129 / 500000000) (Real.log (1457721 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1457721 / 1000000) = -Real.log (1000000 / 1457721) := by
    rw [show ((1457721 / 1000000) : ℝ) = ((1000000 / 1457721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (611974649 / 1000000000) ≤ -Real.log (542279 / 1000000) ∧
    -Real.log (542279 / 1000000) ≤ (12239493 / 20000000) := by
  have h := checkLog_sound (w := (457721 / 1542279)) (n := 12)
    (lo := (611974649 / 1000000000)) (hi := (12239493 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 542279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 542279) = 1/(542279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-12239493 / 20000000) (-611974649 / 1000000000) (Real.log (542279 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (294743581 / 1000000000) ≤ -Real.log (500000 / 671391) ∧
    -Real.log (500000 / 671391) ≤ (147371791 / 500000000) := by
  have h := checkLog_sound (w := (171391 / 1171391)) (n := 12)
    (lo := (294743581 / 1000000000)) (hi := (147371791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671391 / 500000) = 1/(500000 / 671391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (294743581 / 1000000000) (147371791 / 500000000) (Real.log (671391 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (671391 / 500000) = -Real.log (500000 / 671391) := by
    rw [show ((671391 / 500000) : ℝ) = ((500000 / 671391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (26233719 / 62500000) ≤ -Real.log (328609 / 500000) ∧
    -Real.log (328609 / 500000) ≤ (83947901 / 200000000) := by
  have h := checkLog_sound (w := (171391 / 828609)) (n := 12)
    (lo := (26233719 / 62500000)) (hi := (83947901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 328609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 328609) = 1/(328609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-83947901 / 200000000) (-26233719 / 62500000) (Real.log (328609 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (147650239 / 500000000) ≤ -Real.log (100000 / 134353) ∧
    -Real.log (100000 / 134353) ≤ (295300479 / 1000000000) := by
  have h := checkLog_sound (w := (34353 / 234353)) (n := 12)
    (lo := (147650239 / 500000000)) (hi := (295300479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134353 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134353 / 100000) = 1/(100000 / 134353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (147650239 / 500000000) (295300479 / 1000000000) (Real.log (134353 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (134353 / 100000) = -Real.log (100000 / 134353) := by
    rw [show ((134353 / 100000) : ℝ) = ((100000 / 134353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (420878283 / 1000000000) ≤ -Real.log (65647 / 100000) ∧
    -Real.log (65647 / 100000) ≤ (105219571 / 250000000) := by
  have h := checkLog_sound (w := (34353 / 165647)) (n := 12)
    (lo := (420878283 / 1000000000)) (hi := (105219571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 65647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 65647) = 1/(65647 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-105219571 / 250000000) (-420878283 / 1000000000) (Real.log (65647 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (986600829 / 1000000000) ≤ -Real.log (100000000000 / 268210203841) ∧
    -Real.log (100000000000 / 268210203841) ≤ (986600831 / 1000000000) := by
  have h := checkLog_sound (w := (68210203841 / 468210203841)) (n := 12)
    (lo := (293453649 / 1000000000)) (hi := (5869073 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268210203841 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(268210203841 / 200000000000) = 1/(100000000000 / 268210203841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (986600829 / 1000000000) (986600831 / 1000000000) (Real.log (268210203841 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (268210203841 / 100000000000) = -Real.log (100000000000 / 268210203841) := by
    rw [show ((268210203841 / 100000000000) : ℝ) = ((100000000000 / 268210203841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (494424453 / 500000000) ≤ -Real.log (500000000000 / 1344069196853) ∧
    -Real.log (500000000000 / 1344069196853) ≤ (247212227 / 250000000) := by
  have h := checkLog_sound (w := (344069196853 / 2344069196853)) (n := 12)
    (lo := (147850863 / 500000000)) (hi := (295701727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1344069196853 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1344069196853 / 1000000000000) = 1/(500000000000 / 1344069196853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (494424453 / 500000000) (247212227 / 250000000) (Real.log (1344069196853 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1344069196853 / 500000000000) = -Real.log (500000000000 / 1344069196853) := by
    rw [show ((1344069196853 / 500000000000) : ℝ) = ((500000000000 / 1344069196853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (178620771 / 250000000) ≤ -Real.log (31250000000 / 63847821423) ∧
    -Real.log (31250000000 / 63847821423) ≤ (357241543 / 500000000) := by
  have h := checkLog_sound (w := (1347821423 / 126347821423)) (n := 12)
    (lo := (666747 / 31250000)) (hi := (4267181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63847821423 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63847821423 / 62500000000) = 1/(31250000000 / 63847821423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (178620771 / 250000000) (357241543 / 500000000) (Real.log (63847821423 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (63847821423 / 31250000000) = -Real.log (31250000000 / 63847821423) := by
    rw [show ((63847821423 / 31250000000) : ℝ) = ((31250000000 / 63847821423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (716178761 / 1000000000) ≤ -Real.log (500000000000 / 1023298856003) ∧
    -Real.log (500000000000 / 1023298856003) ≤ (716178763 / 1000000000) := by
  have h := checkLog_sound (w := (23298856003 / 2023298856003)) (n := 12)
    (lo := (23031581 / 1000000000)) (hi := (11515791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1023298856003 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1023298856003 / 1000000000000) = 1/(500000000000 / 1023298856003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (716178761 / 1000000000) (716178763 / 1000000000) (Real.log (1023298856003 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1023298856003 / 500000000000) = -Real.log (500000000000 / 1023298856003) := by
    rw [show ((1023298856003 / 500000000000) : ℝ) = ((500000000000 / 1023298856003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0178

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0179Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0179
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

theorem reflection_log_1_neg : (137526921 / 500000000) ≤ -Real.log (5120 / 6741) ∧
    -Real.log (5120 / 6741) ≤ (275053843 / 1000000000) := by
  have h := checkLog_sound (w := (1621 / 11861)) (n := 12)
    (lo := (137526921 / 500000000)) (hi := (275053843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6741 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6741 / 5120) = 1/(5120 / 6741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (137526921 / 500000000) (275053843 / 1000000000) (Real.log (6741 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6741 / 5120) = -Real.log (5120 / 6741) := by
    rw [show ((6741 / 5120) : ℝ) = ((5120 / 6741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (15227089 / 40000000) ≤ -Real.log (3499 / 5120) ∧
    -Real.log (3499 / 5120) ≤ (190338613 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 8619)) (n := 12)
    (lo := (15227089 / 40000000)) (hi := (190338613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3499) = 1/(3499 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-190338613 / 500000000) (-15227089 / 40000000) (Real.log (3499 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (54921741 / 200000000) ≤ -Real.log (2560 / 3369) ∧
    -Real.log (2560 / 3369) ≤ (137304353 / 500000000) := by
  have h := checkLog_sound (w := (809 / 5929)) (n := 12)
    (lo := (54921741 / 200000000)) (hi := (137304353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3369 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3369 / 2560) = 1/(2560 / 3369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (54921741 / 200000000) (137304353 / 500000000) (Real.log (3369 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3369 / 2560) = -Real.log (2560 / 3369) := by
    rw [show ((3369 / 2560) : ℝ) = ((2560 / 3369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (75964041 / 200000000) ≤ -Real.log (1751 / 2560) ∧
    -Real.log (1751 / 2560) ≤ (189910103 / 500000000) := by
  have h := checkLog_sound (w := (809 / 4311)) (n := 12)
    (lo := (75964041 / 200000000)) (hi := (189910103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1751) = 1/(1751 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-189910103 / 500000000) (-75964041 / 200000000) (Real.log (1751 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (490543193 / 1000000000) ≤ -Real.log (2560 / 4181) ∧
    -Real.log (2560 / 4181) ≤ (245271597 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 6741)) (n := 12)
    (lo := (490543193 / 1000000000)) (hi := (245271597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4181 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4181 / 2560) = 1/(2560 / 4181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (490543193 / 1000000000) (245271597 / 500000000) (Real.log (4181 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4181 / 2560) = -Real.log (2560 / 4181) := by
    rw [show ((4181 / 2560) : ℝ) = ((2560 / 4181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1002947057 / 1000000000) ≤ -Real.log (939 / 2560) ∧
    -Real.log (939 / 2560) ≤ (1002947059 / 1000000000) := by
  have h := checkLog_sound (w := (341 / 2219)) (n := 12)
    (lo := (309799877 / 1000000000)) (hi := (154899939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 939) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 939) = 1/(939 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1002947059 / 1000000000) (-1002947057 / 1000000000) (Real.log (939 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122456351 / 250000000) ≤ -Real.log (1280 / 2089) ∧
    -Real.log (1280 / 2089) ≤ (97965081 / 200000000) := by
  have h := checkLog_sound (w := (809 / 3369)) (n := 12)
    (lo := (122456351 / 250000000)) (hi := (97965081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2089 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2089 / 1280) = 1/(1280 / 2089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122456351 / 250000000) (97965081 / 200000000) (Real.log (2089 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2089 / 1280) = -Real.log (1280 / 2089) := by
    rw [show ((2089 / 1280) : ℝ) = ((1280 / 2089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (499878631 / 500000000) ≤ -Real.log (471 / 1280) ∧
    -Real.log (471 / 1280) ≤ (62484829 / 62500000) := by
  have h := checkLog_sound (w := (169 / 1111)) (n := 12)
    (lo := (153305041 / 500000000)) (hi := (306610083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 471) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 471) = 1/(471 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-62484829 / 62500000) (-499878631 / 500000000) (Real.log (471 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (375655861 / 1000000000) ≤ -Real.log (500000 / 727973) ∧
    -Real.log (500000 / 727973) ≤ (187827931 / 500000000) := by
  have h := checkLog_sound (w := (227973 / 1227973)) (n := 12)
    (lo := (375655861 / 1000000000)) (hi := (187827931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727973 / 500000) = 1/(500000 / 727973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (375655861 / 1000000000) (187827931 / 500000000) (Real.log (727973 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (727973 / 500000) = -Real.log (500000 / 727973) := by
    rw [show ((727973 / 500000) : ℝ) = ((500000 / 727973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (152176693 / 250000000) ≤ -Real.log (272027 / 500000) ∧
    -Real.log (272027 / 500000) ≤ (608706773 / 1000000000) := by
  have h := checkLog_sound (w := (227973 / 772027)) (n := 12)
    (lo := (152176693 / 250000000)) (hi := (608706773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 272027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 272027) = 1/(272027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-608706773 / 1000000000) (-152176693 / 250000000) (Real.log (272027 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (376265587 / 1000000000) ≤ -Real.log (500000 / 728417) ∧
    -Real.log (500000 / 728417) ≤ (94066397 / 250000000) := by
  have h := checkLog_sound (w := (228417 / 1228417)) (n := 12)
    (lo := (376265587 / 1000000000)) (hi := (94066397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728417 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728417 / 500000) = 1/(500000 / 728417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (376265587 / 1000000000) (94066397 / 250000000) (Real.log (728417 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (728417 / 500000) = -Real.log (500000 / 728417) := by
    rw [show ((728417 / 500000) : ℝ) = ((500000 / 728417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (76292537 / 125000000) ≤ -Real.log (271583 / 500000) ∧
    -Real.log (271583 / 500000) ≤ (610340297 / 1000000000) := by
  have h := checkLog_sound (w := (228417 / 771583)) (n := 12)
    (lo := (76292537 / 125000000)) (hi := (610340297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 271583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 271583) = 1/(271583 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-610340297 / 1000000000) (-76292537 / 125000000) (Real.log (271583 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (294187863 / 1000000000) ≤ -Real.log (250000 / 335509) ∧
    -Real.log (250000 / 335509) ≤ (36773483 / 125000000) := by
  have h := checkLog_sound (w := (85509 / 585509)) (n := 12)
    (lo := (294187863 / 1000000000)) (hi := (36773483 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335509 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335509 / 250000) = 1/(250000 / 335509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (294187863 / 1000000000) (36773483 / 125000000) (Real.log (335509 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (335509 / 250000) = -Real.log (250000 / 335509) := by
    rw [show ((335509 / 250000) : ℝ) = ((250000 / 335509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (20930253 / 50000000) ≤ -Real.log (164491 / 250000) ∧
    -Real.log (164491 / 250000) ≤ (418605061 / 1000000000) := by
  have h := checkLog_sound (w := (85509 / 414491)) (n := 12)
    (lo := (20930253 / 50000000)) (hi := (418605061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 164491) = 1/(164491 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-418605061 / 1000000000) (-20930253 / 50000000) (Real.log (164491 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (11789773 / 40000000) ≤ -Real.log (1000000 / 1342783) ∧
    -Real.log (1000000 / 1342783) ≤ (147372163 / 500000000) := by
  have h := checkLog_sound (w := (342783 / 2342783)) (n := 12)
    (lo := (11789773 / 40000000)) (hi := (147372163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1342783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1342783 / 1000000) = 1/(1000000 / 1342783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (11789773 / 40000000) (147372163 / 500000000) (Real.log (1342783 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1342783 / 1000000) = -Real.log (1000000 / 1342783) := by
    rw [show ((1342783 / 1000000) : ℝ) = ((1000000 / 1342783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16789641 / 40000000) ≤ -Real.log (657217 / 1000000) ∧
    -Real.log (657217 / 1000000) ≤ (209870513 / 500000000) := by
  have h := checkLog_sound (w := (342783 / 1657217)) (n := 12)
    (lo := (16789641 / 40000000)) (hi := (209870513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 657217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 657217) = 1/(657217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-209870513 / 500000000) (-16789641 / 40000000) (Real.log (657217 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (123045329 / 125000000) ≤ -Real.log (500000000000 / 1338052840343) ∧
    -Real.log (500000000000 / 1338052840343) ≤ (492181317 / 500000000) := by
  have h := checkLog_sound (w := (338052840343 / 2338052840343)) (n := 12)
    (lo := (72803863 / 250000000)) (hi := (291215453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338052840343 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1338052840343 / 1000000000000) = 1/(500000000000 / 1338052840343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (123045329 / 125000000) (492181317 / 500000000) (Real.log (1338052840343 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1338052840343 / 500000000000) = -Real.log (500000000000 / 1338052840343) := by
    rw [show ((1338052840343 / 500000000000) : ℝ) = ((500000000000 / 1338052840343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (246651471 / 250000000) ≤ -Real.log (500000000000 / 1341057798169) ∧
    -Real.log (500000000000 / 1341057798169) ≤ (493302943 / 500000000) := by
  have h := checkLog_sound (w := (341057798169 / 2341057798169)) (n := 12)
    (lo := (18341169 / 62500000)) (hi := (58691741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341057798169 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1341057798169 / 1000000000000) = 1/(500000000000 / 1341057798169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (246651471 / 250000000) (493302943 / 500000000) (Real.log (1341057798169 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1341057798169 / 500000000000) = -Real.log (500000000000 / 1341057798169) := by
    rw [show ((1341057798169 / 500000000000) : ℝ) = ((500000000000 / 1341057798169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (712792923 / 1000000000) ≤ -Real.log (100000000000 / 203967998249) ∧
    -Real.log (100000000000 / 203967998249) ≤ (28511717 / 40000000) := by
  have h := checkLog_sound (w := (3967998249 / 403967998249)) (n := 12)
    (lo := (19645743 / 1000000000)) (hi := (1227859 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203967998249 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(203967998249 / 200000000000) = 1/(100000000000 / 203967998249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (712792923 / 1000000000) (28511717 / 40000000) (Real.log (203967998249 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (203967998249 / 100000000000) = -Real.log (100000000000 / 203967998249) := by
    rw [show ((203967998249 / 100000000000) : ℝ) = ((100000000000 / 203967998249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (714485351 / 1000000000) ≤ -Real.log (500000000000 / 1021567457933) ∧
    -Real.log (500000000000 / 1021567457933) ≤ (714485353 / 1000000000) := by
  have h := checkLog_sound (w := (21567457933 / 2021567457933)) (n := 12)
    (lo := (21338171 / 1000000000)) (hi := (5334543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1021567457933 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1021567457933 / 1000000000000) = 1/(500000000000 / 1021567457933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (714485351 / 1000000000) (714485353 / 1000000000) (Real.log (1021567457933 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1021567457933 / 500000000000) = -Real.log (500000000000 / 1021567457933) := by
    rw [show ((1021567457933 / 500000000000) : ℝ) = ((500000000000 / 1021567457933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0179

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0180Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0180
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

theorem reflection_log_1_neg : (54921741 / 200000000) ≤ -Real.log (2560 / 3369) ∧
    -Real.log (2560 / 3369) ≤ (137304353 / 500000000) := by
  have h := checkLog_sound (w := (809 / 5929)) (n := 12)
    (lo := (54921741 / 200000000)) (hi := (137304353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3369 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3369 / 2560) = 1/(2560 / 3369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (54921741 / 200000000) (137304353 / 500000000) (Real.log (3369 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3369 / 2560) = -Real.log (2560 / 3369) := by
    rw [show ((3369 / 2560) : ℝ) = ((2560 / 3369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (75964041 / 200000000) ≤ -Real.log (1751 / 2560) ∧
    -Real.log (1751 / 2560) ≤ (189910103 / 500000000) := by
  have h := checkLog_sound (w := (809 / 4311)) (n := 12)
    (lo := (75964041 / 200000000)) (hi := (189910103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1751) = 1/(1751 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-189910103 / 500000000) (-75964041 / 200000000) (Real.log (1751 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27416337 / 100000000) ≤ -Real.log (1024 / 1347) ∧
    -Real.log (1024 / 1347) ≤ (274163371 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 2371)) (n := 12)
    (lo := (27416337 / 100000000)) (hi := (274163371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1347 / 1024) = 1/(1024 / 1347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27416337 / 100000000) (274163371 / 1000000000) (Real.log (1347 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1347 / 1024) = -Real.log (1024 / 1347) := by
    rw [show ((1347 / 1024) : ℝ) = ((1024 / 1347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (189481959 / 500000000) ≤ -Real.log (701 / 1024) ∧
    -Real.log (701 / 1024) ≤ (378963919 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 1725)) (n := 12)
    (lo := (189481959 / 500000000)) (hi := (378963919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 701) = 1/(701 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-378963919 / 1000000000) (-189481959 / 500000000) (Real.log (701 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (122456351 / 250000000) ≤ -Real.log (1280 / 2089) ∧
    -Real.log (1280 / 2089) ≤ (97965081 / 200000000) := by
  have h := checkLog_sound (w := (809 / 3369)) (n := 12)
    (lo := (122456351 / 250000000)) (hi := (97965081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2089 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2089 / 1280) = 1/(1280 / 2089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (122456351 / 250000000) (97965081 / 200000000) (Real.log (2089 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2089 / 1280) = -Real.log (1280 / 2089) := by
    rw [show ((2089 / 1280) : ℝ) = ((1280 / 2089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (499878631 / 500000000) ≤ -Real.log (471 / 1280) ∧
    -Real.log (471 / 1280) ≤ (62484829 / 62500000) := by
  have h := checkLog_sound (w := (169 / 1111)) (n := 12)
    (lo := (153305041 / 500000000)) (hi := (306610083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 471) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 471) = 1/(471 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-62484829 / 62500000) (-499878631 / 500000000) (Real.log (471 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (489107099 / 1000000000) ≤ -Real.log (512 / 835) ∧
    -Real.log (512 / 835) ≤ (4891071 / 10000000) := by
  have h := checkLog_sound (w := (323 / 1347)) (n := 12)
    (lo := (489107099 / 1000000000)) (hi := (4891071 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835 / 512) = 1/(512 / 835) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (489107099 / 1000000000) (4891071 / 10000000) (Real.log (835 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (835 / 512) = -Real.log (512 / 835) := by
    rw [show ((835 / 512) : ℝ) = ((512 / 835) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (996577609 / 1000000000) ≤ -Real.log (189 / 512) ∧
    -Real.log (189 / 512) ≤ (996577611 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 445)) (n := 12)
    (lo := (303430429 / 1000000000)) (hi := (30343043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 189) = 1/(189 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-996577611 / 1000000000) (-996577609 / 1000000000) (Real.log (189 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (375046449 / 1000000000) ≤ -Real.log (1000000 / 1455059) ∧
    -Real.log (1000000 / 1455059) ≤ (7500929 / 20000000) := by
  have h := checkLog_sound (w := (455059 / 2455059)) (n := 12)
    (lo := (375046449 / 1000000000)) (hi := (7500929 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1455059 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1455059 / 1000000) = 1/(1000000 / 1455059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (375046449 / 1000000000) (7500929 / 20000000) (Real.log (1455059 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1455059 / 1000000) = -Real.log (1000000 / 1455059) := by
    rw [show ((1455059 / 1000000) : ℝ) = ((1000000 / 1455059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (607077747 / 1000000000) ≤ -Real.log (544941 / 1000000) ∧
    -Real.log (544941 / 1000000) ≤ (151769437 / 250000000) := by
  have h := checkLog_sound (w := (455059 / 1544941)) (n := 12)
    (lo := (607077747 / 1000000000)) (hi := (151769437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 544941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 544941) = 1/(544941 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-151769437 / 250000000) (-607077747 / 1000000000) (Real.log (544941 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (93914137 / 250000000) ≤ -Real.log (1000000 / 1455947) ∧
    -Real.log (1000000 / 1455947) ≤ (375656549 / 1000000000) := by
  have h := checkLog_sound (w := (455947 / 2455947)) (n := 12)
    (lo := (93914137 / 250000000)) (hi := (375656549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1455947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1455947 / 1000000) = 1/(1000000 / 1455947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (93914137 / 250000000) (375656549 / 1000000000) (Real.log (1455947 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1455947 / 1000000) = -Real.log (1000000 / 1455947) := by
    rw [show ((1455947 / 1000000) : ℝ) = ((1000000 / 1455947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (60870861 / 100000000) ≤ -Real.log (544053 / 1000000) ∧
    -Real.log (544053 / 1000000) ≤ (608708611 / 1000000000) := by
  have h := checkLog_sound (w := (455947 / 1544053)) (n := 12)
    (lo := (60870861 / 100000000)) (hi := (608708611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 544053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 544053) = 1/(544053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-608708611 / 1000000000) (-60870861 / 100000000) (Real.log (544053 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (146816291 / 500000000) ≤ -Real.log (1000000 / 1341291) ∧
    -Real.log (1000000 / 1341291) ≤ (293632583 / 1000000000) := by
  have h := checkLog_sound (w := (341291 / 2341291)) (n := 12)
    (lo := (146816291 / 500000000)) (hi := (293632583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341291 / 1000000) = 1/(1000000 / 1341291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (146816291 / 500000000) (293632583 / 1000000000) (Real.log (1341291 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1341291 / 1000000) = -Real.log (1000000 / 1341291) := by
    rw [show ((1341291 / 1000000) : ℝ) = ((1000000 / 1341291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (20873671 / 50000000) ≤ -Real.log (658709 / 1000000) ∧
    -Real.log (658709 / 1000000) ≤ (417473421 / 1000000000) := by
  have h := checkLog_sound (w := (341291 / 1658709)) (n := 12)
    (lo := (20873671 / 50000000)) (hi := (417473421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 658709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 658709) = 1/(658709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-417473421 / 1000000000) (-20873671 / 50000000) (Real.log (658709 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (4596697 / 15625000) ≤ -Real.log (1000000 / 1342037) ∧
    -Real.log (1000000 / 1342037) ≤ (294188609 / 1000000000) := by
  have h := checkLog_sound (w := (342037 / 2342037)) (n := 12)
    (lo := (4596697 / 15625000)) (hi := (294188609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1342037 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1342037 / 1000000) = 1/(1000000 / 1342037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4596697 / 15625000) (294188609 / 1000000000) (Real.log (1342037 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1342037 / 1000000) = -Real.log (1000000 / 1342037) := by
    rw [show ((1342037 / 1000000) : ℝ) = ((1000000 / 1342037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (20930329 / 50000000) ≤ -Real.log (657963 / 1000000) ∧
    -Real.log (657963 / 1000000) ≤ (418606581 / 1000000000) := by
  have h := checkLog_sound (w := (342037 / 1657963)) (n := 12)
    (lo := (20930329 / 50000000)) (hi := (418606581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 657963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 657963) = 1/(657963 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-418606581 / 1000000000) (-20930329 / 50000000) (Real.log (657963 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (245531049 / 250000000) ≤ -Real.log (100000000000 / 267012208661) ∧
    -Real.log (100000000000 / 267012208661) ≤ (491062099 / 500000000) := by
  have h := checkLog_sound (w := (67012208661 / 467012208661)) (n := 12)
    (lo := (36122127 / 125000000)) (hi := (288977017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267012208661 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(267012208661 / 200000000000) = 1/(100000000000 / 267012208661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (245531049 / 250000000) (491062099 / 500000000) (Real.log (267012208661 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (267012208661 / 100000000000) = -Real.log (100000000000 / 267012208661) := by
    rw [show ((267012208661 / 100000000000) : ℝ) = ((100000000000 / 267012208661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (984365157 / 1000000000) ≤ -Real.log (125000000000 / 334514054697) ∧
    -Real.log (125000000000 / 334514054697) ≤ (984365159 / 1000000000) := by
  have h := checkLog_sound (w := (84514054697 / 584514054697)) (n := 12)
    (lo := (291217977 / 1000000000)) (hi := (145608989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334514054697 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(334514054697 / 250000000000) = 1/(125000000000 / 334514054697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (984365157 / 1000000000) (984365159 / 1000000000) (Real.log (334514054697 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (334514054697 / 125000000000) = -Real.log (125000000000 / 334514054697) := by
    rw [show ((334514054697 / 125000000000) : ℝ) = ((125000000000 / 334514054697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (355553001 / 500000000) ≤ -Real.log (15625000000 / 31816282873) ∧
    -Real.log (15625000000 / 31816282873) ≤ (177776501 / 250000000) := by
  have h := checkLog_sound (w := (566282873 / 63066282873)) (n := 12)
    (lo := (8979411 / 500000000)) (hi := (17958823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31816282873 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31816282873 / 31250000000) = 1/(15625000000 / 31816282873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (355553001 / 500000000) (177776501 / 250000000) (Real.log (31816282873 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (31816282873 / 15625000000) = -Real.log (15625000000 / 31816282873) := by
    rw [show ((31816282873 / 15625000000) : ℝ) = ((15625000000 / 31816282873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (178198797 / 250000000) ≤ -Real.log (500000000000 / 1019842301163) ∧
    -Real.log (500000000000 / 1019842301163) ≤ (71279519 / 100000000) := by
  have h := checkLog_sound (w := (19842301163 / 2019842301163)) (n := 12)
    (lo := (2456001 / 125000000)) (hi := (19648009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1019842301163 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1019842301163 / 1000000000000) = 1/(500000000000 / 1019842301163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (178198797 / 250000000) (71279519 / 100000000) (Real.log (1019842301163 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1019842301163 / 500000000000) = -Real.log (500000000000 / 1019842301163) := by
    rw [show ((1019842301163 / 500000000000) : ℝ) = ((500000000000 / 1019842301163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0180

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0181Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0181
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

theorem reflection_log_1_neg : (27416337 / 100000000) ≤ -Real.log (1024 / 1347) ∧
    -Real.log (1024 / 1347) ≤ (274163371 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 2371)) (n := 12)
    (lo := (27416337 / 100000000)) (hi := (274163371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1347 / 1024) = 1/(1024 / 1347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27416337 / 100000000) (274163371 / 1000000000) (Real.log (1347 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1347 / 1024) = -Real.log (1024 / 1347) := by
    rw [show ((1347 / 1024) : ℝ) = ((1024 / 1347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (189481959 / 500000000) ≤ -Real.log (701 / 1024) ∧
    -Real.log (701 / 1024) ≤ (378963919 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 1725)) (n := 12)
    (lo := (189481959 / 500000000)) (hi := (378963919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 701) = 1/(701 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-378963919 / 1000000000) (-189481959 / 500000000) (Real.log (701 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (273717837 / 1000000000) ≤ -Real.log (1280 / 1683) ∧
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


theorem reflection_log_3 : Bounds (273717837 / 1000000000) (136858919 / 500000000) (Real.log (1683 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1683 / 1280) = -Real.log (1280 / 1683) := by
    rw [show ((1683 / 1280) : ℝ) = ((1280 / 1683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (94527091 / 250000000) ≤ -Real.log (877 / 1280) ∧
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


theorem reflection_log_4 : Bounds (-75621673 / 200000000) (-94527091 / 250000000) (Real.log (877 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (489107099 / 1000000000) ≤ -Real.log (512 / 835) ∧
    -Real.log (512 / 835) ≤ (4891071 / 10000000) := by
  have h := checkLog_sound (w := (323 / 1347)) (n := 12)
    (lo := (489107099 / 1000000000)) (hi := (4891071 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835 / 512) = 1/(512 / 835) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (489107099 / 1000000000) (4891071 / 10000000) (Real.log (835 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (835 / 512) = -Real.log (512 / 835) := by
    rw [show ((835 / 512) : ℝ) = ((512 / 835) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (996577609 / 1000000000) ≤ -Real.log (189 / 512) ∧
    -Real.log (189 / 512) ≤ (996577611 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 445)) (n := 12)
    (lo := (303430429 / 1000000000)) (hi := (30343043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 189) = 1/(189 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-996577611 / 1000000000) (-996577609 / 1000000000) (Real.log (189 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (244194139 / 500000000) ≤ -Real.log (640 / 1043) ∧
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


theorem reflection_log_7 : Bounds (244194139 / 500000000) (488388279 / 1000000000) (Real.log (1043 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1043 / 640) = -Real.log (640 / 1043) := by
    rw [show ((1043 / 640) : ℝ) = ((640 / 1043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (496704017 / 500000000) ≤ -Real.log (237 / 640) ∧
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


theorem reflection_log_8 : Bounds (-248352009 / 250000000) (-496704017 / 500000000) (Real.log (237 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (187218677 / 500000000) ≤ -Real.log (1000000 / 1454173) ∧
    -Real.log (1000000 / 1454173) ≤ (74887471 / 200000000) := by
  have h := checkLog_sound (w := (454173 / 2454173)) (n := 12)
    (lo := (187218677 / 500000000)) (hi := (74887471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1454173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1454173 / 1000000) = 1/(1000000 / 1454173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (187218677 / 500000000) (74887471 / 200000000) (Real.log (1454173 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1454173 / 1000000) = -Real.log (1000000 / 1454173) := by
    rw [show ((1454173 / 1000000) : ℝ) = ((1000000 / 1454173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (605453203 / 1000000000) ≤ -Real.log (545827 / 1000000) ∧
    -Real.log (545827 / 1000000) ≤ (151363301 / 250000000) := by
  have h := checkLog_sound (w := (454173 / 1545827)) (n := 12)
    (lo := (605453203 / 1000000000)) (hi := (151363301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 545827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 545827) = 1/(545827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-151363301 / 250000000) (-605453203 / 1000000000) (Real.log (545827 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (11720223 / 31250000) ≤ -Real.log (50000 / 72753) ∧
    -Real.log (50000 / 72753) ≤ (375047137 / 1000000000) := by
  have h := checkLog_sound (w := (22753 / 122753)) (n := 12)
    (lo := (11720223 / 31250000)) (hi := (375047137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72753 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72753 / 50000) = 1/(50000 / 72753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (11720223 / 31250000) (375047137 / 1000000000) (Real.log (72753 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (72753 / 50000) = -Real.log (50000 / 72753) := by
    rw [show ((72753 / 50000) : ℝ) = ((50000 / 72753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (303539791 / 500000000) ≤ -Real.log (27247 / 50000) ∧
    -Real.log (27247 / 50000) ≤ (607079583 / 1000000000) := by
  have h := checkLog_sound (w := (22753 / 77247)) (n := 12)
    (lo := (303539791 / 500000000)) (hi := (607079583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 27247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 27247) = 1/(27247 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-607079583 / 1000000000) (-303539791 / 500000000) (Real.log (27247 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (293076993 / 1000000000) ≤ -Real.log (500000 / 670273) ∧
    -Real.log (500000 / 670273) ≤ (146538497 / 500000000) := by
  have h := checkLog_sound (w := (170273 / 1170273)) (n := 12)
    (lo := (293076993 / 1000000000)) (hi := (146538497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670273 / 500000) = 1/(500000 / 670273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (293076993 / 1000000000) (146538497 / 500000000) (Real.log (670273 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (670273 / 500000) = -Real.log (500000 / 670273) := by
    rw [show ((670273 / 500000) : ℝ) = ((500000 / 670273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (416343059 / 1000000000) ≤ -Real.log (329727 / 500000) ∧
    -Real.log (329727 / 500000) ≤ (20817153 / 50000000) := by
  have h := checkLog_sound (w := (170273 / 829727)) (n := 12)
    (lo := (416343059 / 1000000000)) (hi := (20817153 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 329727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 329727) = 1/(329727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-20817153 / 50000000) (-416343059 / 1000000000) (Real.log (329727 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (18352083 / 62500000) ≤ -Real.log (250000 / 335323) ∧
    -Real.log (250000 / 335323) ≤ (293633329 / 1000000000) := by
  have h := checkLog_sound (w := (85323 / 585323)) (n := 12)
    (lo := (18352083 / 62500000)) (hi := (293633329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335323 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335323 / 250000) = 1/(250000 / 335323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (18352083 / 62500000) (293633329 / 1000000000) (Real.log (335323 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (335323 / 250000) = -Real.log (250000 / 335323) := by
    rw [show ((335323 / 250000) : ℝ) = ((250000 / 335323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (208737469 / 500000000) ≤ -Real.log (164677 / 250000) ∧
    -Real.log (164677 / 250000) ≤ (417474939 / 1000000000) := by
  have h := checkLog_sound (w := (85323 / 414677)) (n := 12)
    (lo := (208737469 / 500000000)) (hi := (417474939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 164677) = 1/(164677 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-417474939 / 1000000000) (-208737469 / 500000000) (Real.log (164677 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (244972639 / 250000000) ≤ -Real.log (500000000000 / 1332082326451) ∧
    -Real.log (500000000000 / 1332082326451) ≤ (489945279 / 500000000) := by
  have h := checkLog_sound (w := (332082326451 / 2332082326451)) (n := 12)
    (lo := (17921461 / 62500000)) (hi := (286743377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1332082326451 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1332082326451 / 1000000000000) = 1/(500000000000 / 1332082326451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (244972639 / 250000000) (489945279 / 500000000) (Real.log (1332082326451 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1332082326451 / 500000000000) = -Real.log (500000000000 / 1332082326451) := by
    rw [show ((1332082326451 / 500000000000) : ℝ) = ((500000000000 / 1332082326451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (491063359 / 500000000) ≤ -Real.log (500000000000 / 1335064410761) ∧
    -Real.log (500000000000 / 1335064410761) ≤ (1534573 / 1562500) := by
  have h := checkLog_sound (w := (335064410761 / 2335064410761)) (n := 12)
    (lo := (144489769 / 500000000)) (hi := (288979539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335064410761 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1335064410761 / 1000000000000) = 1/(500000000000 / 1335064410761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (491063359 / 500000000) (1534573 / 1562500) (Real.log (1335064410761 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1335064410761 / 500000000000) = -Real.log (500000000000 / 1335064410761) := by
    rw [show ((1335064410761 / 500000000000) : ℝ) = ((500000000000 / 1335064410761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (177355013 / 250000000) ≤ -Real.log (20000000000 / 40656239859) ∧
    -Real.log (20000000000 / 40656239859) ≤ (354710027 / 500000000) := by
  have h := checkLog_sound (w := (656239859 / 80656239859)) (n := 12)
    (lo := (2034109 / 125000000)) (hi := (16272873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40656239859 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40656239859 / 40000000000) = 1/(20000000000 / 40656239859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (177355013 / 250000000) (354710027 / 500000000) (Real.log (40656239859 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (40656239859 / 20000000000) = -Real.log (20000000000 / 40656239859) := by
    rw [show ((40656239859 / 20000000000) : ℝ) = ((20000000000 / 40656239859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (355554133 / 500000000) ≤ -Real.log (62500000000 / 127265419579) ∧
    -Real.log (62500000000 / 127265419579) ≤ (177777067 / 250000000) := by
  have h := checkLog_sound (w := (2265419579 / 252265419579)) (n := 12)
    (lo := (8980543 / 500000000)) (hi := (17961087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127265419579 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(127265419579 / 125000000000) = 1/(62500000000 / 127265419579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (355554133 / 500000000) (177777067 / 250000000) (Real.log (127265419579 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (127265419579 / 62500000000) = -Real.log (62500000000 / 127265419579) := by
    rw [show ((127265419579 / 62500000000) : ℝ) = ((62500000000 / 127265419579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0181

end


