-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0114__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0114__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:32:11.283621+00:00
-- url     : https://prove2.me/theorems/bb33bf78-38ee-4066-a72f-73b767d94655
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0116)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0116)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0116) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0114 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0115, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0116).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0114__3_q01

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0116 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7424_neg : (11573189 / 100000000) ≤ -Real.log (445357 / 500000) ∧
    -Real.log (445357 / 500000) ≤ (115731891 / 1000000000) := by
  have h := checkLog_sound (w := (54643 / 945357)) (n := 12)
    (lo := (11573189 / 100000000)) (hi := (115731891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 445357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 445357) = 1/(445357 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7424 : Bounds (-115731891 / 1000000000) (-11573189 / 100000000) (Real.log (445357 / 500000)) := by
  have h := reflection_log_7424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7425_neg : (480613 / 40000000) ≤ -Real.log (247014142551 / 250000000000) ∧
    -Real.log (247014142551 / 250000000000) ≤ (6007663 / 500000000) := by
  have h := checkLog_sound (w := (2985857449 / 497014142551)) (n := 12)
    (lo := (480613 / 40000000)) (hi := (6007663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247014142551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247014142551) = 1/(247014142551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7425 : Bounds (-6007663 / 500000000) (-480613 / 40000000) (Real.log (247014142551 / 250000000000)) := by
  have h := reflection_log_7425_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7426_neg : (11911143 / 1000000000) ≤ -Real.log (247039878351 / 250000000000) ∧
    -Real.log (247039878351 / 250000000000) ≤ (1488893 / 125000000) := by
  have h := checkLog_sound (w := (2960121649 / 497039878351)) (n := 12)
    (lo := (11911143 / 1000000000)) (hi := (1488893 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247039878351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247039878351) = 1/(247039878351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7426 : Bounds (-1488893 / 125000000) (-11911143 / 1000000000) (Real.log (247039878351 / 250000000000)) := by
  have h := reflection_log_7426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7427_neg : (109246547 / 500000000) ≤ -Real.log (20000000000 / 24884008501) ∧
    -Real.log (20000000000 / 24884008501) ≤ (43698619 / 200000000) := by
  have h := checkLog_sound (w := (4884008501 / 44884008501)) (n := 12)
    (lo := (109246547 / 500000000)) (hi := (43698619 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24884008501 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24884008501 / 20000000000) = 1/(20000000000 / 24884008501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7427 : Bounds (109246547 / 500000000) (43698619 / 200000000) (Real.log (24884008501 / 20000000000)) := by
  have h := reflection_log_7427_neg
  have he : Real.log (24884008501 / 20000000000) = -Real.log (20000000000 / 24884008501) := by
    rw [show ((24884008501 / 20000000000) : ℝ) = ((20000000000 / 24884008501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7428_neg : (43889691 / 200000000) ≤ -Real.log (500000000000 / 622694826847) ∧
    -Real.log (500000000000 / 622694826847) ≤ (27431057 / 125000000) := by
  have h := checkLog_sound (w := (122694826847 / 1122694826847)) (n := 12)
    (lo := (43889691 / 200000000)) (hi := (27431057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622694826847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(622694826847 / 500000000000) = 1/(500000000000 / 622694826847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7428 : Bounds (43889691 / 200000000) (27431057 / 125000000) (Real.log (622694826847 / 500000000000)) := by
  have h := reflection_log_7428_neg
  have he : Real.log (622694826847 / 500000000000) = -Real.log (500000000000 / 622694826847) := by
    rw [show ((622694826847 / 500000000000) : ℝ) = ((500000000000 / 622694826847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7429_neg : (219456521 / 500000000) ≤ -Real.log (500000000000 / 775510204081) ∧
    -Real.log (500000000000 / 775510204081) ≤ (438913043 / 1000000000) := by
  have h := checkLog_sound (w := (275510204081 / 1275510204081)) (n := 12)
    (lo := (219456521 / 500000000)) (hi := (438913043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775510204081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775510204081 / 500000000000) = 1/(500000000000 / 775510204081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7429 : Bounds (219456521 / 500000000) (438913043 / 1000000000) (Real.log (775510204081 / 500000000000)) := by
  have h := reflection_log_7429_neg
  have he : Real.log (775510204081 / 500000000000) = -Real.log (500000000000 / 775510204081) := by
    rw [show ((775510204081 / 500000000000) : ℝ) = ((500000000000 / 775510204081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7430_neg : (4399621 / 10000000) ≤ -Real.log (62500000000 / 97040523293) ∧
    -Real.log (62500000000 / 97040523293) ≤ (439962101 / 1000000000) := by
  have h := checkLog_sound (w := (34540523293 / 159540523293)) (n := 12)
    (lo := (4399621 / 10000000)) (hi := (439962101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97040523293 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97040523293 / 62500000000) = 1/(62500000000 / 97040523293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7430 : Bounds (4399621 / 10000000) (439962101 / 1000000000) (Real.log (97040523293 / 62500000000)) := by
  have h := reflection_log_7430_neg
  have he : Real.log (97040523293 / 62500000000) = -Real.log (62500000000 / 97040523293) := by
    rw [show ((97040523293 / 62500000000) : ℝ) = ((62500000000 / 97040523293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7431_neg : (98194407 / 500000000) ≤ -Real.log (1000 / 1217) ∧
    -Real.log (1000 / 1217) ≤ (39277763 / 200000000) := by
  have h := checkLog_sound (w := (217 / 2217)) (n := 12)
    (lo := (98194407 / 500000000)) (hi := (39277763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217 / 1000) = 1/(1000 / 1217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7431 : Bounds (98194407 / 500000000) (39277763 / 200000000) (Real.log (1217 / 1000)) := by
  have h := reflection_log_7431_neg
  have he : Real.log (1217 / 1000) = -Real.log (1000 / 1217) := by
    rw [show ((1217 / 1000) : ℝ) = ((1000 / 1217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7432_neg : (122311291 / 500000000) ≤ -Real.log (783 / 1000) ∧
    -Real.log (783 / 1000) ≤ (244622583 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1783)) (n := 12)
    (lo := (122311291 / 500000000)) (hi := (244622583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 783) = 1/(783 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7432 : Bounds (-244622583 / 1000000000) (-122311291 / 500000000) (Real.log (783 / 1000)) := by
  have h := reflection_log_7432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7433_neg : (13561 / 62500000) ≤ -Real.log (1000000 / 1000217) ∧
    -Real.log (1000000 / 1000217) ≤ (216977 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 2000217)) (n := 12)
    (lo := (13561 / 62500000)) (hi := (216977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000217 / 1000000) = 1/(1000000 / 1000217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7433 : Bounds (13561 / 62500000) (216977 / 1000000000) (Real.log (1000217 / 1000000)) := by
  have h := reflection_log_7433_neg
  have he : Real.log (1000217 / 1000000) = -Real.log (1000000 / 1000217) := by
    rw [show ((1000217 / 1000000) : ℝ) = ((1000000 / 1000217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7434_neg : (217023 / 1000000000) ≤ -Real.log (999783 / 1000000) ∧
    -Real.log (999783 / 1000000) ≤ (3391 / 15625000) := by
  have h := checkLog_sound (w := (217 / 1999783)) (n := 12)
    (lo := (217023 / 1000000000)) (hi := (3391 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999783) = 1/(999783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7434 : Bounds (-3391 / 15625000) (-217023 / 1000000000) (Real.log (999783 / 1000000)) := by
  have h := reflection_log_7434_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7435_neg : (51760913 / 500000000) ≤ -Real.log (100000 / 110907) ∧
    -Real.log (100000 / 110907) ≤ (103521827 / 1000000000) := by
  have h := checkLog_sound (w := (10907 / 210907)) (n := 12)
    (lo := (51760913 / 500000000)) (hi := (103521827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110907 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(110907 / 100000) = 1/(100000 / 110907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7435 : Bounds (51760913 / 500000000) (103521827 / 1000000000) (Real.log (110907 / 100000)) := by
  have h := reflection_log_7435_neg
  have he : Real.log (110907 / 100000) = -Real.log (100000 / 110907) := by
    rw [show ((110907 / 100000) : ℝ) = ((100000 / 110907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7436_neg : (57744709 / 500000000) ≤ -Real.log (89093 / 100000) ∧
    -Real.log (89093 / 100000) ≤ (115489419 / 1000000000) := by
  have h := checkLog_sound (w := (10907 / 189093)) (n := 12)
    (lo := (57744709 / 500000000)) (hi := (115489419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 89093) = 1/(89093 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7436 : Bounds (-115489419 / 1000000000) (-57744709 / 500000000) (Real.log (89093 / 100000)) := by
  have h := reflection_log_7436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7437_neg : (103947317 / 1000000000) ≤ -Real.log (500000 / 554771) ∧
    -Real.log (500000 / 554771) ≤ (51973659 / 500000000) := by
  have h := checkLog_sound (w := (54771 / 1054771)) (n := 12)
    (lo := (103947317 / 1000000000)) (hi := (51973659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((554771 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(554771 / 500000) = 1/(500000 / 554771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7437 : Bounds (103947317 / 1000000000) (51973659 / 500000000) (Real.log (554771 / 500000)) := by
  have h := reflection_log_7437_neg
  have he : Real.log (554771 / 500000) = -Real.log (500000 / 554771) := by
    rw [show ((554771 / 500000) : ℝ) = ((500000 / 554771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7438_neg : (116019341 / 1000000000) ≤ -Real.log (445229 / 500000) ∧
    -Real.log (445229 / 500000) ≤ (58009671 / 500000000) := by
  have h := checkLog_sound (w := (54771 / 945229)) (n := 12)
    (lo := (116019341 / 1000000000)) (hi := (58009671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 445229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 445229) = 1/(445229 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7438 : Bounds (-58009671 / 500000000) (-116019341 / 1000000000) (Real.log (445229 / 500000)) := by
  have h := reflection_log_7438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7439_neg : (1509003 / 125000000) ≤ -Real.log (247000137559 / 250000000000) ∧
    -Real.log (247000137559 / 250000000000) ≤ (482881 / 40000000) := by
  have h := checkLog_sound (w := (2999862441 / 497000137559)) (n := 12)
    (lo := (1509003 / 125000000)) (hi := (482881 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247000137559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247000137559) = 1/(247000137559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7439 : Bounds (-482881 / 40000000) (-1509003 / 125000000) (Real.log (247000137559 / 250000000000)) := by
  have h := reflection_log_7439_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7440_neg : (11967591 / 1000000000) ≤ -Real.log (9881037351 / 10000000000) ∧
    -Real.log (9881037351 / 10000000000) ≤ (1495949 / 125000000) := by
  have h := checkLog_sound (w := (118962649 / 19881037351)) (n := 12)
    (lo := (11967591 / 1000000000)) (hi := (1495949 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9881037351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9881037351) = 1/(9881037351 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7440 : Bounds (-1495949 / 125000000) (-11967591 / 1000000000) (Real.log (9881037351 / 10000000000)) := by
  have h := reflection_log_7440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7441_neg : (54752811 / 250000000) ≤ -Real.log (500000000000 / 622422637019) ∧
    -Real.log (500000000000 / 622422637019) ≤ (43802249 / 200000000) := by
  have h := checkLog_sound (w := (122422637019 / 1122422637019)) (n := 12)
    (lo := (54752811 / 250000000)) (hi := (43802249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622422637019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(622422637019 / 500000000000) = 1/(500000000000 / 622422637019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7441 : Bounds (54752811 / 250000000) (43802249 / 200000000) (Real.log (622422637019 / 500000000000)) := by
  have h := reflection_log_7441_neg
  have he : Real.log (622422637019 / 500000000000) = -Real.log (500000000000 / 622422637019) := by
    rw [show ((622422637019 / 500000000000) : ℝ) = ((500000000000 / 622422637019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7442_neg : (219966659 / 1000000000) ≤ -Real.log (250000000000 / 311508796597) ∧
    -Real.log (250000000000 / 311508796597) ≤ (10998333 / 50000000) := by
  have h := checkLog_sound (w := (61508796597 / 561508796597)) (n := 12)
    (lo := (219966659 / 1000000000)) (hi := (10998333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311508796597 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311508796597 / 250000000000) = 1/(250000000000 / 311508796597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7442 : Bounds (219966659 / 1000000000) (10998333 / 50000000) (Real.log (311508796597 / 250000000000)) := by
  have h := reflection_log_7442_neg
  have he : Real.log (311508796597 / 250000000000) = -Real.log (250000000000 / 311508796597) := by
    rw [show ((311508796597 / 250000000000) : ℝ) = ((250000000000 / 311508796597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7443_neg : (4399621 / 10000000) ≤ -Real.log (500000000000 / 776324186343) ∧
    -Real.log (500000000000 / 776324186343) ≤ (439962101 / 1000000000) := by
  have h := checkLog_sound (w := (276324186343 / 1276324186343)) (n := 12)
    (lo := (4399621 / 10000000)) (hi := (439962101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776324186343 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776324186343 / 500000000000) = 1/(500000000000 / 776324186343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7443 : Bounds (4399621 / 10000000) (439962101 / 1000000000) (Real.log (776324186343 / 500000000000)) := by
  have h := reflection_log_7443_neg
  have he : Real.log (776324186343 / 500000000000) = -Real.log (500000000000 / 776324186343) := by
    rw [show ((776324186343 / 500000000000) : ℝ) = ((500000000000 / 776324186343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7444_neg : (110252849 / 250000000) ≤ -Real.log (250000000000 / 388569604087) ∧
    -Real.log (250000000000 / 388569604087) ≤ (441011397 / 1000000000) := by
  have h := checkLog_sound (w := (138569604087 / 638569604087)) (n := 12)
    (lo := (110252849 / 250000000)) (hi := (441011397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388569604087 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388569604087 / 250000000000) = 1/(250000000000 / 388569604087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7444 : Bounds (110252849 / 250000000) (441011397 / 1000000000) (Real.log (388569604087 / 250000000000)) := by
  have h := reflection_log_7444_neg
  have he : Real.log (388569604087 / 250000000000) = -Real.log (250000000000 / 388569604087) := by
    rw [show ((388569604087 / 250000000000) : ℝ) = ((250000000000 / 388569604087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7445_neg : (7871983 / 40000000) ≤ -Real.log (400 / 487) ∧
    -Real.log (400 / 487) ≤ (24599947 / 125000000) := by
  have h := checkLog_sound (w := (87 / 887)) (n := 12)
    (lo := (7871983 / 40000000)) (hi := (24599947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487 / 400) = 1/(400 / 487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7445 : Bounds (7871983 / 40000000) (24599947 / 125000000) (Real.log (487 / 400)) := by
  have h := reflection_log_7445_neg
  have he : Real.log (487 / 400) = -Real.log (400 / 487) := by
    rw [show ((487 / 400) : ℝ) = ((400 / 487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7446_neg : (61315339 / 250000000) ≤ -Real.log (313 / 400) ∧
    -Real.log (313 / 400) ≤ (245261357 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 713)) (n := 12)
    (lo := (61315339 / 250000000)) (hi := (245261357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 313) = 1/(313 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7446 : Bounds (-245261357 / 1000000000) (-61315339 / 250000000) (Real.log (313 / 400)) := by
  have h := reflection_log_7446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7447_neg : (54369 / 250000000) ≤ -Real.log (400000 / 400087) ∧
    -Real.log (400000 / 400087) ≤ (217477 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 800087)) (n := 12)
    (lo := (54369 / 250000000)) (hi := (217477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400087 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400087 / 400000) = 1/(400000 / 400087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7447 : Bounds (54369 / 250000000) (217477 / 1000000000) (Real.log (400087 / 400000)) := by
  have h := reflection_log_7447_neg
  have he : Real.log (400087 / 400000) = -Real.log (400000 / 400087) := by
    rw [show ((400087 / 400000) : ℝ) = ((400000 / 400087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7448_neg : (217523 / 1000000000) ≤ -Real.log (399913 / 400000) ∧
    -Real.log (399913 / 400000) ≤ (54381 / 250000000) := by
  have h := checkLog_sound (w := (87 / 799913)) (n := 12)
    (lo := (217523 / 1000000000)) (hi := (54381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399913) = 1/(399913 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7448 : Bounds (-54381 / 250000000) (-217523 / 1000000000) (Real.log (399913 / 400000)) := by
  have h := reflection_log_7448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7449_neg : (103752623 / 1000000000) ≤ -Real.log (500000 / 554663) ∧
    -Real.log (500000 / 554663) ≤ (6484539 / 62500000) := by
  have h := checkLog_sound (w := (54663 / 1054663)) (n := 12)
    (lo := (103752623 / 1000000000)) (hi := (6484539 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((554663 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(554663 / 500000) = 1/(500000 / 554663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7449 : Bounds (103752623 / 1000000000) (6484539 / 62500000) (Real.log (554663 / 500000)) := by
  have h := reflection_log_7449_neg
  have he : Real.log (554663 / 500000) = -Real.log (500000 / 554663) := by
    rw [show ((554663 / 500000) : ℝ) = ((500000 / 554663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7450_neg : (115776799 / 1000000000) ≤ -Real.log (445337 / 500000) ∧
    -Real.log (445337 / 500000) ≤ (144721 / 1250000) := by
  have h := checkLog_sound (w := (54663 / 945337)) (n := 12)
    (lo := (115776799 / 1000000000)) (hi := (144721 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 445337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 445337) = 1/(445337 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7450 : Bounds (-144721 / 1250000) (-115776799 / 1000000000) (Real.log (445337 / 500000)) := by
  have h := reflection_log_7450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7451_neg : (104178917 / 1000000000) ≤ -Real.log (1000000 / 1109799) ∧
    -Real.log (1000000 / 1109799) ≤ (52089459 / 500000000) := by
  have h := checkLog_sound (w := (109799 / 2109799)) (n := 12)
    (lo := (104178917 / 1000000000)) (hi := (52089459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1109799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1109799 / 1000000) = 1/(1000000 / 1109799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7451 : Bounds (104178917 / 1000000000) (52089459 / 500000000) (Real.log (1109799 / 1000000)) := by
  have h := reflection_log_7451_neg
  have he : Real.log (1109799 / 1000000) = -Real.log (1000000 / 1109799) := by
    rw [show ((1109799 / 1000000) : ℝ) = ((1000000 / 1109799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7452_neg : (116307999 / 1000000000) ≤ -Real.log (890201 / 1000000) ∧
    -Real.log (890201 / 1000000) ≤ (29077 / 250000) := by
  have h := checkLog_sound (w := (109799 / 1890201)) (n := 12)
    (lo := (116307999 / 1000000000)) (hi := (29077 / 250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 890201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 890201) = 1/(890201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7452 : Bounds (-29077 / 250000) (-116307999 / 1000000000) (Real.log (890201 / 1000000)) := by
  have h := reflection_log_7452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7453_neg : (12129081 / 1000000000) ≤ -Real.log (987944179599 / 1000000000000) ∧
    -Real.log (987944179599 / 1000000000000) ≤ (6064541 / 500000000) := by
  have h := checkLog_sound (w := (12055820401 / 1987944179599)) (n := 12)
    (lo := (12129081 / 1000000000)) (hi := (6064541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987944179599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987944179599) = 1/(987944179599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7453 : Bounds (-6064541 / 500000000) (-12129081 / 1000000000) (Real.log (987944179599 / 1000000000000)) := by
  have h := reflection_log_7453_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7454_neg : (480967 / 40000000) ≤ -Real.log (247011956431 / 250000000000) ∧
    -Real.log (247011956431 / 250000000000) ≤ (751511 / 62500000) := by
  have h := checkLog_sound (w := (2988043569 / 497011956431)) (n := 12)
    (lo := (480967 / 40000000)) (hi := (751511 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247011956431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247011956431) = 1/(247011956431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7454 : Bounds (-751511 / 62500000) (-480967 / 40000000) (Real.log (247011956431 / 250000000000)) := by
  have h := reflection_log_7454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7455_neg : (219529423 / 1000000000) ≤ -Real.log (500000000000 / 622745246857) ∧
    -Real.log (500000000000 / 622745246857) ≤ (13720589 / 62500000) := by
  have h := checkLog_sound (w := (122745246857 / 1122745246857)) (n := 12)
    (lo := (219529423 / 1000000000)) (hi := (13720589 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622745246857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(622745246857 / 500000000000) = 1/(500000000000 / 622745246857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7455 : Bounds (219529423 / 1000000000) (13720589 / 62500000) (Real.log (622745246857 / 500000000000)) := by
  have h := reflection_log_7455_neg
  have he : Real.log (622745246857 / 500000000000) = -Real.log (500000000000 / 622745246857) := by
    rw [show ((622745246857 / 500000000000) : ℝ) = ((500000000000 / 622745246857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7456_neg : (55121729 / 250000000) ≤ -Real.log (125000000000 / 155835451769) ∧
    -Real.log (125000000000 / 155835451769) ≤ (220486917 / 1000000000) := by
  have h := checkLog_sound (w := (30835451769 / 280835451769)) (n := 12)
    (lo := (55121729 / 250000000)) (hi := (220486917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155835451769 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155835451769 / 125000000000) = 1/(125000000000 / 155835451769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7456 : Bounds (55121729 / 250000000) (220486917 / 1000000000) (Real.log (155835451769 / 125000000000)) := by
  have h := reflection_log_7456_neg
  have he : Real.log (155835451769 / 125000000000) = -Real.log (125000000000 / 155835451769) := by
    rw [show ((155835451769 / 125000000000) : ℝ) = ((125000000000 / 155835451769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7457_neg : (110252849 / 250000000) ≤ -Real.log (500000000000 / 777139208173) ∧
    -Real.log (500000000000 / 777139208173) ≤ (441011397 / 1000000000) := by
  have h := checkLog_sound (w := (277139208173 / 1277139208173)) (n := 12)
    (lo := (110252849 / 250000000)) (hi := (441011397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777139208173 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777139208173 / 500000000000) = 1/(500000000000 / 777139208173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7457 : Bounds (110252849 / 250000000) (441011397 / 1000000000) (Real.log (777139208173 / 500000000000)) := by
  have h := reflection_log_7457_neg
  have he : Real.log (777139208173 / 500000000000) = -Real.log (500000000000 / 777139208173) := by
    rw [show ((777139208173 / 500000000000) : ℝ) = ((500000000000 / 777139208173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7458_neg : (110515233 / 250000000) ≤ -Real.log (250000000000 / 388977635783) ∧
    -Real.log (250000000000 / 388977635783) ≤ (442060933 / 1000000000) := by
  have h := checkLog_sound (w := (138977635783 / 638977635783)) (n := 12)
    (lo := (110515233 / 250000000)) (hi := (442060933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388977635783 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388977635783 / 250000000000) = 1/(250000000000 / 388977635783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7458 : Bounds (110515233 / 250000000) (442060933 / 1000000000) (Real.log (388977635783 / 250000000000)) := by
  have h := reflection_log_7458_neg
  have he : Real.log (388977635783 / 250000000000) = -Real.log (250000000000 / 388977635783) := by
    rw [show ((388977635783 / 250000000000) : ℝ) = ((250000000000 / 388977635783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7459_neg : (197210169 / 1000000000) ≤ -Real.log (500 / 609) ∧
    -Real.log (500 / 609) ≤ (19721017 / 100000000) := by
  have h := checkLog_sound (w := (109 / 1109)) (n := 12)
    (lo := (197210169 / 1000000000)) (hi := (19721017 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609 / 500) = 1/(500 / 609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7459 : Bounds (197210169 / 1000000000) (19721017 / 100000000) (Real.log (609 / 500)) := by
  have h := reflection_log_7459_neg
  have he : Real.log (609 / 500) = -Real.log (500 / 609) := by
    rw [show ((609 / 500) : ℝ) = ((500 / 609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7460_neg : (122950269 / 500000000) ≤ -Real.log (391 / 500) ∧
    -Real.log (391 / 500) ≤ (245900539 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 891)) (n := 12)
    (lo := (122950269 / 500000000)) (hi := (245900539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 391) = 1/(391 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7460 : Bounds (-245900539 / 1000000000) (-122950269 / 500000000) (Real.log (391 / 500)) := by
  have h := reflection_log_7460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7461_neg : (27247 / 125000000) ≤ -Real.log (500000 / 500109) ∧
    -Real.log (500000 / 500109) ≤ (217977 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1000109)) (n := 12)
    (lo := (27247 / 125000000)) (hi := (217977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500109 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500109 / 500000) = 1/(500000 / 500109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7461 : Bounds (27247 / 125000000) (217977 / 1000000000) (Real.log (500109 / 500000)) := by
  have h := reflection_log_7461_neg
  have he : Real.log (500109 / 500000) = -Real.log (500000 / 500109) := by
    rw [show ((500109 / 500000) : ℝ) = ((500000 / 500109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7462_neg : (218023 / 1000000000) ≤ -Real.log (499891 / 500000) ∧
    -Real.log (499891 / 500000) ≤ (27253 / 125000000) := by
  have h := checkLog_sound (w := (109 / 999891)) (n := 12)
    (lo := (218023 / 1000000000)) (hi := (27253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499891) = 1/(499891 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7462 : Bounds (-27253 / 125000000) (-218023 / 1000000000) (Real.log (499891 / 500000)) := by
  have h := reflection_log_7462_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7463_neg : (103984269 / 1000000000) ≤ -Real.log (1000000 / 1109583) ∧
    -Real.log (1000000 / 1109583) ≤ (10398427 / 100000000) := by
  have h := checkLog_sound (w := (109583 / 2109583)) (n := 12)
    (lo := (103984269 / 1000000000)) (hi := (10398427 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1109583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1109583 / 1000000) = 1/(1000000 / 1109583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7463 : Bounds (103984269 / 1000000000) (10398427 / 100000000) (Real.log (1109583 / 1000000)) := by
  have h := reflection_log_7463_neg
  have he : Real.log (1109583 / 1000000) = -Real.log (1000000 / 1109583) := by
    rw [show ((1109583 / 1000000) : ℝ) = ((1000000 / 1109583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7464_neg : (58032693 / 500000000) ≤ -Real.log (890417 / 1000000) ∧
    -Real.log (890417 / 1000000) ≤ (116065387 / 1000000000) := by
  have h := checkLog_sound (w := (109583 / 1890417)) (n := 12)
    (lo := (58032693 / 500000000)) (hi := (116065387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 890417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 890417) = 1/(890417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7464 : Bounds (-116065387 / 1000000000) (-58032693 / 500000000) (Real.log (890417 / 1000000)) := by
  have h := reflection_log_7464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7465_neg : (3262827 / 31250000) ≤ -Real.log (125000 / 138757) ∧
    -Real.log (125000 / 138757) ≤ (20882093 / 200000000) := by
  have h := checkLog_sound (w := (13757 / 263757)) (n := 12)
    (lo := (3262827 / 31250000)) (hi := (20882093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138757 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138757 / 125000) = 1/(125000 / 138757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7465 : Bounds (3262827 / 31250000) (20882093 / 200000000) (Real.log (138757 / 125000)) := by
  have h := reflection_log_7465_neg
  have he : Real.log (138757 / 125000) = -Real.log (125000 / 138757) := by
    rw [show ((138757 / 125000) : ℝ) = ((125000 / 138757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7466_neg : (116596739 / 1000000000) ≤ -Real.log (111243 / 125000) ∧
    -Real.log (111243 / 125000) ≤ (5829837 / 50000000) := by
  have h := checkLog_sound (w := (13757 / 236243)) (n := 12)
    (lo := (116596739 / 1000000000)) (hi := (5829837 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 111243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 111243) = 1/(111243 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7466 : Bounds (-5829837 / 50000000) (-116596739 / 1000000000) (Real.log (111243 / 125000)) := by
  have h := reflection_log_7466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7467_neg : (487451 / 40000000) ≤ -Real.log (15435744951 / 15625000000) ∧
    -Real.log (15435744951 / 15625000000) ≤ (3046569 / 250000000) := by
  have h := checkLog_sound (w := (189255049 / 31060744951)) (n := 12)
    (lo := (487451 / 40000000)) (hi := (3046569 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15435744951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15435744951) = 1/(15435744951 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7467 : Bounds (-3046569 / 250000000) (-487451 / 40000000) (Real.log (15435744951 / 15625000000)) := by
  have h := reflection_log_7467_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7468_neg : (12081117 / 1000000000) ≤ -Real.log (987991566111 / 1000000000000) ∧
    -Real.log (987991566111 / 1000000000000) ≤ (6040559 / 500000000) := by
  have h := checkLog_sound (w := (12008433889 / 1987991566111)) (n := 12)
    (lo := (12081117 / 1000000000)) (hi := (6040559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987991566111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987991566111) = 1/(987991566111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7468 : Bounds (-6040559 / 500000000) (-12081117 / 1000000000) (Real.log (987991566111 / 1000000000000)) := by
  have h := reflection_log_7468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7469_neg : (44009931 / 200000000) ≤ -Real.log (500000000000 / 623069303483) ∧
    -Real.log (500000000000 / 623069303483) ≤ (27506207 / 125000000) := by
  have h := checkLog_sound (w := (123069303483 / 1123069303483)) (n := 12)
    (lo := (44009931 / 200000000)) (hi := (27506207 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623069303483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623069303483 / 500000000000) = 1/(500000000000 / 623069303483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7469 : Bounds (44009931 / 200000000) (27506207 / 125000000) (Real.log (623069303483 / 500000000000)) := by
  have h := reflection_log_7469_neg
  have he : Real.log (623069303483 / 500000000000) = -Real.log (500000000000 / 623069303483) := by
    rw [show ((623069303483 / 500000000000) : ℝ) = ((500000000000 / 623069303483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7470_neg : (55251801 / 250000000) ≤ -Real.log (500000000000 / 623666208211) ∧
    -Real.log (500000000000 / 623666208211) ≤ (44201441 / 200000000) := by
  have h := checkLog_sound (w := (123666208211 / 1123666208211)) (n := 12)
    (lo := (55251801 / 250000000)) (hi := (44201441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623666208211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623666208211 / 500000000000) = 1/(500000000000 / 623666208211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7470 : Bounds (55251801 / 250000000) (44201441 / 200000000) (Real.log (623666208211 / 500000000000)) := by
  have h := reflection_log_7470_neg
  have he : Real.log (623666208211 / 500000000000) = -Real.log (500000000000 / 623666208211) := by
    rw [show ((623666208211 / 500000000000) : ℝ) = ((500000000000 / 623666208211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7471_neg : (110515233 / 250000000) ≤ -Real.log (100000000000 / 155591054313) ∧
    -Real.log (100000000000 / 155591054313) ≤ (442060933 / 1000000000) := by
  have h := checkLog_sound (w := (55591054313 / 255591054313)) (n := 12)
    (lo := (110515233 / 250000000)) (hi := (442060933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155591054313 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155591054313 / 100000000000) = 1/(100000000000 / 155591054313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7471 : Bounds (110515233 / 250000000) (442060933 / 1000000000) (Real.log (155591054313 / 100000000000)) := by
  have h := reflection_log_7471_neg
  have he : Real.log (155591054313 / 100000000000) = -Real.log (100000000000 / 155591054313) := by
    rw [show ((155591054313 / 100000000000) : ℝ) = ((100000000000 / 155591054313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7472_neg : (443110707 / 1000000000) ≤ -Real.log (500000000000 / 778772378517) ∧
    -Real.log (500000000000 / 778772378517) ≤ (110777677 / 250000000) := by
  have h := checkLog_sound (w := (278772378517 / 1278772378517)) (n := 12)
    (lo := (443110707 / 1000000000)) (hi := (110777677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((778772378517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(778772378517 / 500000000000) = 1/(500000000000 / 778772378517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7472 : Bounds (443110707 / 1000000000) (110777677 / 250000000) (Real.log (778772378517 / 500000000000)) := by
  have h := reflection_log_7472_neg
  have he : Real.log (778772378517 / 500000000000) = -Real.log (500000000000 / 778772378517) := by
    rw [show ((778772378517 / 500000000000) : ℝ) = ((500000000000 / 778772378517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7473_neg : (98810297 / 500000000) ≤ -Real.log (2000 / 2437) ∧
    -Real.log (2000 / 2437) ≤ (39524119 / 200000000) := by
  have h := checkLog_sound (w := (437 / 4437)) (n := 12)
    (lo := (98810297 / 500000000)) (hi := (39524119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2437 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2437 / 2000) = 1/(2000 / 2437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7473 : Bounds (98810297 / 500000000) (39524119 / 200000000) (Real.log (2437 / 2000)) := by
  have h := reflection_log_7473_neg
  have he : Real.log (2437 / 2000) = -Real.log (2000 / 2437) := by
    rw [show ((2437 / 2000) : ℝ) = ((2000 / 2437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7474_neg : (246540129 / 1000000000) ≤ -Real.log (1563 / 2000) ∧
    -Real.log (1563 / 2000) ≤ (24654013 / 100000000) := by
  have h := checkLog_sound (w := (437 / 3563)) (n := 12)
    (lo := (246540129 / 1000000000)) (hi := (24654013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1563) = 1/(1563 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7474 : Bounds (-24654013 / 100000000) (-246540129 / 1000000000) (Real.log (1563 / 2000)) := by
  have h := reflection_log_7474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7475_neg : (54619 / 250000000) ≤ -Real.log (2000000 / 2000437) ∧
    -Real.log (2000000 / 2000437) ≤ (218477 / 1000000000) := by
  have h := checkLog_sound (w := (437 / 4000437)) (n := 12)
    (lo := (54619 / 250000000)) (hi := (218477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000437 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000437 / 2000000) = 1/(2000000 / 2000437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7475 : Bounds (54619 / 250000000) (218477 / 1000000000) (Real.log (2000437 / 2000000)) := by
  have h := reflection_log_7475_neg
  have he : Real.log (2000437 / 2000000) = -Real.log (2000000 / 2000437) := by
    rw [show ((2000437 / 2000000) : ℝ) = ((2000000 / 2000437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7476_neg : (218523 / 1000000000) ≤ -Real.log (1999563 / 2000000) ∧
    -Real.log (1999563 / 2000000) ≤ (54631 / 250000000) := by
  have h := checkLog_sound (w := (437 / 3999563)) (n := 12)
    (lo := (218523 / 1000000000)) (hi := (54631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999563) = 1/(1999563 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7476 : Bounds (-54631 / 250000000) (-218523 / 1000000000) (Real.log (1999563 / 2000000)) := by
  have h := reflection_log_7476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7477_neg : (104214959 / 1000000000) ≤ -Real.log (1000000 / 1109839) ∧
    -Real.log (1000000 / 1109839) ≤ (1302687 / 12500000) := by
  have h := checkLog_sound (w := (109839 / 2109839)) (n := 12)
    (lo := (104214959 / 1000000000)) (hi := (1302687 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1109839 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1109839 / 1000000) = 1/(1000000 / 1109839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7477 : Bounds (104214959 / 1000000000) (1302687 / 12500000) (Real.log (1109839 / 1000000)) := by
  have h := reflection_log_7477_neg
  have he : Real.log (1109839 / 1000000) = -Real.log (1000000 / 1109839) := by
    rw [show ((1109839 / 1000000) : ℝ) = ((1000000 / 1109839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7478_neg : (116352933 / 1000000000) ≤ -Real.log (890161 / 1000000) ∧
    -Real.log (890161 / 1000000) ≤ (58176467 / 500000000) := by
  have h := checkLog_sound (w := (109839 / 1890161)) (n := 12)
    (lo := (116352933 / 1000000000)) (hi := (58176467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 890161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 890161) = 1/(890161 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7478 : Bounds (-58176467 / 500000000) (-116352933 / 1000000000) (Real.log (890161 / 1000000)) := by
  have h := reflection_log_7478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7479_neg : (104641957 / 1000000000) ≤ -Real.log (1000000 / 1110313) ∧
    -Real.log (1000000 / 1110313) ≤ (52320979 / 500000000) := by
  have h := checkLog_sound (w := (110313 / 2110313)) (n := 12)
    (lo := (104641957 / 1000000000)) (hi := (52320979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1110313 / 1000000) = 1/(1000000 / 1110313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7479 : Bounds (104641957 / 1000000000) (52320979 / 500000000) (Real.log (1110313 / 1000000)) := by
  have h := reflection_log_7479_neg
  have he : Real.log (1110313 / 1000000) = -Real.log (1000000 / 1110313) := by
    rw [show ((1110313 / 1000000) : ℝ) = ((1000000 / 1110313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7480_neg : (116885563 / 1000000000) ≤ -Real.log (889687 / 1000000) ∧
    -Real.log (889687 / 1000000) ≤ (29221391 / 250000000) := by
  have h := checkLog_sound (w := (110313 / 1889687)) (n := 12)
    (lo := (116885563 / 1000000000)) (hi := (29221391 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 889687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 889687) = 1/(889687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7480 : Bounds (-29221391 / 250000000) (-116885563 / 1000000000) (Real.log (889687 / 1000000)) := by
  have h := reflection_log_7480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7481_neg : (2448721 / 200000000) ≤ -Real.log (987831042031 / 1000000000000) ∧
    -Real.log (987831042031 / 1000000000000) ≤ (6121803 / 500000000) := by
  have h := checkLog_sound (w := (12168957969 / 1987831042031)) (n := 12)
    (lo := (2448721 / 200000000)) (hi := (6121803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987831042031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987831042031) = 1/(987831042031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7481 : Bounds (-6121803 / 500000000) (-2448721 / 200000000) (Real.log (987831042031 / 1000000000000)) := by
  have h := reflection_log_7481_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7482_neg : (12137973 / 1000000000) ≤ -Real.log (987935394079 / 1000000000000) ∧
    -Real.log (987935394079 / 1000000000000) ≤ (6068987 / 500000000) := by
  have h := checkLog_sound (w := (12064605921 / 1987935394079)) (n := 12)
    (lo := (12137973 / 1000000000)) (hi := (6068987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987935394079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987935394079) = 1/(987935394079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7482 : Bounds (-6068987 / 500000000) (-12137973 / 1000000000) (Real.log (987935394079 / 1000000000000)) := by
  have h := reflection_log_7482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7483_neg : (220567893 / 1000000000) ≤ -Real.log (100000000000 / 124678457043) ∧
    -Real.log (100000000000 / 124678457043) ≤ (110283947 / 500000000) := by
  have h := checkLog_sound (w := (24678457043 / 224678457043)) (n := 12)
    (lo := (220567893 / 1000000000)) (hi := (110283947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124678457043 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124678457043 / 100000000000) = 1/(100000000000 / 124678457043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7483 : Bounds (220567893 / 1000000000) (110283947 / 500000000) (Real.log (124678457043 / 100000000000)) := by
  have h := reflection_log_7483_neg
  have he : Real.log (124678457043 / 100000000000) = -Real.log (100000000000 / 124678457043) := by
    rw [show ((124678457043 / 100000000000) : ℝ) = ((100000000000 / 124678457043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7484_neg : (221527521 / 1000000000) ≤ -Real.log (125000000000 / 155997699191) ∧
    -Real.log (125000000000 / 155997699191) ≤ (110763761 / 500000000) := by
  have h := checkLog_sound (w := (30997699191 / 280997699191)) (n := 12)
    (lo := (221527521 / 1000000000)) (hi := (110763761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155997699191 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155997699191 / 125000000000) = 1/(125000000000 / 155997699191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7484 : Bounds (221527521 / 1000000000) (110763761 / 500000000) (Real.log (155997699191 / 125000000000)) := by
  have h := reflection_log_7484_neg
  have he : Real.log (155997699191 / 125000000000) = -Real.log (125000000000 / 155997699191) := by
    rw [show ((155997699191 / 125000000000) : ℝ) = ((125000000000 / 155997699191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7485_neg : (443110707 / 1000000000) ≤ -Real.log (125000000000 / 194693094629) ∧
    -Real.log (125000000000 / 194693094629) ≤ (110777677 / 250000000) := by
  have h := checkLog_sound (w := (69693094629 / 319693094629)) (n := 12)
    (lo := (443110707 / 1000000000)) (hi := (110777677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194693094629 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194693094629 / 125000000000) = 1/(125000000000 / 194693094629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7485 : Bounds (443110707 / 1000000000) (110777677 / 250000000) (Real.log (194693094629 / 125000000000)) := by
  have h := reflection_log_7485_neg
  have he : Real.log (194693094629 / 125000000000) = -Real.log (125000000000 / 194693094629) := by
    rw [show ((194693094629 / 125000000000) : ℝ) = ((125000000000 / 194693094629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7486_neg : (444160723 / 1000000000) ≤ -Real.log (500000000000 / 779590531031) ∧
    -Real.log (500000000000 / 779590531031) ≤ (111040181 / 250000000) := by
  have h := checkLog_sound (w := (279590531031 / 1279590531031)) (n := 12)
    (lo := (444160723 / 1000000000)) (hi := (111040181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779590531031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779590531031 / 500000000000) = 1/(500000000000 / 779590531031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7486 : Bounds (444160723 / 1000000000) (111040181 / 250000000) (Real.log (779590531031 / 500000000000)) := by
  have h := reflection_log_7486_neg
  have he : Real.log (779590531031 / 500000000000) = -Real.log (500000000000 / 779590531031) := by
    rw [show ((779590531031 / 500000000000) : ℝ) = ((500000000000 / 779590531031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7487_neg : (3960617 / 20000000) ≤ -Real.log (1000 / 1219) ∧
    -Real.log (1000 / 1219) ≤ (198030851 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 2219)) (n := 12)
    (lo := (3960617 / 20000000)) (hi := (198030851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219 / 1000) = 1/(1000 / 1219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7487 : Bounds (3960617 / 20000000) (198030851 / 1000000000) (Real.log (1219 / 1000)) := by
  have h := reflection_log_7487_neg
  have he : Real.log (1219 / 1000) = -Real.log (1000 / 1219) := by
    rw [show ((1219 / 1000) : ℝ) = ((1000 / 1219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


