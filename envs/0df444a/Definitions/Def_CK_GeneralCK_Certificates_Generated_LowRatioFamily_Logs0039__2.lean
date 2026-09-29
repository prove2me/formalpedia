-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0039__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0039__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:12:59.562085+00:00
-- url     : https://prove2.me/theorems/9185f96a-5ef0-470d-a2f9-5c2de8759837
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0039 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0040)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0039 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0040)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0039 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0040)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0039 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0040) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0039 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0040).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0039 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2496_neg : (88117807 / 1000000000) ≤ -Real.log (915653 / 1000000) ∧
    -Real.log (915653 / 1000000) ≤ (5507363 / 62500000) := by
  have h := checkLog_sound (w := (84347 / 1915653)) (n := 12)
    (lo := (88117807 / 1000000000)) (hi := (5507363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915653) = 1/(915653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2496 : Bounds (-5507363 / 62500000) (-88117807 / 1000000000) (Real.log (915653 / 1000000)) := by
  have h := reflection_log_2496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2497_neg : (40589953 / 500000000) ≤ -Real.log (500000 / 542283) ∧
    -Real.log (500000 / 542283) ≤ (81179907 / 1000000000) := by
  have h := checkLog_sound (w := (42283 / 1042283)) (n := 12)
    (lo := (40589953 / 500000000)) (hi := (81179907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542283 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542283 / 500000) = 1/(500000 / 542283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2497 : Bounds (40589953 / 500000000) (81179907 / 1000000000) (Real.log (542283 / 500000)) := by
  have h := reflection_log_2497_neg
  have he : Real.log (542283 / 500000) = -Real.log (500000 / 542283) := by
    rw [show ((542283 / 500000) : ℝ) = ((500000 / 542283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2498_neg : (88357009 / 1000000000) ≤ -Real.log (457717 / 500000) ∧
    -Real.log (457717 / 500000) ≤ (8835701 / 100000000) := by
  have h := checkLog_sound (w := (42283 / 957717)) (n := 12)
    (lo := (88357009 / 1000000000)) (hi := (8835701 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457717) = 1/(457717 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2498 : Bounds (-8835701 / 100000000) (-88357009 / 1000000000) (Real.log (457717 / 500000)) := by
  have h := reflection_log_2498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2499_neg : (3588551 / 500000000) ≤ -Real.log (248212147911 / 250000000000) ∧
    -Real.log (248212147911 / 250000000000) ≤ (7177103 / 1000000000) := by
  have h := checkLog_sound (w := (1787852089 / 498212147911)) (n := 12)
    (lo := (3588551 / 500000000)) (hi := (7177103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248212147911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248212147911) = 1/(248212147911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2499 : Bounds (-7177103 / 1000000000) (-3588551 / 500000000) (Real.log (248212147911 / 250000000000)) := by
  have h := reflection_log_2499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2500_neg : (1784961 / 250000000) ≤ -Real.log (992885583591 / 1000000000000) ∧
    -Real.log (992885583591 / 1000000000000) ≤ (1427969 / 200000000) := by
  have h := checkLog_sound (w := (7114416409 / 1992885583591)) (n := 12)
    (lo := (1784961 / 250000000)) (hi := (1427969 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992885583591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992885583591) = 1/(992885583591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2500 : Bounds (-1427969 / 200000000) (-1784961 / 250000000) (Real.log (992885583591 / 1000000000000)) := by
  have h := reflection_log_2500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2501_neg : (169095769 / 1000000000) ≤ -Real.log (500000000000 / 592116773493) ∧
    -Real.log (500000000000 / 592116773493) ≤ (16909577 / 100000000) := by
  have h := checkLog_sound (w := (92116773493 / 1092116773493)) (n := 12)
    (lo := (169095769 / 1000000000)) (hi := (16909577 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592116773493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592116773493 / 500000000000) = 1/(500000000000 / 592116773493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2501 : Bounds (169095769 / 1000000000) (16909577 / 100000000) (Real.log (592116773493 / 500000000000)) := by
  have h := reflection_log_2501_neg
  have he : Real.log (592116773493 / 500000000000) = -Real.log (500000000000 / 592116773493) := by
    rw [show ((592116773493 / 500000000000) : ℝ) = ((500000000000 / 592116773493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2502_neg : (42384229 / 250000000) ≤ -Real.log (250000000000 / 296189020727) ∧
    -Real.log (250000000000 / 296189020727) ≤ (169536917 / 1000000000) := by
  have h := checkLog_sound (w := (46189020727 / 546189020727)) (n := 12)
    (lo := (42384229 / 250000000)) (hi := (169536917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296189020727 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296189020727 / 250000000000) = 1/(250000000000 / 296189020727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2502 : Bounds (42384229 / 250000000) (169536917 / 1000000000) (Real.log (296189020727 / 250000000000)) := by
  have h := reflection_log_2502_neg
  have he : Real.log (296189020727 / 250000000000) = -Real.log (250000000000 / 296189020727) := by
    rw [show ((296189020727 / 250000000000) : ℝ) = ((250000000000 / 296189020727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2503_neg : (169607861 / 500000000) ≤ -Real.log (500000000000 / 701923076923) ∧
    -Real.log (500000000000 / 701923076923) ≤ (339215723 / 1000000000) := by
  have h := checkLog_sound (w := (201923076923 / 1201923076923)) (n := 12)
    (lo := (169607861 / 500000000)) (hi := (339215723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701923076923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701923076923 / 500000000000) = 1/(500000000000 / 701923076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2503 : Bounds (169607861 / 500000000) (339215723 / 1000000000) (Real.log (701923076923 / 500000000000)) := by
  have h := reflection_log_2503_neg
  have he : Real.log (701923076923 / 500000000000) = -Real.log (500000000000 / 701923076923) := by
    rw [show ((701923076923 / 500000000000) : ℝ) = ((500000000000 / 701923076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2504_neg : (169710767 / 500000000) ≤ -Real.log (500000000000 / 702067556197) ∧
    -Real.log (500000000000 / 702067556197) ≤ (67884307 / 200000000) := by
  have h := checkLog_sound (w := (202067556197 / 1202067556197)) (n := 12)
    (lo := (169710767 / 500000000)) (hi := (67884307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702067556197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702067556197 / 500000000000) = 1/(500000000000 / 702067556197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2504 : Bounds (169710767 / 500000000) (67884307 / 200000000) (Real.log (702067556197 / 500000000000)) := by
  have h := reflection_log_2504_neg
  have he : Real.log (702067556197 / 500000000000) = -Real.log (500000000000 / 702067556197) := by
    rw [show ((702067556197 / 500000000000) : ℝ) = ((500000000000 / 702067556197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2505_neg : (77732051 / 500000000) ≤ -Real.log (5000 / 5841) ∧
    -Real.log (5000 / 5841) ≤ (155464103 / 1000000000) := by
  have h := checkLog_sound (w := (841 / 10841)) (n := 12)
    (lo := (77732051 / 500000000)) (hi := (155464103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5841 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5841 / 5000) = 1/(5000 / 5841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2505 : Bounds (77732051 / 500000000) (155464103 / 1000000000) (Real.log (5841 / 5000)) := by
  have h := reflection_log_2505_neg
  have he : Real.log (5841 / 5000) = -Real.log (5000 / 5841) := by
    rw [show ((5841 / 5000) : ℝ) = ((5000 / 5841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2506_neg : (184163251 / 1000000000) ≤ -Real.log (4159 / 5000) ∧
    -Real.log (4159 / 5000) ≤ (46040813 / 250000000) := by
  have h := checkLog_sound (w := (841 / 9159)) (n := 12)
    (lo := (184163251 / 1000000000)) (hi := (46040813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4159) = 1/(4159 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2506 : Bounds (-46040813 / 250000000) (-184163251 / 1000000000) (Real.log (4159 / 5000)) := by
  have h := reflection_log_2506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2507_neg : (33637 / 200000000) ≤ -Real.log (5000000 / 5000841) ∧
    -Real.log (5000000 / 5000841) ≤ (84093 / 500000000) := by
  have h := checkLog_sound (w := (841 / 10000841)) (n := 12)
    (lo := (33637 / 200000000)) (hi := (84093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000841 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000841 / 5000000) = 1/(5000000 / 5000841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2507 : Bounds (33637 / 200000000) (84093 / 500000000) (Real.log (5000841 / 5000000)) := by
  have h := reflection_log_2507_neg
  have he : Real.log (5000841 / 5000000) = -Real.log (5000000 / 5000841) := by
    rw [show ((5000841 / 5000000) : ℝ) = ((5000000 / 5000841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2508_neg : (84107 / 500000000) ≤ -Real.log (4999159 / 5000000) ∧
    -Real.log (4999159 / 5000000) ≤ (33643 / 200000000) := by
  have h := checkLog_sound (w := (841 / 9999159)) (n := 12)
    (lo := (84107 / 500000000)) (hi := (33643 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999159) = 1/(4999159 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2508 : Bounds (-33643 / 200000000) (-84107 / 500000000) (Real.log (4999159 / 5000000)) := by
  have h := reflection_log_2508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2509_neg : (40512497 / 500000000) ≤ -Real.log (500000 / 542199) ∧
    -Real.log (500000 / 542199) ≤ (16204999 / 200000000) := by
  have h := checkLog_sound (w := (42199 / 1042199)) (n := 12)
    (lo := (40512497 / 500000000)) (hi := (16204999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542199 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542199 / 500000) = 1/(500000 / 542199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2509 : Bounds (40512497 / 500000000) (16204999 / 200000000) (Real.log (542199 / 500000)) := by
  have h := reflection_log_2509_neg
  have he : Real.log (542199 / 500000) = -Real.log (500000 / 542199) := by
    rw [show ((542199 / 500000) : ℝ) = ((500000 / 542199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2510_neg : (44086753 / 500000000) ≤ -Real.log (457801 / 500000) ∧
    -Real.log (457801 / 500000) ≤ (88173507 / 1000000000) := by
  have h := checkLog_sound (w := (42199 / 957801)) (n := 12)
    (lo := (44086753 / 500000000)) (hi := (88173507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457801) = 1/(457801 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2510 : Bounds (-88173507 / 1000000000) (-44086753 / 500000000) (Real.log (457801 / 500000)) := by
  have h := reflection_log_2510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2511_neg : (81226929 / 1000000000) ≤ -Real.log (1000000 / 1084617) ∧
    -Real.log (1000000 / 1084617) ≤ (8122693 / 100000000) := by
  have h := checkLog_sound (w := (84617 / 2084617)) (n := 12)
    (lo := (81226929 / 1000000000)) (hi := (8122693 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084617 / 1000000) = 1/(1000000 / 1084617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2511 : Bounds (81226929 / 1000000000) (8122693 / 100000000) (Real.log (1084617 / 1000000)) := by
  have h := reflection_log_2511_neg
  have he : Real.log (1084617 / 1000000) = -Real.log (1000000 / 1084617) := by
    rw [show ((1084617 / 1000000) : ℝ) = ((1000000 / 1084617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2512_neg : (44206361 / 500000000) ≤ -Real.log (915383 / 1000000) ∧
    -Real.log (915383 / 1000000) ≤ (88412723 / 1000000000) := by
  have h := checkLog_sound (w := (84617 / 1915383)) (n := 12)
    (lo := (44206361 / 500000000)) (hi := (88412723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915383) = 1/(915383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2512 : Bounds (-88412723 / 1000000000) (-44206361 / 500000000) (Real.log (915383 / 1000000)) := by
  have h := reflection_log_2512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2513_neg : (56139 / 7812500) ≤ -Real.log (992839963311 / 1000000000000) ∧
    -Real.log (992839963311 / 1000000000000) ≤ (7185793 / 1000000000) := by
  have h := checkLog_sound (w := (7160036689 / 1992839963311)) (n := 12)
    (lo := (56139 / 7812500)) (hi := (7185793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992839963311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992839963311) = 1/(992839963311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2513 : Bounds (-7185793 / 1000000000) (-56139 / 7812500) (Real.log (992839963311 / 1000000000000)) := by
  have h := reflection_log_2513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2514_neg : (223391 / 31250000) ≤ -Real.log (248219244399 / 250000000000) ∧
    -Real.log (248219244399 / 250000000000) ≤ (7148513 / 1000000000) := by
  have h := checkLog_sound (w := (1780755601 / 498219244399)) (n := 12)
    (lo := (223391 / 31250000)) (hi := (7148513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248219244399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248219244399) = 1/(248219244399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2514 : Bounds (-7148513 / 1000000000) (-223391 / 31250000) (Real.log (248219244399 / 250000000000)) := by
  have h := reflection_log_2514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2515_neg : (338397 / 2000000) ≤ -Real.log (500000000000 / 592177605553) ∧
    -Real.log (500000000000 / 592177605553) ≤ (169198501 / 1000000000) := by
  have h := checkLog_sound (w := (92177605553 / 1092177605553)) (n := 12)
    (lo := (338397 / 2000000)) (hi := (169198501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592177605553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592177605553 / 500000000000) = 1/(500000000000 / 592177605553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2515 : Bounds (338397 / 2000000) (169198501 / 1000000000) (Real.log (592177605553 / 500000000000)) := by
  have h := reflection_log_2515_neg
  have he : Real.log (592177605553 / 500000000000) = -Real.log (500000000000 / 592177605553) := by
    rw [show ((592177605553 / 500000000000) : ℝ) = ((500000000000 / 592177605553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2516_neg : (169639651 / 1000000000) ≤ -Real.log (15625000000 / 18513715707) ∧
    -Real.log (15625000000 / 18513715707) ≤ (42409913 / 250000000) := by
  have h := checkLog_sound (w := (2888715707 / 34138715707)) (n := 12)
    (lo := (169639651 / 1000000000)) (hi := (42409913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18513715707 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18513715707 / 15625000000) = 1/(15625000000 / 18513715707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2516 : Bounds (169639651 / 1000000000) (42409913 / 250000000) (Real.log (18513715707 / 15625000000)) := by
  have h := reflection_log_2516_neg
  have he : Real.log (18513715707 / 15625000000) = -Real.log (15625000000 / 18513715707) := by
    rw [show ((18513715707 / 15625000000) : ℝ) = ((15625000000 / 18513715707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2517_neg : (169710767 / 500000000) ≤ -Real.log (125000000000 / 175516889049) ∧
    -Real.log (125000000000 / 175516889049) ≤ (67884307 / 200000000) := by
  have h := checkLog_sound (w := (50516889049 / 300516889049)) (n := 12)
    (lo := (169710767 / 500000000)) (hi := (67884307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175516889049 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175516889049 / 125000000000) = 1/(125000000000 / 175516889049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2517 : Bounds (169710767 / 500000000) (67884307 / 200000000) (Real.log (175516889049 / 125000000000)) := by
  have h := reflection_log_2517_neg
  have he : Real.log (175516889049 / 125000000000) = -Real.log (125000000000 / 175516889049) := by
    rw [show ((175516889049 / 125000000000) : ℝ) = ((125000000000 / 175516889049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2518_neg : (169813677 / 500000000) ≤ -Real.log (50000000000 / 70221207021) ∧
    -Real.log (50000000000 / 70221207021) ≤ (67925471 / 200000000) := by
  have h := checkLog_sound (w := (20221207021 / 120221207021)) (n := 12)
    (lo := (169813677 / 500000000)) (hi := (67925471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70221207021 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70221207021 / 50000000000) = 1/(50000000000 / 70221207021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2518 : Bounds (169813677 / 500000000) (67925471 / 200000000) (Real.log (70221207021 / 50000000000)) := by
  have h := reflection_log_2518_neg
  have he : Real.log (70221207021 / 50000000000) = -Real.log (50000000000 / 70221207021) := by
    rw [show ((70221207021 / 50000000000) : ℝ) = ((50000000000 / 70221207021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2519_neg : (1555497 / 10000000) ≤ -Real.log (10000 / 11683) ∧
    -Real.log (10000 / 11683) ≤ (155549701 / 1000000000) := by
  have h := checkLog_sound (w := (1683 / 21683)) (n := 12)
    (lo := (1555497 / 10000000)) (hi := (155549701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11683 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11683 / 10000) = 1/(10000 / 11683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2519 : Bounds (1555497 / 10000000) (155549701 / 1000000000) (Real.log (11683 / 10000)) := by
  have h := reflection_log_2519_neg
  have he : Real.log (11683 / 10000) = -Real.log (10000 / 11683) := by
    rw [show ((11683 / 10000) : ℝ) = ((10000 / 11683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2520_neg : (4607087 / 25000000) ≤ -Real.log (8317 / 10000) ∧
    -Real.log (8317 / 10000) ≤ (184283481 / 1000000000) := by
  have h := checkLog_sound (w := (1683 / 18317)) (n := 12)
    (lo := (4607087 / 25000000)) (hi := (184283481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8317) = 1/(8317 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2520 : Bounds (-184283481 / 1000000000) (-4607087 / 25000000) (Real.log (8317 / 10000)) := by
  have h := reflection_log_2520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2521_neg : (33657 / 200000000) ≤ -Real.log (10000000 / 10001683) ∧
    -Real.log (10000000 / 10001683) ≤ (84143 / 500000000) := by
  have h := checkLog_sound (w := (1683 / 20001683)) (n := 12)
    (lo := (33657 / 200000000)) (hi := (84143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001683 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001683 / 10000000) = 1/(10000000 / 10001683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2521 : Bounds (33657 / 200000000) (84143 / 500000000) (Real.log (10001683 / 10000000)) := by
  have h := reflection_log_2521_neg
  have he : Real.log (10001683 / 10000000) = -Real.log (10000000 / 10001683) := by
    rw [show ((10001683 / 10000000) : ℝ) = ((10000000 / 10001683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2522_neg : (84157 / 500000000) ≤ -Real.log (9998317 / 10000000) ∧
    -Real.log (9998317 / 10000000) ≤ (33663 / 200000000) := by
  have h := checkLog_sound (w := (1683 / 19998317)) (n := 12)
    (lo := (84157 / 500000000)) (hi := (33663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998317) = 1/(9998317 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2522 : Bounds (-33663 / 200000000) (-84157 / 500000000) (Real.log (9998317 / 10000000)) := by
  have h := reflection_log_2522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2523_neg : (81071101 / 1000000000) ≤ -Real.log (31250 / 33889) ∧
    -Real.log (31250 / 33889) ≤ (40535551 / 500000000) := by
  have h := checkLog_sound (w := (2639 / 65139)) (n := 12)
    (lo := (81071101 / 1000000000)) (hi := (40535551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33889 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33889 / 31250) = 1/(31250 / 33889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2523 : Bounds (81071101 / 1000000000) (40535551 / 500000000) (Real.log (33889 / 31250)) := by
  have h := reflection_log_2523_neg
  have he : Real.log (33889 / 31250) = -Real.log (31250 / 33889) := by
    rw [show ((33889 / 31250) : ℝ) = ((31250 / 33889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2524_neg : (22057029 / 250000000) ≤ -Real.log (28611 / 31250) ∧
    -Real.log (28611 / 31250) ≤ (88228117 / 1000000000) := by
  have h := checkLog_sound (w := (2639 / 59861)) (n := 12)
    (lo := (22057029 / 250000000)) (hi := (88228117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28611) = 1/(28611 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2524 : Bounds (-88228117 / 1000000000) (-22057029 / 250000000) (Real.log (28611 / 31250)) := by
  have h := reflection_log_2524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2525_neg : (81273949 / 1000000000) ≤ -Real.log (250000 / 271167) ∧
    -Real.log (250000 / 271167) ≤ (1625479 / 20000000) := by
  have h := checkLog_sound (w := (21167 / 521167)) (n := 12)
    (lo := (81273949 / 1000000000)) (hi := (1625479 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271167 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271167 / 250000) = 1/(250000 / 271167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2525 : Bounds (81273949 / 1000000000) (1625479 / 20000000) (Real.log (271167 / 250000)) := by
  have h := reflection_log_2525_neg
  have he : Real.log (271167 / 250000) = -Real.log (250000 / 271167) := by
    rw [show ((271167 / 250000) : ℝ) = ((250000 / 271167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2526_neg : (88468437 / 1000000000) ≤ -Real.log (228833 / 250000) ∧
    -Real.log (228833 / 250000) ≤ (44234219 / 500000000) := by
  have h := checkLog_sound (w := (21167 / 478833)) (n := 12)
    (lo := (88468437 / 1000000000)) (hi := (44234219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228833) = 1/(228833 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2526 : Bounds (-44234219 / 500000000) (-88468437 / 1000000000) (Real.log (228833 / 250000)) := by
  have h := reflection_log_2526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2527_neg : (899311 / 125000000) ≤ -Real.log (62051958111 / 62500000000) ∧
    -Real.log (62051958111 / 62500000000) ≤ (7194489 / 1000000000) := by
  have h := checkLog_sound (w := (448041889 / 124551958111)) (n := 12)
    (lo := (899311 / 125000000)) (hi := (7194489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62051958111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62051958111) = 1/(62051958111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2527 : Bounds (-7194489 / 1000000000) (-899311 / 125000000) (Real.log (62051958111 / 62500000000)) := by
  have h := reflection_log_2527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2528_neg : (1431403 / 200000000) ≤ -Real.log (969598179 / 976562500) ∧
    -Real.log (969598179 / 976562500) ≤ (894627 / 125000000) := by
  have h := checkLog_sound (w := (6964321 / 1946160679)) (n := 12)
    (lo := (1431403 / 200000000)) (hi := (894627 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 969598179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 969598179) = 1/(969598179 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2528 : Bounds (-894627 / 125000000) (-1431403 / 200000000) (Real.log (969598179 / 976562500)) := by
  have h := reflection_log_2528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2529_neg : (84649609 / 500000000) ≤ -Real.log (250000000000 / 296118625703) ∧
    -Real.log (250000000000 / 296118625703) ≤ (169299219 / 1000000000) := by
  have h := checkLog_sound (w := (46118625703 / 546118625703)) (n := 12)
    (lo := (84649609 / 500000000)) (hi := (169299219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296118625703 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296118625703 / 250000000000) = 1/(250000000000 / 296118625703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2529 : Bounds (84649609 / 500000000) (169299219 / 1000000000) (Real.log (296118625703 / 250000000000)) := by
  have h := reflection_log_2529_neg
  have he : Real.log (296118625703 / 250000000000) = -Real.log (250000000000 / 296118625703) := by
    rw [show ((296118625703 / 250000000000) : ℝ) = ((250000000000 / 296118625703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2530_neg : (169742387 / 1000000000) ≤ -Real.log (31250000000 / 37031235661) ∧
    -Real.log (31250000000 / 37031235661) ≤ (42435597 / 250000000) := by
  have h := checkLog_sound (w := (5781235661 / 68281235661)) (n := 12)
    (lo := (169742387 / 1000000000)) (hi := (42435597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37031235661 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37031235661 / 31250000000) = 1/(31250000000 / 37031235661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2530 : Bounds (169742387 / 1000000000) (42435597 / 250000000) (Real.log (37031235661 / 31250000000)) := by
  have h := reflection_log_2530_neg
  have he : Real.log (37031235661 / 31250000000) = -Real.log (31250000000 / 37031235661) := by
    rw [show ((37031235661 / 31250000000) : ℝ) = ((31250000000 / 37031235661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2531_neg : (169813677 / 500000000) ≤ -Real.log (500000000000 / 702212070209) ∧
    -Real.log (500000000000 / 702212070209) ≤ (67925471 / 200000000) := by
  have h := checkLog_sound (w := (202212070209 / 1202212070209)) (n := 12)
    (lo := (169813677 / 500000000)) (hi := (67925471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702212070209 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702212070209 / 500000000000) = 1/(500000000000 / 702212070209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2531 : Bounds (169813677 / 500000000) (67925471 / 200000000) (Real.log (702212070209 / 500000000000)) := by
  have h := reflection_log_2531_neg
  have he : Real.log (702212070209 / 500000000000) = -Real.log (500000000000 / 702212070209) := by
    rw [show ((702212070209 / 500000000000) : ℝ) = ((500000000000 / 702212070209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2532_neg : (16991659 / 50000000) ≤ -Real.log (250000000000 / 351178309487) ∧
    -Real.log (250000000000 / 351178309487) ≤ (339833181 / 1000000000) := by
  have h := checkLog_sound (w := (101178309487 / 601178309487)) (n := 12)
    (lo := (16991659 / 50000000)) (hi := (339833181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351178309487 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351178309487 / 250000000000) = 1/(250000000000 / 351178309487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2532 : Bounds (16991659 / 50000000) (339833181 / 1000000000) (Real.log (351178309487 / 250000000000)) := by
  have h := reflection_log_2532_neg
  have he : Real.log (351178309487 / 250000000000) = -Real.log (250000000000 / 351178309487) := by
    rw [show ((351178309487 / 250000000000) : ℝ) = ((250000000000 / 351178309487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2533_neg : (155635291 / 1000000000) ≤ -Real.log (2500 / 2921) ∧
    -Real.log (2500 / 2921) ≤ (38908823 / 250000000) := by
  have h := checkLog_sound (w := (421 / 5421)) (n := 12)
    (lo := (155635291 / 1000000000)) (hi := (38908823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2921 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2921 / 2500) = 1/(2500 / 2921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2533 : Bounds (155635291 / 1000000000) (38908823 / 250000000) (Real.log (2921 / 2500)) := by
  have h := reflection_log_2533_neg
  have he : Real.log (2921 / 2500) = -Real.log (2500 / 2921) := by
    rw [show ((2921 / 2500) : ℝ) = ((2500 / 2921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2534_neg : (92201861 / 500000000) ≤ -Real.log (2079 / 2500) ∧
    -Real.log (2079 / 2500) ≤ (184403723 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 4579)) (n := 12)
    (lo := (92201861 / 500000000)) (hi := (184403723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2079) = 1/(2079 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2534 : Bounds (-184403723 / 1000000000) (-92201861 / 500000000) (Real.log (2079 / 2500)) := by
  have h := reflection_log_2534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2535_neg : (33677 / 200000000) ≤ -Real.log (2500000 / 2500421) ∧
    -Real.log (2500000 / 2500421) ≤ (84193 / 500000000) := by
  have h := checkLog_sound (w := (421 / 5000421)) (n := 12)
    (lo := (33677 / 200000000)) (hi := (84193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500421 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500421 / 2500000) = 1/(2500000 / 2500421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2535 : Bounds (33677 / 200000000) (84193 / 500000000) (Real.log (2500421 / 2500000)) := by
  have h := reflection_log_2535_neg
  have he : Real.log (2500421 / 2500000) = -Real.log (2500000 / 2500421) := by
    rw [show ((2500421 / 2500000) : ℝ) = ((2500000 / 2500421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2536_neg : (84207 / 500000000) ≤ -Real.log (2499579 / 2500000) ∧
    -Real.log (2499579 / 2500000) ≤ (33683 / 200000000) := by
  have h := checkLog_sound (w := (421 / 4999579)) (n := 12)
    (lo := (84207 / 500000000)) (hi := (33683 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499579) = 1/(2499579 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2536 : Bounds (-33683 / 200000000) (-84207 / 500000000) (Real.log (2499579 / 2500000)) := by
  have h := reflection_log_2536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2537_neg : (81118129 / 1000000000) ≤ -Real.log (1000000 / 1084499) ∧
    -Real.log (1000000 / 1084499) ≤ (8111813 / 100000000) := by
  have h := checkLog_sound (w := (84499 / 2084499)) (n := 12)
    (lo := (81118129 / 1000000000)) (hi := (8111813 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084499 / 1000000) = 1/(1000000 / 1084499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2537 : Bounds (81118129 / 1000000000) (8111813 / 100000000) (Real.log (1084499 / 1000000)) := by
  have h := reflection_log_2537_neg
  have he : Real.log (1084499 / 1000000) = -Real.log (1000000 / 1084499) := by
    rw [show ((1084499 / 1000000) : ℝ) = ((1000000 / 1084499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2538_neg : (44141911 / 500000000) ≤ -Real.log (915501 / 1000000) ∧
    -Real.log (915501 / 1000000) ≤ (88283823 / 1000000000) := by
  have h := checkLog_sound (w := (84499 / 1915501)) (n := 12)
    (lo := (44141911 / 500000000)) (hi := (88283823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915501) = 1/(915501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2538 : Bounds (-88283823 / 1000000000) (-44141911 / 500000000) (Real.log (915501 / 1000000)) := by
  have h := reflection_log_2538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2539_neg : (16264009 / 200000000) ≤ -Real.log (500000 / 542359) ∧
    -Real.log (500000 / 542359) ≤ (40660023 / 500000000) := by
  have h := checkLog_sound (w := (42359 / 1042359)) (n := 12)
    (lo := (16264009 / 200000000)) (hi := (40660023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542359 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542359 / 500000) = 1/(500000 / 542359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2539 : Bounds (16264009 / 200000000) (40660023 / 500000000) (Real.log (542359 / 500000)) := by
  have h := reflection_log_2539_neg
  have he : Real.log (542359 / 500000) = -Real.log (500000 / 542359) := by
    rw [show ((542359 / 500000) : ℝ) = ((500000 / 542359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2540_neg : (11065383 / 125000000) ≤ -Real.log (457641 / 500000) ∧
    -Real.log (457641 / 500000) ≤ (17704613 / 200000000) := by
  have h := checkLog_sound (w := (42359 / 957641)) (n := 12)
    (lo := (11065383 / 125000000)) (hi := (17704613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457641) = 1/(457641 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2540 : Bounds (-17704613 / 200000000) (-11065383 / 125000000) (Real.log (457641 / 500000)) := by
  have h := reflection_log_2540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2541_neg : (7203019 / 1000000000) ≤ -Real.log (248205715119 / 250000000000) ∧
    -Real.log (248205715119 / 250000000000) ≤ (360151 / 50000000) := by
  have h := checkLog_sound (w := (1794284881 / 498205715119)) (n := 12)
    (lo := (7203019 / 1000000000)) (hi := (360151 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248205715119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248205715119) = 1/(248205715119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2541 : Bounds (-360151 / 50000000) (-7203019 / 1000000000) (Real.log (248205715119 / 250000000000)) := by
  have h := reflection_log_2541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2542_neg : (7165693 / 1000000000) ≤ -Real.log (992859918999 / 1000000000000) ∧
    -Real.log (992859918999 / 1000000000000) ≤ (3582847 / 500000000) := by
  have h := checkLog_sound (w := (7140081001 / 1992859918999)) (n := 12)
    (lo := (7165693 / 1000000000)) (hi := (3582847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992859918999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992859918999) = 1/(992859918999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2542 : Bounds (-3582847 / 500000000) (-7165693 / 1000000000) (Real.log (992859918999 / 1000000000000)) := by
  have h := reflection_log_2542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2543_neg : (169401951 / 1000000000) ≤ -Real.log (500000000000 / 592298096889) ∧
    -Real.log (500000000000 / 592298096889) ≤ (5293811 / 31250000) := by
  have h := checkLog_sound (w := (92298096889 / 1092298096889)) (n := 12)
    (lo := (169401951 / 1000000000)) (hi := (5293811 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592298096889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592298096889 / 500000000000) = 1/(500000000000 / 592298096889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2543 : Bounds (169401951 / 1000000000) (5293811 / 31250000) (Real.log (592298096889 / 500000000000)) := by
  have h := reflection_log_2543_neg
  have he : Real.log (592298096889 / 500000000000) = -Real.log (500000000000 / 592298096889) := by
    rw [show ((592298096889 / 500000000000) : ℝ) = ((500000000000 / 592298096889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2544_neg : (169843109 / 1000000000) ≤ -Real.log (500000000000 / 592559451623) ∧
    -Real.log (500000000000 / 592559451623) ≤ (16984311 / 100000000) := by
  have h := checkLog_sound (w := (92559451623 / 1092559451623)) (n := 12)
    (lo := (169843109 / 1000000000)) (hi := (16984311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592559451623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592559451623 / 500000000000) = 1/(500000000000 / 592559451623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2544 : Bounds (169843109 / 1000000000) (16984311 / 100000000) (Real.log (592559451623 / 500000000000)) := by
  have h := reflection_log_2544_neg
  have he : Real.log (592559451623 / 500000000000) = -Real.log (500000000000 / 592559451623) := by
    rw [show ((592559451623 / 500000000000) : ℝ) = ((500000000000 / 592559451623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2545_neg : (16991659 / 50000000) ≤ -Real.log (500000000000 / 702356618973) ∧
    -Real.log (500000000000 / 702356618973) ≤ (339833181 / 1000000000) := by
  have h := checkLog_sound (w := (202356618973 / 1202356618973)) (n := 12)
    (lo := (16991659 / 50000000)) (hi := (339833181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702356618973 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702356618973 / 500000000000) = 1/(500000000000 / 702356618973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2545 : Bounds (16991659 / 50000000) (339833181 / 1000000000) (Real.log (702356618973 / 500000000000)) := by
  have h := reflection_log_2545_neg
  have he : Real.log (702356618973 / 500000000000) = -Real.log (500000000000 / 702356618973) := by
    rw [show ((702356618973 / 500000000000) : ℝ) = ((500000000000 / 702356618973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2546_neg : (170019507 / 500000000) ≤ -Real.log (250000000000 / 351250601251) ∧
    -Real.log (250000000000 / 351250601251) ≤ (68007803 / 200000000) := by
  have h := checkLog_sound (w := (101250601251 / 601250601251)) (n := 12)
    (lo := (170019507 / 500000000)) (hi := (68007803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351250601251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351250601251 / 250000000000) = 1/(250000000000 / 351250601251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2546 : Bounds (170019507 / 500000000) (68007803 / 200000000) (Real.log (351250601251 / 250000000000)) := by
  have h := reflection_log_2546_neg
  have he : Real.log (351250601251 / 250000000000) = -Real.log (250000000000 / 351250601251) := by
    rw [show ((351250601251 / 250000000000) : ℝ) = ((250000000000 / 351250601251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2547_neg : (77860437 / 500000000) ≤ -Real.log (2000 / 2337) ∧
    -Real.log (2000 / 2337) ≤ (1245767 / 8000000) := by
  have h := checkLog_sound (w := (337 / 4337)) (n := 12)
    (lo := (77860437 / 500000000)) (hi := (1245767 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2337 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2337 / 2000) = 1/(2000 / 2337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2547 : Bounds (77860437 / 500000000) (1245767 / 8000000) (Real.log (2337 / 2000)) := by
  have h := reflection_log_2547_neg
  have he : Real.log (2337 / 2000) = -Real.log (2000 / 2337) := by
    rw [show ((2337 / 2000) : ℝ) = ((2000 / 2337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2548_neg : (9226199 / 50000000) ≤ -Real.log (1663 / 2000) ∧
    -Real.log (1663 / 2000) ≤ (184523981 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 3663)) (n := 12)
    (lo := (9226199 / 50000000)) (hi := (184523981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1663) = 1/(1663 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2548 : Bounds (-184523981 / 1000000000) (-9226199 / 50000000) (Real.log (1663 / 2000)) := by
  have h := reflection_log_2548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2549_neg : (33697 / 200000000) ≤ -Real.log (2000000 / 2000337) ∧
    -Real.log (2000000 / 2000337) ≤ (84243 / 500000000) := by
  have h := checkLog_sound (w := (337 / 4000337)) (n := 12)
    (lo := (33697 / 200000000)) (hi := (84243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000337 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000337 / 2000000) = 1/(2000000 / 2000337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2549 : Bounds (33697 / 200000000) (84243 / 500000000) (Real.log (2000337 / 2000000)) := by
  have h := reflection_log_2549_neg
  have he : Real.log (2000337 / 2000000) = -Real.log (2000000 / 2000337) := by
    rw [show ((2000337 / 2000000) : ℝ) = ((2000000 / 2000337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2550_neg : (84257 / 500000000) ≤ -Real.log (1999663 / 2000000) ∧
    -Real.log (1999663 / 2000000) ≤ (33703 / 200000000) := by
  have h := checkLog_sound (w := (337 / 3999663)) (n := 12)
    (lo := (84257 / 500000000)) (hi := (33703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999663) = 1/(1999663 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2550 : Bounds (-33703 / 200000000) (-84257 / 500000000) (Real.log (1999663 / 2000000)) := by
  have h := reflection_log_2550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2551_neg : (40582577 / 500000000) ≤ -Real.log (20000 / 21691) ∧
    -Real.log (20000 / 21691) ≤ (16233031 / 200000000) := by
  have h := checkLog_sound (w := (1691 / 41691)) (n := 12)
    (lo := (40582577 / 500000000)) (hi := (16233031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21691 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21691 / 20000) = 1/(20000 / 21691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2551 : Bounds (40582577 / 500000000) (16233031 / 200000000) (Real.log (21691 / 20000)) := by
  have h := reflection_log_2551_neg
  have he : Real.log (21691 / 20000) = -Real.log (20000 / 21691) := by
    rw [show ((21691 / 20000) : ℝ) = ((20000 / 21691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2552_neg : (88339531 / 1000000000) ≤ -Real.log (18309 / 20000) ∧
    -Real.log (18309 / 20000) ≤ (22084883 / 250000000) := by
  have h := checkLog_sound (w := (1691 / 38309)) (n := 12)
    (lo := (88339531 / 1000000000)) (hi := (22084883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18309) = 1/(18309 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2552 : Bounds (-22084883 / 250000000) (-88339531 / 1000000000) (Real.log (18309 / 20000)) := by
  have h := reflection_log_2552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2553_neg : (81367061 / 1000000000) ≤ -Real.log (1000000 / 1084769) ∧
    -Real.log (1000000 / 1084769) ≤ (40683531 / 500000000) := by
  have h := checkLog_sound (w := (84769 / 2084769)) (n := 12)
    (lo := (81367061 / 1000000000)) (hi := (40683531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084769 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084769 / 1000000) = 1/(1000000 / 1084769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2553 : Bounds (81367061 / 1000000000) (40683531 / 500000000) (Real.log (1084769 / 1000000)) := by
  have h := reflection_log_2553_neg
  have he : Real.log (1084769 / 1000000) = -Real.log (1000000 / 1084769) := by
    rw [show ((1084769 / 1000000) : ℝ) = ((1000000 / 1084769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2554_neg : (44289393 / 500000000) ≤ -Real.log (915231 / 1000000) ∧
    -Real.log (915231 / 1000000) ≤ (88578787 / 1000000000) := by
  have h := checkLog_sound (w := (84769 / 1915231)) (n := 12)
    (lo := (44289393 / 500000000)) (hi := (88578787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915231) = 1/(915231 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2554 : Bounds (-88578787 / 1000000000) (-44289393 / 500000000) (Real.log (915231 / 1000000)) := by
  have h := reflection_log_2554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2555_neg : (288469 / 40000000) ≤ -Real.log (992814216639 / 1000000000000) ∧
    -Real.log (992814216639 / 1000000000000) ≤ (3605863 / 500000000) := by
  have h := checkLog_sound (w := (7185783361 / 1992814216639)) (n := 12)
    (lo := (288469 / 40000000)) (hi := (3605863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992814216639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992814216639) = 1/(992814216639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2555 : Bounds (-3605863 / 500000000) (-288469 / 40000000) (Real.log (992814216639 / 1000000000000)) := by
  have h := reflection_log_2555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2556_neg : (896797 / 125000000) ≤ -Real.log (397140519 / 400000000) ∧
    -Real.log (397140519 / 400000000) ≤ (7174377 / 1000000000) := by
  have h := checkLog_sound (w := (2859481 / 797140519)) (n := 12)
    (lo := (896797 / 125000000)) (hi := (7174377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 397140519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 397140519) = 1/(397140519 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2556 : Bounds (-7174377 / 1000000000) (-896797 / 125000000) (Real.log (397140519 / 400000000)) := by
  have h := reflection_log_2556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2557_neg : (33900937 / 200000000) ≤ -Real.log (10000000000 / 11847178983) ∧
    -Real.log (10000000000 / 11847178983) ≤ (84752343 / 500000000) := by
  have h := checkLog_sound (w := (1847178983 / 21847178983)) (n := 12)
    (lo := (33900937 / 200000000)) (hi := (84752343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11847178983 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11847178983 / 10000000000) = 1/(10000000000 / 11847178983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2557 : Bounds (33900937 / 200000000) (84752343 / 500000000) (Real.log (11847178983 / 10000000000)) := by
  have h := reflection_log_2557_neg
  have he : Real.log (11847178983 / 10000000000) = -Real.log (10000000000 / 11847178983) := by
    rw [show ((11847178983 / 10000000000) : ℝ) = ((10000000000 / 11847178983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2558_neg : (169945847 / 1000000000) ≤ -Real.log (500000000000 / 592620333009) ∧
    -Real.log (500000000000 / 592620333009) ≤ (21243231 / 125000000) := by
  have h := checkLog_sound (w := (92620333009 / 1092620333009)) (n := 12)
    (lo := (169945847 / 1000000000)) (hi := (21243231 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592620333009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592620333009 / 500000000000) = 1/(500000000000 / 592620333009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2558 : Bounds (169945847 / 1000000000) (21243231 / 125000000) (Real.log (592620333009 / 500000000000)) := by
  have h := reflection_log_2558_neg
  have he : Real.log (592620333009 / 500000000000) = -Real.log (500000000000 / 592620333009) := by
    rw [show ((592620333009 / 500000000000) : ℝ) = ((500000000000 / 592620333009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2559_neg : (170019507 / 500000000) ≤ -Real.log (500000000000 / 702501202501) ∧
    -Real.log (500000000000 / 702501202501) ≤ (68007803 / 200000000) := by
  have h := checkLog_sound (w := (202501202501 / 1202501202501)) (n := 12)
    (lo := (170019507 / 500000000)) (hi := (68007803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702501202501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702501202501 / 500000000000) = 1/(500000000000 / 702501202501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2559 : Bounds (170019507 / 500000000) (68007803 / 200000000) (Real.log (702501202501 / 500000000000)) := by
  have h := reflection_log_2559_neg
  have he : Real.log (702501202501 / 500000000000) = -Real.log (500000000000 / 702501202501) := by
    rw [show ((702501202501 / 500000000000) : ℝ) = ((500000000000 / 702501202501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0040 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2560_neg : (68048971 / 200000000) ≤ -Real.log (250000000000 / 351322910403) ∧
    -Real.log (250000000000 / 351322910403) ≤ (42530607 / 125000000) := by
  have h := checkLog_sound (w := (101322910403 / 601322910403)) (n := 12)
    (lo := (68048971 / 200000000)) (hi := (42530607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351322910403 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351322910403 / 250000000000) = 1/(250000000000 / 351322910403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2560 : Bounds (68048971 / 200000000) (42530607 / 125000000) (Real.log (351322910403 / 250000000000)) := by
  have h := reflection_log_2560_neg
  have he : Real.log (351322910403 / 250000000000) = -Real.log (250000000000 / 351322910403) := by
    rw [show ((351322910403 / 250000000000) : ℝ) = ((250000000000 / 351322910403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2561_neg : (155806451 / 1000000000) ≤ -Real.log (5000 / 5843) ∧
    -Real.log (5000 / 5843) ≤ (38951613 / 250000000) := by
  have h := checkLog_sound (w := (843 / 10843)) (n := 12)
    (lo := (155806451 / 1000000000)) (hi := (38951613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5843 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5843 / 5000) = 1/(5000 / 5843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2561 : Bounds (155806451 / 1000000000) (38951613 / 250000000) (Real.log (5843 / 5000)) := by
  have h := reflection_log_2561_neg
  have he : Real.log (5843 / 5000) = -Real.log (5000 / 5843) := by
    rw [show ((5843 / 5000) : ℝ) = ((5000 / 5843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2562_neg : (46161063 / 250000000) ≤ -Real.log (4157 / 5000) ∧
    -Real.log (4157 / 5000) ≤ (184644253 / 1000000000) := by
  have h := checkLog_sound (w := (843 / 9157)) (n := 12)
    (lo := (46161063 / 250000000)) (hi := (184644253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4157) = 1/(4157 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2562 : Bounds (-184644253 / 1000000000) (-46161063 / 250000000) (Real.log (4157 / 5000)) := by
  have h := reflection_log_2562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2563_neg : (33717 / 200000000) ≤ -Real.log (5000000 / 5000843) ∧
    -Real.log (5000000 / 5000843) ≤ (84293 / 500000000) := by
  have h := checkLog_sound (w := (843 / 10000843)) (n := 12)
    (lo := (33717 / 200000000)) (hi := (84293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000843 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000843 / 5000000) = 1/(5000000 / 5000843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2563 : Bounds (33717 / 200000000) (84293 / 500000000) (Real.log (5000843 / 5000000)) := by
  have h := reflection_log_2563_neg
  have he : Real.log (5000843 / 5000000) = -Real.log (5000000 / 5000843) := by
    rw [show ((5000843 / 5000000) : ℝ) = ((5000000 / 5000843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2564_neg : (84307 / 500000000) ≤ -Real.log (4999157 / 5000000) ∧
    -Real.log (4999157 / 5000000) ≤ (33723 / 200000000) := by
  have h := checkLog_sound (w := (843 / 9999157)) (n := 12)
    (lo := (84307 / 500000000)) (hi := (33723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999157) = 1/(4999157 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2564 : Bounds (-33723 / 200000000) (-84307 / 500000000) (Real.log (4999157 / 5000000)) := by
  have h := reflection_log_2564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2565_neg : (81212177 / 1000000000) ≤ -Real.log (1000000 / 1084601) ∧
    -Real.log (1000000 / 1084601) ≤ (40606089 / 500000000) := by
  have h := checkLog_sound (w := (84601 / 2084601)) (n := 12)
    (lo := (81212177 / 1000000000)) (hi := (40606089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084601 / 1000000) = 1/(1000000 / 1084601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2565 : Bounds (81212177 / 1000000000) (40606089 / 500000000) (Real.log (1084601 / 1000000)) := by
  have h := reflection_log_2565_neg
  have he : Real.log (1084601 / 1000000) = -Real.log (1000000 / 1084601) := by
    rw [show ((1084601 / 1000000) : ℝ) = ((1000000 / 1084601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2566_neg : (88395243 / 1000000000) ≤ -Real.log (915399 / 1000000) ∧
    -Real.log (915399 / 1000000) ≤ (22098811 / 250000000) := by
  have h := checkLog_sound (w := (84601 / 1915399)) (n := 12)
    (lo := (88395243 / 1000000000)) (hi := (22098811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915399) = 1/(915399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2566 : Bounds (-22098811 / 250000000) (-88395243 / 1000000000) (Real.log (915399 / 1000000)) := by
  have h := reflection_log_2566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2567_neg : (40707037 / 500000000) ≤ -Real.log (50000 / 54241) ∧
    -Real.log (50000 / 54241) ≤ (3256563 / 40000000) := by
  have h := checkLog_sound (w := (4241 / 104241)) (n := 12)
    (lo := (40707037 / 500000000)) (hi := (3256563 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54241 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54241 / 50000) = 1/(50000 / 54241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2567 : Bounds (40707037 / 500000000) (3256563 / 40000000) (Real.log (54241 / 50000)) := by
  have h := reflection_log_2567_neg
  have he : Real.log (54241 / 50000) = -Real.log (50000 / 54241) := by
    rw [show ((54241 / 50000) : ℝ) = ((50000 / 54241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2568_neg : (88634511 / 1000000000) ≤ -Real.log (45759 / 50000) ∧
    -Real.log (45759 / 50000) ≤ (5539657 / 62500000) := by
  have h := checkLog_sound (w := (4241 / 95759)) (n := 12)
    (lo := (88634511 / 1000000000)) (hi := (5539657 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45759) = 1/(45759 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2568 : Bounds (-5539657 / 62500000) (-88634511 / 1000000000) (Real.log (45759 / 50000)) := by
  have h := reflection_log_2568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2569_neg : (7220437 / 1000000000) ≤ -Real.log (2482013919 / 2500000000) ∧
    -Real.log (2482013919 / 2500000000) ≤ (3610219 / 500000000) := by
  have h := checkLog_sound (w := (17986081 / 4982013919)) (n := 12)
    (lo := (7220437 / 1000000000)) (hi := (3610219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2482013919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2482013919) = 1/(2482013919 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2569 : Bounds (-3610219 / 500000000) (-7220437 / 1000000000) (Real.log (2482013919 / 2500000000)) := by
  have h := reflection_log_2569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2570_neg : (1436613 / 200000000) ≤ -Real.log (992842670799 / 1000000000000) ∧
    -Real.log (992842670799 / 1000000000000) ≤ (3591533 / 500000000) := by
  have h := checkLog_sound (w := (7157329201 / 1992842670799)) (n := 12)
    (lo := (1436613 / 200000000)) (hi := (3591533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992842670799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992842670799) = 1/(992842670799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2570 : Bounds (-3591533 / 500000000) (-1436613 / 200000000) (Real.log (992842670799 / 1000000000000)) := by
  have h := reflection_log_2570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2571_neg : (8480371 / 50000000) ≤ -Real.log (7812500000 / 9256559503) ∧
    -Real.log (7812500000 / 9256559503) ≤ (169607421 / 1000000000) := by
  have h := checkLog_sound (w := (1444059503 / 17069059503)) (n := 12)
    (lo := (8480371 / 50000000)) (hi := (169607421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9256559503 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9256559503 / 7812500000) = 1/(7812500000 / 9256559503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2571 : Bounds (8480371 / 50000000) (169607421 / 1000000000) (Real.log (9256559503 / 7812500000)) := by
  have h := reflection_log_2571_neg
  have he : Real.log (9256559503 / 7812500000) = -Real.log (7812500000 / 9256559503) := by
    rw [show ((9256559503 / 7812500000) : ℝ) = ((7812500000 / 9256559503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2572_neg : (85024293 / 500000000) ≤ -Real.log (500000000000 / 592681221181) ∧
    -Real.log (500000000000 / 592681221181) ≤ (170048587 / 1000000000) := by
  have h := checkLog_sound (w := (92681221181 / 1092681221181)) (n := 12)
    (lo := (85024293 / 500000000)) (hi := (170048587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592681221181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592681221181 / 500000000000) = 1/(500000000000 / 592681221181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2572 : Bounds (85024293 / 500000000) (170048587 / 1000000000) (Real.log (592681221181 / 500000000000)) := by
  have h := reflection_log_2572_neg
  have he : Real.log (592681221181 / 500000000000) = -Real.log (500000000000 / 592681221181) := by
    rw [show ((592681221181 / 500000000000) : ℝ) = ((500000000000 / 592681221181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2573_neg : (68048971 / 200000000) ≤ -Real.log (100000000000 / 140529164161) ∧
    -Real.log (100000000000 / 140529164161) ≤ (42530607 / 125000000) := by
  have h := checkLog_sound (w := (40529164161 / 240529164161)) (n := 12)
    (lo := (68048971 / 200000000)) (hi := (42530607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140529164161 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140529164161 / 100000000000) = 1/(100000000000 / 140529164161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2573 : Bounds (68048971 / 200000000) (42530607 / 125000000) (Real.log (140529164161 / 100000000000)) := by
  have h := reflection_log_2573_neg
  have he : Real.log (140529164161 / 100000000000) = -Real.log (100000000000 / 140529164161) := by
    rw [show ((140529164161 / 100000000000) : ℝ) = ((100000000000 / 140529164161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2574_neg : (340450703 / 1000000000) ≤ -Real.log (5000000000 / 7027904739) ∧
    -Real.log (5000000000 / 7027904739) ≤ (21278169 / 62500000) := by
  have h := checkLog_sound (w := (2027904739 / 12027904739)) (n := 12)
    (lo := (340450703 / 1000000000)) (hi := (21278169 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7027904739 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7027904739 / 5000000000) = 1/(5000000000 / 7027904739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2574 : Bounds (340450703 / 1000000000) (21278169 / 62500000) (Real.log (7027904739 / 5000000000)) := by
  have h := reflection_log_2574_neg
  have he : Real.log (7027904739 / 5000000000) = -Real.log (5000000000 / 7027904739) := by
    rw [show ((7027904739 / 5000000000) : ℝ) = ((5000000000 / 7027904739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2575_neg : (155892019 / 1000000000) ≤ -Real.log (10000 / 11687) ∧
    -Real.log (10000 / 11687) ≤ (7794601 / 50000000) := by
  have h := checkLog_sound (w := (1687 / 21687)) (n := 12)
    (lo := (155892019 / 1000000000)) (hi := (7794601 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11687 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11687 / 10000) = 1/(10000 / 11687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2575 : Bounds (155892019 / 1000000000) (7794601 / 50000000) (Real.log (11687 / 10000)) := by
  have h := reflection_log_2575_neg
  have he : Real.log (11687 / 10000) = -Real.log (10000 / 11687) := by
    rw [show ((11687 / 10000) : ℝ) = ((10000 / 11687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2576_neg : (92382269 / 500000000) ≤ -Real.log (8313 / 10000) ∧
    -Real.log (8313 / 10000) ≤ (184764539 / 1000000000) := by
  have h := checkLog_sound (w := (1687 / 18313)) (n := 12)
    (lo := (92382269 / 500000000)) (hi := (184764539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8313) = 1/(8313 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2576 : Bounds (-184764539 / 1000000000) (-92382269 / 500000000) (Real.log (8313 / 10000)) := by
  have h := reflection_log_2576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2577_neg : (33737 / 200000000) ≤ -Real.log (10000000 / 10001687) ∧
    -Real.log (10000000 / 10001687) ≤ (84343 / 500000000) := by
  have h := checkLog_sound (w := (1687 / 20001687)) (n := 12)
    (lo := (33737 / 200000000)) (hi := (84343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001687 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001687 / 10000000) = 1/(10000000 / 10001687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2577 : Bounds (33737 / 200000000) (84343 / 500000000) (Real.log (10001687 / 10000000)) := by
  have h := reflection_log_2577_neg
  have he : Real.log (10001687 / 10000000) = -Real.log (10000000 / 10001687) := by
    rw [show ((10001687 / 10000000) : ℝ) = ((10000000 / 10001687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2578_neg : (84357 / 500000000) ≤ -Real.log (9998313 / 10000000) ∧
    -Real.log (9998313 / 10000000) ≤ (33743 / 200000000) := by
  have h := checkLog_sound (w := (1687 / 19998313)) (n := 12)
    (lo := (84357 / 500000000)) (hi := (33743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998313) = 1/(9998313 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2578 : Bounds (-33743 / 200000000) (-84357 / 500000000) (Real.log (9998313 / 10000000)) := by
  have h := reflection_log_2578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2579_neg : (20314569 / 250000000) ≤ -Real.log (1000000 / 1084651) ∧
    -Real.log (1000000 / 1084651) ≤ (81258277 / 1000000000) := by
  have h := checkLog_sound (w := (84651 / 2084651)) (n := 12)
    (lo := (20314569 / 250000000)) (hi := (81258277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084651 / 1000000) = 1/(1000000 / 1084651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2579 : Bounds (20314569 / 250000000) (81258277 / 1000000000) (Real.log (1084651 / 1000000)) := by
  have h := reflection_log_2579_neg
  have he : Real.log (1084651 / 1000000) = -Real.log (1000000 / 1084651) := by
    rw [show ((1084651 / 1000000) : ℝ) = ((1000000 / 1084651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2580_neg : (17689973 / 200000000) ≤ -Real.log (915349 / 1000000) ∧
    -Real.log (915349 / 1000000) ≤ (44224933 / 500000000) := by
  have h := checkLog_sound (w := (84651 / 1915349)) (n := 12)
    (lo := (17689973 / 200000000)) (hi := (44224933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915349) = 1/(915349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2580 : Bounds (-44224933 / 500000000) (-17689973 / 200000000) (Real.log (915349 / 1000000)) := by
  have h := reflection_log_2580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2581_neg : (16292217 / 200000000) ≤ -Real.log (1000000 / 1084871) ∧
    -Real.log (1000000 / 1084871) ≤ (40730543 / 500000000) := by
  have h := checkLog_sound (w := (84871 / 2084871)) (n := 12)
    (lo := (16292217 / 200000000)) (hi := (40730543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084871 / 1000000) = 1/(1000000 / 1084871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2581 : Bounds (16292217 / 200000000) (40730543 / 500000000) (Real.log (1084871 / 1000000)) := by
  have h := reflection_log_2581_neg
  have he : Real.log (1084871 / 1000000) = -Real.log (1000000 / 1084871) := by
    rw [show ((1084871 / 1000000) : ℝ) = ((1000000 / 1084871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2582_neg : (277157 / 3125000) ≤ -Real.log (915129 / 1000000) ∧
    -Real.log (915129 / 1000000) ≤ (88690241 / 1000000000) := by
  have h := checkLog_sound (w := (84871 / 1915129)) (n := 12)
    (lo := (277157 / 3125000)) (hi := (88690241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915129) = 1/(915129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2582 : Bounds (-88690241 / 1000000000) (-277157 / 3125000) (Real.log (915129 / 1000000)) := by
  have h := reflection_log_2582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2583_neg : (3614577 / 500000000) ≤ -Real.log (992796913359 / 1000000000000) ∧
    -Real.log (992796913359 / 1000000000000) ≤ (1445831 / 200000000) := by
  have h := checkLog_sound (w := (7203086641 / 1992796913359)) (n := 12)
    (lo := (3614577 / 500000000)) (hi := (1445831 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992796913359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992796913359) = 1/(992796913359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2583 : Bounds (-1445831 / 200000000) (-3614577 / 500000000) (Real.log (992796913359 / 1000000000000)) := by
  have h := reflection_log_2583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2584_neg : (7191589 / 1000000000) ≤ -Real.log (992834208199 / 1000000000000) ∧
    -Real.log (992834208199 / 1000000000000) ≤ (719159 / 100000000) := by
  have h := checkLog_sound (w := (7165791801 / 1992834208199)) (n := 12)
    (lo := (7191589 / 1000000000)) (hi := (719159 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992834208199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992834208199) = 1/(992834208199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2584 : Bounds (-719159 / 100000000) (-7191589 / 1000000000) (Real.log (992834208199 / 1000000000000)) := by
  have h := reflection_log_2584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2585_neg : (169708141 / 1000000000) ≤ -Real.log (62500000000 / 74059935063) ∧
    -Real.log (62500000000 / 74059935063) ≤ (84854071 / 500000000) := by
  have h := checkLog_sound (w := (11559935063 / 136559935063)) (n := 12)
    (lo := (169708141 / 1000000000)) (hi := (84854071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74059935063 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74059935063 / 62500000000) = 1/(62500000000 / 74059935063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2585 : Bounds (169708141 / 1000000000) (84854071 / 500000000) (Real.log (74059935063 / 62500000000)) := by
  have h := reflection_log_2585_neg
  have he : Real.log (74059935063 / 62500000000) = -Real.log (62500000000 / 74059935063) := by
    rw [show ((74059935063 / 62500000000) : ℝ) = ((62500000000 / 74059935063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2586_neg : (6806053 / 40000000) ≤ -Real.log (500000000000 / 592742116139) ∧
    -Real.log (500000000000 / 592742116139) ≤ (85075663 / 500000000) := by
  have h := checkLog_sound (w := (92742116139 / 1092742116139)) (n := 12)
    (lo := (6806053 / 40000000)) (hi := (85075663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592742116139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592742116139 / 500000000000) = 1/(500000000000 / 592742116139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2586 : Bounds (6806053 / 40000000) (85075663 / 500000000) (Real.log (592742116139 / 500000000000)) := by
  have h := reflection_log_2586_neg
  have he : Real.log (592742116139 / 500000000000) = -Real.log (500000000000 / 592742116139) := by
    rw [show ((592742116139 / 500000000000) : ℝ) = ((500000000000 / 592742116139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2587_neg : (340450703 / 1000000000) ≤ -Real.log (500000000000 / 702790473899) ∧
    -Real.log (500000000000 / 702790473899) ≤ (21278169 / 62500000) := by
  have h := checkLog_sound (w := (202790473899 / 1202790473899)) (n := 12)
    (lo := (340450703 / 1000000000)) (hi := (21278169 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702790473899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702790473899 / 500000000000) = 1/(500000000000 / 702790473899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2587 : Bounds (340450703 / 1000000000) (21278169 / 62500000) (Real.log (702790473899 / 500000000000)) := by
  have h := reflection_log_2587_neg
  have he : Real.log (702790473899 / 500000000000) = -Real.log (500000000000 / 702790473899) := by
    rw [show ((702790473899 / 500000000000) : ℝ) = ((500000000000 / 702790473899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2588_neg : (170328279 / 500000000) ≤ -Real.log (100000000000 / 140587032359) ∧
    -Real.log (100000000000 / 140587032359) ≤ (340656559 / 1000000000) := by
  have h := checkLog_sound (w := (40587032359 / 240587032359)) (n := 12)
    (lo := (170328279 / 500000000)) (hi := (340656559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140587032359 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140587032359 / 100000000000) = 1/(100000000000 / 140587032359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2588 : Bounds (170328279 / 500000000) (340656559 / 1000000000) (Real.log (140587032359 / 100000000000)) := by
  have h := reflection_log_2588_neg
  have he : Real.log (140587032359 / 100000000000) = -Real.log (100000000000 / 140587032359) := by
    rw [show ((140587032359 / 100000000000) : ℝ) = ((100000000000 / 140587032359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2589_neg : (155977581 / 1000000000) ≤ -Real.log (1250 / 1461) ∧
    -Real.log (1250 / 1461) ≤ (77988791 / 500000000) := by
  have h := checkLog_sound (w := (211 / 2711)) (n := 12)
    (lo := (155977581 / 1000000000)) (hi := (77988791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1461 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1461 / 1250) = 1/(1250 / 1461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2589 : Bounds (155977581 / 1000000000) (77988791 / 500000000) (Real.log (1461 / 1250)) := by
  have h := reflection_log_2589_neg
  have he : Real.log (1461 / 1250) = -Real.log (1250 / 1461) := by
    rw [show ((1461 / 1250) : ℝ) = ((1250 / 1461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2590_neg : (184884839 / 1000000000) ≤ -Real.log (1039 / 1250) ∧
    -Real.log (1039 / 1250) ≤ (4622121 / 25000000) := by
  have h := checkLog_sound (w := (211 / 2289)) (n := 12)
    (lo := (184884839 / 1000000000)) (hi := (4622121 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1039) = 1/(1039 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2590 : Bounds (-4622121 / 25000000) (-184884839 / 1000000000) (Real.log (1039 / 1250)) := by
  have h := reflection_log_2590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2591_neg : (33757 / 200000000) ≤ -Real.log (1250000 / 1250211) ∧
    -Real.log (1250000 / 1250211) ≤ (84393 / 500000000) := by
  have h := checkLog_sound (w := (211 / 2500211)) (n := 12)
    (lo := (33757 / 200000000)) (hi := (84393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250211 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250211 / 1250000) = 1/(1250000 / 1250211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2591 : Bounds (33757 / 200000000) (84393 / 500000000) (Real.log (1250211 / 1250000)) := by
  have h := reflection_log_2591_neg
  have he : Real.log (1250211 / 1250000) = -Real.log (1250000 / 1250211) := by
    rw [show ((1250211 / 1250000) : ℝ) = ((1250000 / 1250211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2592_neg : (84407 / 500000000) ≤ -Real.log (1249789 / 1250000) ∧
    -Real.log (1249789 / 1250000) ≤ (33763 / 200000000) := by
  have h := checkLog_sound (w := (211 / 2499789)) (n := 12)
    (lo := (84407 / 500000000)) (hi := (33763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249789) = 1/(1249789 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2592 : Bounds (-33763 / 200000000) (-84407 / 500000000) (Real.log (1249789 / 1250000)) := by
  have h := reflection_log_2592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2593_neg : (40652647 / 500000000) ≤ -Real.log (500000 / 542351) ∧
    -Real.log (500000 / 542351) ≤ (16261059 / 200000000) := by
  have h := checkLog_sound (w := (42351 / 1042351)) (n := 12)
    (lo := (40652647 / 500000000)) (hi := (16261059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542351 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542351 / 500000) = 1/(500000 / 542351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2593 : Bounds (40652647 / 500000000) (16261059 / 200000000) (Real.log (542351 / 500000)) := by
  have h := reflection_log_2593_neg
  have he : Real.log (542351 / 500000) = -Real.log (500000 / 542351) := by
    rw [show ((542351 / 500000) : ℝ) = ((500000 / 542351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2594_neg : (88505583 / 1000000000) ≤ -Real.log (457649 / 500000) ∧
    -Real.log (457649 / 500000) ≤ (5531599 / 62500000) := by
  have h := checkLog_sound (w := (42351 / 957649)) (n := 12)
    (lo := (88505583 / 1000000000)) (hi := (5531599 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457649) = 1/(457649 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2594 : Bounds (-5531599 / 62500000) (-88505583 / 1000000000) (Real.log (457649 / 500000)) := by
  have h := reflection_log_2594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2595_neg : (16301619 / 200000000) ≤ -Real.log (500000 / 542461) ∧
    -Real.log (500000 / 542461) ≤ (318391 / 3906250) := by
  have h := checkLog_sound (w := (42461 / 1042461)) (n := 12)
    (lo := (16301619 / 200000000)) (hi := (318391 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542461 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542461 / 500000) = 1/(500000 / 542461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2595 : Bounds (16301619 / 200000000) (318391 / 3906250) (Real.log (542461 / 500000)) := by
  have h := reflection_log_2595_neg
  have he : Real.log (542461 / 500000) = -Real.log (500000 / 542461) := by
    rw [show ((542461 / 500000) : ℝ) = ((500000 / 542461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2596_neg : (88745971 / 1000000000) ≤ -Real.log (457539 / 500000) ∧
    -Real.log (457539 / 500000) ≤ (22186493 / 250000000) := by
  have h := checkLog_sound (w := (42461 / 957539)) (n := 12)
    (lo := (88745971 / 1000000000)) (hi := (22186493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457539) = 1/(457539 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2596 : Bounds (-22186493 / 250000000) (-88745971 / 1000000000) (Real.log (457539 / 500000)) := by
  have h := reflection_log_2596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2597_neg : (1809469 / 250000000) ≤ -Real.log (248197063479 / 250000000000) ∧
    -Real.log (248197063479 / 250000000000) ≤ (7237877 / 1000000000) := by
  have h := checkLog_sound (w := (1802936521 / 498197063479)) (n := 12)
    (lo := (1809469 / 250000000)) (hi := (7237877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248197063479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248197063479) = 1/(248197063479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2597 : Bounds (-7237877 / 1000000000) (-1809469 / 250000000) (Real.log (248197063479 / 250000000000)) := by
  have h := reflection_log_2597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2598_neg : (225009 / 31250000) ≤ -Real.log (248206392799 / 250000000000) ∧
    -Real.log (248206392799 / 250000000000) ≤ (7200289 / 1000000000) := by
  have h := checkLog_sound (w := (1793607201 / 498206392799)) (n := 12)
    (lo := (225009 / 31250000)) (hi := (7200289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248206392799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248206392799) = 1/(248206392799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2598 : Bounds (-7200289 / 1000000000) (-225009 / 31250000) (Real.log (248206392799 / 250000000000)) := by
  have h := reflection_log_2598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2599_neg : (84905439 / 500000000) ≤ -Real.log (500000000000 / 592540352977) ∧
    -Real.log (500000000000 / 592540352977) ≤ (169810879 / 1000000000) := by
  have h := checkLog_sound (w := (92540352977 / 1092540352977)) (n := 12)
    (lo := (84905439 / 500000000)) (hi := (169810879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592540352977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592540352977 / 500000000000) = 1/(500000000000 / 592540352977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2599 : Bounds (84905439 / 500000000) (169810879 / 1000000000) (Real.log (592540352977 / 500000000000)) := by
  have h := reflection_log_2599_neg
  have he : Real.log (592540352977 / 500000000000) = -Real.log (500000000000 / 592540352977) := by
    rw [show ((592540352977 / 500000000000) : ℝ) = ((500000000000 / 592540352977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2600_neg : (85127033 / 500000000) ≤ -Real.log (100000000000 / 118560603577) ∧
    -Real.log (100000000000 / 118560603577) ≤ (170254067 / 1000000000) := by
  have h := checkLog_sound (w := (18560603577 / 218560603577)) (n := 12)
    (lo := (85127033 / 500000000)) (hi := (170254067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118560603577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118560603577 / 100000000000) = 1/(100000000000 / 118560603577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2600 : Bounds (85127033 / 500000000) (170254067 / 1000000000) (Real.log (118560603577 / 100000000000)) := by
  have h := reflection_log_2600_neg
  have he : Real.log (118560603577 / 100000000000) = -Real.log (100000000000 / 118560603577) := by
    rw [show ((118560603577 / 100000000000) : ℝ) = ((100000000000 / 118560603577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2601_neg : (170328279 / 500000000) ≤ -Real.log (250000000000 / 351467580897) ∧
    -Real.log (250000000000 / 351467580897) ≤ (340656559 / 1000000000) := by
  have h := checkLog_sound (w := (101467580897 / 601467580897)) (n := 12)
    (lo := (170328279 / 500000000)) (hi := (340656559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351467580897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351467580897 / 250000000000) = 1/(250000000000 / 351467580897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2601 : Bounds (170328279 / 500000000) (340656559 / 1000000000) (Real.log (351467580897 / 250000000000)) := by
  have h := reflection_log_2601_neg
  have he : Real.log (351467580897 / 250000000000) = -Real.log (250000000000 / 351467580897) := by
    rw [show ((351467580897 / 250000000000) : ℝ) = ((250000000000 / 351467580897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2602_neg : (17043121 / 50000000) ≤ -Real.log (100000000000 / 140615976901) ∧
    -Real.log (100000000000 / 140615976901) ≤ (340862421 / 1000000000) := by
  have h := checkLog_sound (w := (40615976901 / 240615976901)) (n := 12)
    (lo := (17043121 / 50000000)) (hi := (340862421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140615976901 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140615976901 / 100000000000) = 1/(100000000000 / 140615976901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2602 : Bounds (17043121 / 50000000) (340862421 / 1000000000) (Real.log (140615976901 / 100000000000)) := by
  have h := reflection_log_2602_neg
  have he : Real.log (140615976901 / 100000000000) = -Real.log (100000000000 / 140615976901) := by
    rw [show ((140615976901 / 100000000000) : ℝ) = ((100000000000 / 140615976901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2603_neg : (31212627 / 200000000) ≤ -Real.log (10000 / 11689) ∧
    -Real.log (10000 / 11689) ≤ (4876973 / 31250000) := by
  have h := checkLog_sound (w := (1689 / 21689)) (n := 12)
    (lo := (31212627 / 200000000)) (hi := (4876973 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11689 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11689 / 10000) = 1/(10000 / 11689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2603 : Bounds (31212627 / 200000000) (4876973 / 31250000) (Real.log (11689 / 10000)) := by
  have h := reflection_log_2603_neg
  have he : Real.log (11689 / 10000) = -Real.log (10000 / 11689) := by
    rw [show ((11689 / 10000) : ℝ) = ((10000 / 11689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2604_neg : (92502577 / 500000000) ≤ -Real.log (8311 / 10000) ∧
    -Real.log (8311 / 10000) ≤ (37001031 / 200000000) := by
  have h := checkLog_sound (w := (1689 / 18311)) (n := 12)
    (lo := (92502577 / 500000000)) (hi := (37001031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8311) = 1/(8311 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2604 : Bounds (-37001031 / 200000000) (-92502577 / 500000000) (Real.log (8311 / 10000)) := by
  have h := reflection_log_2604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2605_neg : (33777 / 200000000) ≤ -Real.log (10000000 / 10001689) ∧
    -Real.log (10000000 / 10001689) ≤ (84443 / 500000000) := by
  have h := checkLog_sound (w := (1689 / 20001689)) (n := 12)
    (lo := (33777 / 200000000)) (hi := (84443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001689 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001689 / 10000000) = 1/(10000000 / 10001689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2605 : Bounds (33777 / 200000000) (84443 / 500000000) (Real.log (10001689 / 10000000)) := by
  have h := reflection_log_2605_neg
  have he : Real.log (10001689 / 10000000) = -Real.log (10000000 / 10001689) := by
    rw [show ((10001689 / 10000000) : ℝ) = ((10000000 / 10001689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2606_neg : (84457 / 500000000) ≤ -Real.log (9998311 / 10000000) ∧
    -Real.log (9998311 / 10000000) ≤ (33783 / 200000000) := by
  have h := checkLog_sound (w := (1689 / 19998311)) (n := 12)
    (lo := (84457 / 500000000)) (hi := (33783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998311) = 1/(9998311 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2606 : Bounds (-33783 / 200000000) (-84457 / 500000000) (Real.log (9998311 / 10000000)) := by
  have h := reflection_log_2606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2607_neg : (81352311 / 1000000000) ≤ -Real.log (1000000 / 1084753) ∧
    -Real.log (1000000 / 1084753) ≤ (10169039 / 125000000) := by
  have h := checkLog_sound (w := (84753 / 2084753)) (n := 12)
    (lo := (81352311 / 1000000000)) (hi := (10169039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084753 / 1000000) = 1/(1000000 / 1084753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2607 : Bounds (81352311 / 1000000000) (10169039 / 125000000) (Real.log (1084753 / 1000000)) := by
  have h := reflection_log_2607_neg
  have he : Real.log (1084753 / 1000000) = -Real.log (1000000 / 1084753) := by
    rw [show ((1084753 / 1000000) : ℝ) = ((1000000 / 1084753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2608_neg : (11070163 / 125000000) ≤ -Real.log (915247 / 1000000) ∧
    -Real.log (915247 / 1000000) ≤ (17712261 / 200000000) := by
  have h := checkLog_sound (w := (84753 / 1915247)) (n := 12)
    (lo := (11070163 / 125000000)) (hi := (17712261 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915247) = 1/(915247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2608 : Bounds (-17712261 / 200000000) (-11070163 / 125000000) (Real.log (915247 / 1000000)) := by
  have h := reflection_log_2608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2609_neg : (81555101 / 1000000000) ≤ -Real.log (1000000 / 1084973) ∧
    -Real.log (1000000 / 1084973) ≤ (40777551 / 500000000) := by
  have h := checkLog_sound (w := (84973 / 2084973)) (n := 12)
    (lo := (81555101 / 1000000000)) (hi := (40777551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084973 / 1000000) = 1/(1000000 / 1084973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2609 : Bounds (81555101 / 1000000000) (40777551 / 500000000) (Real.log (1084973 / 1000000)) := by
  have h := reflection_log_2609_neg
  have he : Real.log (1084973 / 1000000) = -Real.log (1000000 / 1084973) := by
    rw [show ((1084973 / 1000000) : ℝ) = ((1000000 / 1084973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2610_neg : (17760341 / 200000000) ≤ -Real.log (915027 / 1000000) ∧
    -Real.log (915027 / 1000000) ≤ (44400853 / 500000000) := by
  have h := checkLog_sound (w := (84973 / 1915027)) (n := 12)
    (lo := (17760341 / 200000000)) (hi := (44400853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915027) = 1/(915027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2610 : Bounds (-44400853 / 500000000) (-17760341 / 200000000) (Real.log (915027 / 1000000)) := by
  have h := reflection_log_2610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2611_neg : (1811651 / 250000000) ≤ -Real.log (992779589271 / 1000000000000) ∧
    -Real.log (992779589271 / 1000000000000) ≤ (1449321 / 200000000) := by
  have h := checkLog_sound (w := (7220410729 / 1992779589271)) (n := 12)
    (lo := (1811651 / 250000000)) (hi := (1449321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992779589271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992779589271) = 1/(992779589271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2611 : Bounds (-1449321 / 200000000) (-1811651 / 250000000) (Real.log (992779589271 / 1000000000000)) := by
  have h := reflection_log_2611_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2612_neg : (7208993 / 1000000000) ≤ -Real.log (992816928991 / 1000000000000) ∧
    -Real.log (992816928991 / 1000000000000) ≤ (3604497 / 500000000) := by
  have h := checkLog_sound (w := (7183071009 / 1992816928991)) (n := 12)
    (lo := (7208993 / 1000000000)) (hi := (3604497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992816928991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992816928991) = 1/(992816928991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2612 : Bounds (-3604497 / 500000000) (-7208993 / 1000000000) (Real.log (992816928991 / 1000000000000)) := by
  have h := reflection_log_2612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2613_neg : (10619601 / 62500000) ≤ -Real.log (100000000000 / 118520246447) ∧
    -Real.log (100000000000 / 118520246447) ≤ (169913617 / 1000000000) := by
  have h := checkLog_sound (w := (18520246447 / 218520246447)) (n := 12)
    (lo := (10619601 / 62500000)) (hi := (169913617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118520246447 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118520246447 / 100000000000) = 1/(100000000000 / 118520246447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2613 : Bounds (10619601 / 62500000) (169913617 / 1000000000) (Real.log (118520246447 / 100000000000)) := by
  have h := reflection_log_2613_neg
  have he : Real.log (118520246447 / 100000000000) = -Real.log (100000000000 / 118520246447) := by
    rw [show ((118520246447 / 100000000000) : ℝ) = ((100000000000 / 118520246447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2614_neg : (170356807 / 1000000000) ≤ -Real.log (25000000000 / 29643196321) ∧
    -Real.log (25000000000 / 29643196321) ≤ (21294601 / 125000000) := by
  have h := checkLog_sound (w := (4643196321 / 54643196321)) (n := 12)
    (lo := (170356807 / 1000000000)) (hi := (21294601 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29643196321 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29643196321 / 25000000000) = 1/(25000000000 / 29643196321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2614 : Bounds (170356807 / 1000000000) (21294601 / 125000000) (Real.log (29643196321 / 25000000000)) := by
  have h := reflection_log_2614_neg
  have he : Real.log (29643196321 / 25000000000) = -Real.log (25000000000 / 29643196321) := by
    rw [show ((29643196321 / 25000000000) : ℝ) = ((25000000000 / 29643196321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2615_neg : (17043121 / 50000000) ≤ -Real.log (62500000000 / 87884985563) ∧
    -Real.log (62500000000 / 87884985563) ≤ (340862421 / 1000000000) := by
  have h := checkLog_sound (w := (25384985563 / 150384985563)) (n := 12)
    (lo := (17043121 / 50000000)) (hi := (340862421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87884985563 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87884985563 / 62500000000) = 1/(62500000000 / 87884985563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2615 : Bounds (17043121 / 50000000) (340862421 / 1000000000) (Real.log (87884985563 / 62500000000)) := by
  have h := reflection_log_2615_neg
  have he : Real.log (87884985563 / 62500000000) = -Real.log (62500000000 / 87884985563) := by
    rw [show ((87884985563 / 62500000000) : ℝ) = ((62500000000 / 87884985563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2616_neg : (34106829 / 100000000) ≤ -Real.log (500000000000 / 703224642041) ∧
    -Real.log (500000000000 / 703224642041) ≤ (341068291 / 1000000000) := by
  have h := checkLog_sound (w := (203224642041 / 1203224642041)) (n := 12)
    (lo := (34106829 / 100000000)) (hi := (341068291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703224642041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703224642041 / 500000000000) = 1/(500000000000 / 703224642041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2616 : Bounds (34106829 / 100000000) (341068291 / 1000000000) (Real.log (703224642041 / 500000000000)) := by
  have h := reflection_log_2616_neg
  have he : Real.log (703224642041 / 500000000000) = -Real.log (500000000000 / 703224642041) := by
    rw [show ((703224642041 / 500000000000) : ℝ) = ((500000000000 / 703224642041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2617_neg : (78074341 / 500000000) ≤ -Real.log (1000 / 1169) ∧
    -Real.log (1000 / 1169) ≤ (156148683 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 2169)) (n := 12)
    (lo := (78074341 / 500000000)) (hi := (156148683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169 / 1000) = 1/(1000 / 1169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2617 : Bounds (78074341 / 500000000) (156148683 / 1000000000) (Real.log (1169 / 1000)) := by
  have h := reflection_log_2617_neg
  have he : Real.log (1169 / 1000) = -Real.log (1000 / 1169) := by
    rw [show ((1169 / 1000) : ℝ) = ((1000 / 1169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2618_neg : (46281371 / 250000000) ≤ -Real.log (831 / 1000) ∧
    -Real.log (831 / 1000) ≤ (37025097 / 200000000) := by
  have h := checkLog_sound (w := (169 / 1831)) (n := 12)
    (lo := (46281371 / 250000000)) (hi := (37025097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 831) = 1/(831 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2618 : Bounds (-37025097 / 200000000) (-46281371 / 250000000) (Real.log (831 / 1000)) := by
  have h := reflection_log_2618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2619_neg : (33797 / 200000000) ≤ -Real.log (1000000 / 1000169) ∧
    -Real.log (1000000 / 1000169) ≤ (84493 / 500000000) := by
  have h := checkLog_sound (w := (169 / 2000169)) (n := 12)
    (lo := (33797 / 200000000)) (hi := (84493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000169 / 1000000) = 1/(1000000 / 1000169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2619 : Bounds (33797 / 200000000) (84493 / 500000000) (Real.log (1000169 / 1000000)) := by
  have h := reflection_log_2619_neg
  have he : Real.log (1000169 / 1000000) = -Real.log (1000000 / 1000169) := by
    rw [show ((1000169 / 1000000) : ℝ) = ((1000000 / 1000169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2620_neg : (84507 / 500000000) ≤ -Real.log (999831 / 1000000) ∧
    -Real.log (999831 / 1000000) ≤ (33803 / 200000000) := by
  have h := checkLog_sound (w := (169 / 1999831)) (n := 12)
    (lo := (84507 / 500000000)) (hi := (33803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999831) = 1/(999831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2620 : Bounds (-33803 / 200000000) (-84507 / 500000000) (Real.log (999831 / 1000000)) := by
  have h := reflection_log_2620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2621_neg : (3255973 / 40000000) ≤ -Real.log (250000 / 271201) ∧
    -Real.log (250000 / 271201) ≤ (40699663 / 500000000) := by
  have h := checkLog_sound (w := (21201 / 521201)) (n := 12)
    (lo := (3255973 / 40000000)) (hi := (40699663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271201 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271201 / 250000) = 1/(250000 / 271201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2621 : Bounds (3255973 / 40000000) (40699663 / 500000000) (Real.log (271201 / 250000)) := by
  have h := reflection_log_2621_neg
  have he : Real.log (271201 / 250000) = -Real.log (250000 / 271201) := by
    rw [show ((271201 / 250000) : ℝ) = ((250000 / 271201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2622_neg : (22154257 / 250000000) ≤ -Real.log (228799 / 250000) ∧
    -Real.log (228799 / 250000) ≤ (88617029 / 1000000000) := by
  have h := checkLog_sound (w := (21201 / 478799)) (n := 12)
    (lo := (22154257 / 250000000)) (hi := (88617029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228799) = 1/(228799 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2622 : Bounds (-88617029 / 1000000000) (-22154257 / 250000000) (Real.log (228799 / 250000)) := by
  have h := reflection_log_2622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2623_neg : (2550037 / 31250000) ≤ -Real.log (1000000 / 1085023) ∧
    -Real.log (1000000 / 1085023) ≤ (16320237 / 200000000) := by
  have h := checkLog_sound (w := (85023 / 2085023)) (n := 12)
    (lo := (2550037 / 31250000)) (hi := (16320237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085023 / 1000000) = 1/(1000000 / 1085023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2623 : Bounds (2550037 / 31250000) (16320237 / 200000000) (Real.log (1085023 / 1000000)) := by
  have h := reflection_log_2623_neg
  have he : Real.log (1085023 / 1000000) = -Real.log (1000000 / 1085023) := by
    rw [show ((1085023 / 1000000) : ℝ) = ((1000000 / 1085023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


