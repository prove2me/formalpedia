-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0148__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0148__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T00:02:18.486146+00:00
-- url     : https://prove2.me/theorems/8c5b6871-3cdd-49c5-8ad9-d72c206b8950
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0148 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0149, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0148 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0149, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0150)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0148 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0149, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0150)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0148 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0149, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0150) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0148 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0149, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0150).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0148 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9472_neg : (145021 / 500000000) ≤ -Real.log (99971 / 100000) ∧
    -Real.log (99971 / 100000) ≤ (290043 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 199971)) (n := 12)
    (lo := (145021 / 500000000)) (hi := (290043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99971) = 1/(99971 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9472 : Bounds (-290043 / 1000000000) (-145021 / 500000000) (Real.log (99971 / 100000)) := by
  have h := reflection_log_9472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9473_neg : (137019053 / 1000000000) ≤ -Real.log (20000 / 22937) ∧
    -Real.log (20000 / 22937) ≤ (68509527 / 500000000) := by
  have h := checkLog_sound (w := (2937 / 42937)) (n := 12)
    (lo := (137019053 / 1000000000)) (hi := (68509527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22937 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22937 / 20000) = 1/(20000 / 22937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9473 : Bounds (137019053 / 1000000000) (68509527 / 500000000) (Real.log (22937 / 20000)) := by
  have h := reflection_log_9473_neg
  have he : Real.log (22937 / 20000) = -Real.log (20000 / 22937) := by
    rw [show ((22937 / 20000) : ℝ) = ((20000 / 22937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9474_neg : (158819897 / 1000000000) ≤ -Real.log (17063 / 20000) ∧
    -Real.log (17063 / 20000) ≤ (79409949 / 500000000) := by
  have h := checkLog_sound (w := (2937 / 37063)) (n := 12)
    (lo := (158819897 / 1000000000)) (hi := (79409949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 17063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 17063) = 1/(17063 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9474 : Bounds (-79409949 / 500000000) (-158819897 / 1000000000) (Real.log (17063 / 20000)) := by
  have h := reflection_log_9474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9475_neg : (13749677 / 100000000) ≤ -Real.log (500000 / 573699) ∧
    -Real.log (500000 / 573699) ≤ (137496771 / 1000000000) := by
  have h := checkLog_sound (w := (73699 / 1073699)) (n := 12)
    (lo := (13749677 / 100000000)) (hi := (137496771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(573699 / 500000) = 1/(500000 / 573699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9475 : Bounds (13749677 / 100000000) (137496771 / 1000000000) (Real.log (573699 / 500000)) := by
  have h := reflection_log_9475_neg
  have he : Real.log (573699 / 500000) = -Real.log (500000 / 573699) := by
    rw [show ((573699 / 500000) : ℝ) = ((500000 / 573699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9476_neg : (39865607 / 250000000) ≤ -Real.log (426301 / 500000) ∧
    -Real.log (426301 / 500000) ≤ (159462429 / 1000000000) := by
  have h := checkLog_sound (w := (73699 / 926301)) (n := 12)
    (lo := (39865607 / 250000000)) (hi := (159462429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 426301) = 1/(426301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9476 : Bounds (-159462429 / 1000000000) (-39865607 / 250000000) (Real.log (426301 / 500000)) := by
  have h := reflection_log_9476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9477_neg : (10982829 / 500000000) ≤ -Real.log (244568457399 / 250000000000) ∧
    -Real.log (244568457399 / 250000000000) ≤ (21965659 / 1000000000) := by
  have h := checkLog_sound (w := (5431542601 / 494568457399)) (n := 12)
    (lo := (10982829 / 500000000)) (hi := (21965659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244568457399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244568457399) = 1/(244568457399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9477 : Bounds (-21965659 / 1000000000) (-10982829 / 500000000) (Real.log (244568457399 / 250000000000)) := by
  have h := reflection_log_9477_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9478_neg : (21800843 / 1000000000) ≤ -Real.log (391374031 / 400000000) ∧
    -Real.log (391374031 / 400000000) ≤ (5450211 / 250000000) := by
  have h := checkLog_sound (w := (8625969 / 791374031)) (n := 12)
    (lo := (21800843 / 1000000000)) (hi := (5450211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 391374031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 391374031) = 1/(391374031 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9478 : Bounds (-5450211 / 250000000) (-21800843 / 1000000000) (Real.log (391374031 / 400000000)) := by
  have h := reflection_log_9478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9479_neg : (5916779 / 20000000) ≤ -Real.log (250000000000 / 336063412061) ∧
    -Real.log (250000000000 / 336063412061) ≤ (295838951 / 1000000000) := by
  have h := checkLog_sound (w := (86063412061 / 586063412061)) (n := 12)
    (lo := (5916779 / 20000000)) (hi := (295838951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336063412061 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336063412061 / 250000000000) = 1/(250000000000 / 336063412061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9479 : Bounds (5916779 / 20000000) (295838951 / 1000000000) (Real.log (336063412061 / 250000000000)) := by
  have h := reflection_log_9479_neg
  have he : Real.log (336063412061 / 250000000000) = -Real.log (250000000000 / 336063412061) := by
    rw [show ((336063412061 / 250000000000) : ℝ) = ((250000000000 / 336063412061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9480_neg : (296959199 / 1000000000) ≤ -Real.log (25000000000 / 33644009749) ∧
    -Real.log (25000000000 / 33644009749) ≤ (371199 / 1250000) := by
  have h := checkLog_sound (w := (8644009749 / 58644009749)) (n := 12)
    (lo := (296959199 / 1000000000)) (hi := (371199 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33644009749 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33644009749 / 25000000000) = 1/(25000000000 / 33644009749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9480 : Bounds (296959199 / 1000000000) (371199 / 1250000) (Real.log (33644009749 / 25000000000)) := by
  have h := reflection_log_9480_neg
  have he : Real.log (33644009749 / 25000000000) = -Real.log (25000000000 / 33644009749) := by
    rw [show ((33644009749 / 25000000000) : ℝ) = ((25000000000 / 33644009749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9481_neg : (596040877 / 1000000000) ≤ -Real.log (250000000000 / 453729767769) ∧
    -Real.log (250000000000 / 453729767769) ≤ (298020439 / 500000000) := by
  have h := checkLog_sound (w := (203729767769 / 703729767769)) (n := 12)
    (lo := (596040877 / 1000000000)) (hi := (298020439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((453729767769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(453729767769 / 250000000000) = 1/(250000000000 / 453729767769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9481 : Bounds (596040877 / 1000000000) (298020439 / 500000000) (Real.log (453729767769 / 250000000000)) := by
  have h := reflection_log_9481_neg
  have he : Real.log (453729767769 / 250000000000) = -Real.log (250000000000 / 453729767769) := by
    rw [show ((453729767769 / 250000000000) : ℝ) = ((250000000000 / 453729767769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9482_neg : (597132527 / 1000000000) ≤ -Real.log (250000000000 / 454225352113) ∧
    -Real.log (250000000000 / 454225352113) ≤ (37320783 / 62500000) := by
  have h := checkLog_sound (w := (204225352113 / 704225352113)) (n := 12)
    (lo := (597132527 / 1000000000)) (hi := (37320783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((454225352113 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(454225352113 / 250000000000) = 1/(250000000000 / 454225352113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9482 : Bounds (597132527 / 1000000000) (37320783 / 62500000) (Real.log (454225352113 / 250000000000)) := by
  have h := reflection_log_9482_neg
  have he : Real.log (454225352113 / 250000000000) = -Real.log (250000000000 / 454225352113) := by
    rw [show ((454225352113 / 250000000000) : ℝ) = ((250000000000 / 454225352113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9483_neg : (12751487 / 50000000) ≤ -Real.log (2000 / 2581) ∧
    -Real.log (2000 / 2581) ≤ (255029741 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 4581)) (n := 12)
    (lo := (12751487 / 50000000)) (hi := (255029741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2581 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2581 / 2000) = 1/(2000 / 2581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9483 : Bounds (12751487 / 50000000) (255029741 / 1000000000) (Real.log (2581 / 2000)) := by
  have h := reflection_log_9483_neg
  have he : Real.log (2581 / 2000) = -Real.log (2000 / 2581) := by
    rw [show ((2581 / 2000) : ℝ) = ((2000 / 2581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9484_neg : (171597391 / 500000000) ≤ -Real.log (1419 / 2000) ∧
    -Real.log (1419 / 2000) ≤ (343194783 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 3419)) (n := 12)
    (lo := (171597391 / 500000000)) (hi := (343194783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1419) = 1/(1419 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9484 : Bounds (-343194783 / 1000000000) (-171597391 / 500000000) (Real.log (1419 / 2000)) := by
  have h := reflection_log_9484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9485_neg : (290457 / 1000000000) ≤ -Real.log (2000000 / 2000581) ∧
    -Real.log (2000000 / 2000581) ≤ (145229 / 500000000) := by
  have h := checkLog_sound (w := (581 / 4000581)) (n := 12)
    (lo := (290457 / 1000000000)) (hi := (145229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000581 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000581 / 2000000) = 1/(2000000 / 2000581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9485 : Bounds (290457 / 1000000000) (145229 / 500000000) (Real.log (2000581 / 2000000)) := by
  have h := reflection_log_9485_neg
  have he : Real.log (2000581 / 2000000) = -Real.log (2000000 / 2000581) := by
    rw [show ((2000581 / 2000000) : ℝ) = ((2000000 / 2000581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9486_neg : (145271 / 500000000) ≤ -Real.log (1999419 / 2000000) ∧
    -Real.log (1999419 / 2000000) ≤ (290543 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 3999419)) (n := 12)
    (lo := (145271 / 500000000)) (hi := (290543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999419) = 1/(1999419 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9486 : Bounds (-290543 / 1000000000) (-145271 / 500000000) (Real.log (1999419 / 2000000)) := by
  have h := reflection_log_9486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9487_neg : (137247479 / 1000000000) ≤ -Real.log (125000 / 143389) ∧
    -Real.log (125000 / 143389) ≤ (3431187 / 25000000) := by
  have h := checkLog_sound (w := (18389 / 268389)) (n := 12)
    (lo := (137247479 / 1000000000)) (hi := (3431187 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143389 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143389 / 125000) = 1/(125000 / 143389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9487 : Bounds (137247479 / 1000000000) (3431187 / 25000000) (Real.log (143389 / 125000)) := by
  have h := reflection_log_9487_neg
  have he : Real.log (143389 / 125000) = -Real.log (125000 / 143389) := by
    rw [show ((143389 / 125000) : ℝ) = ((125000 / 143389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9488_neg : (159127041 / 1000000000) ≤ -Real.log (106611 / 125000) ∧
    -Real.log (106611 / 125000) ≤ (79563521 / 500000000) := by
  have h := checkLog_sound (w := (18389 / 231611)) (n := 12)
    (lo := (159127041 / 1000000000)) (hi := (79563521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106611) = 1/(106611 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9488 : Bounds (-79563521 / 500000000) (-159127041 / 1000000000) (Real.log (106611 / 125000)) := by
  have h := reflection_log_9488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9489_neg : (68862543 / 500000000) ≤ -Real.log (50000 / 57383) ∧
    -Real.log (50000 / 57383) ≤ (137725087 / 1000000000) := by
  have h := checkLog_sound (w := (7383 / 107383)) (n := 12)
    (lo := (68862543 / 500000000)) (hi := (137725087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57383 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57383 / 50000) = 1/(50000 / 57383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9489 : Bounds (68862543 / 500000000) (137725087 / 1000000000) (Real.log (57383 / 50000)) := by
  have h := reflection_log_9489_neg
  have he : Real.log (57383 / 50000) = -Real.log (50000 / 57383) := by
    rw [show ((57383 / 50000) : ℝ) = ((50000 / 57383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9490_neg : (15976977 / 100000000) ≤ -Real.log (42617 / 50000) ∧
    -Real.log (42617 / 50000) ≤ (159769771 / 1000000000) := by
  have h := checkLog_sound (w := (7383 / 92617)) (n := 12)
    (lo := (15976977 / 100000000)) (hi := (159769771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42617) = 1/(42617 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9490 : Bounds (-159769771 / 1000000000) (-15976977 / 100000000) (Real.log (42617 / 50000)) := by
  have h := reflection_log_9490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9491_neg : (22044683 / 1000000000) ≤ -Real.log (2445491311 / 2500000000) ∧
    -Real.log (2445491311 / 2500000000) ≤ (5511171 / 250000000) := by
  have h := checkLog_sound (w := (54508689 / 4945491311)) (n := 12)
    (lo := (22044683 / 1000000000)) (hi := (5511171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2445491311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2445491311) = 1/(2445491311 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9491 : Bounds (-5511171 / 250000000) (-22044683 / 1000000000) (Real.log (2445491311 / 2500000000)) := by
  have h := reflection_log_9491_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9492_neg : (21879561 / 1000000000) ≤ -Real.log (15286844679 / 15625000000) ∧
    -Real.log (15286844679 / 15625000000) ≤ (10939781 / 500000000) := by
  have h := checkLog_sound (w := (338155321 / 30911844679)) (n := 12)
    (lo := (21879561 / 1000000000)) (hi := (10939781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15286844679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15286844679) = 1/(15286844679 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9492 : Bounds (-10939781 / 500000000) (-21879561 / 1000000000) (Real.log (15286844679 / 15625000000)) := by
  have h := reflection_log_9492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9493_neg : (7409363 / 25000000) ≤ -Real.log (125000000000 / 168121722899) ∧
    -Real.log (125000000000 / 168121722899) ≤ (296374521 / 1000000000) := by
  have h := checkLog_sound (w := (43121722899 / 293121722899)) (n := 12)
    (lo := (7409363 / 25000000)) (hi := (296374521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168121722899 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168121722899 / 125000000000) = 1/(125000000000 / 168121722899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9493 : Bounds (7409363 / 25000000) (296374521 / 1000000000) (Real.log (168121722899 / 125000000000)) := by
  have h := reflection_log_9493_neg
  have he : Real.log (168121722899 / 125000000000) = -Real.log (125000000000 / 168121722899) := by
    rw [show ((168121722899 / 125000000000) : ℝ) = ((125000000000 / 168121722899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9494_neg : (297494857 / 1000000000) ≤ -Real.log (500000000000 / 673240725533) ∧
    -Real.log (500000000000 / 673240725533) ≤ (148747429 / 500000000) := by
  have h := checkLog_sound (w := (173240725533 / 1173240725533)) (n := 12)
    (lo := (297494857 / 1000000000)) (hi := (148747429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673240725533 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673240725533 / 500000000000) = 1/(500000000000 / 673240725533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9494 : Bounds (297494857 / 1000000000) (148747429 / 500000000) (Real.log (673240725533 / 500000000000)) := by
  have h := reflection_log_9494_neg
  have he : Real.log (673240725533 / 500000000000) = -Real.log (500000000000 / 673240725533) := by
    rw [show ((673240725533 / 500000000000) : ℝ) = ((500000000000 / 673240725533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9495_neg : (597132527 / 1000000000) ≤ -Real.log (20000000000 / 36338028169) ∧
    -Real.log (20000000000 / 36338028169) ≤ (37320783 / 62500000) := by
  have h := checkLog_sound (w := (16338028169 / 56338028169)) (n := 12)
    (lo := (597132527 / 1000000000)) (hi := (37320783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36338028169 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36338028169 / 20000000000) = 1/(20000000000 / 36338028169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9495 : Bounds (597132527 / 1000000000) (37320783 / 62500000) (Real.log (36338028169 / 20000000000)) := by
  have h := reflection_log_9495_neg
  have he : Real.log (36338028169 / 20000000000) = -Real.log (20000000000 / 36338028169) := by
    rw [show ((36338028169 / 20000000000) : ℝ) = ((20000000000 / 36338028169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9496_neg : (299112261 / 500000000) ≤ -Real.log (500000000000 / 909443269909) ∧
    -Real.log (500000000000 / 909443269909) ≤ (598224523 / 1000000000) := by
  have h := checkLog_sound (w := (409443269909 / 1409443269909)) (n := 12)
    (lo := (299112261 / 500000000)) (hi := (598224523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909443269909 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909443269909 / 500000000000) = 1/(500000000000 / 909443269909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9496 : Bounds (299112261 / 500000000) (598224523 / 1000000000) (Real.log (909443269909 / 500000000000)) := by
  have h := reflection_log_9496_neg
  have he : Real.log (909443269909 / 500000000000) = -Real.log (500000000000 / 909443269909) := by
    rw [show ((909443269909 / 500000000000) : ℝ) = ((500000000000 / 909443269909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9497_neg : (255417111 / 1000000000) ≤ -Real.log (1000 / 1291) ∧
    -Real.log (1000 / 1291) ≤ (31927139 / 125000000) := by
  have h := checkLog_sound (w := (291 / 2291)) (n := 12)
    (lo := (255417111 / 1000000000)) (hi := (31927139 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1291 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1291 / 1000) = 1/(1000 / 1291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9497 : Bounds (255417111 / 1000000000) (31927139 / 125000000) (Real.log (1291 / 1000)) := by
  have h := reflection_log_9497_neg
  have he : Real.log (1291 / 1000) = -Real.log (1000 / 1291) := by
    rw [show ((1291 / 1000) : ℝ) = ((1000 / 1291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9498_neg : (42987469 / 125000000) ≤ -Real.log (709 / 1000) ∧
    -Real.log (709 / 1000) ≤ (343899753 / 1000000000) := by
  have h := checkLog_sound (w := (291 / 1709)) (n := 12)
    (lo := (42987469 / 125000000)) (hi := (343899753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 709) = 1/(709 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9498 : Bounds (-343899753 / 1000000000) (-42987469 / 125000000) (Real.log (709 / 1000)) := by
  have h := reflection_log_9498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9499_neg : (290957 / 1000000000) ≤ -Real.log (1000000 / 1000291) ∧
    -Real.log (1000000 / 1000291) ≤ (145479 / 500000000) := by
  have h := checkLog_sound (w := (291 / 2000291)) (n := 12)
    (lo := (290957 / 1000000000)) (hi := (145479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000291 / 1000000) = 1/(1000000 / 1000291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9499 : Bounds (290957 / 1000000000) (145479 / 500000000) (Real.log (1000291 / 1000000)) := by
  have h := reflection_log_9499_neg
  have he : Real.log (1000291 / 1000000) = -Real.log (1000000 / 1000291) := by
    rw [show ((1000291 / 1000000) : ℝ) = ((1000000 / 1000291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9500_neg : (145521 / 500000000) ≤ -Real.log (999709 / 1000000) ∧
    -Real.log (999709 / 1000000) ≤ (291043 / 1000000000) := by
  have h := checkLog_sound (w := (291 / 1999709)) (n := 12)
    (lo := (145521 / 500000000)) (hi := (291043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999709) = 1/(999709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9500 : Bounds (-291043 / 1000000000) (-145521 / 500000000) (Real.log (999709 / 1000000)) := by
  have h := reflection_log_9500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9501_neg : (137475853 / 1000000000) ≤ -Real.log (500000 / 573687) ∧
    -Real.log (500000 / 573687) ≤ (68737927 / 500000000) := by
  have h := checkLog_sound (w := (73687 / 1073687)) (n := 12)
    (lo := (137475853 / 1000000000)) (hi := (68737927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573687 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(573687 / 500000) = 1/(500000 / 573687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9501 : Bounds (137475853 / 1000000000) (68737927 / 500000000) (Real.log (573687 / 500000)) := by
  have h := reflection_log_9501_neg
  have he : Real.log (573687 / 500000) = -Real.log (500000 / 573687) := by
    rw [show ((573687 / 500000) : ℝ) = ((500000 / 573687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9502_neg : (3985857 / 25000000) ≤ -Real.log (426313 / 500000) ∧
    -Real.log (426313 / 500000) ≤ (159434281 / 1000000000) := by
  have h := checkLog_sound (w := (73687 / 926313)) (n := 12)
    (lo := (3985857 / 25000000)) (hi := (159434281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 426313) = 1/(426313 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9502 : Bounds (-159434281 / 1000000000) (-3985857 / 25000000) (Real.log (426313 / 500000)) := by
  have h := reflection_log_9502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9503_neg : (68977111 / 500000000) ≤ -Real.log (1000000 / 1147923) ∧
    -Real.log (1000000 / 1147923) ≤ (137954223 / 1000000000) := by
  have h := checkLog_sound (w := (147923 / 2147923)) (n := 12)
    (lo := (68977111 / 500000000)) (hi := (137954223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1147923 / 1000000) = 1/(1000000 / 1147923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9503 : Bounds (68977111 / 500000000) (137954223 / 1000000000) (Real.log (1147923 / 1000000)) := by
  have h := reflection_log_9503_neg
  have he : Real.log (1147923 / 1000000) = -Real.log (1000000 / 1147923) := by
    rw [show ((1147923 / 1000000) : ℝ) = ((1000000 / 1147923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9504_neg : (8003919 / 50000000) ≤ -Real.log (852077 / 1000000) ∧
    -Real.log (852077 / 1000000) ≤ (160078381 / 1000000000) := by
  have h := checkLog_sound (w := (147923 / 1852077)) (n := 12)
    (lo := (8003919 / 50000000)) (hi := (160078381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 852077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 852077) = 1/(852077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9504 : Bounds (-160078381 / 1000000000) (-8003919 / 50000000) (Real.log (852077 / 1000000)) := by
  have h := reflection_log_9504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9505_neg : (11062079 / 500000000) ≤ -Real.log (978118786071 / 1000000000000) ∧
    -Real.log (978118786071 / 1000000000000) ≤ (22124159 / 1000000000) := by
  have h := checkLog_sound (w := (21881213929 / 1978118786071)) (n := 12)
    (lo := (11062079 / 500000000)) (hi := (22124159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978118786071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978118786071) = 1/(978118786071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9505 : Bounds (-22124159 / 1000000000) (-11062079 / 500000000) (Real.log (978118786071 / 1000000000000)) := by
  have h := reflection_log_9505_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9506_neg : (21958427 / 1000000000) ≤ -Real.log (244570226031 / 250000000000) ∧
    -Real.log (244570226031 / 250000000000) ≤ (5489607 / 250000000) := by
  have h := checkLog_sound (w := (5429773969 / 494570226031)) (n := 12)
    (lo := (21958427 / 1000000000)) (hi := (5489607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244570226031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244570226031) = 1/(244570226031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9506 : Bounds (-5489607 / 250000000) (-21958427 / 1000000000) (Real.log (244570226031 / 250000000000)) := by
  have h := reflection_log_9506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9507_neg : (296910133 / 1000000000) ≤ -Real.log (250000000000 / 336423590179) ∧
    -Real.log (250000000000 / 336423590179) ≤ (148455067 / 500000000) := by
  have h := checkLog_sound (w := (86423590179 / 586423590179)) (n := 12)
    (lo := (296910133 / 1000000000)) (hi := (148455067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336423590179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336423590179 / 250000000000) = 1/(250000000000 / 336423590179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9507 : Bounds (296910133 / 1000000000) (148455067 / 500000000) (Real.log (336423590179 / 250000000000)) := by
  have h := reflection_log_9507_neg
  have he : Real.log (336423590179 / 250000000000) = -Real.log (250000000000 / 336423590179) := by
    rw [show ((336423590179 / 250000000000) : ℝ) = ((250000000000 / 336423590179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9508_neg : (298032603 / 1000000000) ≤ -Real.log (250000000000 / 336801427571) ∧
    -Real.log (250000000000 / 336801427571) ≤ (74508151 / 250000000) := by
  have h := checkLog_sound (w := (86801427571 / 586801427571)) (n := 12)
    (lo := (298032603 / 1000000000)) (hi := (74508151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336801427571 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336801427571 / 250000000000) = 1/(250000000000 / 336801427571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9508 : Bounds (298032603 / 1000000000) (74508151 / 250000000) (Real.log (336801427571 / 250000000000)) := by
  have h := reflection_log_9508_neg
  have he : Real.log (336801427571 / 250000000000) = -Real.log (250000000000 / 336801427571) := by
    rw [show ((336801427571 / 250000000000) : ℝ) = ((250000000000 / 336801427571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9509_neg : (299112261 / 500000000) ≤ -Real.log (125000000000 / 227360817477) ∧
    -Real.log (125000000000 / 227360817477) ≤ (598224523 / 1000000000) := by
  have h := checkLog_sound (w := (102360817477 / 352360817477)) (n := 12)
    (lo := (299112261 / 500000000)) (hi := (598224523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227360817477 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227360817477 / 125000000000) = 1/(125000000000 / 227360817477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9509 : Bounds (299112261 / 500000000) (598224523 / 1000000000) (Real.log (227360817477 / 125000000000)) := by
  have h := reflection_log_9509_neg
  have he : Real.log (227360817477 / 125000000000) = -Real.log (125000000000 / 227360817477) := by
    rw [show ((227360817477 / 125000000000) : ℝ) = ((125000000000 / 227360817477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9510_neg : (4682163 / 7812500) ≤ -Real.log (62500000000 / 113804654443) ∧
    -Real.log (62500000000 / 113804654443) ≤ (119863373 / 200000000) := by
  have h := checkLog_sound (w := (51304654443 / 176304654443)) (n := 12)
    (lo := (4682163 / 7812500)) (hi := (119863373 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113804654443 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113804654443 / 62500000000) = 1/(62500000000 / 113804654443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9510 : Bounds (4682163 / 7812500) (119863373 / 200000000) (Real.log (113804654443 / 62500000000)) := by
  have h := reflection_log_9510_neg
  have he : Real.log (113804654443 / 62500000000) = -Real.log (62500000000 / 113804654443) := by
    rw [show ((113804654443 / 62500000000) : ℝ) = ((62500000000 / 113804654443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9511_neg : (255804333 / 1000000000) ≤ -Real.log (2000 / 2583) ∧
    -Real.log (2000 / 2583) ≤ (127902167 / 500000000) := by
  have h := checkLog_sound (w := (583 / 4583)) (n := 12)
    (lo := (255804333 / 1000000000)) (hi := (127902167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2583 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2583 / 2000) = 1/(2000 / 2583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9511 : Bounds (255804333 / 1000000000) (127902167 / 500000000) (Real.log (2583 / 2000)) := by
  have h := reflection_log_9511_neg
  have he : Real.log (2583 / 2000) = -Real.log (2000 / 2583) := by
    rw [show ((2583 / 2000) : ℝ) = ((2000 / 2583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9512_neg : (344605219 / 1000000000) ≤ -Real.log (1417 / 2000) ∧
    -Real.log (1417 / 2000) ≤ (17230261 / 50000000) := by
  have h := checkLog_sound (w := (583 / 3417)) (n := 12)
    (lo := (344605219 / 1000000000)) (hi := (17230261 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1417) = 1/(1417 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9512 : Bounds (-17230261 / 50000000) (-344605219 / 1000000000) (Real.log (1417 / 2000)) := by
  have h := reflection_log_9512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9513_neg : (291457 / 1000000000) ≤ -Real.log (2000000 / 2000583) ∧
    -Real.log (2000000 / 2000583) ≤ (145729 / 500000000) := by
  have h := checkLog_sound (w := (583 / 4000583)) (n := 12)
    (lo := (291457 / 1000000000)) (hi := (145729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000583 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000583 / 2000000) = 1/(2000000 / 2000583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9513 : Bounds (291457 / 1000000000) (145729 / 500000000) (Real.log (2000583 / 2000000)) := by
  have h := reflection_log_9513_neg
  have he : Real.log (2000583 / 2000000) = -Real.log (2000000 / 2000583) := by
    rw [show ((2000583 / 2000000) : ℝ) = ((2000000 / 2000583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9514_neg : (145771 / 500000000) ≤ -Real.log (1999417 / 2000000) ∧
    -Real.log (1999417 / 2000000) ≤ (291543 / 1000000000) := by
  have h := checkLog_sound (w := (583 / 3999417)) (n := 12)
    (lo := (145771 / 500000000)) (hi := (291543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999417) = 1/(1999417 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9514 : Bounds (-291543 / 1000000000) (-145771 / 500000000) (Real.log (1999417 / 2000000)) := by
  have h := reflection_log_9514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9515_neg : (137703303 / 1000000000) ≤ -Real.log (200000 / 229527) ∧
    -Real.log (200000 / 229527) ≤ (17212913 / 125000000) := by
  have h := checkLog_sound (w := (29527 / 429527)) (n := 12)
    (lo := (137703303 / 1000000000)) (hi := (17212913 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229527 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229527 / 200000) = 1/(200000 / 229527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9515 : Bounds (137703303 / 1000000000) (17212913 / 125000000) (Real.log (229527 / 200000)) := by
  have h := reflection_log_9515_neg
  have he : Real.log (229527 / 200000) = -Real.log (200000 / 229527) := by
    rw [show ((229527 / 200000) : ℝ) = ((200000 / 229527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9516_neg : (3993511 / 25000000) ≤ -Real.log (170473 / 200000) ∧
    -Real.log (170473 / 200000) ≤ (159740441 / 1000000000) := by
  have h := checkLog_sound (w := (29527 / 370473)) (n := 12)
    (lo := (3993511 / 25000000)) (hi := (159740441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 170473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 170473) = 1/(170473 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9516 : Bounds (-159740441 / 1000000000) (-3993511 / 25000000) (Real.log (170473 / 200000)) := by
  have h := reflection_log_9516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9517_neg : (69091217 / 500000000) ≤ -Real.log (200000 / 229637) ∧
    -Real.log (200000 / 229637) ≤ (27636487 / 200000000) := by
  have h := checkLog_sound (w := (29637 / 429637)) (n := 12)
    (lo := (69091217 / 500000000)) (hi := (27636487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229637 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229637 / 200000) = 1/(200000 / 229637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9517 : Bounds (69091217 / 500000000) (27636487 / 200000000) (Real.log (229637 / 200000)) := by
  have h := reflection_log_9517_neg
  have he : Real.log (229637 / 200000) = -Real.log (200000 / 229637) := by
    rw [show ((229637 / 200000) : ℝ) = ((200000 / 229637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9518_neg : (160385911 / 1000000000) ≤ -Real.log (170363 / 200000) ∧
    -Real.log (170363 / 200000) ≤ (20048239 / 125000000) := by
  have h := checkLog_sound (w := (29637 / 370363)) (n := 12)
    (lo := (160385911 / 1000000000)) (hi := (20048239 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 170363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 170363) = 1/(170363 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9518 : Bounds (-20048239 / 125000000) (-160385911 / 1000000000) (Real.log (170363 / 200000)) := by
  have h := reflection_log_9518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9519_neg : (22203477 / 1000000000) ≤ -Real.log (39121648231 / 40000000000) ∧
    -Real.log (39121648231 / 40000000000) ≤ (11101739 / 500000000) := by
  have h := checkLog_sound (w := (878351769 / 79121648231)) (n := 12)
    (lo := (22203477 / 1000000000)) (hi := (11101739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39121648231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39121648231) = 1/(39121648231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9519 : Bounds (-11101739 / 500000000) (-22203477 / 1000000000) (Real.log (39121648231 / 40000000000)) := by
  have h := reflection_log_9519_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9520_neg : (22037137 / 1000000000) ≤ -Real.log (39128156271 / 40000000000) ∧
    -Real.log (39128156271 / 40000000000) ≤ (11018569 / 500000000) := by
  have h := checkLog_sound (w := (871843729 / 79128156271)) (n := 12)
    (lo := (22037137 / 1000000000)) (hi := (11018569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39128156271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39128156271) = 1/(39128156271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9520 : Bounds (-11018569 / 500000000) (-22037137 / 1000000000) (Real.log (39128156271 / 40000000000)) := by
  have h := reflection_log_9520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9521_neg : (297443743 / 1000000000) ≤ -Real.log (125000000000 / 168301578549) ∧
    -Real.log (125000000000 / 168301578549) ≤ (9295117 / 31250000) := by
  have h := checkLog_sound (w := (43301578549 / 293301578549)) (n := 12)
    (lo := (297443743 / 1000000000)) (hi := (9295117 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168301578549 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168301578549 / 125000000000) = 1/(125000000000 / 168301578549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9521 : Bounds (297443743 / 1000000000) (9295117 / 31250000) (Real.log (168301578549 / 125000000000)) := by
  have h := reflection_log_9521_neg
  have he : Real.log (168301578549 / 125000000000) = -Real.log (125000000000 / 168301578549) := by
    rw [show ((168301578549 / 125000000000) : ℝ) = ((125000000000 / 168301578549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9522_neg : (149284173 / 500000000) ≤ -Real.log (20000000000 / 26958553207) ∧
    -Real.log (20000000000 / 26958553207) ≤ (298568347 / 1000000000) := by
  have h := checkLog_sound (w := (6958553207 / 46958553207)) (n := 12)
    (lo := (149284173 / 500000000)) (hi := (298568347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26958553207 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26958553207 / 20000000000) = 1/(20000000000 / 26958553207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9522 : Bounds (149284173 / 500000000) (298568347 / 1000000000) (Real.log (26958553207 / 20000000000)) := by
  have h := reflection_log_9522_neg
  have he : Real.log (26958553207 / 20000000000) = -Real.log (20000000000 / 26958553207) := by
    rw [show ((26958553207 / 20000000000) : ℝ) = ((20000000000 / 26958553207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9523_neg : (4682163 / 7812500) ≤ -Real.log (500000000000 / 910437235543) ∧
    -Real.log (500000000000 / 910437235543) ≤ (119863373 / 200000000) := by
  have h := checkLog_sound (w := (410437235543 / 1410437235543)) (n := 12)
    (lo := (4682163 / 7812500)) (hi := (119863373 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((910437235543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(910437235543 / 500000000000) = 1/(500000000000 / 910437235543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9523 : Bounds (4682163 / 7812500) (119863373 / 200000000) (Real.log (910437235543 / 500000000000)) := by
  have h := reflection_log_9523_neg
  have he : Real.log (910437235543 / 500000000000) = -Real.log (500000000000 / 910437235543) := by
    rw [show ((910437235543 / 500000000000) : ℝ) = ((500000000000 / 910437235543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9524_neg : (600409553 / 1000000000) ≤ -Real.log (250000000000 / 455716302047) ∧
    -Real.log (250000000000 / 455716302047) ≤ (300204777 / 500000000) := by
  have h := checkLog_sound (w := (205716302047 / 705716302047)) (n := 12)
    (lo := (600409553 / 1000000000)) (hi := (300204777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455716302047 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455716302047 / 250000000000) = 1/(250000000000 / 455716302047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9524 : Bounds (600409553 / 1000000000) (300204777 / 500000000) (Real.log (455716302047 / 250000000000)) := by
  have h := reflection_log_9524_neg
  have he : Real.log (455716302047 / 250000000000) = -Real.log (250000000000 / 455716302047) := by
    rw [show ((455716302047 / 250000000000) : ℝ) = ((250000000000 / 455716302047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9525_neg : (51238281 / 200000000) ≤ -Real.log (250 / 323) ∧
    -Real.log (250 / 323) ≤ (128095703 / 500000000) := by
  have h := checkLog_sound (w := (73 / 573)) (n := 12)
    (lo := (51238281 / 200000000)) (hi := (128095703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323 / 250) = 1/(250 / 323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9525 : Bounds (51238281 / 200000000) (128095703 / 500000000) (Real.log (323 / 250)) := by
  have h := reflection_log_9525_neg
  have he : Real.log (323 / 250) = -Real.log (250 / 323) := by
    rw [show ((323 / 250) : ℝ) = ((250 / 323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9526_neg : (69062237 / 200000000) ≤ -Real.log (177 / 250) ∧
    -Real.log (177 / 250) ≤ (172655593 / 500000000) := by
  have h := checkLog_sound (w := (73 / 427)) (n := 12)
    (lo := (69062237 / 200000000)) (hi := (172655593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 177) = 1/(177 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9526 : Bounds (-172655593 / 500000000) (-69062237 / 200000000) (Real.log (177 / 250)) := by
  have h := reflection_log_9526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9527_neg : (291957 / 1000000000) ≤ -Real.log (250000 / 250073) ∧
    -Real.log (250000 / 250073) ≤ (145979 / 500000000) := by
  have h := checkLog_sound (w := (73 / 500073)) (n := 12)
    (lo := (291957 / 1000000000)) (hi := (145979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250073 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250073 / 250000) = 1/(250000 / 250073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9527 : Bounds (291957 / 1000000000) (145979 / 500000000) (Real.log (250073 / 250000)) := by
  have h := reflection_log_9527_neg
  have he : Real.log (250073 / 250000) = -Real.log (250000 / 250073) := by
    rw [show ((250073 / 250000) : ℝ) = ((250000 / 250073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9528_neg : (146021 / 500000000) ≤ -Real.log (249927 / 250000) ∧
    -Real.log (249927 / 250000) ≤ (292043 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 499927)) (n := 12)
    (lo := (146021 / 500000000)) (hi := (292043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249927) = 1/(249927 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9528 : Bounds (-292043 / 1000000000) (-146021 / 500000000) (Real.log (249927 / 250000)) := by
  have h := reflection_log_9528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9529_neg : (34482893 / 250000000) ≤ -Real.log (1000000 / 1147897) ∧
    -Real.log (1000000 / 1147897) ≤ (137931573 / 1000000000) := by
  have h := checkLog_sound (w := (147897 / 2147897)) (n := 12)
    (lo := (34482893 / 250000000)) (hi := (137931573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1147897 / 1000000) = 1/(1000000 / 1147897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9529 : Bounds (34482893 / 250000000) (137931573 / 1000000000) (Real.log (1147897 / 1000000)) := by
  have h := reflection_log_9529_neg
  have he : Real.log (1147897 / 1000000) = -Real.log (1000000 / 1147897) := by
    rw [show ((1147897 / 1000000) : ℝ) = ((1000000 / 1147897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9530_neg : (160047867 / 1000000000) ≤ -Real.log (852103 / 1000000) ∧
    -Real.log (852103 / 1000000) ≤ (40011967 / 250000000) := by
  have h := checkLog_sound (w := (147897 / 1852103)) (n := 12)
    (lo := (160047867 / 1000000000)) (hi := (40011967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 852103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 852103) = 1/(852103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9530 : Bounds (-40011967 / 250000000) (-160047867 / 1000000000) (Real.log (852103 / 1000000)) := by
  have h := reflection_log_9530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9531_neg : (69205297 / 500000000) ≤ -Real.log (1000000 / 1148447) ∧
    -Real.log (1000000 / 1148447) ≤ (27682119 / 200000000) := by
  have h := checkLog_sound (w := (148447 / 2148447)) (n := 12)
    (lo := (69205297 / 500000000)) (hi := (27682119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148447 / 1000000) = 1/(1000000 / 1148447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9531 : Bounds (69205297 / 500000000) (27682119 / 200000000) (Real.log (1148447 / 1000000)) := by
  have h := reflection_log_9531_neg
  have he : Real.log (1148447 / 1000000) = -Real.log (1000000 / 1148447) := by
    rw [show ((1148447 / 1000000) : ℝ) = ((1000000 / 1148447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9532_neg : (160693537 / 1000000000) ≤ -Real.log (851553 / 1000000) ∧
    -Real.log (851553 / 1000000) ≤ (80346769 / 500000000) := by
  have h := checkLog_sound (w := (148447 / 1851553)) (n := 12)
    (lo := (160693537 / 1000000000)) (hi := (80346769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851553) = 1/(851553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9532 : Bounds (-80346769 / 500000000) (-160693537 / 1000000000) (Real.log (851553 / 1000000)) := by
  have h := reflection_log_9532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9533_neg : (11141471 / 500000000) ≤ -Real.log (977963488191 / 1000000000000) ∧
    -Real.log (977963488191 / 1000000000000) ≤ (22282943 / 1000000000) := by
  have h := checkLog_sound (w := (22036511809 / 1977963488191)) (n := 12)
    (lo := (11141471 / 500000000)) (hi := (22282943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977963488191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977963488191) = 1/(977963488191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9533 : Bounds (-22282943 / 1000000000) (-11141471 / 500000000) (Real.log (977963488191 / 1000000000000)) := by
  have h := reflection_log_9533_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9534_neg : (11058147 / 500000000) ≤ -Real.log (978126477391 / 1000000000000) ∧
    -Real.log (978126477391 / 1000000000000) ≤ (4423259 / 200000000) := by
  have h := checkLog_sound (w := (21873522609 / 1978126477391)) (n := 12)
    (lo := (11058147 / 500000000)) (hi := (4423259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978126477391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978126477391) = 1/(978126477391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9534 : Bounds (-4423259 / 200000000) (-11058147 / 500000000) (Real.log (978126477391 / 1000000000000)) := by
  have h := reflection_log_9534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9535_neg : (3724743 / 12500000) ≤ -Real.log (250000000000 / 336783522649) ∧
    -Real.log (250000000000 / 336783522649) ≤ (297979441 / 1000000000) := by
  have h := checkLog_sound (w := (86783522649 / 586783522649)) (n := 12)
    (lo := (3724743 / 12500000)) (hi := (297979441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336783522649 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336783522649 / 250000000000) = 1/(250000000000 / 336783522649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9535 : Bounds (3724743 / 12500000) (297979441 / 1000000000) (Real.log (336783522649 / 250000000000)) := by
  have h := reflection_log_9535_neg
  have he : Real.log (336783522649 / 250000000000) = -Real.log (250000000000 / 336783522649) := by
    rw [show ((336783522649 / 250000000000) : ℝ) = ((250000000000 / 336783522649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0149 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9536_neg : (74776033 / 250000000) ≤ -Real.log (500000000000 / 674325027333) ∧
    -Real.log (500000000000 / 674325027333) ≤ (299104133 / 1000000000) := by
  have h := checkLog_sound (w := (174325027333 / 1174325027333)) (n := 12)
    (lo := (74776033 / 250000000)) (hi := (299104133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674325027333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674325027333 / 500000000000) = 1/(500000000000 / 674325027333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9536 : Bounds (74776033 / 250000000) (299104133 / 1000000000) (Real.log (674325027333 / 500000000000)) := by
  have h := reflection_log_9536_neg
  have he : Real.log (674325027333 / 500000000000) = -Real.log (500000000000 / 674325027333) := by
    rw [show ((674325027333 / 500000000000) : ℝ) = ((500000000000 / 674325027333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9537_neg : (600409553 / 1000000000) ≤ -Real.log (500000000000 / 911432604093) ∧
    -Real.log (500000000000 / 911432604093) ≤ (300204777 / 500000000) := by
  have h := checkLog_sound (w := (411432604093 / 1411432604093)) (n := 12)
    (lo := (600409553 / 1000000000)) (hi := (300204777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911432604093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911432604093 / 500000000000) = 1/(500000000000 / 911432604093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9537 : Bounds (600409553 / 1000000000) (300204777 / 500000000) (Real.log (911432604093 / 500000000000)) := by
  have h := reflection_log_9537_neg
  have he : Real.log (911432604093 / 500000000000) = -Real.log (500000000000 / 911432604093) := by
    rw [show ((911432604093 / 500000000000) : ℝ) = ((500000000000 / 911432604093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9538_neg : (60150259 / 100000000) ≤ -Real.log (125000000000 / 228107344633) ∧
    -Real.log (125000000000 / 228107344633) ≤ (601502591 / 1000000000) := by
  have h := checkLog_sound (w := (103107344633 / 353107344633)) (n := 12)
    (lo := (60150259 / 100000000)) (hi := (601502591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228107344633 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228107344633 / 125000000000) = 1/(125000000000 / 228107344633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9538 : Bounds (60150259 / 100000000) (601502591 / 1000000000) (Real.log (228107344633 / 125000000000)) := by
  have h := reflection_log_9538_neg
  have he : Real.log (228107344633 / 125000000000) = -Real.log (125000000000 / 228107344633) := by
    rw [show ((228107344633 / 125000000000) : ℝ) = ((125000000000 / 228107344633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9539_neg : (256578327 / 1000000000) ≤ -Real.log (400 / 517) ∧
    -Real.log (400 / 517) ≤ (32072291 / 125000000) := by
  have h := checkLog_sound (w := (117 / 917)) (n := 12)
    (lo := (256578327 / 1000000000)) (hi := (32072291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(517 / 400) = 1/(400 / 517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9539 : Bounds (256578327 / 1000000000) (32072291 / 125000000) (Real.log (517 / 400)) := by
  have h := reflection_log_9539_neg
  have he : Real.log (517 / 400) = -Real.log (400 / 517) := by
    rw [show ((517 / 400) : ℝ) = ((400 / 517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9540_neg : (346017649 / 1000000000) ≤ -Real.log (283 / 400) ∧
    -Real.log (283 / 400) ≤ (6920353 / 20000000) := by
  have h := checkLog_sound (w := (117 / 683)) (n := 12)
    (lo := (346017649 / 1000000000)) (hi := (6920353 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 283) = 1/(283 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9540 : Bounds (-6920353 / 20000000) (-346017649 / 1000000000) (Real.log (283 / 400)) := by
  have h := reflection_log_9540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9541_neg : (292457 / 1000000000) ≤ -Real.log (400000 / 400117) ∧
    -Real.log (400000 / 400117) ≤ (146229 / 500000000) := by
  have h := checkLog_sound (w := (117 / 800117)) (n := 12)
    (lo := (292457 / 1000000000)) (hi := (146229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400117 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400117 / 400000) = 1/(400000 / 400117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9541 : Bounds (292457 / 1000000000) (146229 / 500000000) (Real.log (400117 / 400000)) := by
  have h := reflection_log_9541_neg
  have he : Real.log (400117 / 400000) = -Real.log (400000 / 400117) := by
    rw [show ((400117 / 400000) : ℝ) = ((400000 / 400117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9542_neg : (146271 / 500000000) ≤ -Real.log (399883 / 400000) ∧
    -Real.log (399883 / 400000) ≤ (292543 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 799883)) (n := 12)
    (lo := (146271 / 500000000)) (hi := (292543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399883) = 1/(399883 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9542 : Bounds (-292543 / 1000000000) (-146271 / 500000000) (Real.log (399883 / 400000)) := by
  have h := reflection_log_9542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9543_neg : (13815979 / 100000000) ≤ -Real.log (1000000 / 1148159) ∧
    -Real.log (1000000 / 1148159) ≤ (138159791 / 1000000000) := by
  have h := checkLog_sound (w := (148159 / 2148159)) (n := 12)
    (lo := (13815979 / 100000000)) (hi := (138159791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148159 / 1000000) = 1/(1000000 / 1148159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9543 : Bounds (13815979 / 100000000) (138159791 / 1000000000) (Real.log (1148159 / 1000000)) := by
  have h := reflection_log_9543_neg
  have he : Real.log (1148159 / 1000000) = -Real.log (1000000 / 1148159) := by
    rw [show ((1148159 / 1000000) : ℝ) = ((1000000 / 1148159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9544_neg : (160355389 / 1000000000) ≤ -Real.log (851841 / 1000000) ∧
    -Real.log (851841 / 1000000) ≤ (16035539 / 100000000) := by
  have h := checkLog_sound (w := (148159 / 1851841)) (n := 12)
    (lo := (160355389 / 1000000000)) (hi := (16035539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851841) = 1/(851841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9544 : Bounds (-16035539 / 100000000) (-160355389 / 1000000000) (Real.log (851841 / 1000000)) := by
  have h := reflection_log_9544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9545_neg : (138638703 / 1000000000) ≤ -Real.log (1000000 / 1148709) ∧
    -Real.log (1000000 / 1148709) ≤ (8664919 / 62500000) := by
  have h := checkLog_sound (w := (148709 / 2148709)) (n := 12)
    (lo := (138638703 / 1000000000)) (hi := (8664919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148709 / 1000000) = 1/(1000000 / 1148709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9545 : Bounds (138638703 / 1000000000) (8664919 / 62500000) (Real.log (1148709 / 1000000)) := by
  have h := reflection_log_9545_neg
  have he : Real.log (1148709 / 1000000) = -Real.log (1000000 / 1148709) := by
    rw [show ((1148709 / 1000000) : ℝ) = ((1000000 / 1148709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9546_neg : (80500629 / 500000000) ≤ -Real.log (851291 / 1000000) ∧
    -Real.log (851291 / 1000000) ≤ (161001259 / 1000000000) := by
  have h := checkLog_sound (w := (148709 / 1851291)) (n := 12)
    (lo := (80500629 / 500000000)) (hi := (161001259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851291) = 1/(851291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9546 : Bounds (-161001259 / 1000000000) (-80500629 / 500000000) (Real.log (851291 / 1000000)) := by
  have h := reflection_log_9546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9547_neg : (4472511 / 200000000) ≤ -Real.log (977885633319 / 1000000000000) ∧
    -Real.log (977885633319 / 1000000000000) ≤ (5590639 / 250000000) := by
  have h := checkLog_sound (w := (22114366681 / 1977885633319)) (n := 12)
    (lo := (4472511 / 200000000)) (hi := (5590639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977885633319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977885633319) = 1/(977885633319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9547 : Bounds (-5590639 / 250000000) (-4472511 / 200000000) (Real.log (977885633319 / 1000000000000)) := by
  have h := reflection_log_9547_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9548_neg : (22195599 / 1000000000) ≤ -Real.log (978048910719 / 1000000000000) ∧
    -Real.log (978048910719 / 1000000000000) ≤ (55489 / 2500000) := by
  have h := checkLog_sound (w := (21951089281 / 1978048910719)) (n := 12)
    (lo := (22195599 / 1000000000)) (hi := (55489 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978048910719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978048910719) = 1/(978048910719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9548 : Bounds (-55489 / 2500000) (-22195599 / 1000000000) (Real.log (978048910719 / 1000000000000)) := by
  have h := reflection_log_9548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9549_neg : (298515179 / 1000000000) ≤ -Real.log (5000000000 / 6739279983) ∧
    -Real.log (5000000000 / 6739279983) ≤ (14925759 / 50000000) := by
  have h := checkLog_sound (w := (1739279983 / 11739279983)) (n := 12)
    (lo := (298515179 / 1000000000)) (hi := (14925759 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6739279983 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6739279983 / 5000000000) = 1/(5000000000 / 6739279983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9549 : Bounds (298515179 / 1000000000) (14925759 / 50000000) (Real.log (6739279983 / 5000000000)) := by
  have h := reflection_log_9549_neg
  have he : Real.log (6739279983 / 5000000000) = -Real.log (5000000000 / 6739279983) := by
    rw [show ((6739279983 / 5000000000) : ℝ) = ((5000000000 / 6739279983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9550_neg : (299639961 / 1000000000) ≤ -Real.log (500000000000 / 674686446821) ∧
    -Real.log (500000000000 / 674686446821) ≤ (149819981 / 500000000) := by
  have h := checkLog_sound (w := (174686446821 / 1174686446821)) (n := 12)
    (lo := (299639961 / 1000000000)) (hi := (149819981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674686446821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674686446821 / 500000000000) = 1/(500000000000 / 674686446821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9550 : Bounds (299639961 / 1000000000) (149819981 / 500000000) (Real.log (674686446821 / 500000000000)) := by
  have h := reflection_log_9550_neg
  have he : Real.log (674686446821 / 500000000000) = -Real.log (500000000000 / 674686446821) := by
    rw [show ((674686446821 / 500000000000) : ℝ) = ((500000000000 / 674686446821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9551_neg : (60150259 / 100000000) ≤ -Real.log (500000000000 / 912429378531) ∧
    -Real.log (500000000000 / 912429378531) ≤ (601502591 / 1000000000) := by
  have h := checkLog_sound (w := (412429378531 / 1412429378531)) (n := 12)
    (lo := (60150259 / 100000000)) (hi := (601502591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((912429378531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(912429378531 / 500000000000) = 1/(500000000000 / 912429378531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9551 : Bounds (60150259 / 100000000) (601502591 / 1000000000) (Real.log (912429378531 / 500000000000)) := by
  have h := reflection_log_9551_neg
  have he : Real.log (912429378531 / 500000000000) = -Real.log (500000000000 / 912429378531) := by
    rw [show ((912429378531 / 500000000000) : ℝ) = ((500000000000 / 912429378531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9552_neg : (75324497 / 125000000) ≤ -Real.log (250000000000 / 456713780919) ∧
    -Real.log (250000000000 / 456713780919) ≤ (602595977 / 1000000000) := by
  have h := checkLog_sound (w := (206713780919 / 706713780919)) (n := 12)
    (lo := (75324497 / 125000000)) (hi := (602595977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((456713780919 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(456713780919 / 250000000000) = 1/(250000000000 / 456713780919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9552 : Bounds (75324497 / 125000000) (602595977 / 1000000000) (Real.log (456713780919 / 250000000000)) := by
  have h := reflection_log_9552_neg
  have he : Real.log (456713780919 / 250000000000) = -Real.log (250000000000 / 456713780919) := by
    rw [show ((456713780919 / 250000000000) : ℝ) = ((250000000000 / 456713780919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9553_neg : (256965099 / 1000000000) ≤ -Real.log (1000 / 1293) ∧
    -Real.log (1000 / 1293) ≤ (2569651 / 10000000) := by
  have h := checkLog_sound (w := (293 / 2293)) (n := 12)
    (lo := (256965099 / 1000000000)) (hi := (2569651 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1293 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1293 / 1000) = 1/(1000 / 1293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9553 : Bounds (256965099 / 1000000000) (2569651 / 10000000) (Real.log (1293 / 1000)) := by
  have h := reflection_log_9553_neg
  have he : Real.log (1293 / 1000) = -Real.log (1000 / 1293) := by
    rw [show ((1293 / 1000) : ℝ) = ((1000 / 1293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9554_neg : (346724613 / 1000000000) ≤ -Real.log (707 / 1000) ∧
    -Real.log (707 / 1000) ≤ (173362307 / 500000000) := by
  have h := checkLog_sound (w := (293 / 1707)) (n := 12)
    (lo := (346724613 / 1000000000)) (hi := (173362307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 707) = 1/(707 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9554 : Bounds (-173362307 / 500000000) (-346724613 / 1000000000) (Real.log (707 / 1000)) := by
  have h := reflection_log_9554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9555_neg : (292957 / 1000000000) ≤ -Real.log (1000000 / 1000293) ∧
    -Real.log (1000000 / 1000293) ≤ (146479 / 500000000) := by
  have h := checkLog_sound (w := (293 / 2000293)) (n := 12)
    (lo := (292957 / 1000000000)) (hi := (146479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000293 / 1000000) = 1/(1000000 / 1000293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9555 : Bounds (292957 / 1000000000) (146479 / 500000000) (Real.log (1000293 / 1000000)) := by
  have h := reflection_log_9555_neg
  have he : Real.log (1000293 / 1000000) = -Real.log (1000000 / 1000293) := by
    rw [show ((1000293 / 1000000) : ℝ) = ((1000000 / 1000293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9556_neg : (146521 / 500000000) ≤ -Real.log (999707 / 1000000) ∧
    -Real.log (999707 / 1000000) ≤ (293043 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 1999707)) (n := 12)
    (lo := (146521 / 500000000)) (hi := (293043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999707) = 1/(999707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9556 : Bounds (-293043 / 1000000000) (-146521 / 500000000) (Real.log (999707 / 1000000)) := by
  have h := reflection_log_9556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9557_neg : (27677591 / 200000000) ≤ -Real.log (1000000 / 1148421) ∧
    -Real.log (1000000 / 1148421) ≤ (34596989 / 250000000) := by
  have h := checkLog_sound (w := (148421 / 2148421)) (n := 12)
    (lo := (27677591 / 200000000)) (hi := (34596989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148421 / 1000000) = 1/(1000000 / 1148421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9557 : Bounds (27677591 / 200000000) (34596989 / 250000000) (Real.log (1148421 / 1000000)) := by
  have h := reflection_log_9557_neg
  have he : Real.log (1148421 / 1000000) = -Real.log (1000000 / 1148421) := by
    rw [show ((1148421 / 1000000) : ℝ) = ((1000000 / 1148421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9558_neg : (32132601 / 200000000) ≤ -Real.log (851579 / 1000000) ∧
    -Real.log (851579 / 1000000) ≤ (80331503 / 500000000) := by
  have h := checkLog_sound (w := (148421 / 1851579)) (n := 12)
    (lo := (32132601 / 200000000)) (hi := (80331503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851579) = 1/(851579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9558 : Bounds (-80331503 / 500000000) (-32132601 / 200000000) (Real.log (851579 / 1000000)) := by
  have h := reflection_log_9558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9559_neg : (138867629 / 1000000000) ≤ -Real.log (250000 / 287243) ∧
    -Real.log (250000 / 287243) ≤ (13886763 / 100000000) := by
  have h := checkLog_sound (w := (37243 / 537243)) (n := 12)
    (lo := (138867629 / 1000000000)) (hi := (13886763 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287243 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287243 / 250000) = 1/(250000 / 287243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9559 : Bounds (138867629 / 1000000000) (13886763 / 100000000) (Real.log (287243 / 250000)) := by
  have h := reflection_log_9559_neg
  have he : Real.log (287243 / 250000) = -Real.log (250000 / 287243) := by
    rw [show ((287243 / 250000) : ℝ) = ((250000 / 287243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9560_neg : (20163781 / 125000000) ≤ -Real.log (212757 / 250000) ∧
    -Real.log (212757 / 250000) ≤ (161310249 / 1000000000) := by
  have h := checkLog_sound (w := (37243 / 462757)) (n := 12)
    (lo := (20163781 / 125000000)) (hi := (161310249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212757) = 1/(212757 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9560 : Bounds (-161310249 / 1000000000) (-20163781 / 125000000) (Real.log (212757 / 250000)) := by
  have h := reflection_log_9560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9561_neg : (11221309 / 500000000) ≤ -Real.log (61112958951 / 62500000000) ∧
    -Real.log (61112958951 / 62500000000) ≤ (22442619 / 1000000000) := by
  have h := checkLog_sound (w := (1387041049 / 123612958951)) (n := 12)
    (lo := (11221309 / 500000000)) (hi := (22442619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61112958951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61112958951) = 1/(61112958951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9561 : Bounds (-22442619 / 1000000000) (-11221309 / 500000000) (Real.log (61112958951 / 62500000000)) := by
  have h := reflection_log_9561_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9562_neg : (445501 / 20000000) ≤ -Real.log (977971206759 / 1000000000000) ∧
    -Real.log (977971206759 / 1000000000000) ≤ (22275051 / 1000000000) := by
  have h := checkLog_sound (w := (22028793241 / 1977971206759)) (n := 12)
    (lo := (445501 / 20000000)) (hi := (22275051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977971206759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977971206759) = 1/(977971206759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9562 : Bounds (-22275051 / 1000000000) (-445501 / 20000000) (Real.log (977971206759 / 1000000000000)) := by
  have h := reflection_log_9562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9563_neg : (299050961 / 1000000000) ≤ -Real.log (250000000000 / 337144586703) ∧
    -Real.log (250000000000 / 337144586703) ≤ (149525481 / 500000000) := by
  have h := checkLog_sound (w := (87144586703 / 587144586703)) (n := 12)
    (lo := (299050961 / 1000000000)) (hi := (149525481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337144586703 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337144586703 / 250000000000) = 1/(250000000000 / 337144586703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9563 : Bounds (299050961 / 1000000000) (149525481 / 500000000) (Real.log (337144586703 / 250000000000)) := by
  have h := reflection_log_9563_neg
  have he : Real.log (337144586703 / 250000000000) = -Real.log (250000000000 / 337144586703) := by
    rw [show ((337144586703 / 250000000000) : ℝ) = ((250000000000 / 337144586703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9564_neg : (150088939 / 500000000) ≤ -Real.log (500000000000 / 675049469583) ∧
    -Real.log (500000000000 / 675049469583) ≤ (300177879 / 1000000000) := by
  have h := checkLog_sound (w := (175049469583 / 1175049469583)) (n := 12)
    (lo := (150088939 / 500000000)) (hi := (300177879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675049469583 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675049469583 / 500000000000) = 1/(500000000000 / 675049469583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9564 : Bounds (150088939 / 500000000) (300177879 / 1000000000) (Real.log (675049469583 / 500000000000)) := by
  have h := reflection_log_9564_neg
  have he : Real.log (675049469583 / 500000000000) = -Real.log (500000000000 / 675049469583) := by
    rw [show ((675049469583 / 500000000000) : ℝ) = ((500000000000 / 675049469583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9565_neg : (75324497 / 125000000) ≤ -Real.log (500000000000 / 913427561837) ∧
    -Real.log (500000000000 / 913427561837) ≤ (602595977 / 1000000000) := by
  have h := checkLog_sound (w := (413427561837 / 1413427561837)) (n := 12)
    (lo := (75324497 / 125000000)) (hi := (602595977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((913427561837 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(913427561837 / 500000000000) = 1/(500000000000 / 913427561837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9565 : Bounds (75324497 / 125000000) (602595977 / 1000000000) (Real.log (913427561837 / 500000000000)) := by
  have h := reflection_log_9565_neg
  have he : Real.log (913427561837 / 500000000000) = -Real.log (500000000000 / 913427561837) := by
    rw [show ((913427561837 / 500000000000) : ℝ) = ((500000000000 / 913427561837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9566_neg : (37730607 / 62500000) ≤ -Real.log (250000000000 / 457213578501) ∧
    -Real.log (250000000000 / 457213578501) ≤ (603689713 / 1000000000) := by
  have h := checkLog_sound (w := (207213578501 / 707213578501)) (n := 12)
    (lo := (37730607 / 62500000)) (hi := (603689713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457213578501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457213578501 / 250000000000) = 1/(250000000000 / 457213578501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9566 : Bounds (37730607 / 62500000) (603689713 / 1000000000) (Real.log (457213578501 / 250000000000)) := by
  have h := reflection_log_9566_neg
  have he : Real.log (457213578501 / 250000000000) = -Real.log (250000000000 / 457213578501) := by
    rw [show ((457213578501 / 250000000000) : ℝ) = ((250000000000 / 457213578501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9567_neg : (128675861 / 500000000) ≤ -Real.log (2000 / 2587) ∧
    -Real.log (2000 / 2587) ≤ (257351723 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 4587)) (n := 12)
    (lo := (128675861 / 500000000)) (hi := (257351723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2587 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2587 / 2000) = 1/(2000 / 2587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9567 : Bounds (128675861 / 500000000) (257351723 / 1000000000) (Real.log (2587 / 2000)) := by
  have h := reflection_log_9567_neg
  have he : Real.log (2587 / 2000) = -Real.log (2000 / 2587) := by
    rw [show ((2587 / 2000) : ℝ) = ((2000 / 2587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9568_neg : (86858019 / 250000000) ≤ -Real.log (1413 / 2000) ∧
    -Real.log (1413 / 2000) ≤ (347432077 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 3413)) (n := 12)
    (lo := (86858019 / 250000000)) (hi := (347432077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1413) = 1/(1413 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9568 : Bounds (-347432077 / 1000000000) (-86858019 / 250000000) (Real.log (1413 / 2000)) := by
  have h := reflection_log_9568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9569_neg : (18341 / 62500000) ≤ -Real.log (2000000 / 2000587) ∧
    -Real.log (2000000 / 2000587) ≤ (293457 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 4000587)) (n := 12)
    (lo := (18341 / 62500000)) (hi := (293457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000587 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000587 / 2000000) = 1/(2000000 / 2000587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9569 : Bounds (18341 / 62500000) (293457 / 1000000000) (Real.log (2000587 / 2000000)) := by
  have h := reflection_log_9569_neg
  have he : Real.log (2000587 / 2000000) = -Real.log (2000000 / 2000587) := by
    rw [show ((2000587 / 2000000) : ℝ) = ((2000000 / 2000587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9570_neg : (293543 / 1000000000) ≤ -Real.log (1999413 / 2000000) ∧
    -Real.log (1999413 / 2000000) ≤ (36693 / 125000000) := by
  have h := checkLog_sound (w := (587 / 3999413)) (n := 12)
    (lo := (293543 / 1000000000)) (hi := (36693 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999413) = 1/(1999413 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9570 : Bounds (-36693 / 125000000) (-293543 / 1000000000) (Real.log (1999413 / 2000000)) := by
  have h := reflection_log_9570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9571_neg : (69307599 / 500000000) ≤ -Real.log (500000 / 574341) ∧
    -Real.log (500000 / 574341) ≤ (138615199 / 1000000000) := by
  have h := checkLog_sound (w := (74341 / 1074341)) (n := 12)
    (lo := (69307599 / 500000000)) (hi := (138615199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574341 / 500000) = 1/(500000 / 574341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9571 : Bounds (69307599 / 500000000) (138615199 / 1000000000) (Real.log (574341 / 500000)) := by
  have h := reflection_log_9571_neg
  have he : Real.log (574341 / 500000) = -Real.log (500000 / 574341) := by
    rw [show ((574341 / 500000) : ℝ) = ((500000 / 574341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9572_neg : (80484771 / 500000000) ≤ -Real.log (425659 / 500000) ∧
    -Real.log (425659 / 500000) ≤ (160969543 / 1000000000) := by
  have h := checkLog_sound (w := (74341 / 925659)) (n := 12)
    (lo := (80484771 / 500000000)) (hi := (160969543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425659) = 1/(425659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9572 : Bounds (-160969543 / 1000000000) (-80484771 / 500000000) (Real.log (425659 / 500000)) := by
  have h := reflection_log_9572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9573_neg : (139095633 / 1000000000) ≤ -Real.log (500000 / 574617) ∧
    -Real.log (500000 / 574617) ≤ (69547817 / 500000000) := by
  have h := checkLog_sound (w := (74617 / 1074617)) (n := 12)
    (lo := (139095633 / 1000000000)) (hi := (69547817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574617 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574617 / 500000) = 1/(500000 / 574617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9573 : Bounds (139095633 / 1000000000) (69547817 / 500000000) (Real.log (574617 / 500000)) := by
  have h := reflection_log_9573_neg
  have he : Real.log (574617 / 500000) = -Real.log (500000 / 574617) := by
    rw [show ((574617 / 500000) : ℝ) = ((500000 / 574617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9574_neg : (80809079 / 500000000) ≤ -Real.log (425383 / 500000) ∧
    -Real.log (425383 / 500000) ≤ (161618159 / 1000000000) := by
  have h := checkLog_sound (w := (74617 / 925383)) (n := 12)
    (lo := (80809079 / 500000000)) (hi := (161618159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425383) = 1/(425383 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9574 : Bounds (-161618159 / 1000000000) (-80809079 / 500000000) (Real.log (425383 / 500000)) := by
  have h := reflection_log_9574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9575_neg : (900901 / 40000000) ≤ -Real.log (244432303311 / 250000000000) ∧
    -Real.log (244432303311 / 250000000000) ≤ (11261263 / 500000000) := by
  have h := checkLog_sound (w := (5567696689 / 494432303311)) (n := 12)
    (lo := (900901 / 40000000)) (hi := (11261263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244432303311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244432303311) = 1/(244432303311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9575 : Bounds (-11261263 / 500000000) (-900901 / 40000000) (Real.log (244432303311 / 250000000000)) := by
  have h := reflection_log_9575_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9576_neg : (2794293 / 125000000) ≤ -Real.log (244473415719 / 250000000000) ∧
    -Real.log (244473415719 / 250000000000) ≤ (4470869 / 200000000) := by
  have h := checkLog_sound (w := (5526584281 / 494473415719)) (n := 12)
    (lo := (2794293 / 125000000)) (hi := (4470869 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244473415719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244473415719) = 1/(244473415719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9576 : Bounds (-4470869 / 200000000) (-2794293 / 125000000) (Real.log (244473415719 / 250000000000)) := by
  have h := reflection_log_9576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9577_neg : (14979237 / 50000000) ≤ -Real.log (500000000000 / 674649191019) ∧
    -Real.log (500000000000 / 674649191019) ≤ (299584741 / 1000000000) := by
  have h := checkLog_sound (w := (174649191019 / 1174649191019)) (n := 12)
    (lo := (14979237 / 50000000)) (hi := (299584741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674649191019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674649191019 / 500000000000) = 1/(500000000000 / 674649191019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9577 : Bounds (14979237 / 50000000) (299584741 / 1000000000) (Real.log (674649191019 / 500000000000)) := by
  have h := reflection_log_9577_neg
  have he : Real.log (674649191019 / 500000000000) = -Real.log (500000000000 / 674649191019) := by
    rw [show ((674649191019 / 500000000000) : ℝ) = ((500000000000 / 674649191019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9578_neg : (4698653 / 15625000) ≤ -Real.log (500000000000 / 675411335197) ∧
    -Real.log (500000000000 / 675411335197) ≤ (300713793 / 1000000000) := by
  have h := checkLog_sound (w := (175411335197 / 1175411335197)) (n := 12)
    (lo := (4698653 / 15625000)) (hi := (300713793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675411335197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675411335197 / 500000000000) = 1/(500000000000 / 675411335197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9578 : Bounds (4698653 / 15625000) (300713793 / 1000000000) (Real.log (675411335197 / 500000000000)) := by
  have h := reflection_log_9578_neg
  have he : Real.log (675411335197 / 500000000000) = -Real.log (500000000000 / 675411335197) := by
    rw [show ((675411335197 / 500000000000) : ℝ) = ((500000000000 / 675411335197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9579_neg : (37730607 / 62500000) ≤ -Real.log (500000000000 / 914427157001) ∧
    -Real.log (500000000000 / 914427157001) ≤ (603689713 / 1000000000) := by
  have h := checkLog_sound (w := (414427157001 / 1414427157001)) (n := 12)
    (lo := (37730607 / 62500000)) (hi := (603689713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((914427157001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(914427157001 / 500000000000) = 1/(500000000000 / 914427157001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9579 : Bounds (37730607 / 62500000) (603689713 / 1000000000) (Real.log (914427157001 / 500000000000)) := by
  have h := reflection_log_9579_neg
  have he : Real.log (914427157001 / 500000000000) = -Real.log (500000000000 / 914427157001) := by
    rw [show ((914427157001 / 500000000000) : ℝ) = ((500000000000 / 914427157001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9580_neg : (604783799 / 1000000000) ≤ -Real.log (500000000000 / 915428167021) ∧
    -Real.log (500000000000 / 915428167021) ≤ (3023919 / 5000000) := by
  have h := checkLog_sound (w := (415428167021 / 1415428167021)) (n := 12)
    (lo := (604783799 / 1000000000)) (hi := (3023919 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915428167021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915428167021 / 500000000000) = 1/(500000000000 / 915428167021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9580 : Bounds (604783799 / 1000000000) (3023919 / 5000000) (Real.log (915428167021 / 500000000000)) := by
  have h := reflection_log_9580_neg
  have he : Real.log (915428167021 / 500000000000) = -Real.log (500000000000 / 915428167021) := by
    rw [show ((915428167021 / 500000000000) : ℝ) = ((500000000000 / 915428167021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9581_neg : (64434549 / 250000000) ≤ -Real.log (500 / 647) ∧
    -Real.log (500 / 647) ≤ (257738197 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 1147)) (n := 12)
    (lo := (64434549 / 250000000)) (hi := (257738197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647 / 500) = 1/(500 / 647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9581 : Bounds (64434549 / 250000000) (257738197 / 1000000000) (Real.log (647 / 500)) := by
  have h := reflection_log_9581_neg
  have he : Real.log (647 / 500) = -Real.log (500 / 647) := by
    rw [show ((647 / 500) : ℝ) = ((500 / 647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9582_neg : (348140041 / 1000000000) ≤ -Real.log (353 / 500) ∧
    -Real.log (353 / 500) ≤ (174070021 / 500000000) := by
  have h := checkLog_sound (w := (147 / 853)) (n := 12)
    (lo := (348140041 / 1000000000)) (hi := (174070021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 353) = 1/(353 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9582 : Bounds (-174070021 / 500000000) (-348140041 / 1000000000) (Real.log (353 / 500)) := by
  have h := reflection_log_9582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9583_neg : (73489 / 250000000) ≤ -Real.log (500000 / 500147) ∧
    -Real.log (500000 / 500147) ≤ (293957 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 1000147)) (n := 12)
    (lo := (73489 / 250000000)) (hi := (293957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500147 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500147 / 500000) = 1/(500000 / 500147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9583 : Bounds (73489 / 250000000) (293957 / 1000000000) (Real.log (500147 / 500000)) := by
  have h := reflection_log_9583_neg
  have he : Real.log (500147 / 500000) = -Real.log (500000 / 500147) := by
    rw [show ((500147 / 500000) : ℝ) = ((500000 / 500147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9584_neg : (294043 / 1000000000) ≤ -Real.log (499853 / 500000) ∧
    -Real.log (499853 / 500000) ≤ (73511 / 250000000) := by
  have h := checkLog_sound (w := (147 / 999853)) (n := 12)
    (lo := (294043 / 1000000000)) (hi := (73511 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499853) = 1/(499853 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9584 : Bounds (-73511 / 250000000) (-294043 / 1000000000) (Real.log (499853 / 500000)) := by
  have h := reflection_log_9584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9585_neg : (138843259 / 1000000000) ≤ -Real.log (62500 / 71809) ∧
    -Real.log (62500 / 71809) ≤ (6942163 / 50000000) := by
  have h := checkLog_sound (w := (9309 / 134309)) (n := 12)
    (lo := (138843259 / 1000000000)) (hi := (6942163 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71809 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71809 / 62500) = 1/(62500 / 71809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9585 : Bounds (138843259 / 1000000000) (6942163 / 50000000) (Real.log (71809 / 62500)) := by
  have h := reflection_log_9585_neg
  have he : Real.log (71809 / 62500) = -Real.log (62500 / 71809) := by
    rw [show ((71809 / 62500) : ℝ) = ((62500 / 71809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9586_neg : (161277347 / 1000000000) ≤ -Real.log (53191 / 62500) ∧
    -Real.log (53191 / 62500) ≤ (40319337 / 250000000) := by
  have h := checkLog_sound (w := (9309 / 115691)) (n := 12)
    (lo := (161277347 / 1000000000)) (hi := (40319337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 53191) = 1/(53191 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9586 : Bounds (-40319337 / 250000000) (-161277347 / 1000000000) (Real.log (53191 / 62500)) := by
  have h := reflection_log_9586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9587_neg : (27864891 / 200000000) ≤ -Real.log (1000000 / 1149497) ∧
    -Real.log (1000000 / 1149497) ≤ (17415557 / 125000000) := by
  have h := checkLog_sound (w := (149497 / 2149497)) (n := 12)
    (lo := (27864891 / 200000000)) (hi := (17415557 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149497 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1149497 / 1000000) = 1/(1000000 / 1149497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9587 : Bounds (27864891 / 200000000) (17415557 / 125000000) (Real.log (1149497 / 1000000)) := by
  have h := reflection_log_9587_neg
  have he : Real.log (1149497 / 1000000) = -Real.log (1000000 / 1149497) := by
    rw [show ((1149497 / 1000000) : ℝ) = ((1000000 / 1149497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9588_neg : (161927339 / 1000000000) ≤ -Real.log (850503 / 1000000) ∧
    -Real.log (850503 / 1000000) ≤ (8096367 / 50000000) := by
  have h := checkLog_sound (w := (149497 / 1850503)) (n := 12)
    (lo := (161927339 / 1000000000)) (hi := (8096367 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 850503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 850503) = 1/(850503 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9588 : Bounds (-8096367 / 50000000) (-161927339 / 1000000000) (Real.log (850503 / 1000000)) := by
  have h := reflection_log_9588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9589_neg : (5650721 / 250000000) ≤ -Real.log (977650646991 / 1000000000000) ∧
    -Real.log (977650646991 / 1000000000000) ≤ (4520577 / 200000000) := by
  have h := checkLog_sound (w := (22349353009 / 1977650646991)) (n := 12)
    (lo := (5650721 / 250000000)) (hi := (4520577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977650646991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977650646991) = 1/(977650646991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9589 : Bounds (-4520577 / 200000000) (-5650721 / 250000000) (Real.log (977650646991 / 1000000000000)) := by
  have h := reflection_log_9589_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9590_neg : (22434087 / 1000000000) ≤ -Real.log (3819592519 / 3906250000) ∧
    -Real.log (3819592519 / 3906250000) ≤ (2804261 / 125000000) := by
  have h := checkLog_sound (w := (86657481 / 7725842519)) (n := 12)
    (lo := (22434087 / 1000000000)) (hi := (2804261 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3819592519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3819592519) = 1/(3819592519 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9590 : Bounds (-2804261 / 125000000) (-22434087 / 1000000000) (Real.log (3819592519 / 3906250000)) := by
  have h := reflection_log_9590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9591_neg : (300120607 / 1000000000) ≤ -Real.log (500000000000 / 675010810099) ∧
    -Real.log (500000000000 / 675010810099) ≤ (9378769 / 31250000) := by
  have h := checkLog_sound (w := (175010810099 / 1175010810099)) (n := 12)
    (lo := (300120607 / 1000000000)) (hi := (9378769 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675010810099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675010810099 / 500000000000) = 1/(500000000000 / 675010810099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9591 : Bounds (300120607 / 1000000000) (9378769 / 31250000) (Real.log (675010810099 / 500000000000)) := by
  have h := reflection_log_9591_neg
  have he : Real.log (675010810099 / 500000000000) = -Real.log (500000000000 / 675010810099) := by
    rw [show ((675010810099 / 500000000000) : ℝ) = ((500000000000 / 675010810099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9592_neg : (60250359 / 200000000) ≤ -Real.log (500000000000 / 675774806203) ∧
    -Real.log (500000000000 / 675774806203) ≤ (75312949 / 250000000) := by
  have h := checkLog_sound (w := (175774806203 / 1175774806203)) (n := 12)
    (lo := (60250359 / 200000000)) (hi := (75312949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675774806203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675774806203 / 500000000000) = 1/(500000000000 / 675774806203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9592 : Bounds (60250359 / 200000000) (75312949 / 250000000) (Real.log (675774806203 / 500000000000)) := by
  have h := reflection_log_9592_neg
  have he : Real.log (675774806203 / 500000000000) = -Real.log (500000000000 / 675774806203) := by
    rw [show ((675774806203 / 500000000000) : ℝ) = ((500000000000 / 675774806203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9593_neg : (604783799 / 1000000000) ≤ -Real.log (25000000000 / 45771408351) ∧
    -Real.log (25000000000 / 45771408351) ≤ (3023919 / 5000000) := by
  have h := checkLog_sound (w := (20771408351 / 70771408351)) (n := 12)
    (lo := (604783799 / 1000000000)) (hi := (3023919 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45771408351 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45771408351 / 25000000000) = 1/(25000000000 / 45771408351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9593 : Bounds (604783799 / 1000000000) (3023919 / 5000000) (Real.log (45771408351 / 25000000000)) := by
  have h := reflection_log_9593_neg
  have he : Real.log (45771408351 / 25000000000) = -Real.log (25000000000 / 45771408351) := by
    rw [show ((45771408351 / 25000000000) : ℝ) = ((25000000000 / 45771408351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9594_neg : (605878237 / 1000000000) ≤ -Real.log (500000000000 / 916430594901) ∧
    -Real.log (500000000000 / 916430594901) ≤ (302939119 / 500000000) := by
  have h := checkLog_sound (w := (416430594901 / 1416430594901)) (n := 12)
    (lo := (605878237 / 1000000000)) (hi := (302939119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((916430594901 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(916430594901 / 500000000000) = 1/(500000000000 / 916430594901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9594 : Bounds (605878237 / 1000000000) (302939119 / 500000000) (Real.log (916430594901 / 500000000000)) := by
  have h := reflection_log_9594_neg
  have he : Real.log (916430594901 / 500000000000) = -Real.log (500000000000 / 916430594901) := by
    rw [show ((916430594901 / 500000000000) : ℝ) = ((500000000000 / 916430594901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9595_neg : (6453113 / 25000000) ≤ -Real.log (2000 / 2589) ∧
    -Real.log (2000 / 2589) ≤ (258124521 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 4589)) (n := 12)
    (lo := (6453113 / 25000000)) (hi := (258124521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2589 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2589 / 2000) = 1/(2000 / 2589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9595 : Bounds (6453113 / 25000000) (258124521 / 1000000000) (Real.log (2589 / 2000)) := by
  have h := reflection_log_9595_neg
  have he : Real.log (2589 / 2000) = -Real.log (2000 / 2589) := by
    rw [show ((2589 / 2000) : ℝ) = ((2000 / 2589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9596_neg : (348848507 / 1000000000) ≤ -Real.log (1411 / 2000) ∧
    -Real.log (1411 / 2000) ≤ (87212127 / 250000000) := by
  have h := checkLog_sound (w := (589 / 3411)) (n := 12)
    (lo := (348848507 / 1000000000)) (hi := (87212127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1411) = 1/(1411 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9596 : Bounds (-87212127 / 250000000) (-348848507 / 1000000000) (Real.log (1411 / 2000)) := by
  have h := reflection_log_9596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9597_neg : (36807 / 125000000) ≤ -Real.log (2000000 / 2000589) ∧
    -Real.log (2000000 / 2000589) ≤ (294457 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 4000589)) (n := 12)
    (lo := (36807 / 125000000)) (hi := (294457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000589 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000589 / 2000000) = 1/(2000000 / 2000589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9597 : Bounds (36807 / 125000000) (294457 / 1000000000) (Real.log (2000589 / 2000000)) := by
  have h := reflection_log_9597_neg
  have he : Real.log (2000589 / 2000000) = -Real.log (2000000 / 2000589) := by
    rw [show ((2000589 / 2000000) : ℝ) = ((2000000 / 2000589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9598_neg : (294543 / 1000000000) ≤ -Real.log (1999411 / 2000000) ∧
    -Real.log (1999411 / 2000000) ≤ (18409 / 62500000) := by
  have h := checkLog_sound (w := (589 / 3999411)) (n := 12)
    (lo := (294543 / 1000000000)) (hi := (18409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999411) = 1/(1999411 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9598 : Bounds (-18409 / 62500000) (-294543 / 1000000000) (Real.log (1999411 / 2000000)) := by
  have h := reflection_log_9598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9599_neg : (139071269 / 1000000000) ≤ -Real.log (500000 / 574603) ∧
    -Real.log (500000 / 574603) ≤ (13907127 / 100000000) := by
  have h := checkLog_sound (w := (74603 / 1074603)) (n := 12)
    (lo := (139071269 / 1000000000)) (hi := (13907127 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574603 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574603 / 500000) = 1/(500000 / 574603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9599 : Bounds (139071269 / 1000000000) (13907127 / 100000000) (Real.log (574603 / 500000)) := by
  have h := reflection_log_9599_neg
  have he : Real.log (574603 / 500000) = -Real.log (500000 / 574603) := by
    rw [show ((574603 / 500000) : ℝ) = ((500000 / 574603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0150 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9600_neg : (161585247 / 1000000000) ≤ -Real.log (425397 / 500000) ∧
    -Real.log (425397 / 500000) ≤ (5049539 / 31250000) := by
  have h := checkLog_sound (w := (74603 / 925397)) (n := 12)
    (lo := (161585247 / 1000000000)) (hi := (5049539 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425397) = 1/(425397 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9600 : Bounds (-5049539 / 31250000) (-161585247 / 1000000000) (Real.log (425397 / 500000)) := by
  have h := reflection_log_9600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9601_neg : (27910471 / 200000000) ≤ -Real.log (1000000 / 1149759) ∧
    -Real.log (1000000 / 1149759) ≤ (34888089 / 250000000) := by
  have h := checkLog_sound (w := (149759 / 2149759)) (n := 12)
    (lo := (27910471 / 200000000)) (hi := (34888089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1149759 / 1000000) = 1/(1000000 / 1149759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9601 : Bounds (27910471 / 200000000) (34888089 / 250000000) (Real.log (1149759 / 1000000)) := by
  have h := reflection_log_9601_neg
  have he : Real.log (1149759 / 1000000) = -Real.log (1000000 / 1149759) := by
    rw [show ((1149759 / 1000000) : ℝ) = ((1000000 / 1149759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9602_neg : (2027943 / 12500000) ≤ -Real.log (850241 / 1000000) ∧
    -Real.log (850241 / 1000000) ≤ (162235441 / 1000000000) := by
  have h := checkLog_sound (w := (149759 / 1850241)) (n := 12)
    (lo := (2027943 / 12500000)) (hi := (162235441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 850241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 850241) = 1/(850241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9602 : Bounds (-162235441 / 1000000000) (-2027943 / 12500000) (Real.log (850241 / 1000000)) := by
  have h := reflection_log_9602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9603_neg : (4536617 / 200000000) ≤ -Real.log (977572241919 / 1000000000000) ∧
    -Real.log (977572241919 / 1000000000000) ≤ (11341543 / 500000000) := by
  have h := checkLog_sound (w := (22427758081 / 1977572241919)) (n := 12)
    (lo := (4536617 / 200000000)) (hi := (11341543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977572241919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977572241919) = 1/(977572241919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9603 : Bounds (-11341543 / 500000000) (-4536617 / 200000000) (Real.log (977572241919 / 1000000000000)) := by
  have h := reflection_log_9603_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9604_neg : (11256989 / 500000000) ≤ -Real.log (244434392391 / 250000000000) ∧
    -Real.log (244434392391 / 250000000000) ≤ (22513979 / 1000000000) := by
  have h := checkLog_sound (w := (5565607609 / 494434392391)) (n := 12)
    (lo := (11256989 / 500000000)) (hi := (22513979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244434392391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244434392391) = 1/(244434392391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9604 : Bounds (-22513979 / 1000000000) (-11256989 / 500000000) (Real.log (244434392391 / 250000000000)) := by
  have h := reflection_log_9604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9605_neg : (75164129 / 250000000) ≤ -Real.log (500000000000 / 675372651899) ∧
    -Real.log (500000000000 / 675372651899) ≤ (300656517 / 1000000000) := by
  have h := checkLog_sound (w := (175372651899 / 1175372651899)) (n := 12)
    (lo := (75164129 / 250000000)) (hi := (300656517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675372651899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675372651899 / 500000000000) = 1/(500000000000 / 675372651899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9605 : Bounds (75164129 / 250000000) (300656517 / 1000000000) (Real.log (675372651899 / 500000000000)) := by
  have h := reflection_log_9605_neg
  have he : Real.log (675372651899 / 500000000000) = -Real.log (500000000000 / 675372651899) := by
    rw [show ((675372651899 / 500000000000) : ℝ) = ((500000000000 / 675372651899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9606_neg : (60357559 / 200000000) ≤ -Real.log (50000000000 / 67613711877) ∧
    -Real.log (50000000000 / 67613711877) ≤ (75446949 / 250000000) := by
  have h := checkLog_sound (w := (17613711877 / 117613711877)) (n := 12)
    (lo := (60357559 / 200000000)) (hi := (75446949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67613711877 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67613711877 / 50000000000) = 1/(50000000000 / 67613711877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9606 : Bounds (60357559 / 200000000) (75446949 / 250000000) (Real.log (67613711877 / 50000000000)) := by
  have h := reflection_log_9606_neg
  have he : Real.log (67613711877 / 50000000000) = -Real.log (50000000000 / 67613711877) := by
    rw [show ((67613711877 / 50000000000) : ℝ) = ((50000000000 / 67613711877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9607_neg : (605878237 / 1000000000) ≤ -Real.log (5000000000 / 9164305949) ∧
    -Real.log (5000000000 / 9164305949) ≤ (302939119 / 500000000) := by
  have h := checkLog_sound (w := (4164305949 / 14164305949)) (n := 12)
    (lo := (605878237 / 1000000000)) (hi := (302939119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9164305949 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9164305949 / 5000000000) = 1/(5000000000 / 9164305949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9607 : Bounds (605878237 / 1000000000) (302939119 / 500000000) (Real.log (9164305949 / 5000000000)) := by
  have h := reflection_log_9607_neg
  have he : Real.log (9164305949 / 5000000000) = -Real.log (5000000000 / 9164305949) := by
    rw [show ((9164305949 / 5000000000) : ℝ) = ((5000000000 / 9164305949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9608_neg : (606973027 / 1000000000) ≤ -Real.log (500000000000 / 917434443657) ∧
    -Real.log (500000000000 / 917434443657) ≤ (151743257 / 250000000) := by
  have h := checkLog_sound (w := (417434443657 / 1417434443657)) (n := 12)
    (lo := (606973027 / 1000000000)) (hi := (151743257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917434443657 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917434443657 / 500000000000) = 1/(500000000000 / 917434443657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9608 : Bounds (606973027 / 1000000000) (151743257 / 250000000) (Real.log (917434443657 / 500000000000)) := by
  have h := reflection_log_9608_neg
  have he : Real.log (917434443657 / 500000000000) = -Real.log (500000000000 / 917434443657) := by
    rw [show ((917434443657 / 500000000000) : ℝ) = ((500000000000 / 917434443657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9609_neg : (51702139 / 200000000) ≤ -Real.log (200 / 259) ∧
    -Real.log (200 / 259) ≤ (32313837 / 125000000) := by
  have h := checkLog_sound (w := (59 / 459)) (n := 12)
    (lo := (51702139 / 200000000)) (hi := (32313837 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259 / 200) = 1/(200 / 259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9609 : Bounds (51702139 / 200000000) (32313837 / 125000000) (Real.log (259 / 200)) := by
  have h := reflection_log_9609_neg
  have he : Real.log (259 / 200) = -Real.log (200 / 259) := by
    rw [show ((259 / 200) : ℝ) = ((200 / 259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9610_neg : (87389369 / 250000000) ≤ -Real.log (141 / 200) ∧
    -Real.log (141 / 200) ≤ (349557477 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 341)) (n := 12)
    (lo := (87389369 / 250000000)) (hi := (349557477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 141) = 1/(141 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9610 : Bounds (-349557477 / 1000000000) (-87389369 / 250000000) (Real.log (141 / 200)) := by
  have h := reflection_log_9610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9611_neg : (73739 / 250000000) ≤ -Real.log (200000 / 200059) ∧
    -Real.log (200000 / 200059) ≤ (294957 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 400059)) (n := 12)
    (lo := (73739 / 250000000)) (hi := (294957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200059 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200059 / 200000) = 1/(200000 / 200059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9611 : Bounds (73739 / 250000000) (294957 / 1000000000) (Real.log (200059 / 200000)) := by
  have h := reflection_log_9611_neg
  have he : Real.log (200059 / 200000) = -Real.log (200000 / 200059) := by
    rw [show ((200059 / 200000) : ℝ) = ((200000 / 200059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9612_neg : (295043 / 1000000000) ≤ -Real.log (199941 / 200000) ∧
    -Real.log (199941 / 200000) ≤ (73761 / 250000000) := by
  have h := checkLog_sound (w := (59 / 399941)) (n := 12)
    (lo := (295043 / 1000000000)) (hi := (73761 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199941) = 1/(199941 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9612 : Bounds (-73761 / 250000000) (-295043 / 1000000000) (Real.log (199941 / 200000)) := by
  have h := reflection_log_9612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9613_neg : (69649613 / 500000000) ≤ -Real.log (250000 / 287367) ∧
    -Real.log (250000 / 287367) ≤ (139299227 / 1000000000) := by
  have h := checkLog_sound (w := (37367 / 537367)) (n := 12)
    (lo := (69649613 / 500000000)) (hi := (139299227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287367 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287367 / 250000) = 1/(250000 / 287367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9613 : Bounds (69649613 / 500000000) (139299227 / 1000000000) (Real.log (287367 / 250000)) := by
  have h := reflection_log_9613_neg
  have he : Real.log (287367 / 250000) = -Real.log (250000 / 287367) := by
    rw [show ((287367 / 250000) : ℝ) = ((250000 / 287367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9614_neg : (80946621 / 500000000) ≤ -Real.log (212633 / 250000) ∧
    -Real.log (212633 / 250000) ≤ (161893243 / 1000000000) := by
  have h := checkLog_sound (w := (37367 / 462633)) (n := 12)
    (lo := (80946621 / 500000000)) (hi := (161893243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212633) = 1/(212633 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9614 : Bounds (-161893243 / 1000000000) (-80946621 / 500000000) (Real.log (212633 / 250000)) := by
  have h := reflection_log_9614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9615_neg : (139780203 / 1000000000) ≤ -Real.log (1000000 / 1150021) ∧
    -Real.log (1000000 / 1150021) ≤ (34945051 / 250000000) := by
  have h := checkLog_sound (w := (150021 / 2150021)) (n := 12)
    (lo := (139780203 / 1000000000)) (hi := (34945051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150021 / 1000000) = 1/(1000000 / 1150021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9615 : Bounds (139780203 / 1000000000) (34945051 / 250000000) (Real.log (1150021 / 1000000)) := by
  have h := reflection_log_9615_neg
  have he : Real.log (1150021 / 1000000) = -Real.log (1000000 / 1150021) := by
    rw [show ((1150021 / 1000000) : ℝ) = ((1000000 / 1150021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9616_neg : (32508727 / 200000000) ≤ -Real.log (849979 / 1000000) ∧
    -Real.log (849979 / 1000000) ≤ (40635909 / 250000000) := by
  have h := checkLog_sound (w := (150021 / 1849979)) (n := 12)
    (lo := (32508727 / 200000000)) (hi := (40635909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849979) = 1/(849979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9616 : Bounds (-40635909 / 250000000) (-32508727 / 200000000) (Real.log (849979 / 1000000)) := by
  have h := reflection_log_9616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9617_neg : (2845429 / 125000000) ≤ -Real.log (977493699559 / 1000000000000) ∧
    -Real.log (977493699559 / 1000000000000) ≤ (22763433 / 1000000000) := by
  have h := checkLog_sound (w := (22506300441 / 1977493699559)) (n := 12)
    (lo := (2845429 / 125000000)) (hi := (22763433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977493699559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977493699559) = 1/(977493699559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9617 : Bounds (-22763433 / 1000000000) (-2845429 / 125000000) (Real.log (977493699559 / 1000000000000)) := by
  have h := reflection_log_9617_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9618_neg : (706063 / 31250000) ≤ -Real.log (61103707311 / 62500000000) ∧
    -Real.log (61103707311 / 62500000000) ≤ (22594017 / 1000000000) := by
  have h := checkLog_sound (w := (1396292689 / 123603707311)) (n := 12)
    (lo := (706063 / 31250000)) (hi := (22594017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61103707311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61103707311) = 1/(61103707311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9618 : Bounds (-22594017 / 1000000000) (-706063 / 31250000) (Real.log (61103707311 / 62500000000)) := by
  have h := reflection_log_9618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9619_neg : (301192469 / 1000000000) ≤ -Real.log (31250000000 / 42233419789) ∧
    -Real.log (31250000000 / 42233419789) ≤ (30119247 / 100000000) := by
  have h := checkLog_sound (w := (10983419789 / 73483419789)) (n := 12)
    (lo := (301192469 / 1000000000)) (hi := (30119247 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42233419789 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42233419789 / 31250000000) = 1/(31250000000 / 42233419789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9619 : Bounds (301192469 / 1000000000) (30119247 / 100000000) (Real.log (42233419789 / 31250000000)) := by
  have h := reflection_log_9619_neg
  have he : Real.log (42233419789 / 31250000000) = -Real.log (31250000000 / 42233419789) := by
    rw [show ((42233419789 / 31250000000) : ℝ) = ((31250000000 / 42233419789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9620_neg : (151161919 / 500000000) ≤ -Real.log (250000000000 / 338249827349) ∧
    -Real.log (250000000000 / 338249827349) ≤ (302323839 / 1000000000) := by
  have h := checkLog_sound (w := (88249827349 / 588249827349)) (n := 12)
    (lo := (151161919 / 500000000)) (hi := (302323839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338249827349 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338249827349 / 250000000000) = 1/(250000000000 / 338249827349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9620 : Bounds (151161919 / 500000000) (302323839 / 1000000000) (Real.log (338249827349 / 250000000000)) := by
  have h := reflection_log_9620_neg
  have he : Real.log (338249827349 / 250000000000) = -Real.log (250000000000 / 338249827349) := by
    rw [show ((338249827349 / 250000000000) : ℝ) = ((250000000000 / 338249827349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9621_neg : (606973027 / 1000000000) ≤ -Real.log (62500000000 / 114679305457) ∧
    -Real.log (62500000000 / 114679305457) ≤ (151743257 / 250000000) := by
  have h := checkLog_sound (w := (52179305457 / 177179305457)) (n := 12)
    (lo := (606973027 / 1000000000)) (hi := (151743257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114679305457 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114679305457 / 62500000000) = 1/(62500000000 / 114679305457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9621 : Bounds (606973027 / 1000000000) (151743257 / 250000000) (Real.log (114679305457 / 62500000000)) := by
  have h := reflection_log_9621_neg
  have he : Real.log (114679305457 / 62500000000) = -Real.log (62500000000 / 114679305457) := by
    rw [show ((114679305457 / 62500000000) : ℝ) = ((62500000000 / 114679305457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9622_neg : (608068171 / 1000000000) ≤ -Real.log (500000000000 / 918439716313) ∧
    -Real.log (500000000000 / 918439716313) ≤ (152017043 / 250000000) := by
  have h := checkLog_sound (w := (418439716313 / 1418439716313)) (n := 12)
    (lo := (608068171 / 1000000000)) (hi := (152017043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918439716313 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918439716313 / 500000000000) = 1/(500000000000 / 918439716313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9622 : Bounds (608068171 / 1000000000) (152017043 / 250000000) (Real.log (918439716313 / 500000000000)) := by
  have h := reflection_log_9622_neg
  have he : Real.log (918439716313 / 500000000000) = -Real.log (500000000000 / 918439716313) := by
    rw [show ((918439716313 / 500000000000) : ℝ) = ((500000000000 / 918439716313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9623_neg : (258896721 / 1000000000) ≤ -Real.log (2000 / 2591) ∧
    -Real.log (2000 / 2591) ≤ (129448361 / 500000000) := by
  have h := checkLog_sound (w := (591 / 4591)) (n := 12)
    (lo := (258896721 / 1000000000)) (hi := (129448361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2591 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2591 / 2000) = 1/(2000 / 2591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9623 : Bounds (258896721 / 1000000000) (129448361 / 500000000) (Real.log (2591 / 2000)) := by
  have h := reflection_log_9623_neg
  have he : Real.log (2591 / 2000) = -Real.log (2000 / 2591) := by
    rw [show ((2591 / 2000) : ℝ) = ((2000 / 2591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9624_neg : (350266947 / 1000000000) ≤ -Real.log (1409 / 2000) ∧
    -Real.log (1409 / 2000) ≤ (87566737 / 250000000) := by
  have h := checkLog_sound (w := (591 / 3409)) (n := 12)
    (lo := (350266947 / 1000000000)) (hi := (87566737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1409) = 1/(1409 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9624 : Bounds (-87566737 / 250000000) (-350266947 / 1000000000) (Real.log (1409 / 2000)) := by
  have h := reflection_log_9624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9625_neg : (9233 / 31250000) ≤ -Real.log (2000000 / 2000591) ∧
    -Real.log (2000000 / 2000591) ≤ (295457 / 1000000000) := by
  have h := checkLog_sound (w := (591 / 4000591)) (n := 12)
    (lo := (9233 / 31250000)) (hi := (295457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000591 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000591 / 2000000) = 1/(2000000 / 2000591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9625 : Bounds (9233 / 31250000) (295457 / 1000000000) (Real.log (2000591 / 2000000)) := by
  have h := reflection_log_9625_neg
  have he : Real.log (2000591 / 2000000) = -Real.log (2000000 / 2000591) := by
    rw [show ((2000591 / 2000000) : ℝ) = ((2000000 / 2000591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9626_neg : (295543 / 1000000000) ≤ -Real.log (1999409 / 2000000) ∧
    -Real.log (1999409 / 2000000) ≤ (36943 / 125000000) := by
  have h := checkLog_sound (w := (591 / 3999409)) (n := 12)
    (lo := (295543 / 1000000000)) (hi := (36943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999409) = 1/(1999409 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9626 : Bounds (-36943 / 125000000) (-295543 / 1000000000) (Real.log (1999409 / 2000000)) := by
  have h := reflection_log_9626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9627_neg : (34881783 / 250000000) ≤ -Real.log (100000 / 114973) ∧
    -Real.log (100000 / 114973) ≤ (139527133 / 1000000000) := by
  have h := checkLog_sound (w := (14973 / 214973)) (n := 12)
    (lo := (34881783 / 250000000)) (hi := (139527133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114973 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114973 / 100000) = 1/(100000 / 114973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9627 : Bounds (34881783 / 250000000) (139527133 / 1000000000) (Real.log (114973 / 100000)) := by
  have h := reflection_log_9627_neg
  have he : Real.log (114973 / 100000) = -Real.log (100000 / 114973) := by
    rw [show ((114973 / 100000) : ℝ) = ((100000 / 114973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9628_neg : (40550333 / 250000000) ≤ -Real.log (85027 / 100000) ∧
    -Real.log (85027 / 100000) ≤ (162201333 / 1000000000) := by
  have h := checkLog_sound (w := (14973 / 185027)) (n := 12)
    (lo := (40550333 / 250000000)) (hi := (162201333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85027) = 1/(85027 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9628 : Bounds (-162201333 / 1000000000) (-40550333 / 250000000) (Real.log (85027 / 100000)) := by
  have h := reflection_log_9628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9629_neg : (35002217 / 250000000) ≤ -Real.log (250000 / 287571) ∧
    -Real.log (250000 / 287571) ≤ (140008869 / 1000000000) := by
  have h := checkLog_sound (w := (37571 / 537571)) (n := 12)
    (lo := (35002217 / 250000000)) (hi := (140008869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287571 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287571 / 250000) = 1/(250000 / 287571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9629 : Bounds (35002217 / 250000000) (140008869 / 1000000000) (Real.log (287571 / 250000)) := by
  have h := reflection_log_9629_neg
  have he : Real.log (287571 / 250000) = -Real.log (250000 / 287571) := by
    rw [show ((287571 / 250000) : ℝ) = ((250000 / 287571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9630_neg : (81426551 / 500000000) ≤ -Real.log (212429 / 250000) ∧
    -Real.log (212429 / 250000) ≤ (162853103 / 1000000000) := by
  have h := checkLog_sound (w := (37571 / 462429)) (n := 12)
    (lo := (81426551 / 500000000)) (hi := (162853103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212429) = 1/(212429 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9630 : Bounds (-162853103 / 1000000000) (-81426551 / 500000000) (Real.log (212429 / 250000)) := by
  have h := reflection_log_9630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9631_neg : (11422117 / 500000000) ≤ -Real.log (61088419959 / 62500000000) ∧
    -Real.log (61088419959 / 62500000000) ≤ (4568847 / 200000000) := by
  have h := checkLog_sound (w := (1411580041 / 123588419959)) (n := 12)
    (lo := (11422117 / 500000000)) (hi := (4568847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61088419959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61088419959) = 1/(61088419959 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9631 : Bounds (-4568847 / 200000000) (-11422117 / 500000000) (Real.log (61088419959 / 62500000000)) := by
  have h := reflection_log_9631_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9632_neg : (113371 / 5000000) ≤ -Real.log (9775809271 / 10000000000) ∧
    -Real.log (9775809271 / 10000000000) ≤ (22674201 / 1000000000) := by
  have h := checkLog_sound (w := (224190729 / 19775809271)) (n := 12)
    (lo := (113371 / 5000000)) (hi := (22674201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9775809271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9775809271) = 1/(9775809271 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9632 : Bounds (-22674201 / 1000000000) (-113371 / 5000000) (Real.log (9775809271 / 10000000000)) := by
  have h := reflection_log_9632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9633_neg : (60345693 / 200000000) ≤ -Real.log (1562500000 / 2112803139) ∧
    -Real.log (1562500000 / 2112803139) ≤ (150864233 / 500000000) := by
  have h := checkLog_sound (w := (550303139 / 3675303139)) (n := 12)
    (lo := (60345693 / 200000000)) (hi := (150864233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112803139 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112803139 / 1562500000) = 1/(1562500000 / 2112803139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9633 : Bounds (60345693 / 200000000) (150864233 / 500000000) (Real.log (2112803139 / 1562500000)) := by
  have h := reflection_log_9633_neg
  have he : Real.log (2112803139 / 1562500000) = -Real.log (1562500000 / 2112803139) := by
    rw [show ((2112803139 / 1562500000) : ℝ) = ((1562500000 / 2112803139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9634_neg : (302861971 / 1000000000) ≤ -Real.log (500000000000 / 676863799199) ∧
    -Real.log (500000000000 / 676863799199) ≤ (75715493 / 250000000) := by
  have h := checkLog_sound (w := (176863799199 / 1176863799199)) (n := 12)
    (lo := (302861971 / 1000000000)) (hi := (75715493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676863799199 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676863799199 / 500000000000) = 1/(500000000000 / 676863799199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9634 : Bounds (302861971 / 1000000000) (75715493 / 250000000) (Real.log (676863799199 / 500000000000)) := by
  have h := reflection_log_9634_neg
  have he : Real.log (676863799199 / 500000000000) = -Real.log (500000000000 / 676863799199) := by
    rw [show ((676863799199 / 500000000000) : ℝ) = ((500000000000 / 676863799199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9635_neg : (608068171 / 1000000000) ≤ -Real.log (62500000000 / 114804964539) ∧
    -Real.log (62500000000 / 114804964539) ≤ (152017043 / 250000000) := by
  have h := checkLog_sound (w := (52304964539 / 177304964539)) (n := 12)
    (lo := (608068171 / 1000000000)) (hi := (152017043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114804964539 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114804964539 / 62500000000) = 1/(62500000000 / 114804964539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9635 : Bounds (608068171 / 1000000000) (152017043 / 250000000) (Real.log (114804964539 / 62500000000)) := by
  have h := reflection_log_9635_neg
  have he : Real.log (114804964539 / 62500000000) = -Real.log (62500000000 / 114804964539) := by
    rw [show ((114804964539 / 62500000000) : ℝ) = ((62500000000 / 114804964539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9636_neg : (152290917 / 250000000) ≤ -Real.log (250000000000 / 459723207949) ∧
    -Real.log (250000000000 / 459723207949) ≤ (609163669 / 1000000000) := by
  have h := checkLog_sound (w := (209723207949 / 709723207949)) (n := 12)
    (lo := (152290917 / 250000000)) (hi := (609163669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((459723207949 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(459723207949 / 250000000000) = 1/(250000000000 / 459723207949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9636 : Bounds (152290917 / 250000000) (609163669 / 1000000000) (Real.log (459723207949 / 250000000000)) := by
  have h := reflection_log_9636_neg
  have he : Real.log (459723207949 / 250000000000) = -Real.log (250000000000 / 459723207949) := by
    rw [show ((459723207949 / 250000000000) : ℝ) = ((250000000000 / 459723207949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9637_neg : (259282597 / 1000000000) ≤ -Real.log (125 / 162) ∧
    -Real.log (125 / 162) ≤ (129641299 / 500000000) := by
  have h := checkLog_sound (w := (37 / 287)) (n := 12)
    (lo := (259282597 / 1000000000)) (hi := (129641299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162 / 125) = 1/(125 / 162) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9637 : Bounds (259282597 / 1000000000) (129641299 / 500000000) (Real.log (162 / 125)) := by
  have h := reflection_log_9637_neg
  have he : Real.log (162 / 125) = -Real.log (125 / 162) := by
    rw [show ((162 / 125) : ℝ) = ((125 / 162) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9638_neg : (175488461 / 500000000) ≤ -Real.log (88 / 125) ∧
    -Real.log (88 / 125) ≤ (350976923 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 213)) (n := 12)
    (lo := (175488461 / 500000000)) (hi := (350976923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 88) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 88) = 1/(88 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9638 : Bounds (-350976923 / 1000000000) (-175488461 / 500000000) (Real.log (88 / 125)) := by
  have h := reflection_log_9638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9639_neg : (73989 / 250000000) ≤ -Real.log (125000 / 125037) ∧
    -Real.log (125000 / 125037) ≤ (295957 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 250037)) (n := 12)
    (lo := (73989 / 250000000)) (hi := (295957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125037 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125037 / 125000) = 1/(125000 / 125037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9639 : Bounds (73989 / 250000000) (295957 / 1000000000) (Real.log (125037 / 125000)) := by
  have h := reflection_log_9639_neg
  have he : Real.log (125037 / 125000) = -Real.log (125000 / 125037) := by
    rw [show ((125037 / 125000) : ℝ) = ((125000 / 125037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9640_neg : (296043 / 1000000000) ≤ -Real.log (124963 / 125000) ∧
    -Real.log (124963 / 125000) ≤ (74011 / 250000000) := by
  have h := checkLog_sound (w := (37 / 249963)) (n := 12)
    (lo := (296043 / 1000000000)) (hi := (74011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124963) = 1/(124963 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9640 : Bounds (-74011 / 250000000) (-296043 / 1000000000) (Real.log (124963 / 125000)) := by
  have h := reflection_log_9640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9641_neg : (27950997 / 200000000) ≤ -Real.log (125000 / 143749) ∧
    -Real.log (125000 / 143749) ≤ (69877493 / 500000000) := by
  have h := checkLog_sound (w := (18749 / 268749)) (n := 12)
    (lo := (27950997 / 200000000)) (hi := (69877493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143749 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143749 / 125000) = 1/(125000 / 143749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9641 : Bounds (27950997 / 200000000) (69877493 / 500000000) (Real.log (143749 / 125000)) := by
  have h := reflection_log_9641_neg
  have he : Real.log (143749 / 125000) = -Real.log (125000 / 143749) := by
    rw [show ((143749 / 125000) : ℝ) = ((125000 / 143749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9642_neg : (162509517 / 1000000000) ≤ -Real.log (106251 / 125000) ∧
    -Real.log (106251 / 125000) ≤ (81254759 / 500000000) := by
  have h := checkLog_sound (w := (18749 / 231251)) (n := 12)
    (lo := (162509517 / 1000000000)) (hi := (81254759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106251) = 1/(106251 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9642 : Bounds (-81254759 / 500000000) (-162509517 / 1000000000) (Real.log (106251 / 125000)) := by
  have h := reflection_log_9642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9643_neg : (140237481 / 1000000000) ≤ -Real.log (1000000 / 1150547) ∧
    -Real.log (1000000 / 1150547) ≤ (70118741 / 500000000) := by
  have h := checkLog_sound (w := (150547 / 2150547)) (n := 12)
    (lo := (140237481 / 1000000000)) (hi := (70118741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150547 / 1000000) = 1/(1000000 / 1150547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9643 : Bounds (140237481 / 1000000000) (70118741 / 500000000) (Real.log (1150547 / 1000000)) := by
  have h := reflection_log_9643_neg
  have he : Real.log (1150547 / 1000000) = -Real.log (1000000 / 1150547) := by
    rw [show ((1150547 / 1000000) : ℝ) = ((1000000 / 1150547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9644_neg : (81581333 / 500000000) ≤ -Real.log (849453 / 1000000) ∧
    -Real.log (849453 / 1000000) ≤ (163162667 / 1000000000) := by
  have h := checkLog_sound (w := (150547 / 1849453)) (n := 12)
    (lo := (81581333 / 500000000)) (hi := (163162667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849453) = 1/(849453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9644 : Bounds (-163162667 / 1000000000) (-81581333 / 500000000) (Real.log (849453 / 1000000)) := by
  have h := reflection_log_9644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9645_neg : (179103 / 7812500) ≤ -Real.log (977335600791 / 1000000000000) ∧
    -Real.log (977335600791 / 1000000000000) ≤ (4585037 / 200000000) := by
  have h := checkLog_sound (w := (22664399209 / 1977335600791)) (n := 12)
    (lo := (179103 / 7812500)) (hi := (4585037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977335600791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977335600791) = 1/(977335600791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9645 : Bounds (-4585037 / 200000000) (-179103 / 7812500) (Real.log (977335600791 / 1000000000000)) := by
  have h := reflection_log_9645_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9646_neg : (22754531 / 1000000000) ≤ -Real.log (15273474999 / 15625000000) ∧
    -Real.log (15273474999 / 15625000000) ≤ (5688633 / 250000000) := by
  have h := checkLog_sound (w := (351525001 / 30898474999)) (n := 12)
    (lo := (22754531 / 1000000000)) (hi := (5688633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15273474999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15273474999) = 1/(15273474999 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9646 : Bounds (-5688633 / 250000000) (-22754531 / 1000000000) (Real.log (15273474999 / 15625000000)) := by
  have h := reflection_log_9646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9647_neg : (302264503 / 1000000000) ≤ -Real.log (20000000000 / 27058380627) ∧
    -Real.log (20000000000 / 27058380627) ≤ (37783063 / 125000000) := by
  have h := checkLog_sound (w := (7058380627 / 47058380627)) (n := 12)
    (lo := (302264503 / 1000000000)) (hi := (37783063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27058380627 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27058380627 / 20000000000) = 1/(20000000000 / 27058380627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9647 : Bounds (302264503 / 1000000000) (37783063 / 125000000) (Real.log (27058380627 / 20000000000)) := by
  have h := reflection_log_9647_neg
  have he : Real.log (27058380627 / 20000000000) = -Real.log (20000000000 / 27058380627) := by
    rw [show ((27058380627 / 20000000000) : ℝ) = ((20000000000 / 27058380627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9648_neg : (303400147 / 1000000000) ≤ -Real.log (500000000000 / 677228169187) ∧
    -Real.log (500000000000 / 677228169187) ≤ (75850037 / 250000000) := by
  have h := checkLog_sound (w := (177228169187 / 1177228169187)) (n := 12)
    (lo := (303400147 / 1000000000)) (hi := (75850037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677228169187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677228169187 / 500000000000) = 1/(500000000000 / 677228169187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9648 : Bounds (303400147 / 1000000000) (75850037 / 250000000) (Real.log (677228169187 / 500000000000)) := by
  have h := reflection_log_9648_neg
  have he : Real.log (677228169187 / 500000000000) = -Real.log (500000000000 / 677228169187) := by
    rw [show ((677228169187 / 500000000000) : ℝ) = ((500000000000 / 677228169187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9649_neg : (152290917 / 250000000) ≤ -Real.log (500000000000 / 919446415897) ∧
    -Real.log (500000000000 / 919446415897) ≤ (609163669 / 1000000000) := by
  have h := checkLog_sound (w := (419446415897 / 1419446415897)) (n := 12)
    (lo := (152290917 / 250000000)) (hi := (609163669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((919446415897 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(919446415897 / 500000000000) = 1/(500000000000 / 919446415897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9649 : Bounds (152290917 / 250000000) (609163669 / 1000000000) (Real.log (919446415897 / 500000000000)) := by
  have h := reflection_log_9649_neg
  have he : Real.log (919446415897 / 500000000000) = -Real.log (500000000000 / 919446415897) := by
    rw [show ((919446415897 / 500000000000) : ℝ) = ((500000000000 / 919446415897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9650_neg : (1907061 / 3125000) ≤ -Real.log (100000000000 / 184090909091) ∧
    -Real.log (100000000000 / 184090909091) ≤ (610259521 / 1000000000) := by
  have h := checkLog_sound (w := (84090909091 / 284090909091)) (n := 12)
    (lo := (1907061 / 3125000)) (hi := (610259521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184090909091 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184090909091 / 100000000000) = 1/(100000000000 / 184090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9650 : Bounds (1907061 / 3125000) (610259521 / 1000000000) (Real.log (184090909091 / 100000000000)) := by
  have h := reflection_log_9650_neg
  have he : Real.log (184090909091 / 100000000000) = -Real.log (100000000000 / 184090909091) := by
    rw [show ((184090909091 / 100000000000) : ℝ) = ((100000000000 / 184090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9651_neg : (10386733 / 40000000) ≤ -Real.log (2000 / 2593) ∧
    -Real.log (2000 / 2593) ≤ (129834163 / 500000000) := by
  have h := checkLog_sound (w := (593 / 4593)) (n := 12)
    (lo := (10386733 / 40000000)) (hi := (129834163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2593 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2593 / 2000) = 1/(2000 / 2593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9651 : Bounds (10386733 / 40000000) (129834163 / 500000000) (Real.log (2593 / 2000)) := by
  have h := reflection_log_9651_neg
  have he : Real.log (2593 / 2000) = -Real.log (2000 / 2593) := by
    rw [show ((2593 / 2000) : ℝ) = ((2000 / 2593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9652_neg : (175843701 / 500000000) ≤ -Real.log (1407 / 2000) ∧
    -Real.log (1407 / 2000) ≤ (351687403 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 3407)) (n := 12)
    (lo := (175843701 / 500000000)) (hi := (351687403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1407) = 1/(1407 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9652 : Bounds (-351687403 / 1000000000) (-175843701 / 500000000) (Real.log (1407 / 2000)) := by
  have h := reflection_log_9652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9653_neg : (37057 / 125000000) ≤ -Real.log (2000000 / 2000593) ∧
    -Real.log (2000000 / 2000593) ≤ (296457 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 4000593)) (n := 12)
    (lo := (37057 / 125000000)) (hi := (296457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000593 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000593 / 2000000) = 1/(2000000 / 2000593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9653 : Bounds (37057 / 125000000) (296457 / 1000000000) (Real.log (2000593 / 2000000)) := by
  have h := reflection_log_9653_neg
  have he : Real.log (2000593 / 2000000) = -Real.log (2000000 / 2000593) := by
    rw [show ((2000593 / 2000000) : ℝ) = ((2000000 / 2000593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9654_neg : (296543 / 1000000000) ≤ -Real.log (1999407 / 2000000) ∧
    -Real.log (1999407 / 2000000) ≤ (9267 / 31250000) := by
  have h := checkLog_sound (w := (593 / 3999407)) (n := 12)
    (lo := (296543 / 1000000000)) (hi := (9267 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999407) = 1/(1999407 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9654 : Bounds (-9267 / 31250000) (-296543 / 1000000000) (Real.log (1999407 / 2000000)) := by
  have h := reflection_log_9654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9655_neg : (17497957 / 125000000) ≤ -Real.log (200000 / 230051) ∧
    -Real.log (200000 / 230051) ≤ (139983657 / 1000000000) := by
  have h := checkLog_sound (w := (30051 / 430051)) (n := 12)
    (lo := (17497957 / 125000000)) (hi := (139983657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230051 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230051 / 200000) = 1/(200000 / 230051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9655 : Bounds (17497957 / 125000000) (139983657 / 1000000000) (Real.log (230051 / 200000)) := by
  have h := reflection_log_9655_neg
  have he : Real.log (230051 / 200000) = -Real.log (200000 / 230051) := by
    rw [show ((230051 / 200000) : ℝ) = ((200000 / 230051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9656_neg : (81409487 / 500000000) ≤ -Real.log (169949 / 200000) ∧
    -Real.log (169949 / 200000) ≤ (6512759 / 40000000) := by
  have h := checkLog_sound (w := (30051 / 369949)) (n := 12)
    (lo := (81409487 / 500000000)) (hi := (6512759 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169949) = 1/(169949 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9656 : Bounds (-6512759 / 40000000) (-81409487 / 500000000) (Real.log (169949 / 200000)) := by
  have h := reflection_log_9656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9657_neg : (140465173 / 1000000000) ≤ -Real.log (1000000 / 1150809) ∧
    -Real.log (1000000 / 1150809) ≤ (70232587 / 500000000) := by
  have h := checkLog_sound (w := (150809 / 2150809)) (n := 12)
    (lo := (140465173 / 1000000000)) (hi := (70232587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150809 / 1000000) = 1/(1000000 / 1150809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9657 : Bounds (140465173 / 1000000000) (70232587 / 500000000) (Real.log (1150809 / 1000000)) := by
  have h := reflection_log_9657_neg
  have he : Real.log (1150809 / 1000000) = -Real.log (1000000 / 1150809) := by
    rw [show ((1150809 / 1000000) : ℝ) = ((1000000 / 1150809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9658_neg : (163471147 / 1000000000) ≤ -Real.log (849191 / 1000000) ∧
    -Real.log (849191 / 1000000) ≤ (40867787 / 250000000) := by
  have h := checkLog_sound (w := (150809 / 1849191)) (n := 12)
    (lo := (163471147 / 1000000000)) (hi := (40867787 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849191) = 1/(849191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9658 : Bounds (-40867787 / 250000000) (-163471147 / 1000000000) (Real.log (849191 / 1000000)) := by
  have h := reflection_log_9658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9659_neg : (11502987 / 500000000) ≤ -Real.log (977256645519 / 1000000000000) ∧
    -Real.log (977256645519 / 1000000000000) ≤ (920239 / 40000000) := by
  have h := checkLog_sound (w := (22743354481 / 1977256645519)) (n := 12)
    (lo := (11502987 / 500000000)) (hi := (920239 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977256645519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977256645519) = 1/(977256645519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9659 : Bounds (-920239 / 40000000) (-11502987 / 500000000) (Real.log (977256645519 / 1000000000000)) := by
  have h := reflection_log_9659_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9660_neg : (22835317 / 1000000000) ≤ -Real.log (39096937399 / 40000000000) ∧
    -Real.log (39096937399 / 40000000000) ≤ (11417659 / 500000000) := by
  have h := checkLog_sound (w := (903062601 / 79096937399)) (n := 12)
    (lo := (22835317 / 1000000000)) (hi := (11417659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39096937399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39096937399) = 1/(39096937399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9660 : Bounds (-11417659 / 500000000) (-22835317 / 1000000000) (Real.log (39096937399 / 40000000000)) := by
  have h := reflection_log_9660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9661_neg : (302802631 / 1000000000) ≤ -Real.log (20000000000 / 27072945413) ∧
    -Real.log (20000000000 / 27072945413) ≤ (37850329 / 125000000) := by
  have h := checkLog_sound (w := (7072945413 / 47072945413)) (n := 12)
    (lo := (302802631 / 1000000000)) (hi := (37850329 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27072945413 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27072945413 / 20000000000) = 1/(20000000000 / 27072945413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9661 : Bounds (302802631 / 1000000000) (37850329 / 125000000) (Real.log (27072945413 / 20000000000)) := by
  have h := reflection_log_9661_neg
  have he : Real.log (27072945413 / 20000000000) = -Real.log (20000000000 / 27072945413) := by
    rw [show ((27072945413 / 20000000000) : ℝ) = ((20000000000 / 27072945413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9662_neg : (949801 / 3125000) ≤ -Real.log (500000000000 / 677591378147) ∧
    -Real.log (500000000000 / 677591378147) ≤ (303936321 / 1000000000) := by
  have h := checkLog_sound (w := (177591378147 / 1177591378147)) (n := 12)
    (lo := (949801 / 3125000)) (hi := (303936321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677591378147 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677591378147 / 500000000000) = 1/(500000000000 / 677591378147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9662 : Bounds (949801 / 3125000) (303936321 / 1000000000) (Real.log (677591378147 / 500000000000)) := by
  have h := reflection_log_9662_neg
  have he : Real.log (677591378147 / 500000000000) = -Real.log (500000000000 / 677591378147) := by
    rw [show ((677591378147 / 500000000000) : ℝ) = ((500000000000 / 677591378147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9663_neg : (1907061 / 3125000) ≤ -Real.log (250000000000 / 460227272727) ∧
    -Real.log (250000000000 / 460227272727) ≤ (610259521 / 1000000000) := by
  have h := checkLog_sound (w := (210227272727 / 710227272727)) (n := 12)
    (lo := (1907061 / 3125000)) (hi := (610259521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((460227272727 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(460227272727 / 250000000000) = 1/(250000000000 / 460227272727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9663 : Bounds (1907061 / 3125000) (610259521 / 1000000000) (Real.log (460227272727 / 250000000000)) := by
  have h := reflection_log_9663_neg
  have he : Real.log (460227272727 / 250000000000) = -Real.log (250000000000 / 460227272727) := by
    rw [show ((460227272727 / 250000000000) : ℝ) = ((250000000000 / 460227272727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


