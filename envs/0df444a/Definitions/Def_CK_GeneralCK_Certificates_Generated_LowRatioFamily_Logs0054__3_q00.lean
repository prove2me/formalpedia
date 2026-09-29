-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0054__3_q00
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0054__3_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T03:15:27.050972+00:00
-- url     : https://prove2.me/theorems/86866e92-28fa-49f0-895c-784331c0e587
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0056) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0056) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0056) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0054 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0055, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0056) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3456_neg : (14137349 / 40000000) ≤ -Real.log (100000000000 / 142394861229) ∧
    -Real.log (100000000000 / 142394861229) ≤ (176716863 / 500000000) := by
  have h := checkLog_sound (w := (42394861229 / 242394861229)) (n := 12)
    (lo := (14137349 / 40000000)) (hi := (176716863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142394861229 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142394861229 / 100000000000) = 1/(100000000000 / 142394861229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3456 : Bounds (14137349 / 40000000) (176716863 / 500000000) (Real.log (142394861229 / 100000000000)) := by
  have h := reflection_log_3456_neg
  have he : Real.log (142394861229 / 100000000000) = -Real.log (100000000000 / 142394861229) := by
    rw [show ((142394861229 / 100000000000) : ℝ) = ((100000000000 / 142394861229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3457_neg : (161268147 / 1000000000) ≤ -Real.log (40 / 47) ∧
    -Real.log (40 / 47) ≤ (40317037 / 250000000) := by
  have h := checkLog_sound (w := (7 / 87)) (n := 12)
    (lo := (161268147 / 1000000000)) (hi := (40317037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47 / 40) = 1/(40 / 47) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3457 : Bounds (161268147 / 1000000000) (40317037 / 250000000) (Real.log (47 / 40)) := by
  have h := reflection_log_3457_neg
  have he : Real.log (47 / 40) = -Real.log (40 / 47) := by
    rw [show ((47 / 40) : ℝ) = ((40 / 47) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3458_neg : (48092973 / 250000000) ≤ -Real.log (33 / 40) ∧
    -Real.log (33 / 40) ≤ (192371893 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 33) = 1/(33 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3458 : Bounds (-192371893 / 1000000000) (-48092973 / 250000000) (Real.log (33 / 40)) := by
  have h := reflection_log_3458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3459_neg : (21873 / 125000000) ≤ -Real.log (40000 / 40007) ∧
    -Real.log (40000 / 40007) ≤ (34997 / 200000000) := by
  have h := checkLog_sound (w := (7 / 80007)) (n := 12)
    (lo := (21873 / 125000000)) (hi := (34997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40007 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40007 / 40000) = 1/(40000 / 40007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3459 : Bounds (21873 / 125000000) (34997 / 200000000) (Real.log (40007 / 40000)) := by
  have h := reflection_log_3459_neg
  have he : Real.log (40007 / 40000) = -Real.log (40000 / 40007) := by
    rw [show ((40007 / 40000) : ℝ) = ((40000 / 40007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3460_neg : (35003 / 200000000) ≤ -Real.log (39993 / 40000) ∧
    -Real.log (39993 / 40000) ≤ (21877 / 125000000) := by
  have h := checkLog_sound (w := (7 / 79993)) (n := 12)
    (lo := (35003 / 200000000)) (hi := (21877 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39993) = 1/(39993 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3460 : Bounds (-21877 / 125000000) (-35003 / 200000000) (Real.log (39993 / 40000)) := by
  have h := reflection_log_3460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3461_neg : (5262647 / 62500000) ≤ -Real.log (1000000 / 1087849) ∧
    -Real.log (1000000 / 1087849) ≤ (84202353 / 1000000000) := by
  have h := checkLog_sound (w := (87849 / 2087849)) (n := 12)
    (lo := (5262647 / 62500000)) (hi := (84202353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087849 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087849 / 1000000) = 1/(1000000 / 1087849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3461 : Bounds (5262647 / 62500000) (84202353 / 1000000000) (Real.log (1087849 / 1000000)) := by
  have h := reflection_log_3461_neg
  have he : Real.log (1087849 / 1000000) = -Real.log (1000000 / 1087849) := by
    rw [show ((1087849 / 1000000) : ℝ) = ((1000000 / 1087849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3462_neg : (22987433 / 250000000) ≤ -Real.log (912151 / 1000000) ∧
    -Real.log (912151 / 1000000) ≤ (91949733 / 1000000000) := by
  have h := checkLog_sound (w := (87849 / 1912151)) (n := 12)
    (lo := (22987433 / 250000000)) (hi := (91949733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912151) = 1/(912151 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3462 : Bounds (-91949733 / 1000000000) (-22987433 / 250000000) (Real.log (912151 / 1000000)) := by
  have h := reflection_log_3462_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3463_neg : (84410079 / 1000000000) ≤ -Real.log (40000 / 43523) ∧
    -Real.log (40000 / 43523) ≤ (527563 / 6250000) := by
  have h := checkLog_sound (w := (3523 / 83523)) (n := 12)
    (lo := (84410079 / 1000000000)) (hi := (527563 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43523 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43523 / 40000) = 1/(40000 / 43523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3463 : Bounds (84410079 / 1000000000) (527563 / 6250000) (Real.log (43523 / 40000)) := by
  have h := reflection_log_3463_neg
  have he : Real.log (43523 / 40000) = -Real.log (40000 / 43523) := by
    rw [show ((43523 / 40000) : ℝ) = ((40000 / 43523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3464_neg : (92197529 / 1000000000) ≤ -Real.log (36477 / 40000) ∧
    -Real.log (36477 / 40000) ≤ (9219753 / 100000000) := by
  have h := checkLog_sound (w := (3523 / 76477)) (n := 12)
    (lo := (92197529 / 1000000000)) (hi := (9219753 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36477) = 1/(36477 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3464 : Bounds (-9219753 / 100000000) (-92197529 / 1000000000) (Real.log (36477 / 40000)) := by
  have h := reflection_log_3464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3465_neg : (7787449 / 1000000000) ≤ -Real.log (1587588471 / 1600000000) ∧
    -Real.log (1587588471 / 1600000000) ≤ (155749 / 20000000) := by
  have h := checkLog_sound (w := (12411529 / 3187588471)) (n := 12)
    (lo := (7787449 / 1000000000)) (hi := (155749 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1587588471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1587588471) = 1/(1587588471 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3465 : Bounds (-155749 / 20000000) (-7787449 / 1000000000) (Real.log (1587588471 / 1600000000)) := by
  have h := reflection_log_3465_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3466_neg : (387369 / 50000000) ≤ -Real.log (992282553199 / 1000000000000) ∧
    -Real.log (992282553199 / 1000000000000) ≤ (7747381 / 1000000000) := by
  have h := checkLog_sound (w := (7717446801 / 1992282553199)) (n := 12)
    (lo := (387369 / 50000000)) (hi := (7747381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992282553199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992282553199) = 1/(992282553199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3466 : Bounds (-7747381 / 1000000000) (-387369 / 50000000) (Real.log (992282553199 / 1000000000000)) := by
  have h := reflection_log_3466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3467_neg : (44038021 / 250000000) ≤ -Real.log (250000000000 / 298154855939) ∧
    -Real.log (250000000000 / 298154855939) ≤ (35230417 / 200000000) := by
  have h := checkLog_sound (w := (48154855939 / 548154855939)) (n := 12)
    (lo := (44038021 / 250000000)) (hi := (35230417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298154855939 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298154855939 / 250000000000) = 1/(250000000000 / 298154855939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3467 : Bounds (44038021 / 250000000) (35230417 / 200000000) (Real.log (298154855939 / 250000000000)) := by
  have h := reflection_log_3467_neg
  have he : Real.log (298154855939 / 250000000000) = -Real.log (250000000000 / 298154855939) := by
    rw [show ((298154855939 / 250000000000) : ℝ) = ((250000000000 / 298154855939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3468_neg : (176607609 / 1000000000) ≤ -Real.log (500000000000 / 596581407463) ∧
    -Real.log (500000000000 / 596581407463) ≤ (17660761 / 100000000) := by
  have h := checkLog_sound (w := (96581407463 / 1096581407463)) (n := 12)
    (lo := (176607609 / 1000000000)) (hi := (17660761 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596581407463 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596581407463 / 500000000000) = 1/(500000000000 / 596581407463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3468 : Bounds (176607609 / 1000000000) (17660761 / 100000000) (Real.log (596581407463 / 500000000000)) := by
  have h := reflection_log_3468_neg
  have he : Real.log (596581407463 / 500000000000) = -Real.log (500000000000 / 596581407463) := by
    rw [show ((596581407463 / 500000000000) : ℝ) = ((500000000000 / 596581407463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3469_neg : (14137349 / 40000000) ≤ -Real.log (15625000000 / 22249197067) ∧
    -Real.log (15625000000 / 22249197067) ≤ (176716863 / 500000000) := by
  have h := checkLog_sound (w := (6624197067 / 37874197067)) (n := 12)
    (lo := (14137349 / 40000000)) (hi := (176716863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22249197067 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22249197067 / 15625000000) = 1/(15625000000 / 22249197067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3469 : Bounds (14137349 / 40000000) (176716863 / 500000000) (Real.log (22249197067 / 15625000000)) := by
  have h := reflection_log_3469_neg
  have he : Real.log (22249197067 / 15625000000) = -Real.log (15625000000 / 22249197067) := by
    rw [show ((22249197067 / 15625000000) : ℝ) = ((15625000000 / 22249197067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3470_neg : (8841001 / 25000000) ≤ -Real.log (250000000000 / 356060606061) ∧
    -Real.log (250000000000 / 356060606061) ≤ (353640041 / 1000000000) := by
  have h := checkLog_sound (w := (106060606061 / 606060606061)) (n := 12)
    (lo := (8841001 / 25000000)) (hi := (353640041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356060606061 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(356060606061 / 250000000000) = 1/(250000000000 / 356060606061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3470 : Bounds (8841001 / 25000000) (353640041 / 1000000000) (Real.log (356060606061 / 250000000000)) := by
  have h := reflection_log_3470_neg
  have he : Real.log (356060606061 / 250000000000) = -Real.log (250000000000 / 356060606061) := by
    rw [show ((356060606061 / 250000000000) : ℝ) = ((250000000000 / 356060606061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3471_neg : (645413 / 4000000) ≤ -Real.log (10000 / 11751) ∧
    -Real.log (10000 / 11751) ≤ (161353251 / 1000000000) := by
  have h := checkLog_sound (w := (1751 / 21751)) (n := 12)
    (lo := (645413 / 4000000)) (hi := (161353251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11751 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11751 / 10000) = 1/(10000 / 11751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3471 : Bounds (645413 / 4000000) (161353251 / 1000000000) (Real.log (11751 / 10000)) := by
  have h := reflection_log_3471_neg
  have he : Real.log (11751 / 10000) = -Real.log (10000 / 11751) := by
    rw [show ((11751 / 10000) : ℝ) = ((10000 / 11751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3472_neg : (24061639 / 125000000) ≤ -Real.log (8249 / 10000) ∧
    -Real.log (8249 / 10000) ≤ (192493113 / 1000000000) := by
  have h := checkLog_sound (w := (1751 / 18249)) (n := 12)
    (lo := (24061639 / 125000000)) (hi := (192493113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8249) = 1/(8249 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3472 : Bounds (-192493113 / 1000000000) (-24061639 / 125000000) (Real.log (8249 / 10000)) := by
  have h := reflection_log_3472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3473_neg : (43771 / 250000000) ≤ -Real.log (10000000 / 10001751) ∧
    -Real.log (10000000 / 10001751) ≤ (35017 / 200000000) := by
  have h := checkLog_sound (w := (1751 / 20001751)) (n := 12)
    (lo := (43771 / 250000000)) (hi := (35017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001751 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001751 / 10000000) = 1/(10000000 / 10001751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3473 : Bounds (43771 / 250000000) (35017 / 200000000) (Real.log (10001751 / 10000000)) := by
  have h := reflection_log_3473_neg
  have he : Real.log (10001751 / 10000000) = -Real.log (10000000 / 10001751) := by
    rw [show ((10001751 / 10000000) : ℝ) = ((10000000 / 10001751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3474_neg : (35023 / 200000000) ≤ -Real.log (9998249 / 10000000) ∧
    -Real.log (9998249 / 10000000) ≤ (43779 / 250000000) := by
  have h := checkLog_sound (w := (1751 / 19998249)) (n := 12)
    (lo := (35023 / 200000000)) (hi := (43779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998249) = 1/(9998249 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3474 : Bounds (-43779 / 250000000) (-35023 / 200000000) (Real.log (9998249 / 10000000)) := by
  have h := reflection_log_3474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3475_neg : (5265577 / 62500000) ≤ -Real.log (10000 / 10879) ∧
    -Real.log (10000 / 10879) ≤ (84249233 / 1000000000) := by
  have h := checkLog_sound (w := (879 / 20879)) (n := 12)
    (lo := (5265577 / 62500000)) (hi := (84249233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10879 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10879 / 10000) = 1/(10000 / 10879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3475 : Bounds (5265577 / 62500000) (84249233 / 1000000000) (Real.log (10879 / 10000)) := by
  have h := reflection_log_3475_neg
  have he : Real.log (10879 / 10000) = -Real.log (10000 / 10879) := by
    rw [show ((10879 / 10000) : ℝ) = ((10000 / 10879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3476_neg : (18401129 / 200000000) ≤ -Real.log (9121 / 10000) ∧
    -Real.log (9121 / 10000) ≤ (46002823 / 500000000) := by
  have h := checkLog_sound (w := (879 / 19121)) (n := 12)
    (lo := (18401129 / 200000000)) (hi := (46002823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 9121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 9121) = 1/(9121 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3476 : Bounds (-46002823 / 500000000) (-18401129 / 200000000) (Real.log (9121 / 10000)) := by
  have h := reflection_log_3476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3477_neg : (1689139 / 20000000) ≤ -Real.log (500000 / 544063) ∧
    -Real.log (500000 / 544063) ≤ (84456951 / 1000000000) := by
  have h := checkLog_sound (w := (44063 / 1044063)) (n := 12)
    (lo := (1689139 / 20000000)) (hi := (84456951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544063 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544063 / 500000) = 1/(500000 / 544063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3477 : Bounds (1689139 / 20000000) (84456951 / 1000000000) (Real.log (544063 / 500000)) := by
  have h := reflection_log_3477_neg
  have he : Real.log (544063 / 500000) = -Real.log (500000 / 544063) := by
    rw [show ((544063 / 500000) : ℝ) = ((500000 / 544063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3478_neg : (5765841 / 62500000) ≤ -Real.log (455937 / 500000) ∧
    -Real.log (455937 / 500000) ≤ (92253457 / 1000000000) := by
  have h := checkLog_sound (w := (44063 / 955937)) (n := 12)
    (lo := (5765841 / 62500000)) (hi := (92253457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455937) = 1/(455937 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3478 : Bounds (-92253457 / 1000000000) (-5765841 / 62500000) (Real.log (455937 / 500000)) := by
  have h := reflection_log_3478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3479_neg : (1559301 / 200000000) ≤ -Real.log (248058452031 / 250000000000) ∧
    -Real.log (248058452031 / 250000000000) ≤ (3898253 / 500000000) := by
  have h := checkLog_sound (w := (1941547969 / 498058452031)) (n := 12)
    (lo := (1559301 / 200000000)) (hi := (3898253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248058452031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248058452031) = 1/(248058452031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3479 : Bounds (-3898253 / 500000000) (-1559301 / 200000000) (Real.log (248058452031 / 250000000000)) := by
  have h := reflection_log_3479_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3480_neg : (7756413 / 1000000000) ≤ -Real.log (99227359 / 100000000) ∧
    -Real.log (99227359 / 100000000) ≤ (3878207 / 500000000) := by
  have h := checkLog_sound (w := (772641 / 199227359)) (n := 12)
    (lo := (7756413 / 1000000000)) (hi := (3878207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 99227359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 99227359) = 1/(99227359 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3480 : Bounds (-3878207 / 500000000) (-7756413 / 1000000000) (Real.log (99227359 / 100000000)) := by
  have h := reflection_log_3480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3481_neg : (88127439 / 500000000) ≤ -Real.log (10000000000 / 11927420239) ∧
    -Real.log (10000000000 / 11927420239) ≤ (176254879 / 1000000000) := by
  have h := checkLog_sound (w := (1927420239 / 21927420239)) (n := 12)
    (lo := (88127439 / 500000000)) (hi := (176254879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11927420239 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11927420239 / 10000000000) = 1/(10000000000 / 11927420239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3481 : Bounds (88127439 / 500000000) (176254879 / 1000000000) (Real.log (11927420239 / 10000000000)) := by
  have h := reflection_log_3481_neg
  have he : Real.log (11927420239 / 10000000000) = -Real.log (10000000000 / 11927420239) := by
    rw [show ((11927420239 / 10000000000) : ℝ) = ((10000000000 / 11927420239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3482_neg : (88355203 / 500000000) ≤ -Real.log (500000000000 / 596642737923) ∧
    -Real.log (500000000000 / 596642737923) ≤ (176710407 / 1000000000) := by
  have h := checkLog_sound (w := (96642737923 / 1096642737923)) (n := 12)
    (lo := (88355203 / 500000000)) (hi := (176710407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596642737923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596642737923 / 500000000000) = 1/(500000000000 / 596642737923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3482 : Bounds (88355203 / 500000000) (176710407 / 1000000000) (Real.log (596642737923 / 500000000000)) := by
  have h := reflection_log_3482_neg
  have he : Real.log (596642737923 / 500000000000) = -Real.log (500000000000 / 596642737923) := by
    rw [show ((596642737923 / 500000000000) : ℝ) = ((500000000000 / 596642737923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3483_neg : (8841001 / 25000000) ≤ -Real.log (500000000000 / 712121212121) ∧
    -Real.log (500000000000 / 712121212121) ≤ (353640041 / 1000000000) := by
  have h := checkLog_sound (w := (212121212121 / 1212121212121)) (n := 12)
    (lo := (8841001 / 25000000)) (hi := (353640041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712121212121 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712121212121 / 500000000000) = 1/(500000000000 / 712121212121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3483 : Bounds (8841001 / 25000000) (353640041 / 1000000000) (Real.log (712121212121 / 500000000000)) := by
  have h := reflection_log_3483_neg
  have he : Real.log (712121212121 / 500000000000) = -Real.log (500000000000 / 712121212121) := by
    rw [show ((712121212121 / 500000000000) : ℝ) = ((500000000000 / 712121212121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3484_neg : (176923181 / 500000000) ≤ -Real.log (125000000000 / 178067038429) ∧
    -Real.log (125000000000 / 178067038429) ≤ (353846363 / 1000000000) := by
  have h := checkLog_sound (w := (53067038429 / 303067038429)) (n := 12)
    (lo := (176923181 / 500000000)) (hi := (353846363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178067038429 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178067038429 / 125000000000) = 1/(125000000000 / 178067038429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3484 : Bounds (176923181 / 500000000) (353846363 / 1000000000) (Real.log (178067038429 / 125000000000)) := by
  have h := reflection_log_3484_neg
  have he : Real.log (178067038429 / 125000000000) = -Real.log (125000000000 / 178067038429) := by
    rw [show ((178067038429 / 125000000000) : ℝ) = ((125000000000 / 178067038429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3485_neg : (32287669 / 200000000) ≤ -Real.log (1250 / 1469) ∧
    -Real.log (1250 / 1469) ≤ (80719173 / 500000000) := by
  have h := checkLog_sound (w := (219 / 2719)) (n := 12)
    (lo := (32287669 / 200000000)) (hi := (80719173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1469 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1469 / 1250) = 1/(1250 / 1469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3485 : Bounds (32287669 / 200000000) (80719173 / 500000000) (Real.log (1469 / 1250)) := by
  have h := reflection_log_3485_neg
  have he : Real.log (1469 / 1250) = -Real.log (1250 / 1469) := by
    rw [show ((1469 / 1250) : ℝ) = ((1250 / 1469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3486_neg : (96307173 / 500000000) ≤ -Real.log (1031 / 1250) ∧
    -Real.log (1031 / 1250) ≤ (192614347 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 2281)) (n := 12)
    (lo := (96307173 / 500000000)) (hi := (192614347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1031) = 1/(1031 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3486 : Bounds (-192614347 / 1000000000) (-96307173 / 500000000) (Real.log (1031 / 1250)) := by
  have h := reflection_log_3486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3487_neg : (10949 / 62500000) ≤ -Real.log (1250000 / 1250219) ∧
    -Real.log (1250000 / 1250219) ≤ (35037 / 200000000) := by
  have h := checkLog_sound (w := (219 / 2500219)) (n := 12)
    (lo := (10949 / 62500000)) (hi := (35037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250219 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250219 / 1250000) = 1/(1250000 / 1250219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3487 : Bounds (10949 / 62500000) (35037 / 200000000) (Real.log (1250219 / 1250000)) := by
  have h := reflection_log_3487_neg
  have he : Real.log (1250219 / 1250000) = -Real.log (1250000 / 1250219) := by
    rw [show ((1250219 / 1250000) : ℝ) = ((1250000 / 1250219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3488_neg : (35043 / 200000000) ≤ -Real.log (1249781 / 1250000) ∧
    -Real.log (1249781 / 1250000) ≤ (10951 / 62500000) := by
  have h := checkLog_sound (w := (219 / 2499781)) (n := 12)
    (lo := (35043 / 200000000)) (hi := (10951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249781) = 1/(1249781 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3488 : Bounds (-10951 / 62500000) (-35043 / 200000000) (Real.log (1249781 / 1250000)) := by
  have h := reflection_log_3488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3489_neg : (8429611 / 100000000) ≤ -Real.log (1000000 / 1087951) ∧
    -Real.log (1000000 / 1087951) ≤ (84296111 / 1000000000) := by
  have h := checkLog_sound (w := (87951 / 2087951)) (n := 12)
    (lo := (8429611 / 100000000)) (hi := (84296111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087951 / 1000000) = 1/(1000000 / 1087951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3489 : Bounds (8429611 / 100000000) (84296111 / 1000000000) (Real.log (1087951 / 1000000)) := by
  have h := reflection_log_3489_neg
  have he : Real.log (1087951 / 1000000) = -Real.log (1000000 / 1087951) := by
    rw [show ((1087951 / 1000000) : ℝ) = ((1000000 / 1087951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3490_neg : (46030781 / 500000000) ≤ -Real.log (912049 / 1000000) ∧
    -Real.log (912049 / 1000000) ≤ (92061563 / 1000000000) := by
  have h := checkLog_sound (w := (87951 / 1912049)) (n := 12)
    (lo := (46030781 / 500000000)) (hi := (92061563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912049) = 1/(912049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3490 : Bounds (-92061563 / 1000000000) (-46030781 / 500000000) (Real.log (912049 / 1000000)) := by
  have h := reflection_log_3490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3491_neg : (84503819 / 1000000000) ≤ -Real.log (1000000 / 1088177) ∧
    -Real.log (1000000 / 1088177) ≤ (4225191 / 50000000) := by
  have h := checkLog_sound (w := (88177 / 2088177)) (n := 12)
    (lo := (84503819 / 1000000000)) (hi := (4225191 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088177 / 1000000) = 1/(1000000 / 1088177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3491 : Bounds (84503819 / 1000000000) (4225191 / 50000000) (Real.log (1088177 / 1000000)) := by
  have h := reflection_log_3491_neg
  have he : Real.log (1088177 / 1000000) = -Real.log (1000000 / 1088177) := by
    rw [show ((1088177 / 1000000) : ℝ) = ((1000000 / 1088177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3492_neg : (46154693 / 500000000) ≤ -Real.log (911823 / 1000000) ∧
    -Real.log (911823 / 1000000) ≤ (92309387 / 1000000000) := by
  have h := checkLog_sound (w := (88177 / 1911823)) (n := 12)
    (lo := (46154693 / 500000000)) (hi := (92309387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911823) = 1/(911823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3492 : Bounds (-92309387 / 1000000000) (-46154693 / 500000000) (Real.log (911823 / 1000000)) := by
  have h := reflection_log_3492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3493_neg : (7805567 / 1000000000) ≤ -Real.log (992224816671 / 1000000000000) ∧
    -Real.log (992224816671 / 1000000000000) ≤ (60981 / 7812500) := by
  have h := checkLog_sound (w := (7775183329 / 1992224816671)) (n := 12)
    (lo := (7805567 / 1000000000)) (hi := (60981 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992224816671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992224816671) = 1/(992224816671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3493 : Bounds (-60981 / 7812500) (-7805567 / 1000000000) (Real.log (992224816671 / 1000000000000)) := by
  have h := reflection_log_3493_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3494_neg : (7765451 / 1000000000) ≤ -Real.log (992264621599 / 1000000000000) ∧
    -Real.log (992264621599 / 1000000000000) ≤ (1941363 / 250000000) := by
  have h := checkLog_sound (w := (7735378401 / 1992264621599)) (n := 12)
    (lo := (7765451 / 1000000000)) (hi := (1941363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992264621599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992264621599) = 1/(992264621599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3494 : Bounds (-1941363 / 250000000) (-7765451 / 1000000000) (Real.log (992264621599 / 1000000000000)) := by
  have h := reflection_log_3494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3495_neg : (22044709 / 125000000) ≤ -Real.log (500000000000 / 596432318877) ∧
    -Real.log (500000000000 / 596432318877) ≤ (176357673 / 1000000000) := by
  have h := checkLog_sound (w := (96432318877 / 1096432318877)) (n := 12)
    (lo := (22044709 / 125000000)) (hi := (176357673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596432318877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596432318877 / 500000000000) = 1/(500000000000 / 596432318877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3495 : Bounds (22044709 / 125000000) (176357673 / 1000000000) (Real.log (596432318877 / 500000000000)) := by
  have h := reflection_log_3495_neg
  have he : Real.log (596432318877 / 500000000000) = -Real.log (500000000000 / 596432318877) := by
    rw [show ((596432318877 / 500000000000) : ℝ) = ((500000000000 / 596432318877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3496_neg : (35362641 / 200000000) ≤ -Real.log (500000000000 / 596704075243) ∧
    -Real.log (500000000000 / 596704075243) ≤ (88406603 / 500000000) := by
  have h := checkLog_sound (w := (96704075243 / 1096704075243)) (n := 12)
    (lo := (35362641 / 200000000)) (hi := (88406603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596704075243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596704075243 / 500000000000) = 1/(500000000000 / 596704075243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3496 : Bounds (35362641 / 200000000) (88406603 / 500000000) (Real.log (596704075243 / 500000000000)) := by
  have h := reflection_log_3496_neg
  have he : Real.log (596704075243 / 500000000000) = -Real.log (500000000000 / 596704075243) := by
    rw [show ((596704075243 / 500000000000) : ℝ) = ((500000000000 / 596704075243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3497_neg : (176923181 / 500000000) ≤ -Real.log (100000000000 / 142453630743) ∧
    -Real.log (100000000000 / 142453630743) ≤ (353846363 / 1000000000) := by
  have h := checkLog_sound (w := (42453630743 / 242453630743)) (n := 12)
    (lo := (176923181 / 500000000)) (hi := (353846363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142453630743 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142453630743 / 100000000000) = 1/(100000000000 / 142453630743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3497 : Bounds (176923181 / 500000000) (353846363 / 1000000000) (Real.log (142453630743 / 100000000000)) := by
  have h := reflection_log_3497_neg
  have he : Real.log (142453630743 / 100000000000) = -Real.log (100000000000 / 142453630743) := by
    rw [show ((142453630743 / 100000000000) : ℝ) = ((100000000000 / 142453630743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3498_neg : (88513173 / 250000000) ≤ -Real.log (500000000000 / 712415130941) ∧
    -Real.log (500000000000 / 712415130941) ≤ (354052693 / 1000000000) := by
  have h := checkLog_sound (w := (212415130941 / 1212415130941)) (n := 12)
    (lo := (88513173 / 250000000)) (hi := (354052693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712415130941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712415130941 / 500000000000) = 1/(500000000000 / 712415130941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3498 : Bounds (88513173 / 250000000) (354052693 / 1000000000) (Real.log (712415130941 / 500000000000)) := by
  have h := reflection_log_3498_neg
  have he : Real.log (712415130941 / 500000000000) = -Real.log (500000000000 / 712415130941) := by
    rw [show ((712415130941 / 500000000000) : ℝ) = ((500000000000 / 712415130941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3499_neg : (80761717 / 500000000) ≤ -Real.log (10000 / 11753) ∧
    -Real.log (10000 / 11753) ≤ (32304687 / 200000000) := by
  have h := checkLog_sound (w := (1753 / 21753)) (n := 12)
    (lo := (80761717 / 500000000)) (hi := (32304687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11753 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11753 / 10000) = 1/(10000 / 11753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3499 : Bounds (80761717 / 500000000) (32304687 / 200000000) (Real.log (11753 / 10000)) := by
  have h := reflection_log_3499_neg
  have he : Real.log (11753 / 10000) = -Real.log (10000 / 11753) := by
    rw [show ((11753 / 10000) : ℝ) = ((10000 / 11753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3500_neg : (38547119 / 200000000) ≤ -Real.log (8247 / 10000) ∧
    -Real.log (8247 / 10000) ≤ (48183899 / 250000000) := by
  have h := checkLog_sound (w := (1753 / 18247)) (n := 12)
    (lo := (38547119 / 200000000)) (hi := (48183899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8247) = 1/(8247 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3500 : Bounds (-48183899 / 250000000) (-38547119 / 200000000) (Real.log (8247 / 10000)) := by
  have h := reflection_log_3500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3501_neg : (43821 / 250000000) ≤ -Real.log (10000000 / 10001753) ∧
    -Real.log (10000000 / 10001753) ≤ (35057 / 200000000) := by
  have h := checkLog_sound (w := (1753 / 20001753)) (n := 12)
    (lo := (43821 / 250000000)) (hi := (35057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001753 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001753 / 10000000) = 1/(10000000 / 10001753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3501 : Bounds (43821 / 250000000) (35057 / 200000000) (Real.log (10001753 / 10000000)) := by
  have h := reflection_log_3501_neg
  have he : Real.log (10001753 / 10000000) = -Real.log (10000000 / 10001753) := by
    rw [show ((10001753 / 10000000) : ℝ) = ((10000000 / 10001753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3502_neg : (35063 / 200000000) ≤ -Real.log (9998247 / 10000000) ∧
    -Real.log (9998247 / 10000000) ≤ (43829 / 250000000) := by
  have h := checkLog_sound (w := (1753 / 19998247)) (n := 12)
    (lo := (35063 / 200000000)) (hi := (43829 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998247) = 1/(9998247 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3502 : Bounds (-43829 / 250000000) (-35063 / 200000000) (Real.log (9998247 / 10000000)) := by
  have h := reflection_log_3502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3503_neg : (42171493 / 500000000) ≤ -Real.log (500000 / 544001) ∧
    -Real.log (500000 / 544001) ≤ (84342987 / 1000000000) := by
  have h := checkLog_sound (w := (44001 / 1044001)) (n := 12)
    (lo := (42171493 / 500000000)) (hi := (84342987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544001 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544001 / 500000) = 1/(500000 / 544001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3503 : Bounds (42171493 / 500000000) (84342987 / 1000000000) (Real.log (544001 / 500000)) := by
  have h := reflection_log_3503_neg
  have he : Real.log (544001 / 500000) = -Real.log (500000 / 544001) := by
    rw [show ((544001 / 500000) : ℝ) = ((500000 / 544001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3504_neg : (92117481 / 1000000000) ≤ -Real.log (455999 / 500000) ∧
    -Real.log (455999 / 500000) ≤ (46058741 / 500000000) := by
  have h := checkLog_sound (w := (44001 / 955999)) (n := 12)
    (lo := (92117481 / 1000000000)) (hi := (46058741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455999) = 1/(455999 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3504 : Bounds (-46058741 / 500000000) (-92117481 / 1000000000) (Real.log (455999 / 500000)) := by
  have h := reflection_log_3504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3505_neg : (16910137 / 200000000) ≤ -Real.log (250000 / 272057) ∧
    -Real.log (250000 / 272057) ≤ (42275343 / 500000000) := by
  have h := checkLog_sound (w := (22057 / 522057)) (n := 12)
    (lo := (16910137 / 200000000)) (hi := (42275343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272057 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272057 / 250000) = 1/(250000 / 272057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3505 : Bounds (16910137 / 200000000) (42275343 / 500000000) (Real.log (272057 / 250000)) := by
  have h := reflection_log_3505_neg
  have he : Real.log (272057 / 250000) = -Real.log (250000 / 272057) := by
    rw [show ((272057 / 250000) : ℝ) = ((250000 / 272057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3506_neg : (2309133 / 25000000) ≤ -Real.log (227943 / 250000) ∧
    -Real.log (227943 / 250000) ≤ (92365321 / 1000000000) := by
  have h := checkLog_sound (w := (22057 / 477943)) (n := 12)
    (lo := (2309133 / 25000000)) (hi := (92365321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227943) = 1/(227943 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3506 : Bounds (-92365321 / 1000000000) (-2309133 / 25000000) (Real.log (227943 / 250000)) := by
  have h := reflection_log_3506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3507_neg : (3907317 / 500000000) ≤ -Real.log (62013488751 / 62500000000) ∧
    -Real.log (62013488751 / 62500000000) ≤ (1562927 / 200000000) := by
  have h := checkLog_sound (w := (486511249 / 124513488751)) (n := 12)
    (lo := (3907317 / 500000000)) (hi := (1562927 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62013488751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62013488751) = 1/(62013488751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3507 : Bounds (-1562927 / 200000000) (-3907317 / 500000000) (Real.log (62013488751 / 62500000000)) := by
  have h := reflection_log_3507_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3508_neg : (1554899 / 200000000) ≤ -Real.log (248063911999 / 250000000000) ∧
    -Real.log (248063911999 / 250000000000) ≤ (242953 / 31250000) := by
  have h := checkLog_sound (w := (1936088001 / 498063911999)) (n := 12)
    (lo := (1554899 / 200000000)) (hi := (242953 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248063911999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248063911999) = 1/(248063911999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3508 : Bounds (-242953 / 31250000) (-1554899 / 200000000) (Real.log (248063911999 / 250000000000)) := by
  have h := reflection_log_3508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3509_neg : (44115117 / 250000000) ≤ -Real.log (500000000000 / 596493632661) ∧
    -Real.log (500000000000 / 596493632661) ≤ (176460469 / 1000000000) := by
  have h := checkLog_sound (w := (96493632661 / 1096493632661)) (n := 12)
    (lo := (44115117 / 250000000)) (hi := (176460469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596493632661 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596493632661 / 500000000000) = 1/(500000000000 / 596493632661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3509 : Bounds (44115117 / 250000000) (176460469 / 1000000000) (Real.log (596493632661 / 500000000000)) := by
  have h := reflection_log_3509_neg
  have he : Real.log (596493632661 / 500000000000) = -Real.log (500000000000 / 596493632661) := by
    rw [show ((596493632661 / 500000000000) : ℝ) = ((500000000000 / 596493632661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3510_neg : (35383201 / 200000000) ≤ -Real.log (250000000000 / 298382709713) ∧
    -Real.log (250000000000 / 298382709713) ≤ (88458003 / 500000000) := by
  have h := checkLog_sound (w := (48382709713 / 548382709713)) (n := 12)
    (lo := (35383201 / 200000000)) (hi := (88458003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298382709713 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298382709713 / 250000000000) = 1/(250000000000 / 298382709713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3510 : Bounds (35383201 / 200000000) (88458003 / 500000000) (Real.log (298382709713 / 250000000000)) := by
  have h := reflection_log_3510_neg
  have he : Real.log (298382709713 / 250000000000) = -Real.log (250000000000 / 298382709713) := by
    rw [show ((298382709713 / 250000000000) : ℝ) = ((250000000000 / 298382709713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3511_neg : (88513173 / 250000000) ≤ -Real.log (25000000000 / 35620756547) ∧
    -Real.log (25000000000 / 35620756547) ≤ (354052693 / 1000000000) := by
  have h := checkLog_sound (w := (10620756547 / 60620756547)) (n := 12)
    (lo := (88513173 / 250000000)) (hi := (354052693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35620756547 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35620756547 / 25000000000) = 1/(25000000000 / 35620756547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3511 : Bounds (88513173 / 250000000) (354052693 / 1000000000) (Real.log (35620756547 / 25000000000)) := by
  have h := reflection_log_3511_neg
  have he : Real.log (35620756547 / 25000000000) = -Real.log (25000000000 / 35620756547) := by
    rw [show ((35620756547 / 25000000000) : ℝ) = ((25000000000 / 35620756547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3512_neg : (354259029 / 1000000000) ≤ -Real.log (50000000000 / 71256214381) ∧
    -Real.log (50000000000 / 71256214381) ≤ (35425903 / 100000000) := by
  have h := checkLog_sound (w := (21256214381 / 121256214381)) (n := 12)
    (lo := (354259029 / 1000000000)) (hi := (35425903 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71256214381 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71256214381 / 50000000000) = 1/(50000000000 / 71256214381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3512 : Bounds (354259029 / 1000000000) (35425903 / 100000000) (Real.log (71256214381 / 50000000000)) := by
  have h := reflection_log_3512_neg
  have he : Real.log (71256214381 / 50000000000) = -Real.log (50000000000 / 71256214381) := by
    rw [show ((71256214381 / 50000000000) : ℝ) = ((50000000000 / 71256214381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3513_neg : (32321703 / 200000000) ≤ -Real.log (5000 / 5877) ∧
    -Real.log (5000 / 5877) ≤ (40402129 / 250000000) := by
  have h := checkLog_sound (w := (877 / 10877)) (n := 12)
    (lo := (32321703 / 200000000)) (hi := (40402129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5877 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5877 / 5000) = 1/(5000 / 5877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3513 : Bounds (32321703 / 200000000) (40402129 / 250000000) (Real.log (5877 / 5000)) := by
  have h := reflection_log_3513_neg
  have he : Real.log (5877 / 5000) = -Real.log (5000 / 5877) := by
    rw [show ((5877 / 5000) : ℝ) = ((5000 / 5877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3514_neg : (96428429 / 500000000) ≤ -Real.log (4123 / 5000) ∧
    -Real.log (4123 / 5000) ≤ (192856859 / 1000000000) := by
  have h := checkLog_sound (w := (877 / 9123)) (n := 12)
    (lo := (96428429 / 500000000)) (hi := (192856859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4123) = 1/(4123 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3514 : Bounds (-192856859 / 1000000000) (-96428429 / 500000000) (Real.log (4123 / 5000)) := by
  have h := reflection_log_3514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3515_neg : (21923 / 125000000) ≤ -Real.log (5000000 / 5000877) ∧
    -Real.log (5000000 / 5000877) ≤ (35077 / 200000000) := by
  have h := checkLog_sound (w := (877 / 10000877)) (n := 12)
    (lo := (21923 / 125000000)) (hi := (35077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000877 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000877 / 5000000) = 1/(5000000 / 5000877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3515 : Bounds (21923 / 125000000) (35077 / 200000000) (Real.log (5000877 / 5000000)) := by
  have h := reflection_log_3515_neg
  have he : Real.log (5000877 / 5000000) = -Real.log (5000000 / 5000877) := by
    rw [show ((5000877 / 5000000) : ℝ) = ((5000000 / 5000877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3516_neg : (35083 / 200000000) ≤ -Real.log (4999123 / 5000000) ∧
    -Real.log (4999123 / 5000000) ≤ (21927 / 125000000) := by
  have h := checkLog_sound (w := (877 / 9999123)) (n := 12)
    (lo := (35083 / 200000000)) (hi := (21927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999123) = 1/(4999123 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3516 : Bounds (-21927 / 125000000) (-35083 / 200000000) (Real.log (4999123 / 5000000)) := by
  have h := reflection_log_3516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3517_neg : (84388941 / 1000000000) ≤ -Real.log (250000 / 272013) ∧
    -Real.log (250000 / 272013) ≤ (42194471 / 500000000) := by
  have h := checkLog_sound (w := (22013 / 522013)) (n := 12)
    (lo := (84388941 / 1000000000)) (hi := (42194471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272013 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272013 / 250000) = 1/(250000 / 272013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3517 : Bounds (84388941 / 1000000000) (42194471 / 500000000) (Real.log (272013 / 250000)) := by
  have h := reflection_log_3517_neg
  have he : Real.log (272013 / 250000) = -Real.log (250000 / 272013) := by
    rw [show ((272013 / 250000) : ℝ) = ((250000 / 272013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3518_neg : (23043077 / 250000000) ≤ -Real.log (227987 / 250000) ∧
    -Real.log (227987 / 250000) ≤ (92172309 / 1000000000) := by
  have h := checkLog_sound (w := (22013 / 477987)) (n := 12)
    (lo := (23043077 / 250000000)) (hi := (92172309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227987) = 1/(227987 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3518 : Bounds (-92172309 / 1000000000) (-23043077 / 250000000) (Real.log (227987 / 250000)) := by
  have h := reflection_log_3518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3519_neg : (84597549 / 1000000000) ≤ -Real.log (1000000 / 1088279) ∧
    -Real.log (1000000 / 1088279) ≤ (1691951 / 20000000) := by
  have h := checkLog_sound (w := (88279 / 2088279)) (n := 12)
    (lo := (84597549 / 1000000000)) (hi := (1691951 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088279 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088279 / 1000000) = 1/(1000000 / 1088279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3519 : Bounds (84597549 / 1000000000) (1691951 / 20000000) (Real.log (1088279 / 1000000)) := by
  have h := reflection_log_3519_neg
  have he : Real.log (1088279 / 1000000) = -Real.log (1000000 / 1088279) := by
    rw [show ((1088279 / 1000000) : ℝ) = ((1000000 / 1088279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


