-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0083__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0083__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:48:26.234597+00:00
-- url     : https://prove2.me/theorems/146ae0fc-4093-44f7-b1c2-020d3aa1178a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0085)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0085)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0085) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0083 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0084, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0085).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0083__3_q01

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0085 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5440_neg : (190617081 / 1000000000) ≤ -Real.log (31250000000 / 37812376033) ∧
    -Real.log (31250000000 / 37812376033) ≤ (95308541 / 500000000) := by
  have h := checkLog_sound (w := (6562376033 / 69062376033)) (n := 12)
    (lo := (190617081 / 1000000000)) (hi := (95308541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37812376033 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37812376033 / 31250000000) = 1/(31250000000 / 37812376033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5440 : Bounds (190617081 / 1000000000) (95308541 / 500000000) (Real.log (37812376033 / 31250000000)) := by
  have h := reflection_log_5440_neg
  have he : Real.log (37812376033 / 31250000000) = -Real.log (31250000000 / 37812376033) := by
    rw [show ((37812376033 / 31250000000) : ℝ) = ((31250000000 / 37812376033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5441_neg : (38220293 / 200000000) ≤ -Real.log (500000000000 / 605291139213) ∧
    -Real.log (500000000000 / 605291139213) ≤ (95550733 / 500000000) := by
  have h := checkLog_sound (w := (105291139213 / 1105291139213)) (n := 12)
    (lo := (38220293 / 200000000)) (hi := (95550733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605291139213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605291139213 / 500000000000) = 1/(500000000000 / 605291139213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5441 : Bounds (38220293 / 200000000) (95550733 / 500000000) (Real.log (605291139213 / 500000000000)) := by
  have h := reflection_log_5441_neg
  have he : Real.log (605291139213 / 500000000000) = -Real.log (500000000000 / 605291139213) := by
    rw [show ((605291139213 / 500000000000) : ℝ) = ((500000000000 / 605291139213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5442_neg : (191299921 / 500000000) ≤ -Real.log (15625000000 / 22907675709) ∧
    -Real.log (15625000000 / 22907675709) ≤ (382599843 / 1000000000) := by
  have h := checkLog_sound (w := (7282675709 / 38532675709)) (n := 12)
    (lo := (191299921 / 500000000)) (hi := (382599843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22907675709 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22907675709 / 15625000000) = 1/(15625000000 / 22907675709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5442 : Bounds (191299921 / 500000000) (382599843 / 1000000000) (Real.log (22907675709 / 15625000000)) := by
  have h := reflection_log_5442_neg
  have he : Real.log (22907675709 / 15625000000) = -Real.log (15625000000 / 22907675709) := by
    rw [show ((22907675709 / 15625000000) : ℝ) = ((15625000000 / 22907675709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5443_neg : (76561451 / 200000000) ≤ -Real.log (500000000000 / 733197681589) ∧
    -Real.log (500000000000 / 733197681589) ≤ (47850907 / 125000000) := by
  have h := checkLog_sound (w := (233197681589 / 1233197681589)) (n := 12)
    (lo := (76561451 / 200000000)) (hi := (47850907 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733197681589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733197681589 / 500000000000) = 1/(500000000000 / 733197681589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5443 : Bounds (76561451 / 200000000) (47850907 / 125000000) (Real.log (733197681589 / 500000000000)) := by
  have h := reflection_log_5443_neg
  have he : Real.log (733197681589 / 500000000000) = -Real.log (500000000000 / 733197681589) := by
    rw [show ((733197681589 / 500000000000) : ℝ) = ((500000000000 / 733197681589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5444_neg : (43320203 / 250000000) ≤ -Real.log (2500 / 2973) ∧
    -Real.log (2500 / 2973) ≤ (173280813 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 5473)) (n := 12)
    (lo := (43320203 / 250000000)) (hi := (173280813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2973 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2973 / 2500) = 1/(2500 / 2973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5444 : Bounds (43320203 / 250000000) (173280813 / 1000000000) (Real.log (2973 / 2500)) := by
  have h := reflection_log_5444_neg
  have he : Real.log (2973 / 2500) = -Real.log (2500 / 2973) := by
    rw [show ((2973 / 2500) : ℝ) = ((2500 / 2973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5445_neg : (26216733 / 125000000) ≤ -Real.log (2027 / 2500) ∧
    -Real.log (2027 / 2500) ≤ (41946773 / 200000000) := by
  have h := checkLog_sound (w := (473 / 4527)) (n := 12)
    (lo := (26216733 / 125000000)) (hi := (41946773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2027) = 1/(2027 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5445 : Bounds (-41946773 / 200000000) (-26216733 / 125000000) (Real.log (2027 / 2500)) := by
  have h := reflection_log_5445_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5446_neg : (94591 / 500000000) ≤ -Real.log (2500000 / 2500473) ∧
    -Real.log (2500000 / 2500473) ≤ (189183 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 5000473)) (n := 12)
    (lo := (94591 / 500000000)) (hi := (189183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500473 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500473 / 2500000) = 1/(2500000 / 2500473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5446 : Bounds (94591 / 500000000) (189183 / 1000000000) (Real.log (2500473 / 2500000)) := by
  have h := reflection_log_5446_neg
  have he : Real.log (2500473 / 2500000) = -Real.log (2500000 / 2500473) := by
    rw [show ((2500473 / 2500000) : ℝ) = ((2500000 / 2500473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5447_neg : (189217 / 1000000000) ≤ -Real.log (2499527 / 2500000) ∧
    -Real.log (2499527 / 2500000) ≤ (94609 / 500000000) := by
  have h := checkLog_sound (w := (473 / 4999527)) (n := 12)
    (lo := (189217 / 1000000000)) (hi := (94609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499527) = 1/(2499527 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5447 : Bounds (-94609 / 500000000) (-189217 / 1000000000) (Real.log (2499527 / 2500000)) := by
  have h := reflection_log_5447_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5448_neg : (45410057 / 500000000) ≤ -Real.log (31250 / 34221) ∧
    -Real.log (31250 / 34221) ≤ (18164023 / 200000000) := by
  have h := checkLog_sound (w := (2971 / 65471)) (n := 12)
    (lo := (45410057 / 500000000)) (hi := (18164023 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34221 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34221 / 31250) = 1/(31250 / 34221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5448 : Bounds (45410057 / 500000000) (18164023 / 200000000) (Real.log (34221 / 31250)) := by
  have h := reflection_log_5448_neg
  have he : Real.log (34221 / 31250) = -Real.log (31250 / 34221) := by
    rw [show ((34221 / 31250) : ℝ) = ((31250 / 34221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5449_neg : (12487487 / 125000000) ≤ -Real.log (28279 / 31250) ∧
    -Real.log (28279 / 31250) ≤ (99899897 / 1000000000) := by
  have h := checkLog_sound (w := (2971 / 59529)) (n := 12)
    (lo := (12487487 / 125000000)) (hi := (99899897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28279) = 1/(28279 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5449 : Bounds (-99899897 / 1000000000) (-12487487 / 125000000) (Real.log (28279 / 31250)) := by
  have h := reflection_log_5449_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5450_neg : (45519627 / 500000000) ≤ -Real.log (62500 / 68457) ∧
    -Real.log (62500 / 68457) ≤ (18207851 / 200000000) := by
  have h := checkLog_sound (w := (5957 / 130957)) (n := 12)
    (lo := (45519627 / 500000000)) (hi := (18207851 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68457 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68457 / 62500) = 1/(62500 / 68457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5450 : Bounds (45519627 / 500000000) (18207851 / 200000000) (Real.log (68457 / 62500)) := by
  have h := reflection_log_5450_neg
  have he : Real.log (68457 / 62500) = -Real.log (62500 / 68457) := by
    rw [show ((68457 / 62500) : ℝ) = ((62500 / 68457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5451_neg : (50082573 / 500000000) ≤ -Real.log (56543 / 62500) ∧
    -Real.log (56543 / 62500) ≤ (100165147 / 1000000000) := by
  have h := checkLog_sound (w := (5957 / 119043)) (n := 12)
    (lo := (50082573 / 500000000)) (hi := (100165147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56543) = 1/(56543 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5451 : Bounds (-100165147 / 1000000000) (-50082573 / 500000000) (Real.log (56543 / 62500)) := by
  have h := reflection_log_5451_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5452_neg : (9125891 / 1000000000) ≤ -Real.log (3870764151 / 3906250000) ∧
    -Real.log (3870764151 / 3906250000) ≤ (2281473 / 250000000) := by
  have h := checkLog_sound (w := (35485849 / 7777014151)) (n := 12)
    (lo := (9125891 / 1000000000)) (hi := (2281473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3870764151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3870764151) = 1/(3870764151 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5452 : Bounds (-2281473 / 250000000) (-9125891 / 1000000000) (Real.log (3870764151 / 3906250000)) := by
  have h := reflection_log_5452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5453_neg : (9079781 / 1000000000) ≤ -Real.log (967735659 / 976562500) ∧
    -Real.log (967735659 / 976562500) ≤ (4539891 / 500000000) := by
  have h := checkLog_sound (w := (8826841 / 1944298159)) (n := 12)
    (lo := (9079781 / 1000000000)) (hi := (4539891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 967735659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 967735659) = 1/(967735659 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5453 : Bounds (-4539891 / 500000000) (-9079781 / 1000000000) (Real.log (967735659 / 976562500)) := by
  have h := reflection_log_5453_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5454_neg : (19072001 / 100000000) ≤ -Real.log (500000000000 / 605060292089) ∧
    -Real.log (500000000000 / 605060292089) ≤ (190720011 / 1000000000) := by
  have h := checkLog_sound (w := (105060292089 / 1105060292089)) (n := 12)
    (lo := (19072001 / 100000000)) (hi := (190720011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605060292089 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605060292089 / 500000000000) = 1/(500000000000 / 605060292089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5454 : Bounds (19072001 / 100000000) (190720011 / 1000000000) (Real.log (605060292089 / 500000000000)) := by
  have h := reflection_log_5454_neg
  have he : Real.log (605060292089 / 500000000000) = -Real.log (500000000000 / 605060292089) := by
    rw [show ((605060292089 / 500000000000) : ℝ) = ((500000000000 / 605060292089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5455_neg : (478011 / 2500000) ≤ -Real.log (500000000000 / 605353447819) ∧
    -Real.log (500000000000 / 605353447819) ≤ (191204401 / 1000000000) := by
  have h := checkLog_sound (w := (105353447819 / 1105353447819)) (n := 12)
    (lo := (478011 / 2500000)) (hi := (191204401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605353447819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605353447819 / 500000000000) = 1/(500000000000 / 605353447819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5455 : Bounds (478011 / 2500000) (191204401 / 1000000000) (Real.log (605353447819 / 500000000000)) := by
  have h := reflection_log_5455_neg
  have he : Real.log (605353447819 / 500000000000) = -Real.log (500000000000 / 605353447819) := by
    rw [show ((605353447819 / 500000000000) : ℝ) = ((500000000000 / 605353447819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5456_neg : (76561451 / 200000000) ≤ -Real.log (125000000000 / 183299420397) ∧
    -Real.log (125000000000 / 183299420397) ≤ (47850907 / 125000000) := by
  have h := checkLog_sound (w := (58299420397 / 308299420397)) (n := 12)
    (lo := (76561451 / 200000000)) (hi := (47850907 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183299420397 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183299420397 / 125000000000) = 1/(125000000000 / 183299420397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5456 : Bounds (76561451 / 200000000) (47850907 / 125000000) (Real.log (183299420397 / 125000000000)) := by
  have h := reflection_log_5456_neg
  have he : Real.log (183299420397 / 125000000000) = -Real.log (125000000000 / 183299420397) := by
    rw [show ((183299420397 / 125000000000) : ℝ) = ((125000000000 / 183299420397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5457_neg : (95753669 / 250000000) ≤ -Real.log (250000000000 / 366674888999) ∧
    -Real.log (250000000000 / 366674888999) ≤ (383014677 / 1000000000) := by
  have h := checkLog_sound (w := (116674888999 / 616674888999)) (n := 12)
    (lo := (95753669 / 250000000)) (hi := (383014677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366674888999 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366674888999 / 250000000000) = 1/(250000000000 / 366674888999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5457 : Bounds (95753669 / 250000000) (383014677 / 1000000000) (Real.log (366674888999 / 250000000000)) := by
  have h := reflection_log_5457_neg
  have he : Real.log (366674888999 / 250000000000) = -Real.log (250000000000 / 366674888999) := by
    rw [show ((366674888999 / 250000000000) : ℝ) = ((250000000000 / 366674888999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5458_neg : (86682449 / 500000000) ≤ -Real.log (10000 / 11893) ∧
    -Real.log (10000 / 11893) ≤ (173364899 / 1000000000) := by
  have h := checkLog_sound (w := (1893 / 21893)) (n := 12)
    (lo := (86682449 / 500000000)) (hi := (173364899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11893 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11893 / 10000) = 1/(10000 / 11893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5458 : Bounds (86682449 / 500000000) (173364899 / 1000000000) (Real.log (11893 / 10000)) := by
  have h := reflection_log_5458_neg
  have he : Real.log (11893 / 10000) = -Real.log (10000 / 11893) := by
    rw [show ((11893 / 10000) : ℝ) = ((10000 / 11893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5459_neg : (104928603 / 500000000) ≤ -Real.log (8107 / 10000) ∧
    -Real.log (8107 / 10000) ≤ (209857207 / 1000000000) := by
  have h := checkLog_sound (w := (1893 / 18107)) (n := 12)
    (lo := (104928603 / 500000000)) (hi := (209857207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8107) = 1/(8107 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5459 : Bounds (-209857207 / 1000000000) (-104928603 / 500000000) (Real.log (8107 / 10000)) := by
  have h := reflection_log_5459_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5460_neg : (94641 / 500000000) ≤ -Real.log (10000000 / 10001893) ∧
    -Real.log (10000000 / 10001893) ≤ (189283 / 1000000000) := by
  have h := checkLog_sound (w := (1893 / 20001893)) (n := 12)
    (lo := (94641 / 500000000)) (hi := (189283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001893 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001893 / 10000000) = 1/(10000000 / 10001893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5460 : Bounds (94641 / 500000000) (189283 / 1000000000) (Real.log (10001893 / 10000000)) := by
  have h := reflection_log_5460_neg
  have he : Real.log (10001893 / 10000000) = -Real.log (10000000 / 10001893) := by
    rw [show ((10001893 / 10000000) : ℝ) = ((10000000 / 10001893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5461_neg : (189317 / 1000000000) ≤ -Real.log (9998107 / 10000000) ∧
    -Real.log (9998107 / 10000000) ≤ (94659 / 500000000) := by
  have h := checkLog_sound (w := (1893 / 19998107)) (n := 12)
    (lo := (189317 / 1000000000)) (hi := (94659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998107) = 1/(9998107 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5461 : Bounds (-94659 / 500000000) (-189317 / 1000000000) (Real.log (9998107 / 10000000)) := by
  have h := reflection_log_5461_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5462_neg : (18173337 / 200000000) ≤ -Real.log (1000000 / 1095123) ∧
    -Real.log (1000000 / 1095123) ≤ (45433343 / 500000000) := by
  have h := checkLog_sound (w := (95123 / 2095123)) (n := 12)
    (lo := (18173337 / 200000000)) (hi := (45433343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095123 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095123 / 1000000) = 1/(1000000 / 1095123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5462 : Bounds (18173337 / 200000000) (45433343 / 500000000) (Real.log (1095123 / 1000000)) := by
  have h := reflection_log_5462_neg
  have he : Real.log (1095123 / 1000000) = -Real.log (1000000 / 1095123) := by
    rw [show ((1095123 / 1000000) : ℝ) = ((1000000 / 1095123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5463_neg : (3123633 / 31250000) ≤ -Real.log (904877 / 1000000) ∧
    -Real.log (904877 / 1000000) ≤ (99956257 / 1000000000) := by
  have h := checkLog_sound (w := (95123 / 1904877)) (n := 12)
    (lo := (3123633 / 31250000)) (hi := (99956257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904877) = 1/(904877 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5463 : Bounds (-99956257 / 1000000000) (-3123633 / 31250000) (Real.log (904877 / 1000000)) := by
  have h := reflection_log_5463_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5464_neg : (18217163 / 200000000) ≤ -Real.log (1000000 / 1095363) ∧
    -Real.log (1000000 / 1095363) ≤ (11385727 / 125000000) := by
  have h := checkLog_sound (w := (95363 / 2095363)) (n := 12)
    (lo := (18217163 / 200000000)) (hi := (11385727 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095363 / 1000000) = 1/(1000000 / 1095363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5464 : Bounds (18217163 / 200000000) (11385727 / 125000000) (Real.log (1095363 / 1000000)) := by
  have h := reflection_log_5464_neg
  have he : Real.log (1095363 / 1000000) = -Real.log (1000000 / 1095363) := by
    rw [show ((1095363 / 1000000) : ℝ) = ((1000000 / 1095363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5465_neg : (1252769 / 12500000) ≤ -Real.log (904637 / 1000000) ∧
    -Real.log (904637 / 1000000) ≤ (100221521 / 1000000000) := by
  have h := checkLog_sound (w := (95363 / 1904637)) (n := 12)
    (lo := (1252769 / 12500000)) (hi := (100221521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904637) = 1/(904637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5465 : Bounds (-100221521 / 1000000000) (-1252769 / 12500000) (Real.log (904637 / 1000000)) := by
  have h := reflection_log_5465_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5466_neg : (1827141 / 200000000) ≤ -Real.log (990905898231 / 1000000000000) ∧
    -Real.log (990905898231 / 1000000000000) ≤ (4567853 / 500000000) := by
  have h := checkLog_sound (w := (9094101769 / 1990905898231)) (n := 12)
    (lo := (1827141 / 200000000)) (hi := (4567853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990905898231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990905898231) = 1/(990905898231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5466 : Bounds (-4567853 / 500000000) (-1827141 / 200000000) (Real.log (990905898231 / 1000000000000)) := by
  have h := reflection_log_5466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5467_neg : (908957 / 100000000) ≤ -Real.log (990951614871 / 1000000000000) ∧
    -Real.log (990951614871 / 1000000000000) ≤ (9089571 / 1000000000) := by
  have h := checkLog_sound (w := (9048385129 / 1990951614871)) (n := 12)
    (lo := (908957 / 100000000)) (hi := (9089571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990951614871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990951614871) = 1/(990951614871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5467 : Bounds (-9089571 / 1000000000) (-908957 / 100000000) (Real.log (990951614871 / 1000000000000)) := by
  have h := reflection_log_5467_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5468_neg : (190822941 / 1000000000) ≤ -Real.log (50000000000 / 60512257467) ∧
    -Real.log (50000000000 / 60512257467) ≤ (95411471 / 500000000) := by
  have h := checkLog_sound (w := (10512257467 / 110512257467)) (n := 12)
    (lo := (190822941 / 1000000000)) (hi := (95411471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60512257467 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60512257467 / 50000000000) = 1/(50000000000 / 60512257467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5468 : Bounds (190822941 / 1000000000) (95411471 / 500000000) (Real.log (60512257467 / 50000000000)) := by
  have h := reflection_log_5468_neg
  have he : Real.log (60512257467 / 50000000000) = -Real.log (50000000000 / 60512257467) := by
    rw [show ((60512257467 / 50000000000) : ℝ) = ((50000000000 / 60512257467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5469_neg : (38261467 / 200000000) ≤ -Real.log (10000000000 / 12108315269) ∧
    -Real.log (10000000000 / 12108315269) ≤ (23913417 / 125000000) := by
  have h := checkLog_sound (w := (2108315269 / 22108315269)) (n := 12)
    (lo := (38261467 / 200000000)) (hi := (23913417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12108315269 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12108315269 / 10000000000) = 1/(10000000000 / 12108315269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5469 : Bounds (38261467 / 200000000) (23913417 / 125000000) (Real.log (12108315269 / 10000000000)) := by
  have h := reflection_log_5469_neg
  have he : Real.log (12108315269 / 10000000000) = -Real.log (10000000000 / 12108315269) := by
    rw [show ((12108315269 / 10000000000) : ℝ) = ((10000000000 / 12108315269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5470_neg : (95753669 / 250000000) ≤ -Real.log (500000000000 / 733349777997) ∧
    -Real.log (500000000000 / 733349777997) ≤ (383014677 / 1000000000) := by
  have h := checkLog_sound (w := (233349777997 / 1233349777997)) (n := 12)
    (lo := (95753669 / 250000000)) (hi := (383014677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733349777997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733349777997 / 500000000000) = 1/(500000000000 / 733349777997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5470 : Bounds (95753669 / 250000000) (383014677 / 1000000000) (Real.log (733349777997 / 500000000000)) := by
  have h := reflection_log_5470_neg
  have he : Real.log (733349777997 / 500000000000) = -Real.log (500000000000 / 733349777997) := by
    rw [show ((733349777997 / 500000000000) : ℝ) = ((500000000000 / 733349777997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5471_neg : (76644421 / 200000000) ≤ -Real.log (62500000000 / 91687738991) ∧
    -Real.log (62500000000 / 91687738991) ≤ (191611053 / 500000000) := by
  have h := checkLog_sound (w := (29187738991 / 154187738991)) (n := 12)
    (lo := (76644421 / 200000000)) (hi := (191611053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91687738991 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91687738991 / 62500000000) = 1/(62500000000 / 91687738991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5471 : Bounds (76644421 / 200000000) (191611053 / 500000000) (Real.log (91687738991 / 62500000000)) := by
  have h := reflection_log_5471_neg
  have he : Real.log (91687738991 / 62500000000) = -Real.log (62500000000 / 91687738991) := by
    rw [show ((91687738991 / 62500000000) : ℝ) = ((62500000000 / 91687738991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5472_neg : (86724489 / 500000000) ≤ -Real.log (5000 / 5947) ∧
    -Real.log (5000 / 5947) ≤ (173448979 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 10947)) (n := 12)
    (lo := (86724489 / 500000000)) (hi := (173448979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5947 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5947 / 5000) = 1/(5000 / 5947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5472 : Bounds (86724489 / 500000000) (173448979 / 1000000000) (Real.log (5947 / 5000)) := by
  have h := reflection_log_5472_neg
  have he : Real.log (5947 / 5000) = -Real.log (5000 / 5947) := by
    rw [show ((5947 / 5000) : ℝ) = ((5000 / 5947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5473_neg : (52495141 / 250000000) ≤ -Real.log (4053 / 5000) ∧
    -Real.log (4053 / 5000) ≤ (41996113 / 200000000) := by
  have h := checkLog_sound (w := (947 / 9053)) (n := 12)
    (lo := (52495141 / 250000000)) (hi := (41996113 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4053) = 1/(4053 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5473 : Bounds (-41996113 / 200000000) (-52495141 / 250000000) (Real.log (4053 / 5000)) := by
  have h := reflection_log_5473_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5474_neg : (94691 / 500000000) ≤ -Real.log (5000000 / 5000947) ∧
    -Real.log (5000000 / 5000947) ≤ (189383 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 10000947)) (n := 12)
    (lo := (94691 / 500000000)) (hi := (189383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000947 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000947 / 5000000) = 1/(5000000 / 5000947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5474 : Bounds (94691 / 500000000) (189383 / 1000000000) (Real.log (5000947 / 5000000)) := by
  have h := reflection_log_5474_neg
  have he : Real.log (5000947 / 5000000) = -Real.log (5000000 / 5000947) := by
    rw [show ((5000947 / 5000000) : ℝ) = ((5000000 / 5000947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5475_neg : (189417 / 1000000000) ≤ -Real.log (4999053 / 5000000) ∧
    -Real.log (4999053 / 5000000) ≤ (94709 / 500000000) := by
  have h := checkLog_sound (w := (947 / 9999053)) (n := 12)
    (lo := (189417 / 1000000000)) (hi := (94709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999053) = 1/(4999053 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5475 : Bounds (-94709 / 500000000) (-189417 / 1000000000) (Real.log (4999053 / 5000000)) := by
  have h := reflection_log_5475_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5476_neg : (45456627 / 500000000) ≤ -Real.log (500000 / 547587) ∧
    -Real.log (500000 / 547587) ≤ (18182651 / 200000000) := by
  have h := checkLog_sound (w := (47587 / 1047587)) (n := 12)
    (lo := (45456627 / 500000000)) (hi := (18182651 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547587 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547587 / 500000) = 1/(500000 / 547587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5476 : Bounds (45456627 / 500000000) (18182651 / 200000000) (Real.log (547587 / 500000)) := by
  have h := reflection_log_5476_neg
  have he : Real.log (547587 / 500000) = -Real.log (500000 / 547587) := by
    rw [show ((547587 / 500000) : ℝ) = ((500000 / 547587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5477_neg : (50006309 / 500000000) ≤ -Real.log (452413 / 500000) ∧
    -Real.log (452413 / 500000) ≤ (100012619 / 1000000000) := by
  have h := checkLog_sound (w := (47587 / 952413)) (n := 12)
    (lo := (50006309 / 500000000)) (hi := (100012619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452413) = 1/(452413 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5477 : Bounds (-100012619 / 1000000000) (-50006309 / 500000000) (Real.log (452413 / 500000)) := by
  have h := reflection_log_5477_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5478_neg : (45566187 / 500000000) ≤ -Real.log (500000 / 547707) ∧
    -Real.log (500000 / 547707) ≤ (729059 / 8000000) := by
  have h := checkLog_sound (w := (47707 / 1047707)) (n := 12)
    (lo := (45566187 / 500000000)) (hi := (729059 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547707 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547707 / 500000) = 1/(500000 / 547707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5478 : Bounds (45566187 / 500000000) (729059 / 8000000) (Real.log (547707 / 500000)) := by
  have h := reflection_log_5478_neg
  have he : Real.log (547707 / 500000) = -Real.log (500000 / 547707) := by
    rw [show ((547707 / 500000) : ℝ) = ((500000 / 547707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5479_neg : (50138949 / 500000000) ≤ -Real.log (452293 / 500000) ∧
    -Real.log (452293 / 500000) ≤ (100277899 / 1000000000) := by
  have h := checkLog_sound (w := (47707 / 952293)) (n := 12)
    (lo := (50138949 / 500000000)) (hi := (100277899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452293) = 1/(452293 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5479 : Bounds (-100277899 / 1000000000) (-50138949 / 500000000) (Real.log (452293 / 500000)) := by
  have h := reflection_log_5479_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5480_neg : (2286381 / 250000000) ≤ -Real.log (247724042151 / 250000000000) ∧
    -Real.log (247724042151 / 250000000000) ≤ (365821 / 40000000) := by
  have h := checkLog_sound (w := (2275957849 / 497724042151)) (n := 12)
    (lo := (2286381 / 250000000)) (hi := (365821 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247724042151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247724042151) = 1/(247724042151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5480 : Bounds (-365821 / 40000000) (-2286381 / 250000000) (Real.log (247724042151 / 250000000000)) := by
  have h := reflection_log_5480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5481_neg : (2274841 / 250000000) ≤ -Real.log (247735477431 / 250000000000) ∧
    -Real.log (247735477431 / 250000000000) ≤ (1819873 / 200000000) := by
  have h := checkLog_sound (w := (2264522569 / 497735477431)) (n := 12)
    (lo := (2274841 / 250000000)) (hi := (1819873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247735477431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247735477431) = 1/(247735477431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5481 : Bounds (-1819873 / 200000000) (-2274841 / 250000000) (Real.log (247735477431 / 250000000000)) := by
  have h := reflection_log_5481_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5482_neg : (190925873 / 1000000000) ≤ -Real.log (31250000000 / 37824054017) ∧
    -Real.log (31250000000 / 37824054017) ≤ (95462937 / 500000000) := by
  have h := checkLog_sound (w := (6574054017 / 69074054017)) (n := 12)
    (lo := (190925873 / 1000000000)) (hi := (95462937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37824054017 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37824054017 / 31250000000) = 1/(31250000000 / 37824054017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5482 : Bounds (190925873 / 1000000000) (95462937 / 500000000) (Real.log (37824054017 / 31250000000)) := by
  have h := reflection_log_5482_neg
  have he : Real.log (37824054017 / 31250000000) = -Real.log (31250000000 / 37824054017) := by
    rw [show ((37824054017 / 31250000000) : ℝ) = ((31250000000 / 37824054017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5483_neg : (5981571 / 31250000) ≤ -Real.log (125000000000 / 151369521527) ∧
    -Real.log (125000000000 / 151369521527) ≤ (191410273 / 1000000000) := by
  have h := checkLog_sound (w := (26369521527 / 276369521527)) (n := 12)
    (lo := (5981571 / 31250000)) (hi := (191410273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151369521527 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151369521527 / 125000000000) = 1/(125000000000 / 151369521527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5483 : Bounds (5981571 / 31250000) (191410273 / 1000000000) (Real.log (151369521527 / 125000000000)) := by
  have h := reflection_log_5483_neg
  have he : Real.log (151369521527 / 125000000000) = -Real.log (125000000000 / 151369521527) := by
    rw [show ((151369521527 / 125000000000) : ℝ) = ((125000000000 / 151369521527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5484_neg : (76644421 / 200000000) ≤ -Real.log (500000000000 / 733501911927) ∧
    -Real.log (500000000000 / 733501911927) ≤ (191611053 / 500000000) := by
  have h := checkLog_sound (w := (233501911927 / 1233501911927)) (n := 12)
    (lo := (76644421 / 200000000)) (hi := (191611053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733501911927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733501911927 / 500000000000) = 1/(500000000000 / 733501911927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5484 : Bounds (76644421 / 200000000) (191611053 / 500000000) (Real.log (733501911927 / 500000000000)) := by
  have h := reflection_log_5484_neg
  have he : Real.log (733501911927 / 500000000000) = -Real.log (500000000000 / 733501911927) := by
    rw [show ((733501911927 / 500000000000) : ℝ) = ((500000000000 / 733501911927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5485_neg : (383429543 / 1000000000) ≤ -Real.log (125000000000 / 183413520849) ∧
    -Real.log (125000000000 / 183413520849) ≤ (47928693 / 125000000) := by
  have h := checkLog_sound (w := (58413520849 / 308413520849)) (n := 12)
    (lo := (383429543 / 1000000000)) (hi := (47928693 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183413520849 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183413520849 / 125000000000) = 1/(125000000000 / 183413520849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5485 : Bounds (383429543 / 1000000000) (47928693 / 125000000) (Real.log (183413520849 / 125000000000)) := by
  have h := reflection_log_5485_neg
  have he : Real.log (183413520849 / 125000000000) = -Real.log (125000000000 / 183413520849) := by
    rw [show ((183413520849 / 125000000000) : ℝ) = ((125000000000 / 183413520849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5486_neg : (3470661 / 20000000) ≤ -Real.log (2000 / 2379) ∧
    -Real.log (2000 / 2379) ≤ (173533051 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 4379)) (n := 12)
    (lo := (3470661 / 20000000)) (hi := (173533051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2379 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2379 / 2000) = 1/(2000 / 2379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5486 : Bounds (3470661 / 20000000) (173533051 / 1000000000) (Real.log (2379 / 2000)) := by
  have h := reflection_log_5486_neg
  have he : Real.log (2379 / 2000) = -Real.log (2000 / 2379) := by
    rw [show ((2379 / 2000) : ℝ) = ((2000 / 2379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5487_neg : (210103937 / 1000000000) ≤ -Real.log (1621 / 2000) ∧
    -Real.log (1621 / 2000) ≤ (105051969 / 500000000) := by
  have h := checkLog_sound (w := (379 / 3621)) (n := 12)
    (lo := (210103937 / 1000000000)) (hi := (105051969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1621) = 1/(1621 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5487 : Bounds (-105051969 / 500000000) (-210103937 / 1000000000) (Real.log (1621 / 2000)) := by
  have h := reflection_log_5487_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5488_neg : (94741 / 500000000) ≤ -Real.log (2000000 / 2000379) ∧
    -Real.log (2000000 / 2000379) ≤ (189483 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 4000379)) (n := 12)
    (lo := (94741 / 500000000)) (hi := (189483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000379 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000379 / 2000000) = 1/(2000000 / 2000379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5488 : Bounds (94741 / 500000000) (189483 / 1000000000) (Real.log (2000379 / 2000000)) := by
  have h := reflection_log_5488_neg
  have he : Real.log (2000379 / 2000000) = -Real.log (2000000 / 2000379) := by
    rw [show ((2000379 / 2000000) : ℝ) = ((2000000 / 2000379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5489_neg : (189517 / 1000000000) ≤ -Real.log (1999621 / 2000000) ∧
    -Real.log (1999621 / 2000000) ≤ (94759 / 500000000) := by
  have h := checkLog_sound (w := (379 / 3999621)) (n := 12)
    (lo := (189517 / 1000000000)) (hi := (94759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999621) = 1/(1999621 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5489 : Bounds (-94759 / 500000000) (-189517 / 1000000000) (Real.log (1999621 / 2000000)) := by
  have h := reflection_log_5489_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5490_neg : (90959821 / 1000000000) ≤ -Real.log (40000 / 43809) ∧
    -Real.log (40000 / 43809) ≤ (45479911 / 500000000) := by
  have h := checkLog_sound (w := (3809 / 83809)) (n := 12)
    (lo := (90959821 / 1000000000)) (hi := (45479911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43809 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43809 / 40000) = 1/(40000 / 43809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5490 : Bounds (90959821 / 1000000000) (45479911 / 500000000) (Real.log (43809 / 40000)) := by
  have h := reflection_log_5490_neg
  have he : Real.log (43809 / 40000) = -Real.log (40000 / 43809) := by
    rw [show ((43809 / 40000) : ℝ) = ((40000 / 43809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5491_neg : (12508623 / 125000000) ≤ -Real.log (36191 / 40000) ∧
    -Real.log (36191 / 40000) ≤ (20013797 / 200000000) := by
  have h := checkLog_sound (w := (3809 / 76191)) (n := 12)
    (lo := (12508623 / 125000000)) (hi := (20013797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36191) = 1/(36191 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5491 : Bounds (-20013797 / 200000000) (-12508623 / 125000000) (Real.log (36191 / 40000)) := by
  have h := reflection_log_5491_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5492_neg : (9117893 / 100000000) ≤ -Real.log (200000 / 219093) ∧
    -Real.log (200000 / 219093) ≤ (91178931 / 1000000000) := by
  have h := checkLog_sound (w := (19093 / 419093)) (n := 12)
    (lo := (9117893 / 100000000)) (hi := (91178931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219093 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219093 / 200000) = 1/(200000 / 219093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5492 : Bounds (9117893 / 100000000) (91178931 / 1000000000) (Real.log (219093 / 200000)) := by
  have h := reflection_log_5492_neg
  have he : Real.log (219093 / 200000) = -Real.log (200000 / 219093) := by
    rw [show ((219093 / 200000) : ℝ) = ((200000 / 219093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5493_neg : (100334279 / 1000000000) ≤ -Real.log (180907 / 200000) ∧
    -Real.log (180907 / 200000) ≤ (2508357 / 25000000) := by
  have h := checkLog_sound (w := (19093 / 380907)) (n := 12)
    (lo := (100334279 / 1000000000)) (hi := (2508357 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180907) = 1/(180907 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5493 : Bounds (-2508357 / 25000000) (-100334279 / 1000000000) (Real.log (180907 / 200000)) := by
  have h := reflection_log_5493_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5494_neg : (2288837 / 250000000) ≤ -Real.log (39635457351 / 40000000000) ∧
    -Real.log (39635457351 / 40000000000) ≤ (9155349 / 1000000000) := by
  have h := checkLog_sound (w := (364542649 / 79635457351)) (n := 12)
    (lo := (2288837 / 250000000)) (hi := (9155349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39635457351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39635457351) = 1/(39635457351 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5494 : Bounds (-9155349 / 1000000000) (-2288837 / 250000000) (Real.log (39635457351 / 40000000000)) := by
  have h := reflection_log_5494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5495_neg : (9109163 / 1000000000) ≤ -Real.log (1585491519 / 1600000000) ∧
    -Real.log (1585491519 / 1600000000) ≤ (2277291 / 250000000) := by
  have h := checkLog_sound (w := (14508481 / 3185491519)) (n := 12)
    (lo := (9109163 / 1000000000)) (hi := (2277291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1585491519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1585491519) = 1/(1585491519 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5495 : Bounds (-2277291 / 250000000) (-9109163 / 1000000000) (Real.log (1585491519 / 1600000000)) := by
  have h := reflection_log_5495_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5496_neg : (95514403 / 500000000) ≤ -Real.log (7812500000 / 9456986889) ∧
    -Real.log (7812500000 / 9456986889) ≤ (191028807 / 1000000000) := by
  have h := checkLog_sound (w := (1644486889 / 17269486889)) (n := 12)
    (lo := (95514403 / 500000000)) (hi := (191028807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9456986889 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9456986889 / 7812500000) = 1/(7812500000 / 9456986889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5496 : Bounds (95514403 / 500000000) (191028807 / 1000000000) (Real.log (9456986889 / 7812500000)) := by
  have h := reflection_log_5496_neg
  have he : Real.log (9456986889 / 7812500000) = -Real.log (7812500000 / 9456986889) := by
    rw [show ((9456986889 / 7812500000) : ℝ) = ((7812500000 / 9456986889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5497_neg : (19151321 / 100000000) ≤ -Real.log (250000000000 / 302770207897) ∧
    -Real.log (250000000000 / 302770207897) ≤ (191513211 / 1000000000) := by
  have h := checkLog_sound (w := (52770207897 / 552770207897)) (n := 12)
    (lo := (19151321 / 100000000)) (hi := (191513211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302770207897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302770207897 / 250000000000) = 1/(250000000000 / 302770207897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5497 : Bounds (19151321 / 100000000) (191513211 / 1000000000) (Real.log (302770207897 / 250000000000)) := by
  have h := reflection_log_5497_neg
  have he : Real.log (302770207897 / 250000000000) = -Real.log (250000000000 / 302770207897) := by
    rw [show ((302770207897 / 250000000000) : ℝ) = ((250000000000 / 302770207897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5498_neg : (383429543 / 1000000000) ≤ -Real.log (100000000000 / 146730816679) ∧
    -Real.log (100000000000 / 146730816679) ≤ (47928693 / 125000000) := by
  have h := checkLog_sound (w := (46730816679 / 246730816679)) (n := 12)
    (lo := (383429543 / 1000000000)) (hi := (47928693 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146730816679 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146730816679 / 100000000000) = 1/(100000000000 / 146730816679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5498 : Bounds (383429543 / 1000000000) (47928693 / 125000000) (Real.log (146730816679 / 100000000000)) := by
  have h := reflection_log_5498_neg
  have he : Real.log (146730816679 / 100000000000) = -Real.log (100000000000 / 146730816679) := by
    rw [show ((146730816679 / 100000000000) : ℝ) = ((100000000000 / 146730816679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5499_neg : (95909247 / 250000000) ≤ -Real.log (500000000000 / 733806292413) ∧
    -Real.log (500000000000 / 733806292413) ≤ (383636989 / 1000000000) := by
  have h := checkLog_sound (w := (233806292413 / 1233806292413)) (n := 12)
    (lo := (95909247 / 250000000)) (hi := (383636989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733806292413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733806292413 / 500000000000) = 1/(500000000000 / 733806292413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5499 : Bounds (95909247 / 250000000) (383636989 / 1000000000) (Real.log (733806292413 / 500000000000)) := by
  have h := reflection_log_5499_neg
  have he : Real.log (733806292413 / 500000000000) = -Real.log (500000000000 / 733806292413) := by
    rw [show ((733806292413 / 500000000000) : ℝ) = ((500000000000 / 733806292413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5500_neg : (43404279 / 250000000) ≤ -Real.log (1250 / 1487) ∧
    -Real.log (1250 / 1487) ≤ (173617117 / 1000000000) := by
  have h := checkLog_sound (w := (237 / 2737)) (n := 12)
    (lo := (43404279 / 250000000)) (hi := (173617117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1487 / 1250) = 1/(1250 / 1487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5500 : Bounds (43404279 / 250000000) (173617117 / 1000000000) (Real.log (1487 / 1250)) := by
  have h := reflection_log_5500_neg
  have he : Real.log (1487 / 1250) = -Real.log (1250 / 1487) := by
    rw [show ((1487 / 1250) : ℝ) = ((1250 / 1487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5501_neg : (105113663 / 500000000) ≤ -Real.log (1013 / 1250) ∧
    -Real.log (1013 / 1250) ≤ (210227327 / 1000000000) := by
  have h := checkLog_sound (w := (237 / 2263)) (n := 12)
    (lo := (105113663 / 500000000)) (hi := (210227327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1013) = 1/(1013 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5501 : Bounds (-210227327 / 1000000000) (-105113663 / 500000000) (Real.log (1013 / 1250)) := by
  have h := reflection_log_5501_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5502_neg : (94791 / 500000000) ≤ -Real.log (1250000 / 1250237) ∧
    -Real.log (1250000 / 1250237) ≤ (189583 / 1000000000) := by
  have h := checkLog_sound (w := (237 / 2500237)) (n := 12)
    (lo := (94791 / 500000000)) (hi := (189583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250237 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250237 / 1250000) = 1/(1250000 / 1250237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5502 : Bounds (94791 / 500000000) (189583 / 1000000000) (Real.log (1250237 / 1250000)) := by
  have h := reflection_log_5502_neg
  have he : Real.log (1250237 / 1250000) = -Real.log (1250000 / 1250237) := by
    rw [show ((1250237 / 1250000) : ℝ) = ((1250000 / 1250237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5503_neg : (189617 / 1000000000) ≤ -Real.log (1249763 / 1250000) ∧
    -Real.log (1249763 / 1250000) ≤ (94809 / 500000000) := by
  have h := checkLog_sound (w := (237 / 2499763)) (n := 12)
    (lo := (189617 / 1000000000)) (hi := (94809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249763) = 1/(1249763 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5503 : Bounds (-94809 / 500000000) (-189617 / 1000000000) (Real.log (1249763 / 1250000)) := by
  have h := reflection_log_5503_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


