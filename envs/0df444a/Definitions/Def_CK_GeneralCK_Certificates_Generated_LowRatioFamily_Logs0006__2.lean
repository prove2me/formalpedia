-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0006__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0006__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:27:19.531957+00:00
-- url     : https://prove2.me/theorems/7e834ebb-c337-4e01-bf68-99a65de4446f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0006 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0007)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0006 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0007)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0006 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0007)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0006 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0007) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0006 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0007).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0006 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_384_neg : (40009937 / 500000000) ≤ -Real.log (461549 / 500000) ∧
    -Real.log (461549 / 500000) ≤ (640159 / 8000000) := by
  have h := checkLog_sound (w := (38451 / 961549)) (n := 12)
    (lo := (40009937 / 500000000)) (hi := (640159 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461549) = 1/(461549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_384 : Bounds (-640159 / 8000000) (-40009937 / 500000000) (Real.log (461549 / 500000)) := by
  have h := reflection_log_384_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_385_neg : (2965737 / 500000000) ≤ -Real.log (248521520599 / 250000000000) ∧
    -Real.log (248521520599 / 250000000000) ≤ (237259 / 40000000) := by
  have h := checkLog_sound (w := (1478479401 / 498521520599)) (n := 12)
    (lo := (2965737 / 500000000)) (hi := (237259 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248521520599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248521520599) = 1/(248521520599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_385 : Bounds (-237259 / 40000000) (-2965737 / 500000000) (Real.log (248521520599 / 250000000000)) := by
  have h := reflection_log_385_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_386_neg : (5899953 / 1000000000) ≤ -Real.log (248529354199 / 250000000000) ∧
    -Real.log (248529354199 / 250000000000) ≤ (2949977 / 500000000) := by
  have h := checkLog_sound (w := (1470645801 / 498529354199)) (n := 12)
    (lo := (5899953 / 1000000000)) (hi := (2949977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248529354199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248529354199) = 1/(248529354199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_386 : Bounds (-2949977 / 500000000) (-5899953 / 1000000000) (Real.log (248529354199 / 250000000000)) := by
  have h := reflection_log_386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_387_neg : (76848927 / 500000000) ≤ -Real.log (500000000000 / 583069244949) ∧
    -Real.log (500000000000 / 583069244949) ≤ (30739571 / 200000000) := by
  have h := checkLog_sound (w := (83069244949 / 1083069244949)) (n := 12)
    (lo := (76848927 / 500000000)) (hi := (30739571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583069244949 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583069244949 / 500000000000) = 1/(500000000000 / 583069244949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_387 : Bounds (76848927 / 500000000) (30739571 / 200000000) (Real.log (583069244949 / 500000000000)) := by
  have h := reflection_log_387_neg
  have he : Real.log (583069244949 / 500000000000) = -Real.log (500000000000 / 583069244949) := by
    rw [show ((583069244949 / 500000000000) : ℝ) = ((500000000000 / 583069244949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_388_neg : (6164331 / 40000000) ≤ -Real.log (125000000000 / 145827149447) ∧
    -Real.log (125000000000 / 145827149447) ≤ (38527069 / 250000000) := by
  have h := checkLog_sound (w := (20827149447 / 270827149447)) (n := 12)
    (lo := (6164331 / 40000000)) (hi := (38527069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145827149447 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145827149447 / 125000000000) = 1/(125000000000 / 145827149447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_388 : Bounds (6164331 / 40000000) (38527069 / 250000000) (Real.log (145827149447 / 125000000000)) := by
  have h := reflection_log_388_neg
  have he : Real.log (145827149447 / 125000000000) = -Real.log (125000000000 / 145827149447) := by
    rw [show ((145827149447 / 125000000000) : ℝ) = ((125000000000 / 145827149447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_389_neg : (154108517 / 500000000) ≤ -Real.log (500000000000 / 680498170227) ∧
    -Real.log (500000000000 / 680498170227) ≤ (61643407 / 200000000) := by
  have h := checkLog_sound (w := (180498170227 / 1180498170227)) (n := 12)
    (lo := (154108517 / 500000000)) (hi := (61643407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680498170227 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680498170227 / 500000000000) = 1/(500000000000 / 680498170227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_389 : Bounds (154108517 / 500000000) (61643407 / 200000000) (Real.log (680498170227 / 500000000000)) := by
  have h := reflection_log_389_neg
  have he : Real.log (680498170227 / 500000000000) = -Real.log (500000000000 / 680498170227) := by
    rw [show ((680498170227 / 500000000000) : ℝ) = ((500000000000 / 680498170227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_390_neg : (12336873 / 40000000) ≤ -Real.log (250000000000 / 340318772137) ∧
    -Real.log (250000000000 / 340318772137) ≤ (154210913 / 500000000) := by
  have h := checkLog_sound (w := (90318772137 / 590318772137)) (n := 12)
    (lo := (12336873 / 40000000)) (hi := (154210913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340318772137 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340318772137 / 250000000000) = 1/(250000000000 / 340318772137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_390 : Bounds (12336873 / 40000000) (154210913 / 500000000) (Real.log (340318772137 / 250000000000)) := by
  have h := reflection_log_390_neg
  have he : Real.log (340318772137 / 250000000000) = -Real.log (250000000000 / 340318772137) := by
    rw [show ((340318772137 / 250000000000) : ℝ) = ((250000000000 / 340318772137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_391_neg : (142453967 / 1000000000) ≤ -Real.log (10000 / 11531) ∧
    -Real.log (10000 / 11531) ≤ (8903373 / 62500000) := by
  have h := checkLog_sound (w := (1531 / 21531)) (n := 12)
    (lo := (142453967 / 1000000000)) (hi := (8903373 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11531 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11531 / 10000) = 1/(10000 / 11531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_391 : Bounds (142453967 / 1000000000) (8903373 / 62500000) (Real.log (11531 / 10000)) := by
  have h := reflection_log_391_neg
  have he : Real.log (11531 / 10000) = -Real.log (10000 / 11531) := by
    rw [show ((11531 / 10000) : ℝ) = ((10000 / 11531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_392_neg : (33234531 / 200000000) ≤ -Real.log (8469 / 10000) ∧
    -Real.log (8469 / 10000) ≤ (10385791 / 62500000) := by
  have h := checkLog_sound (w := (1531 / 18469)) (n := 12)
    (lo := (33234531 / 200000000)) (hi := (10385791 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8469) = 1/(8469 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_392 : Bounds (-10385791 / 62500000) (-33234531 / 200000000) (Real.log (8469 / 10000)) := by
  have h := reflection_log_392_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_393_neg : (299 / 1953125) ≤ -Real.log (10000000 / 10001531) ∧
    -Real.log (10000000 / 10001531) ≤ (153089 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 20001531)) (n := 12)
    (lo := (299 / 1953125)) (hi := (153089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001531 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001531 / 10000000) = 1/(10000000 / 10001531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_393 : Bounds (299 / 1953125) (153089 / 1000000000) (Real.log (10001531 / 10000000)) := by
  have h := reflection_log_393_neg
  have he : Real.log (10001531 / 10000000) = -Real.log (10000000 / 10001531) := by
    rw [show ((10001531 / 10000000) : ℝ) = ((10000000 / 10001531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_394_neg : (153111 / 1000000000) ≤ -Real.log (9998469 / 10000000) ∧
    -Real.log (9998469 / 10000000) ≤ (19139 / 125000000) := by
  have h := checkLog_sound (w := (1531 / 19998469)) (n := 12)
    (lo := (153111 / 1000000000)) (hi := (19139 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998469) = 1/(9998469 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_394 : Bounds (-19139 / 125000000) (-153111 / 1000000000) (Real.log (9998469 / 10000000)) := by
  have h := reflection_log_394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_395_neg : (73945387 / 1000000000) ≤ -Real.log (250000 / 269187) ∧
    -Real.log (250000 / 269187) ≤ (18486347 / 250000000) := by
  have h := checkLog_sound (w := (19187 / 519187)) (n := 12)
    (lo := (73945387 / 1000000000)) (hi := (18486347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269187 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269187 / 250000) = 1/(250000 / 269187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_395 : Bounds (73945387 / 1000000000) (18486347 / 250000000) (Real.log (269187 / 250000)) := by
  have h := reflection_log_395_neg
  have he : Real.log (269187 / 250000) = -Real.log (250000 / 269187) := by
    rw [show ((269187 / 250000) : ℝ) = ((250000 / 269187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_396_neg : (39926529 / 500000000) ≤ -Real.log (230813 / 250000) ∧
    -Real.log (230813 / 250000) ≤ (79853059 / 1000000000) := by
  have h := checkLog_sound (w := (19187 / 480813)) (n := 12)
    (lo := (39926529 / 500000000)) (hi := (79853059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230813) = 1/(230813 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_396 : Bounds (-79853059 / 1000000000) (-39926529 / 500000000) (Real.log (230813 / 250000)) := by
  have h := reflection_log_396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_397_neg : (74135757 / 1000000000) ≤ -Real.log (1000000 / 1076953) ∧
    -Real.log (1000000 / 1076953) ≤ (37067879 / 500000000) := by
  have h := checkLog_sound (w := (76953 / 2076953)) (n := 12)
    (lo := (74135757 / 1000000000)) (hi := (37067879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076953 / 1000000) = 1/(1000000 / 1076953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_397 : Bounds (74135757 / 1000000000) (37067879 / 500000000) (Real.log (1076953 / 1000000)) := by
  have h := reflection_log_397_neg
  have he : Real.log (1076953 / 1000000) = -Real.log (1000000 / 1076953) := by
    rw [show ((1076953 / 1000000) : ℝ) = ((1000000 / 1076953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_398_neg : (20018781 / 250000000) ≤ -Real.log (923047 / 1000000) ∧
    -Real.log (923047 / 1000000) ≤ (640601 / 8000000) := by
  have h := checkLog_sound (w := (76953 / 1923047)) (n := 12)
    (lo := (20018781 / 250000000)) (hi := (640601 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923047) = 1/(923047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_398 : Bounds (-640601 / 8000000) (-20018781 / 250000000) (Real.log (923047 / 1000000)) := by
  have h := reflection_log_398_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_399_neg : (5939367 / 1000000000) ≤ -Real.log (994078235791 / 1000000000000) ∧
    -Real.log (994078235791 / 1000000000000) ≤ (742421 / 125000000) := by
  have h := checkLog_sound (w := (5921764209 / 1994078235791)) (n := 12)
    (lo := (5939367 / 1000000000)) (hi := (742421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994078235791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994078235791) = 1/(994078235791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_399 : Bounds (-742421 / 125000000) (-5939367 / 1000000000) (Real.log (994078235791 / 1000000000000)) := by
  have h := reflection_log_399_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_400_neg : (5907671 / 1000000000) ≤ -Real.log (62131859031 / 62500000000) ∧
    -Real.log (62131859031 / 62500000000) ≤ (738459 / 125000000) := by
  have h := checkLog_sound (w := (368140969 / 124631859031)) (n := 12)
    (lo := (5907671 / 1000000000)) (hi := (738459 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62131859031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62131859031) = 1/(62131859031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_400 : Bounds (-738459 / 125000000) (-5907671 / 1000000000) (Real.log (62131859031 / 62500000000)) := by
  have h := reflection_log_400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_401_neg : (76899223 / 500000000) ≤ -Real.log (250000000000 / 291563950037) ∧
    -Real.log (250000000000 / 291563950037) ≤ (153798447 / 1000000000) := by
  have h := checkLog_sound (w := (41563950037 / 541563950037)) (n := 12)
    (lo := (76899223 / 500000000)) (hi := (153798447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291563950037 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291563950037 / 250000000000) = 1/(250000000000 / 291563950037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_401 : Bounds (76899223 / 500000000) (153798447 / 1000000000) (Real.log (291563950037 / 250000000000)) := by
  have h := reflection_log_401_neg
  have he : Real.log (291563950037 / 250000000000) = -Real.log (250000000000 / 291563950037) := by
    rw [show ((291563950037 / 250000000000) : ℝ) = ((250000000000 / 291563950037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_402_neg : (77105441 / 500000000) ≤ -Real.log (31250000000 / 36460528283) ∧
    -Real.log (31250000000 / 36460528283) ≤ (154210883 / 1000000000) := by
  have h := checkLog_sound (w := (5210528283 / 67710528283)) (n := 12)
    (lo := (77105441 / 500000000)) (hi := (154210883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36460528283 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36460528283 / 31250000000) = 1/(31250000000 / 36460528283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_402 : Bounds (77105441 / 500000000) (154210883 / 1000000000) (Real.log (36460528283 / 31250000000)) := by
  have h := reflection_log_402_neg
  have he : Real.log (36460528283 / 31250000000) = -Real.log (31250000000 / 36460528283) := by
    rw [show ((36460528283 / 31250000000) : ℝ) = ((31250000000 / 36460528283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_403_neg : (12336873 / 40000000) ≤ -Real.log (500000000000 / 680637544273) ∧
    -Real.log (500000000000 / 680637544273) ≤ (154210913 / 500000000) := by
  have h := checkLog_sound (w := (180637544273 / 1180637544273)) (n := 12)
    (lo := (12336873 / 40000000)) (hi := (154210913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680637544273 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680637544273 / 500000000000) = 1/(500000000000 / 680637544273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_403 : Bounds (12336873 / 40000000) (154210913 / 500000000) (Real.log (680637544273 / 500000000000)) := by
  have h := reflection_log_403_neg
  have he : Real.log (680637544273 / 500000000000) = -Real.log (500000000000 / 680637544273) := by
    rw [show ((680637544273 / 500000000000) : ℝ) = ((500000000000 / 680637544273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_404_neg : (154313311 / 500000000) ≤ -Real.log (250000000000 / 340388475617) ∧
    -Real.log (250000000000 / 340388475617) ≤ (308626623 / 1000000000) := by
  have h := checkLog_sound (w := (90388475617 / 590388475617)) (n := 12)
    (lo := (154313311 / 500000000)) (hi := (308626623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340388475617 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340388475617 / 250000000000) = 1/(250000000000 / 340388475617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_404 : Bounds (154313311 / 500000000) (308626623 / 1000000000) (Real.log (340388475617 / 250000000000)) := by
  have h := reflection_log_404_neg
  have he : Real.log (340388475617 / 250000000000) = -Real.log (250000000000 / 340388475617) := by
    rw [show ((340388475617 / 250000000000) : ℝ) = ((250000000000 / 340388475617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_405_neg : (71270343 / 500000000) ≤ -Real.log (2500 / 2883) ∧
    -Real.log (2500 / 2883) ≤ (142540687 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 5383)) (n := 12)
    (lo := (71270343 / 500000000)) (hi := (142540687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2883 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2883 / 2500) = 1/(2500 / 2883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_405 : Bounds (71270343 / 500000000) (142540687 / 1000000000) (Real.log (2883 / 2500)) := by
  have h := reflection_log_405_neg
  have he : Real.log (2883 / 2500) = -Real.log (2500 / 2883) := by
    rw [show ((2883 / 2500) : ℝ) = ((2500 / 2883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_406_neg : (166290739 / 1000000000) ≤ -Real.log (2117 / 2500) ∧
    -Real.log (2117 / 2500) ≤ (8314537 / 50000000) := by
  have h := checkLog_sound (w := (383 / 4617)) (n := 12)
    (lo := (166290739 / 1000000000)) (hi := (8314537 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2117) = 1/(2117 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_406 : Bounds (-8314537 / 50000000) (-166290739 / 1000000000) (Real.log (2117 / 2500)) := by
  have h := reflection_log_406_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_407_neg : (38297 / 250000000) ≤ -Real.log (2500000 / 2500383) ∧
    -Real.log (2500000 / 2500383) ≤ (153189 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 5000383)) (n := 12)
    (lo := (38297 / 250000000)) (hi := (153189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500383 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500383 / 2500000) = 1/(2500000 / 2500383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_407 : Bounds (38297 / 250000000) (153189 / 1000000000) (Real.log (2500383 / 2500000)) := by
  have h := reflection_log_407_neg
  have he : Real.log (2500383 / 2500000) = -Real.log (2500000 / 2500383) := by
    rw [show ((2500383 / 2500000) : ℝ) = ((2500000 / 2500383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_408_neg : (153211 / 1000000000) ≤ -Real.log (2499617 / 2500000) ∧
    -Real.log (2499617 / 2500000) ≤ (38303 / 250000000) := by
  have h := checkLog_sound (w := (383 / 4999617)) (n := 12)
    (lo := (153211 / 1000000000)) (hi := (38303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499617) = 1/(2499617 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_408 : Bounds (-38303 / 250000000) (-153211 / 1000000000) (Real.log (2499617 / 2500000)) := by
  have h := reflection_log_408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_409_neg : (73992751 / 1000000000) ≤ -Real.log (1000000 / 1076799) ∧
    -Real.log (1000000 / 1076799) ≤ (4624547 / 62500000) := by
  have h := checkLog_sound (w := (76799 / 2076799)) (n := 12)
    (lo := (73992751 / 1000000000)) (hi := (4624547 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076799 / 1000000) = 1/(1000000 / 1076799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_409 : Bounds (73992751 / 1000000000) (4624547 / 62500000) (Real.log (1076799 / 1000000)) := by
  have h := reflection_log_409_neg
  have he : Real.log (1076799 / 1000000) = -Real.log (1000000 / 1076799) := by
    rw [show ((1076799 / 1000000) : ℝ) = ((1000000 / 1076799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_410_neg : (799083 / 10000000) ≤ -Real.log (923201 / 1000000) ∧
    -Real.log (923201 / 1000000) ≤ (79908301 / 1000000000) := by
  have h := checkLog_sound (w := (76799 / 1923201)) (n := 12)
    (lo := (799083 / 10000000)) (hi := (79908301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923201) = 1/(923201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_410 : Bounds (-79908301 / 1000000000) (-799083 / 10000000) (Real.log (923201 / 1000000)) := by
  have h := reflection_log_410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_411_neg : (74182183 / 1000000000) ≤ -Real.log (1000000 / 1077003) ∧
    -Real.log (1000000 / 1077003) ≤ (9272773 / 125000000) := by
  have h := checkLog_sound (w := (77003 / 2077003)) (n := 12)
    (lo := (74182183 / 1000000000)) (hi := (9272773 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077003 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077003 / 1000000) = 1/(1000000 / 1077003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_411 : Bounds (74182183 / 1000000000) (9272773 / 125000000) (Real.log (1077003 / 1000000)) := by
  have h := reflection_log_411_neg
  have he : Real.log (1077003 / 1000000) = -Real.log (1000000 / 1077003) := by
    rw [show ((1077003 / 1000000) : ℝ) = ((1000000 / 1077003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_412_neg : (40064647 / 500000000) ≤ -Real.log (922997 / 1000000) ∧
    -Real.log (922997 / 1000000) ≤ (16025859 / 200000000) := by
  have h := checkLog_sound (w := (77003 / 1922997)) (n := 12)
    (lo := (40064647 / 500000000)) (hi := (16025859 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922997) = 1/(922997 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_412 : Bounds (-16025859 / 200000000) (-40064647 / 500000000) (Real.log (922997 / 1000000)) := by
  have h := reflection_log_412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_413_neg : (5947111 / 1000000000) ≤ -Real.log (994070537991 / 1000000000000) ∧
    -Real.log (994070537991 / 1000000000000) ≤ (743389 / 125000000) := by
  have h := checkLog_sound (w := (5929462009 / 1994070537991)) (n := 12)
    (lo := (5947111 / 1000000000)) (hi := (743389 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994070537991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994070537991) = 1/(994070537991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_413 : Bounds (-743389 / 125000000) (-5947111 / 1000000000) (Real.log (994070537991 / 1000000000000)) := by
  have h := reflection_log_413_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_414_neg : (1478887 / 250000000) ≤ -Real.log (994101913599 / 1000000000000) ∧
    -Real.log (994101913599 / 1000000000000) ≤ (5915549 / 1000000000) := by
  have h := checkLog_sound (w := (5898086401 / 1994101913599)) (n := 12)
    (lo := (1478887 / 250000000)) (hi := (5915549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994101913599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994101913599) = 1/(994101913599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_414 : Bounds (-5915549 / 1000000000) (-1478887 / 250000000) (Real.log (994101913599 / 1000000000000)) := by
  have h := reflection_log_414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_415_neg : (153901051 / 1000000000) ≤ -Real.log (7812500000 / 9112308357) ∧
    -Real.log (7812500000 / 9112308357) ≤ (38475263 / 250000000) := by
  have h := checkLog_sound (w := (1299808357 / 16924808357)) (n := 12)
    (lo := (153901051 / 1000000000)) (hi := (38475263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9112308357 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9112308357 / 7812500000) = 1/(7812500000 / 9112308357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_415 : Bounds (153901051 / 1000000000) (38475263 / 250000000) (Real.log (9112308357 / 7812500000)) := by
  have h := reflection_log_415_neg
  have he : Real.log (9112308357 / 7812500000) = -Real.log (7812500000 / 9112308357) := by
    rw [show ((9112308357 / 7812500000) : ℝ) = ((7812500000 / 9112308357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_416_neg : (77155739 / 500000000) ≤ -Real.log (500000000000 / 583427140067) ∧
    -Real.log (500000000000 / 583427140067) ≤ (154311479 / 1000000000) := by
  have h := checkLog_sound (w := (83427140067 / 1083427140067)) (n := 12)
    (lo := (77155739 / 500000000)) (hi := (154311479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583427140067 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583427140067 / 500000000000) = 1/(500000000000 / 583427140067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_416 : Bounds (77155739 / 500000000) (154311479 / 1000000000) (Real.log (583427140067 / 500000000000)) := by
  have h := reflection_log_416_neg
  have he : Real.log (583427140067 / 500000000000) = -Real.log (500000000000 / 583427140067) := by
    rw [show ((583427140067 / 500000000000) : ℝ) = ((500000000000 / 583427140067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_417_neg : (154313311 / 500000000) ≤ -Real.log (500000000000 / 680776951233) ∧
    -Real.log (500000000000 / 680776951233) ≤ (308626623 / 1000000000) := by
  have h := checkLog_sound (w := (180776951233 / 1180776951233)) (n := 12)
    (lo := (154313311 / 500000000)) (hi := (308626623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680776951233 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680776951233 / 500000000000) = 1/(500000000000 / 680776951233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_417 : Bounds (154313311 / 500000000) (308626623 / 1000000000) (Real.log (680776951233 / 500000000000)) := by
  have h := reflection_log_417_neg
  have he : Real.log (680776951233 / 500000000000) = -Real.log (500000000000 / 680776951233) := by
    rw [show ((680776951233 / 500000000000) : ℝ) = ((500000000000 / 680776951233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_418_neg : (154415713 / 500000000) ≤ -Real.log (6250000000 / 8511454889) ∧
    -Real.log (6250000000 / 8511454889) ≤ (308831427 / 1000000000) := by
  have h := checkLog_sound (w := (2261454889 / 14761454889)) (n := 12)
    (lo := (154415713 / 500000000)) (hi := (308831427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8511454889 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8511454889 / 6250000000) = 1/(6250000000 / 8511454889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_418 : Bounds (154415713 / 500000000) (308831427 / 1000000000) (Real.log (8511454889 / 6250000000)) := by
  have h := reflection_log_418_neg
  have he : Real.log (8511454889 / 6250000000) = -Real.log (6250000000 / 8511454889) := by
    rw [show ((8511454889 / 6250000000) : ℝ) = ((6250000000 / 8511454889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_419_neg : (71313699 / 500000000) ≤ -Real.log (10000 / 11533) ∧
    -Real.log (10000 / 11533) ≤ (142627399 / 1000000000) := by
  have h := checkLog_sound (w := (1533 / 21533)) (n := 12)
    (lo := (71313699 / 500000000)) (hi := (142627399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11533 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11533 / 10000) = 1/(10000 / 11533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_419 : Bounds (71313699 / 500000000) (142627399 / 1000000000) (Real.log (11533 / 10000)) := by
  have h := reflection_log_419_neg
  have he : Real.log (11533 / 10000) = -Real.log (10000 / 11533) := by
    rw [show ((11533 / 10000) : ℝ) = ((10000 / 11533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_420_neg : (83204419 / 500000000) ≤ -Real.log (8467 / 10000) ∧
    -Real.log (8467 / 10000) ≤ (166408839 / 1000000000) := by
  have h := checkLog_sound (w := (1533 / 18467)) (n := 12)
    (lo := (83204419 / 500000000)) (hi := (166408839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8467) = 1/(8467 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_420 : Bounds (-166408839 / 1000000000) (-83204419 / 500000000) (Real.log (8467 / 10000)) := by
  have h := reflection_log_420_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_421_neg : (19161 / 125000000) ≤ -Real.log (10000000 / 10001533) ∧
    -Real.log (10000000 / 10001533) ≤ (153289 / 1000000000) := by
  have h := checkLog_sound (w := (1533 / 20001533)) (n := 12)
    (lo := (19161 / 125000000)) (hi := (153289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001533 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001533 / 10000000) = 1/(10000000 / 10001533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_421 : Bounds (19161 / 125000000) (153289 / 1000000000) (Real.log (10001533 / 10000000)) := by
  have h := reflection_log_421_neg
  have he : Real.log (10001533 / 10000000) = -Real.log (10000000 / 10001533) := by
    rw [show ((10001533 / 10000000) : ℝ) = ((10000000 / 10001533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_422_neg : (153311 / 1000000000) ≤ -Real.log (9998467 / 10000000) ∧
    -Real.log (9998467 / 10000000) ≤ (4791 / 31250000) := by
  have h := checkLog_sound (w := (1533 / 19998467)) (n := 12)
    (lo := (153311 / 1000000000)) (hi := (4791 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998467) = 1/(9998467 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_422 : Bounds (-4791 / 31250000) (-153311 / 1000000000) (Real.log (9998467 / 10000000)) := by
  have h := reflection_log_422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_423_neg : (4627507 / 62500000) ≤ -Real.log (20000 / 21537) ∧
    -Real.log (20000 / 21537) ≤ (74040113 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 41537)) (n := 12)
    (lo := (4627507 / 62500000)) (hi := (74040113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21537 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21537 / 20000) = 1/(20000 / 21537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_423 : Bounds (4627507 / 62500000) (74040113 / 1000000000) (Real.log (21537 / 20000)) := by
  have h := reflection_log_423_neg
  have he : Real.log (21537 / 20000) = -Real.log (20000 / 21537) := by
    rw [show ((21537 / 20000) : ℝ) = ((20000 / 21537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_424_neg : (9995443 / 125000000) ≤ -Real.log (18463 / 20000) ∧
    -Real.log (18463 / 20000) ≤ (15992709 / 200000000) := by
  have h := checkLog_sound (w := (1537 / 38463)) (n := 12)
    (lo := (9995443 / 125000000)) (hi := (15992709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18463) = 1/(18463 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_424 : Bounds (-15992709 / 200000000) (-9995443 / 125000000) (Real.log (18463 / 20000)) := by
  have h := reflection_log_424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_425_neg : (2319673 / 31250000) ≤ -Real.log (500000 / 538527) ∧
    -Real.log (500000 / 538527) ≤ (74229537 / 1000000000) := by
  have h := checkLog_sound (w := (38527 / 1038527)) (n := 12)
    (lo := (2319673 / 31250000)) (hi := (74229537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538527 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538527 / 500000) = 1/(500000 / 538527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_425 : Bounds (2319673 / 31250000) (74229537 / 1000000000) (Real.log (538527 / 500000)) := by
  have h := reflection_log_425_neg
  have he : Real.log (538527 / 500000) = -Real.log (500000 / 538527) := by
    rw [show ((538527 / 500000) : ℝ) = ((500000 / 538527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_426_neg : (80184551 / 1000000000) ≤ -Real.log (461473 / 500000) ∧
    -Real.log (461473 / 500000) ≤ (10023069 / 125000000) := by
  have h := checkLog_sound (w := (38527 / 961473)) (n := 12)
    (lo := (80184551 / 1000000000)) (hi := (10023069 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461473) = 1/(461473 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_426 : Bounds (-10023069 / 125000000) (-80184551 / 1000000000) (Real.log (461473 / 500000)) := by
  have h := reflection_log_426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_427_neg : (2977507 / 500000000) ≤ -Real.log (248515670271 / 250000000000) ∧
    -Real.log (248515670271 / 250000000000) ≤ (1191003 / 200000000) := by
  have h := checkLog_sound (w := (1484329729 / 498515670271)) (n := 12)
    (lo := (2977507 / 500000000)) (hi := (1191003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248515670271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248515670271) = 1/(248515670271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_427 : Bounds (-1191003 / 200000000) (-2977507 / 500000000) (Real.log (248515670271 / 250000000000)) := by
  have h := reflection_log_427_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_428_neg : (5923431 / 1000000000) ≤ -Real.log (397637631 / 400000000) ∧
    -Real.log (397637631 / 400000000) ≤ (740429 / 125000000) := by
  have h := checkLog_sound (w := (2362369 / 797637631)) (n := 12)
    (lo := (5923431 / 1000000000)) (hi := (740429 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 397637631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 397637631) = 1/(397637631 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_428 : Bounds (-740429 / 125000000) (-5923431 / 1000000000) (Real.log (397637631 / 400000000)) := by
  have h := reflection_log_428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_429_neg : (19250457 / 125000000) ≤ -Real.log (500000000000 / 583247576233) ∧
    -Real.log (500000000000 / 583247576233) ≤ (154003657 / 1000000000) := by
  have h := checkLog_sound (w := (83247576233 / 1083247576233)) (n := 12)
    (lo := (19250457 / 125000000)) (hi := (154003657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583247576233 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583247576233 / 500000000000) = 1/(500000000000 / 583247576233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_429 : Bounds (19250457 / 125000000) (154003657 / 1000000000) (Real.log (583247576233 / 500000000000)) := by
  have h := reflection_log_429_neg
  have he : Real.log (583247576233 / 500000000000) = -Real.log (500000000000 / 583247576233) := by
    rw [show ((583247576233 / 500000000000) : ℝ) = ((500000000000 / 583247576233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_430_neg : (154414087 / 1000000000) ≤ -Real.log (125000000000 / 145871751977) ∧
    -Real.log (125000000000 / 145871751977) ≤ (19301761 / 125000000) := by
  have h := checkLog_sound (w := (20871751977 / 270871751977)) (n := 12)
    (lo := (154414087 / 1000000000)) (hi := (19301761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145871751977 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145871751977 / 125000000000) = 1/(125000000000 / 145871751977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_430 : Bounds (154414087 / 1000000000) (19301761 / 125000000) (Real.log (145871751977 / 125000000000)) := by
  have h := reflection_log_430_neg
  have he : Real.log (145871751977 / 125000000000) = -Real.log (125000000000 / 145871751977) := by
    rw [show ((145871751977 / 125000000000) : ℝ) = ((125000000000 / 145871751977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_431_neg : (154415713 / 500000000) ≤ -Real.log (500000000000 / 680916391119) ∧
    -Real.log (500000000000 / 680916391119) ≤ (308831427 / 1000000000) := by
  have h := checkLog_sound (w := (180916391119 / 1180916391119)) (n := 12)
    (lo := (154415713 / 500000000)) (hi := (308831427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680916391119 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680916391119 / 500000000000) = 1/(500000000000 / 680916391119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_431 : Bounds (154415713 / 500000000) (308831427 / 1000000000) (Real.log (680916391119 / 500000000000)) := by
  have h := reflection_log_431_neg
  have he : Real.log (680916391119 / 500000000000) = -Real.log (500000000000 / 680916391119) := by
    rw [show ((680916391119 / 500000000000) : ℝ) = ((500000000000 / 680916391119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_432_neg : (77259059 / 250000000) ≤ -Real.log (500000000000 / 681055863943) ∧
    -Real.log (500000000000 / 681055863943) ≤ (309036237 / 1000000000) := by
  have h := checkLog_sound (w := (181055863943 / 1181055863943)) (n := 12)
    (lo := (77259059 / 250000000)) (hi := (309036237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681055863943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681055863943 / 500000000000) = 1/(500000000000 / 681055863943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_432 : Bounds (77259059 / 250000000) (309036237 / 1000000000) (Real.log (681055863943 / 500000000000)) := by
  have h := reflection_log_432_neg
  have he : Real.log (681055863943 / 500000000000) = -Real.log (500000000000 / 681055863943) := by
    rw [show ((681055863943 / 500000000000) : ℝ) = ((500000000000 / 681055863943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_433_neg : (71357051 / 500000000) ≤ -Real.log (5000 / 5767) ∧
    -Real.log (5000 / 5767) ≤ (142714103 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 10767)) (n := 12)
    (lo := (71357051 / 500000000)) (hi := (142714103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5767 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5767 / 5000) = 1/(5000 / 5767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_433 : Bounds (71357051 / 500000000) (142714103 / 1000000000) (Real.log (5767 / 5000)) := by
  have h := reflection_log_433_neg
  have he : Real.log (5767 / 5000) = -Real.log (5000 / 5767) := by
    rw [show ((5767 / 5000) : ℝ) = ((5000 / 5767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_434_neg : (3330539 / 20000000) ≤ -Real.log (4233 / 5000) ∧
    -Real.log (4233 / 5000) ≤ (166526951 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 9233)) (n := 12)
    (lo := (3330539 / 20000000)) (hi := (166526951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4233) = 1/(4233 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_434 : Bounds (-166526951 / 1000000000) (-3330539 / 20000000) (Real.log (4233 / 5000)) := by
  have h := reflection_log_434_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_435_neg : (38347 / 250000000) ≤ -Real.log (5000000 / 5000767) ∧
    -Real.log (5000000 / 5000767) ≤ (153389 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 10000767)) (n := 12)
    (lo := (38347 / 250000000)) (hi := (153389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000767 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000767 / 5000000) = 1/(5000000 / 5000767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_435 : Bounds (38347 / 250000000) (153389 / 1000000000) (Real.log (5000767 / 5000000)) := by
  have h := reflection_log_435_neg
  have he : Real.log (5000767 / 5000000) = -Real.log (5000000 / 5000767) := by
    rw [show ((5000767 / 5000000) : ℝ) = ((5000000 / 5000767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_436_neg : (153411 / 1000000000) ≤ -Real.log (4999233 / 5000000) ∧
    -Real.log (4999233 / 5000000) ≤ (38353 / 250000000) := by
  have h := checkLog_sound (w := (767 / 9999233)) (n := 12)
    (lo := (153411 / 1000000000)) (hi := (38353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999233) = 1/(4999233 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_436 : Bounds (-38353 / 250000000) (-153411 / 1000000000) (Real.log (4999233 / 5000000)) := by
  have h := reflection_log_436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_437_neg : (74086543 / 1000000000) ≤ -Real.log (10000 / 10769) ∧
    -Real.log (10000 / 10769) ≤ (4630409 / 62500000) := by
  have h := checkLog_sound (w := (769 / 20769)) (n := 12)
    (lo := (74086543 / 1000000000)) (hi := (4630409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10769 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10769 / 10000) = 1/(10000 / 10769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_437 : Bounds (74086543 / 1000000000) (4630409 / 62500000) (Real.log (10769 / 10000)) := by
  have h := reflection_log_437_neg
  have he : Real.log (10769 / 10000) = -Real.log (10000 / 10769) := by
    rw [show ((10769 / 10000) : ℝ) = ((10000 / 10769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_438_neg : (80017707 / 1000000000) ≤ -Real.log (9231 / 10000) ∧
    -Real.log (9231 / 10000) ≤ (20004427 / 250000000) := by
  have h := checkLog_sound (w := (769 / 19231)) (n := 12)
    (lo := (80017707 / 1000000000)) (hi := (20004427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 9231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 9231) = 1/(9231 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_438 : Bounds (-20004427 / 250000000) (-80017707 / 1000000000) (Real.log (9231 / 10000)) := by
  have h := reflection_log_438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_439_neg : (37138443 / 500000000) ≤ -Real.log (200000 / 215421) ∧
    -Real.log (200000 / 215421) ≤ (74276887 / 1000000000) := by
  have h := checkLog_sound (w := (15421 / 415421)) (n := 12)
    (lo := (37138443 / 500000000)) (hi := (74276887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215421 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215421 / 200000) = 1/(200000 / 215421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_439 : Bounds (37138443 / 500000000) (74276887 / 1000000000) (Real.log (215421 / 200000)) := by
  have h := reflection_log_439_neg
  have he : Real.log (215421 / 200000) = -Real.log (200000 / 215421) := by
    rw [show ((215421 / 200000) : ℝ) = ((200000 / 215421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_440_neg : (8023981 / 100000000) ≤ -Real.log (184579 / 200000) ∧
    -Real.log (184579 / 200000) ≤ (80239811 / 1000000000) := by
  have h := checkLog_sound (w := (15421 / 384579)) (n := 12)
    (lo := (8023981 / 100000000)) (hi := (80239811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184579) = 1/(184579 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_440 : Bounds (-80239811 / 1000000000) (-8023981 / 100000000) (Real.log (184579 / 200000)) := by
  have h := reflection_log_440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_441_neg : (5962923 / 1000000000) ≤ -Real.log (39762192759 / 40000000000) ∧
    -Real.log (39762192759 / 40000000000) ≤ (1490731 / 250000000) := by
  have h := checkLog_sound (w := (237807241 / 79762192759)) (n := 12)
    (lo := (5962923 / 1000000000)) (hi := (1490731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39762192759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39762192759) = 1/(39762192759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_441 : Bounds (-1490731 / 250000000) (-5962923 / 1000000000) (Real.log (39762192759 / 40000000000)) := by
  have h := reflection_log_441_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_442_neg : (1482791 / 250000000) ≤ -Real.log (99408639 / 100000000) ∧
    -Real.log (99408639 / 100000000) ≤ (1186233 / 200000000) := by
  have h := checkLog_sound (w := (591361 / 199408639)) (n := 12)
    (lo := (1482791 / 250000000)) (hi := (1186233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 99408639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 99408639) = 1/(99408639 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_442 : Bounds (-1186233 / 200000000) (-1482791 / 250000000) (Real.log (99408639 / 100000000)) := by
  have h := reflection_log_442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_443_neg : (154104251 / 1000000000) ≤ -Real.log (500000000000 / 583306250677) ∧
    -Real.log (500000000000 / 583306250677) ≤ (38526063 / 250000000) := by
  have h := checkLog_sound (w := (83306250677 / 1083306250677)) (n := 12)
    (lo := (154104251 / 1000000000)) (hi := (38526063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583306250677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583306250677 / 500000000000) = 1/(500000000000 / 583306250677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_443 : Bounds (154104251 / 1000000000) (38526063 / 250000000) (Real.log (583306250677 / 500000000000)) := by
  have h := reflection_log_443_neg
  have he : Real.log (583306250677 / 500000000000) = -Real.log (500000000000 / 583306250677) := by
    rw [show ((583306250677 / 500000000000) : ℝ) = ((500000000000 / 583306250677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_444_neg : (19314587 / 125000000) ≤ -Real.log (100000000000 / 116709376473) ∧
    -Real.log (100000000000 / 116709376473) ≤ (154516697 / 1000000000) := by
  have h := checkLog_sound (w := (16709376473 / 216709376473)) (n := 12)
    (lo := (19314587 / 125000000)) (hi := (154516697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116709376473 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116709376473 / 100000000000) = 1/(100000000000 / 116709376473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_444 : Bounds (19314587 / 125000000) (154516697 / 1000000000) (Real.log (116709376473 / 100000000000)) := by
  have h := reflection_log_444_neg
  have he : Real.log (116709376473 / 100000000000) = -Real.log (100000000000 / 116709376473) := by
    rw [show ((116709376473 / 100000000000) : ℝ) = ((100000000000 / 116709376473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_445_neg : (77259059 / 250000000) ≤ -Real.log (250000000000 / 340527931971) ∧
    -Real.log (250000000000 / 340527931971) ≤ (309036237 / 1000000000) := by
  have h := checkLog_sound (w := (90527931971 / 590527931971)) (n := 12)
    (lo := (77259059 / 250000000)) (hi := (309036237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340527931971 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340527931971 / 250000000000) = 1/(250000000000 / 340527931971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_445 : Bounds (77259059 / 250000000) (309036237 / 1000000000) (Real.log (340527931971 / 250000000000)) := by
  have h := reflection_log_445_neg
  have he : Real.log (340527931971 / 250000000000) = -Real.log (250000000000 / 340527931971) := by
    rw [show ((340527931971 / 250000000000) : ℝ) = ((250000000000 / 340527931971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_446_neg : (309241053 / 1000000000) ≤ -Real.log (100000000000 / 136239073943) ∧
    -Real.log (100000000000 / 136239073943) ≤ (154620527 / 500000000) := by
  have h := checkLog_sound (w := (36239073943 / 236239073943)) (n := 12)
    (lo := (309241053 / 1000000000)) (hi := (154620527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136239073943 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136239073943 / 100000000000) = 1/(100000000000 / 136239073943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_446 : Bounds (309241053 / 1000000000) (154620527 / 500000000) (Real.log (136239073943 / 100000000000)) := by
  have h := reflection_log_446_neg
  have he : Real.log (136239073943 / 100000000000) = -Real.log (100000000000 / 136239073943) := by
    rw [show ((136239073943 / 100000000000) : ℝ) = ((100000000000 / 136239073943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_447_neg : (71400399 / 500000000) ≤ -Real.log (2000 / 2307) ∧
    -Real.log (2000 / 2307) ≤ (142800799 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 4307)) (n := 12)
    (lo := (71400399 / 500000000)) (hi := (142800799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2307 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2307 / 2000) = 1/(2000 / 2307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_447 : Bounds (71400399 / 500000000) (142800799 / 1000000000) (Real.log (2307 / 2000)) := by
  have h := reflection_log_447_neg
  have he : Real.log (2307 / 2000) = -Real.log (2000 / 2307) := by
    rw [show ((2307 / 2000) : ℝ) = ((2000 / 2307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0007 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_448_neg : (166645077 / 1000000000) ≤ -Real.log (1693 / 2000) ∧
    -Real.log (1693 / 2000) ≤ (83322539 / 500000000) := by
  have h := checkLog_sound (w := (307 / 3693)) (n := 12)
    (lo := (166645077 / 1000000000)) (hi := (83322539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1693) = 1/(1693 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_448 : Bounds (-83322539 / 500000000) (-166645077 / 1000000000) (Real.log (1693 / 2000)) := by
  have h := reflection_log_448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_449_neg : (9593 / 62500000) ≤ -Real.log (2000000 / 2000307) ∧
    -Real.log (2000000 / 2000307) ≤ (153489 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 4000307)) (n := 12)
    (lo := (9593 / 62500000)) (hi := (153489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000307 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000307 / 2000000) = 1/(2000000 / 2000307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_449 : Bounds (9593 / 62500000) (153489 / 1000000000) (Real.log (2000307 / 2000000)) := by
  have h := reflection_log_449_neg
  have he : Real.log (2000307 / 2000000) = -Real.log (2000000 / 2000307) := by
    rw [show ((2000307 / 2000000) : ℝ) = ((2000000 / 2000307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_450_neg : (153511 / 1000000000) ≤ -Real.log (1999693 / 2000000) ∧
    -Real.log (1999693 / 2000000) ≤ (19189 / 125000000) := by
  have h := checkLog_sound (w := (307 / 3999693)) (n := 12)
    (lo := (153511 / 1000000000)) (hi := (19189 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999693) = 1/(1999693 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_450 : Bounds (-19189 / 125000000) (-153511 / 1000000000) (Real.log (1999693 / 2000000)) := by
  have h := reflection_log_450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_451_neg : (741339 / 10000000) ≤ -Real.log (1000000 / 1076951) ∧
    -Real.log (1000000 / 1076951) ≤ (74133901 / 1000000000) := by
  have h := checkLog_sound (w := (76951 / 2076951)) (n := 12)
    (lo := (741339 / 10000000)) (hi := (74133901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076951 / 1000000) = 1/(1000000 / 1076951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_451 : Bounds (741339 / 10000000) (74133901 / 1000000000) (Real.log (1076951 / 1000000)) := by
  have h := reflection_log_451_neg
  have he : Real.log (1076951 / 1000000) = -Real.log (1000000 / 1076951) := by
    rw [show ((1076951 / 1000000) : ℝ) = ((1000000 / 1076951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_452_neg : (40036479 / 500000000) ≤ -Real.log (923049 / 1000000) ∧
    -Real.log (923049 / 1000000) ≤ (80072959 / 1000000000) := by
  have h := checkLog_sound (w := (76951 / 1923049)) (n := 12)
    (lo := (40036479 / 500000000)) (hi := (80072959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923049) = 1/(923049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_452 : Bounds (-80072959 / 1000000000) (-40036479 / 500000000) (Real.log (923049 / 1000000)) := by
  have h := reflection_log_452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_453_neg : (37161653 / 500000000) ≤ -Real.log (200000 / 215431) ∧
    -Real.log (200000 / 215431) ≤ (74323307 / 1000000000) := by
  have h := checkLog_sound (w := (15431 / 415431)) (n := 12)
    (lo := (37161653 / 500000000)) (hi := (74323307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215431 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215431 / 200000) = 1/(200000 / 215431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_453 : Bounds (37161653 / 500000000) (74323307 / 1000000000) (Real.log (215431 / 200000)) := by
  have h := reflection_log_453_neg
  have he : Real.log (215431 / 200000) = -Real.log (200000 / 215431) := by
    rw [show ((215431 / 200000) : ℝ) = ((200000 / 215431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_454_neg : (80293989 / 1000000000) ≤ -Real.log (184569 / 200000) ∧
    -Real.log (184569 / 200000) ≤ (8029399 / 100000000) := by
  have h := checkLog_sound (w := (15431 / 384569)) (n := 12)
    (lo := (80293989 / 1000000000)) (hi := (8029399 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184569) = 1/(184569 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_454 : Bounds (-8029399 / 100000000) (-80293989 / 1000000000) (Real.log (184569 / 200000)) := by
  have h := reflection_log_454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_455_neg : (5970683 / 1000000000) ≤ -Real.log (39761884239 / 40000000000) ∧
    -Real.log (39761884239 / 40000000000) ≤ (1492671 / 250000000) := by
  have h := checkLog_sound (w := (238115761 / 79761884239)) (n := 12)
    (lo := (5970683 / 1000000000)) (hi := (1492671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39761884239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39761884239) = 1/(39761884239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_455 : Bounds (-1492671 / 250000000) (-5970683 / 1000000000) (Real.log (39761884239 / 40000000000)) := by
  have h := reflection_log_455_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_456_neg : (5939057 / 1000000000) ≤ -Real.log (994078543599 / 1000000000000) ∧
    -Real.log (994078543599 / 1000000000000) ≤ (2969529 / 500000000) := by
  have h := checkLog_sound (w := (5921456401 / 1994078543599)) (n := 12)
    (lo := (5939057 / 1000000000)) (hi := (2969529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994078543599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994078543599) = 1/(994078543599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_456 : Bounds (-2969529 / 500000000) (-5939057 / 1000000000) (Real.log (994078543599 / 1000000000000)) := by
  have h := reflection_log_456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_457_neg : (77103429 / 500000000) ≤ -Real.log (250000000000 / 291683052579) ∧
    -Real.log (250000000000 / 291683052579) ≤ (154206859 / 1000000000) := by
  have h := checkLog_sound (w := (41683052579 / 541683052579)) (n := 12)
    (lo := (77103429 / 500000000)) (hi := (154206859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291683052579 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291683052579 / 250000000000) = 1/(250000000000 / 291683052579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_457 : Bounds (77103429 / 500000000) (154206859 / 1000000000) (Real.log (291683052579 / 250000000000)) := by
  have h := reflection_log_457_neg
  have he : Real.log (291683052579 / 250000000000) = -Real.log (250000000000 / 291683052579) := by
    rw [show ((291683052579 / 250000000000) : ℝ) = ((250000000000 / 291683052579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_458_neg : (30923459 / 200000000) ≤ -Real.log (250000000000 / 291802794619) ∧
    -Real.log (250000000000 / 291802794619) ≤ (9663581 / 62500000) := by
  have h := checkLog_sound (w := (41802794619 / 541802794619)) (n := 12)
    (lo := (30923459 / 200000000)) (hi := (9663581 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291802794619 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291802794619 / 250000000000) = 1/(250000000000 / 291802794619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_458 : Bounds (30923459 / 200000000) (9663581 / 62500000) (Real.log (291802794619 / 250000000000)) := by
  have h := reflection_log_458_neg
  have he : Real.log (291802794619 / 250000000000) = -Real.log (250000000000 / 291802794619) := by
    rw [show ((291802794619 / 250000000000) : ℝ) = ((250000000000 / 291802794619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_459_neg : (309241053 / 1000000000) ≤ -Real.log (250000000000 / 340597684857) ∧
    -Real.log (250000000000 / 340597684857) ≤ (154620527 / 500000000) := by
  have h := checkLog_sound (w := (90597684857 / 590597684857)) (n := 12)
    (lo := (309241053 / 1000000000)) (hi := (154620527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340597684857 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340597684857 / 250000000000) = 1/(250000000000 / 340597684857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_459 : Bounds (309241053 / 1000000000) (154620527 / 500000000) (Real.log (340597684857 / 250000000000)) := by
  have h := reflection_log_459_neg
  have he : Real.log (340597684857 / 250000000000) = -Real.log (250000000000 / 340597684857) := by
    rw [show ((340597684857 / 250000000000) : ℝ) = ((250000000000 / 340597684857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_460_neg : (77361469 / 250000000) ≤ -Real.log (500000000000 / 681334908447) ∧
    -Real.log (500000000000 / 681334908447) ≤ (309445877 / 1000000000) := by
  have h := checkLog_sound (w := (181334908447 / 1181334908447)) (n := 12)
    (lo := (77361469 / 250000000)) (hi := (309445877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681334908447 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681334908447 / 500000000000) = 1/(500000000000 / 681334908447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_460 : Bounds (77361469 / 250000000) (309445877 / 1000000000) (Real.log (681334908447 / 500000000000)) := by
  have h := reflection_log_460_neg
  have he : Real.log (681334908447 / 500000000000) = -Real.log (500000000000 / 681334908447) := by
    rw [show ((681334908447 / 500000000000) : ℝ) = ((500000000000 / 681334908447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_461_neg : (142887487 / 1000000000) ≤ -Real.log (625 / 721) ∧
    -Real.log (625 / 721) ≤ (2232617 / 15625000) := by
  have h := checkLog_sound (w := (48 / 673)) (n := 12)
    (lo := (142887487 / 1000000000)) (hi := (2232617 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721 / 625) = 1/(625 / 721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_461 : Bounds (142887487 / 1000000000) (2232617 / 15625000) (Real.log (721 / 625)) := by
  have h := reflection_log_461_neg
  have he : Real.log (721 / 625) = -Real.log (625 / 721) := by
    rw [show ((721 / 625) : ℝ) = ((625 / 721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_462_neg : (166763217 / 1000000000) ≤ -Real.log (529 / 625) ∧
    -Real.log (529 / 625) ≤ (83381609 / 500000000) := by
  have h := checkLog_sound (w := (48 / 577)) (n := 12)
    (lo := (166763217 / 1000000000)) (hi := (83381609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 529) = 1/(529 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_462 : Bounds (-83381609 / 500000000) (-166763217 / 1000000000) (Real.log (529 / 625)) := by
  have h := reflection_log_462_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_463_neg : (38397 / 250000000) ≤ -Real.log (78125 / 78137) ∧
    -Real.log (78125 / 78137) ≤ (153589 / 1000000000) := by
  have h := checkLog_sound (w := (6 / 78131)) (n := 12)
    (lo := (38397 / 250000000)) (hi := (153589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78137 / 78125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78137 / 78125) = 1/(78125 / 78137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_463 : Bounds (38397 / 250000000) (153589 / 1000000000) (Real.log (78137 / 78125)) := by
  have h := reflection_log_463_neg
  have he : Real.log (78137 / 78125) = -Real.log (78125 / 78137) := by
    rw [show ((78137 / 78125) : ℝ) = ((78125 / 78137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_464_neg : (153611 / 1000000000) ≤ -Real.log (78113 / 78125) ∧
    -Real.log (78113 / 78125) ≤ (38403 / 250000000) := by
  have h := checkLog_sound (w := (6 / 78119)) (n := 12)
    (lo := (153611 / 1000000000)) (hi := (38403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78125 / 78113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78125 / 78113) = 1/(78113 / 78125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_464 : Bounds (-38403 / 250000000) (-153611 / 1000000000) (Real.log (78113 / 78125)) := by
  have h := reflection_log_464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_465_neg : (37090163 / 500000000) ≤ -Real.log (1000000 / 1077001) ∧
    -Real.log (1000000 / 1077001) ≤ (74180327 / 1000000000) := by
  have h := checkLog_sound (w := (77001 / 2077001)) (n := 12)
    (lo := (37090163 / 500000000)) (hi := (74180327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077001 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077001 / 1000000) = 1/(1000000 / 1077001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_465 : Bounds (37090163 / 500000000) (74180327 / 1000000000) (Real.log (1077001 / 1000000)) := by
  have h := reflection_log_465_neg
  have he : Real.log (1077001 / 1000000) = -Real.log (1000000 / 1077001) := by
    rw [show ((1077001 / 1000000) : ℝ) = ((1000000 / 1077001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_466_neg : (80127127 / 1000000000) ≤ -Real.log (922999 / 1000000) ∧
    -Real.log (922999 / 1000000) ≤ (10015891 / 125000000) := by
  have h := checkLog_sound (w := (77001 / 1922999)) (n := 12)
    (lo := (80127127 / 1000000000)) (hi := (10015891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922999) = 1/(922999 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_466 : Bounds (-10015891 / 125000000) (-80127127 / 1000000000) (Real.log (922999 / 1000000)) := by
  have h := reflection_log_466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_467_neg : (74370651 / 1000000000) ≤ -Real.log (500000 / 538603) ∧
    -Real.log (500000 / 538603) ≤ (18592663 / 250000000) := by
  have h := checkLog_sound (w := (38603 / 1038603)) (n := 12)
    (lo := (74370651 / 1000000000)) (hi := (18592663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538603 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538603 / 500000) = 1/(500000 / 538603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_467 : Bounds (74370651 / 1000000000) (18592663 / 250000000) (Real.log (538603 / 500000)) := by
  have h := reflection_log_467_neg
  have he : Real.log (538603 / 500000) = -Real.log (500000 / 538603) := by
    rw [show ((538603 / 500000) : ℝ) = ((500000 / 538603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_468_neg : (40174627 / 500000000) ≤ -Real.log (461397 / 500000) ∧
    -Real.log (461397 / 500000) ≤ (16069851 / 200000000) := by
  have h := checkLog_sound (w := (38603 / 961397)) (n := 12)
    (lo := (40174627 / 500000000)) (hi := (16069851 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461397) = 1/(461397 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_468 : Bounds (-16069851 / 200000000) (-40174627 / 500000000) (Real.log (461397 / 500000)) := by
  have h := reflection_log_468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_469_neg : (2989301 / 500000000) ≤ -Real.log (248509808391 / 250000000000) ∧
    -Real.log (248509808391 / 250000000000) ≤ (5978603 / 1000000000) := by
  have h := checkLog_sound (w := (1490191609 / 498509808391)) (n := 12)
    (lo := (2989301 / 500000000)) (hi := (5978603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248509808391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248509808391) = 1/(248509808391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_469 : Bounds (-5978603 / 1000000000) (-2989301 / 500000000) (Real.log (248509808391 / 250000000000)) := by
  have h := reflection_log_469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_470_neg : (5946801 / 1000000000) ≤ -Real.log (994070845999 / 1000000000000) ∧
    -Real.log (994070845999 / 1000000000000) ≤ (2973401 / 500000000) := by
  have h := checkLog_sound (w := (5929154001 / 1994070845999)) (n := 12)
    (lo := (5946801 / 1000000000)) (hi := (2973401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994070845999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994070845999) = 1/(994070845999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_470 : Bounds (-2973401 / 500000000) (-5946801 / 1000000000) (Real.log (994070845999 / 1000000000000)) := by
  have h := reflection_log_470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_471_neg : (77153727 / 500000000) ≤ -Real.log (250000000000 / 291712396221) ∧
    -Real.log (250000000000 / 291712396221) ≤ (30861491 / 200000000) := by
  have h := checkLog_sound (w := (41712396221 / 541712396221)) (n := 12)
    (lo := (77153727 / 500000000)) (hi := (30861491 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291712396221 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291712396221 / 250000000000) = 1/(250000000000 / 291712396221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_471 : Bounds (77153727 / 500000000) (30861491 / 200000000) (Real.log (291712396221 / 250000000000)) := by
  have h := reflection_log_471_neg
  have he : Real.log (291712396221 / 250000000000) = -Real.log (250000000000 / 291712396221) := by
    rw [show ((291712396221 / 250000000000) : ℝ) = ((250000000000 / 291712396221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_472_neg : (77359953 / 500000000) ≤ -Real.log (250000000000 / 291832738401) ∧
    -Real.log (250000000000 / 291832738401) ≤ (154719907 / 1000000000) := by
  have h := checkLog_sound (w := (41832738401 / 541832738401)) (n := 12)
    (lo := (77359953 / 500000000)) (hi := (154719907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291832738401 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291832738401 / 250000000000) = 1/(250000000000 / 291832738401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_472 : Bounds (77359953 / 500000000) (154719907 / 1000000000) (Real.log (291832738401 / 250000000000)) := by
  have h := reflection_log_472_neg
  have he : Real.log (291832738401 / 250000000000) = -Real.log (250000000000 / 291832738401) := by
    rw [show ((291832738401 / 250000000000) : ℝ) = ((250000000000 / 291832738401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_473_neg : (77361469 / 250000000) ≤ -Real.log (250000000000 / 340667454223) ∧
    -Real.log (250000000000 / 340667454223) ≤ (309445877 / 1000000000) := by
  have h := checkLog_sound (w := (90667454223 / 590667454223)) (n := 12)
    (lo := (77361469 / 250000000)) (hi := (309445877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340667454223 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340667454223 / 250000000000) = 1/(250000000000 / 340667454223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_473 : Bounds (77361469 / 250000000) (309445877 / 1000000000) (Real.log (340667454223 / 250000000000)) := by
  have h := reflection_log_473_neg
  have he : Real.log (340667454223 / 250000000000) = -Real.log (250000000000 / 340667454223) := by
    rw [show ((340667454223 / 250000000000) : ℝ) = ((250000000000 / 340667454223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_474_neg : (61930141 / 200000000) ≤ -Real.log (62500000000 / 85184310019) ∧
    -Real.log (62500000000 / 85184310019) ≤ (154825353 / 500000000) := by
  have h := checkLog_sound (w := (22684310019 / 147684310019)) (n := 12)
    (lo := (61930141 / 200000000)) (hi := (154825353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85184310019 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85184310019 / 62500000000) = 1/(62500000000 / 85184310019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_474 : Bounds (61930141 / 200000000) (154825353 / 500000000) (Real.log (85184310019 / 62500000000)) := by
  have h := reflection_log_474_neg
  have he : Real.log (85184310019 / 62500000000) = -Real.log (62500000000 / 85184310019) := by
    rw [show ((85184310019 / 62500000000) : ℝ) = ((62500000000 / 85184310019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_475_neg : (17871771 / 125000000) ≤ -Real.log (10000 / 11537) ∧
    -Real.log (10000 / 11537) ≤ (142974169 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 21537)) (n := 12)
    (lo := (17871771 / 125000000)) (hi := (142974169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11537 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11537 / 10000) = 1/(10000 / 11537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_475 : Bounds (17871771 / 125000000) (142974169 / 1000000000) (Real.log (11537 / 10000)) := by
  have h := reflection_log_475_neg
  have he : Real.log (11537 / 10000) = -Real.log (10000 / 11537) := by
    rw [show ((11537 / 10000) : ℝ) = ((10000 / 11537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_476_neg : (41720343 / 250000000) ≤ -Real.log (8463 / 10000) ∧
    -Real.log (8463 / 10000) ≤ (166881373 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 18463)) (n := 12)
    (lo := (41720343 / 250000000)) (hi := (166881373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8463) = 1/(8463 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_476 : Bounds (-166881373 / 1000000000) (-41720343 / 250000000) (Real.log (8463 / 10000)) := by
  have h := reflection_log_476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_477_neg : (19211 / 125000000) ≤ -Real.log (10000000 / 10001537) ∧
    -Real.log (10000000 / 10001537) ≤ (153689 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 20001537)) (n := 12)
    (lo := (19211 / 125000000)) (hi := (153689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001537 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001537 / 10000000) = 1/(10000000 / 10001537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_477 : Bounds (19211 / 125000000) (153689 / 1000000000) (Real.log (10001537 / 10000000)) := by
  have h := reflection_log_477_neg
  have he : Real.log (10001537 / 10000000) = -Real.log (10000000 / 10001537) := by
    rw [show ((10001537 / 10000000) : ℝ) = ((10000000 / 10001537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_478_neg : (153711 / 1000000000) ≤ -Real.log (9998463 / 10000000) ∧
    -Real.log (9998463 / 10000000) ≤ (9607 / 62500000) := by
  have h := checkLog_sound (w := (1537 / 19998463)) (n := 12)
    (lo := (153711 / 1000000000)) (hi := (9607 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998463) = 1/(9998463 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_478 : Bounds (-9607 / 62500000) (-153711 / 1000000000) (Real.log (9998463 / 10000000)) := by
  have h := reflection_log_478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_479_neg : (74227679 / 1000000000) ≤ -Real.log (250000 / 269263) ∧
    -Real.log (250000 / 269263) ≤ (463923 / 6250000) := by
  have h := checkLog_sound (w := (19263 / 519263)) (n := 12)
    (lo := (74227679 / 1000000000)) (hi := (463923 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269263 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269263 / 250000) = 1/(250000 / 269263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_479 : Bounds (74227679 / 1000000000) (463923 / 6250000) (Real.log (269263 / 250000)) := by
  have h := reflection_log_479_neg
  have he : Real.log (269263 / 250000) = -Real.log (250000 / 269263) := by
    rw [show ((269263 / 250000) : ℝ) = ((250000 / 269263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_480_neg : (5011399 / 62500000) ≤ -Real.log (230737 / 250000) ∧
    -Real.log (230737 / 250000) ≤ (16036477 / 200000000) := by
  have h := checkLog_sound (w := (19263 / 480737)) (n := 12)
    (lo := (5011399 / 62500000)) (hi := (16036477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230737) = 1/(230737 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_480 : Bounds (-16036477 / 200000000) (-5011399 / 62500000) (Real.log (230737 / 250000)) := by
  have h := reflection_log_480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_481_neg : (14883599 / 200000000) ≤ -Real.log (1000000 / 1077257) ∧
    -Real.log (1000000 / 1077257) ≤ (18604499 / 250000000) := by
  have h := checkLog_sound (w := (77257 / 2077257)) (n := 12)
    (lo := (14883599 / 200000000)) (hi := (18604499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077257 / 1000000) = 1/(1000000 / 1077257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_481 : Bounds (14883599 / 200000000) (18604499 / 250000000) (Real.log (1077257 / 1000000)) := by
  have h := reflection_log_481_neg
  have he : Real.log (1077257 / 1000000) = -Real.log (1000000 / 1077257) := by
    rw [show ((1077257 / 1000000) : ℝ) = ((1000000 / 1077257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_482_neg : (80404523 / 1000000000) ≤ -Real.log (922743 / 1000000) ∧
    -Real.log (922743 / 1000000) ≤ (20101131 / 250000000) := by
  have h := checkLog_sound (w := (77257 / 1922743)) (n := 12)
    (lo := (80404523 / 1000000000)) (hi := (20101131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922743) = 1/(922743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_482 : Bounds (-20101131 / 250000000) (-80404523 / 1000000000) (Real.log (922743 / 1000000)) := by
  have h := reflection_log_482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_483_neg : (5986527 / 1000000000) ≤ -Real.log (994031355951 / 1000000000000) ∧
    -Real.log (994031355951 / 1000000000000) ≤ (187079 / 31250000) := by
  have h := checkLog_sound (w := (5968644049 / 1994031355951)) (n := 12)
    (lo := (5986527 / 1000000000)) (hi := (187079 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994031355951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994031355951) = 1/(994031355951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_483 : Bounds (-187079 / 31250000) (-5986527 / 1000000000) (Real.log (994031355951 / 1000000000000)) := by
  have h := reflection_log_483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_484_neg : (372169 / 62500000) ≤ -Real.log (62128936831 / 62500000000) ∧
    -Real.log (62128936831 / 62500000000) ≤ (1190941 / 200000000) := by
  have h := checkLog_sound (w := (371063169 / 124628936831)) (n := 12)
    (lo := (372169 / 62500000)) (hi := (1190941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62128936831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62128936831) = 1/(62128936831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_484 : Bounds (-1190941 / 200000000) (-372169 / 62500000) (Real.log (62128936831 / 62500000000)) := by
  have h := reflection_log_484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_485_neg : (154410063 / 1000000000) ≤ -Real.log (62500000000 / 72935582503) ∧
    -Real.log (62500000000 / 72935582503) ≤ (9650629 / 62500000) := by
  have h := checkLog_sound (w := (10435582503 / 135435582503)) (n := 12)
    (lo := (154410063 / 1000000000)) (hi := (9650629 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72935582503 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72935582503 / 62500000000) = 1/(62500000000 / 72935582503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_485 : Bounds (154410063 / 1000000000) (9650629 / 62500000) (Real.log (72935582503 / 62500000000)) := by
  have h := reflection_log_485_neg
  have he : Real.log (72935582503 / 62500000000) = -Real.log (62500000000 / 72935582503) := by
    rw [show ((72935582503 / 62500000000) : ℝ) = ((62500000000 / 72935582503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_486_neg : (77411259 / 500000000) ≤ -Real.log (500000000000 / 583725370987) ∧
    -Real.log (500000000000 / 583725370987) ≤ (154822519 / 1000000000) := by
  have h := checkLog_sound (w := (83725370987 / 1083725370987)) (n := 12)
    (lo := (77411259 / 500000000)) (hi := (154822519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583725370987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583725370987 / 500000000000) = 1/(500000000000 / 583725370987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_486 : Bounds (77411259 / 500000000) (154822519 / 1000000000) (Real.log (583725370987 / 500000000000)) := by
  have h := reflection_log_486_neg
  have he : Real.log (583725370987 / 500000000000) = -Real.log (500000000000 / 583725370987) := by
    rw [show ((583725370987 / 500000000000) : ℝ) = ((500000000000 / 583725370987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_487_neg : (61930141 / 200000000) ≤ -Real.log (500000000000 / 681474480151) ∧
    -Real.log (500000000000 / 681474480151) ≤ (154825353 / 500000000) := by
  have h := checkLog_sound (w := (181474480151 / 1181474480151)) (n := 12)
    (lo := (61930141 / 200000000)) (hi := (154825353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681474480151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681474480151 / 500000000000) = 1/(500000000000 / 681474480151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_487 : Bounds (61930141 / 200000000) (154825353 / 500000000) (Real.log (681474480151 / 500000000000)) := by
  have h := reflection_log_487_neg
  have he : Real.log (681474480151 / 500000000000) = -Real.log (500000000000 / 681474480151) := by
    rw [show ((681474480151 / 500000000000) : ℝ) = ((500000000000 / 681474480151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_488_neg : (309855541 / 1000000000) ≤ -Real.log (12500000000 / 17040352121) ∧
    -Real.log (12500000000 / 17040352121) ≤ (154927771 / 500000000) := by
  have h := checkLog_sound (w := (4540352121 / 29540352121)) (n := 12)
    (lo := (309855541 / 1000000000)) (hi := (154927771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17040352121 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17040352121 / 12500000000) = 1/(12500000000 / 17040352121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_488 : Bounds (309855541 / 1000000000) (154927771 / 500000000) (Real.log (17040352121 / 12500000000)) := by
  have h := reflection_log_488_neg
  have he : Real.log (17040352121 / 12500000000) = -Real.log (12500000000 / 17040352121) := by
    rw [show ((17040352121 / 12500000000) : ℝ) = ((12500000000 / 17040352121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_489_neg : (71530421 / 500000000) ≤ -Real.log (5000 / 5769) ∧
    -Real.log (5000 / 5769) ≤ (143060843 / 1000000000) := by
  have h := checkLog_sound (w := (769 / 10769)) (n := 12)
    (lo := (71530421 / 500000000)) (hi := (143060843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5769 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5769 / 5000) = 1/(5000 / 5769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_489 : Bounds (71530421 / 500000000) (143060843 / 1000000000) (Real.log (5769 / 5000)) := by
  have h := reflection_log_489_neg
  have he : Real.log (5769 / 5000) = -Real.log (5000 / 5769) := by
    rw [show ((5769 / 5000) : ℝ) = ((5000 / 5769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_490_neg : (8349977 / 50000000) ≤ -Real.log (4231 / 5000) ∧
    -Real.log (4231 / 5000) ≤ (166999541 / 1000000000) := by
  have h := checkLog_sound (w := (769 / 9231)) (n := 12)
    (lo := (8349977 / 50000000)) (hi := (166999541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4231) = 1/(4231 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_490 : Bounds (-166999541 / 1000000000) (-8349977 / 50000000) (Real.log (4231 / 5000)) := by
  have h := reflection_log_490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_491_neg : (38447 / 250000000) ≤ -Real.log (5000000 / 5000769) ∧
    -Real.log (5000000 / 5000769) ≤ (153789 / 1000000000) := by
  have h := checkLog_sound (w := (769 / 10000769)) (n := 12)
    (lo := (38447 / 250000000)) (hi := (153789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000769 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000769 / 5000000) = 1/(5000000 / 5000769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_491 : Bounds (38447 / 250000000) (153789 / 1000000000) (Real.log (5000769 / 5000000)) := by
  have h := reflection_log_491_neg
  have he : Real.log (5000769 / 5000000) = -Real.log (5000000 / 5000769) := by
    rw [show ((5000769 / 5000000) : ℝ) = ((5000000 / 5000769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_492_neg : (153811 / 1000000000) ≤ -Real.log (4999231 / 5000000) ∧
    -Real.log (4999231 / 5000000) ≤ (38453 / 250000000) := by
  have h := checkLog_sound (w := (769 / 9999231)) (n := 12)
    (lo := (153811 / 1000000000)) (hi := (38453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999231) = 1/(4999231 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_492 : Bounds (-38453 / 250000000) (-153811 / 1000000000) (Real.log (4999231 / 5000000)) := by
  have h := reflection_log_492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_493_neg : (74275029 / 1000000000) ≤ -Real.log (1000000 / 1077103) ∧
    -Real.log (1000000 / 1077103) ≤ (7427503 / 100000000) := by
  have h := checkLog_sound (w := (77103 / 2077103)) (n := 12)
    (lo := (74275029 / 1000000000)) (hi := (7427503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077103 / 1000000) = 1/(1000000 / 1077103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_493 : Bounds (74275029 / 1000000000) (7427503 / 100000000) (Real.log (1077103 / 1000000)) := by
  have h := reflection_log_493_neg
  have he : Real.log (1077103 / 1000000) = -Real.log (1000000 / 1077103) := by
    rw [show ((1077103 / 1000000) : ℝ) = ((1000000 / 1077103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_494_neg : (80237643 / 1000000000) ≤ -Real.log (922897 / 1000000) ∧
    -Real.log (922897 / 1000000) ≤ (20059411 / 250000000) := by
  have h := checkLog_sound (w := (77103 / 1922897)) (n := 12)
    (lo := (80237643 / 1000000000)) (hi := (20059411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922897) = 1/(922897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_494 : Bounds (-20059411 / 250000000) (-80237643 / 1000000000) (Real.log (922897 / 1000000)) := by
  have h := reflection_log_494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_495_neg : (9308051 / 125000000) ≤ -Real.log (1000000 / 1077307) ∧
    -Real.log (1000000 / 1077307) ≤ (74464409 / 1000000000) := by
  have h := checkLog_sound (w := (77307 / 2077307)) (n := 12)
    (lo := (9308051 / 125000000)) (hi := (74464409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077307 / 1000000) = 1/(1000000 / 1077307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_495 : Bounds (9308051 / 125000000) (74464409 / 1000000000) (Real.log (1077307 / 1000000)) := by
  have h := reflection_log_495_neg
  have he : Real.log (1077307 / 1000000) = -Real.log (1000000 / 1077307) := by
    rw [show ((1077307 / 1000000) : ℝ) = ((1000000 / 1077307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_496_neg : (8045871 / 100000000) ≤ -Real.log (922693 / 1000000) ∧
    -Real.log (922693 / 1000000) ≤ (80458711 / 1000000000) := by
  have h := checkLog_sound (w := (77307 / 1922693)) (n := 12)
    (lo := (8045871 / 100000000)) (hi := (80458711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922693) = 1/(922693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_496 : Bounds (-80458711 / 1000000000) (-8045871 / 100000000) (Real.log (922693 / 1000000)) := by
  have h := reflection_log_496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_497_neg : (2997151 / 500000000) ≤ -Real.log (994023627751 / 1000000000000) ∧
    -Real.log (994023627751 / 1000000000000) ≤ (5994303 / 1000000000) := by
  have h := checkLog_sound (w := (5976372249 / 1994023627751)) (n := 12)
    (lo := (2997151 / 500000000)) (hi := (5994303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994023627751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994023627751) = 1/(994023627751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_497 : Bounds (-5994303 / 1000000000) (-2997151 / 500000000) (Real.log (994023627751 / 1000000000000)) := by
  have h := reflection_log_497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_498_neg : (5962613 / 1000000000) ≤ -Real.log (994055127391 / 1000000000000) ∧
    -Real.log (994055127391 / 1000000000000) ≤ (2981307 / 500000000) := by
  have h := checkLog_sound (w := (5944872609 / 1994055127391)) (n := 12)
    (lo := (5962613 / 1000000000)) (hi := (2981307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994055127391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994055127391) = 1/(994055127391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_498 : Bounds (-2981307 / 500000000) (-5962613 / 1000000000) (Real.log (994055127391 / 1000000000000)) := by
  have h := reflection_log_498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_499_neg : (4828521 / 31250000) ≤ -Real.log (250000000000 / 291772267111) ∧
    -Real.log (250000000000 / 291772267111) ≤ (154512673 / 1000000000) := by
  have h := checkLog_sound (w := (41772267111 / 541772267111)) (n := 12)
    (lo := (4828521 / 31250000)) (hi := (154512673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291772267111 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291772267111 / 250000000000) = 1/(250000000000 / 291772267111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_499 : Bounds (4828521 / 31250000) (154512673 / 1000000000) (Real.log (291772267111 / 250000000000)) := by
  have h := reflection_log_499_neg
  have he : Real.log (291772267111 / 250000000000) = -Real.log (250000000000 / 291772267111) := by
    rw [show ((291772267111 / 250000000000) : ℝ) = ((250000000000 / 291772267111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_500_neg : (154923119 / 1000000000) ≤ -Real.log (500000000000 / 583784097203) ∧
    -Real.log (500000000000 / 583784097203) ≤ (1936539 / 12500000) := by
  have h := checkLog_sound (w := (83784097203 / 1083784097203)) (n := 12)
    (lo := (154923119 / 1000000000)) (hi := (1936539 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583784097203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583784097203 / 500000000000) = 1/(500000000000 / 583784097203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_500 : Bounds (154923119 / 1000000000) (1936539 / 12500000) (Real.log (583784097203 / 500000000000)) := by
  have h := reflection_log_500_neg
  have he : Real.log (583784097203 / 500000000000) = -Real.log (500000000000 / 583784097203) := by
    rw [show ((583784097203 / 500000000000) : ℝ) = ((500000000000 / 583784097203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_501_neg : (309855541 / 1000000000) ≤ -Real.log (500000000000 / 681614084839) ∧
    -Real.log (500000000000 / 681614084839) ≤ (154927771 / 500000000) := by
  have h := checkLog_sound (w := (181614084839 / 1181614084839)) (n := 12)
    (lo := (309855541 / 1000000000)) (hi := (154927771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681614084839 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681614084839 / 500000000000) = 1/(500000000000 / 681614084839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_501 : Bounds (309855541 / 1000000000) (154927771 / 500000000) (Real.log (681614084839 / 500000000000)) := by
  have h := reflection_log_501_neg
  have he : Real.log (681614084839 / 500000000000) = -Real.log (500000000000 / 681614084839) := by
    rw [show ((681614084839 / 500000000000) : ℝ) = ((500000000000 / 681614084839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_502_neg : (310060383 / 1000000000) ≤ -Real.log (20000000000 / 27270148901) ∧
    -Real.log (20000000000 / 27270148901) ≤ (9689387 / 31250000) := by
  have h := checkLog_sound (w := (7270148901 / 47270148901)) (n := 12)
    (lo := (310060383 / 1000000000)) (hi := (9689387 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27270148901 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27270148901 / 20000000000) = 1/(20000000000 / 27270148901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_502 : Bounds (310060383 / 1000000000) (9689387 / 31250000) (Real.log (27270148901 / 20000000000)) := by
  have h := reflection_log_502_neg
  have he : Real.log (27270148901 / 20000000000) = -Real.log (20000000000 / 27270148901) := by
    rw [show ((27270148901 / 20000000000) : ℝ) = ((20000000000 / 27270148901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_503_neg : (143147509 / 1000000000) ≤ -Real.log (10000 / 11539) ∧
    -Real.log (10000 / 11539) ≤ (14314751 / 100000000) := by
  have h := checkLog_sound (w := (1539 / 21539)) (n := 12)
    (lo := (143147509 / 1000000000)) (hi := (14314751 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11539 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11539 / 10000) = 1/(10000 / 11539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_503 : Bounds (143147509 / 1000000000) (14314751 / 100000000) (Real.log (11539 / 10000)) := by
  have h := reflection_log_503_neg
  have he : Real.log (11539 / 10000) = -Real.log (10000 / 11539) := by
    rw [show ((11539 / 10000) : ℝ) = ((10000 / 11539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_504_neg : (167117723 / 1000000000) ≤ -Real.log (8461 / 10000) ∧
    -Real.log (8461 / 10000) ≤ (41779431 / 250000000) := by
  have h := checkLog_sound (w := (1539 / 18461)) (n := 12)
    (lo := (167117723 / 1000000000)) (hi := (41779431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8461) = 1/(8461 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_504 : Bounds (-41779431 / 250000000) (-167117723 / 1000000000) (Real.log (8461 / 10000)) := by
  have h := reflection_log_504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_505_neg : (4809 / 31250000) ≤ -Real.log (10000000 / 10001539) ∧
    -Real.log (10000000 / 10001539) ≤ (153889 / 1000000000) := by
  have h := checkLog_sound (w := (1539 / 20001539)) (n := 12)
    (lo := (4809 / 31250000)) (hi := (153889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001539 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001539 / 10000000) = 1/(10000000 / 10001539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_505 : Bounds (4809 / 31250000) (153889 / 1000000000) (Real.log (10001539 / 10000000)) := by
  have h := reflection_log_505_neg
  have he : Real.log (10001539 / 10000000) = -Real.log (10000000 / 10001539) := by
    rw [show ((10001539 / 10000000) : ℝ) = ((10000000 / 10001539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_506_neg : (153911 / 1000000000) ≤ -Real.log (9998461 / 10000000) ∧
    -Real.log (9998461 / 10000000) ≤ (19239 / 125000000) := by
  have h := checkLog_sound (w := (1539 / 19998461)) (n := 12)
    (lo := (153911 / 1000000000)) (hi := (19239 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998461) = 1/(9998461 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_506 : Bounds (-19239 / 125000000) (-153911 / 1000000000) (Real.log (9998461 / 10000000)) := by
  have h := reflection_log_506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_507_neg : (74321449 / 1000000000) ≤ -Real.log (1000000 / 1077153) ∧
    -Real.log (1000000 / 1077153) ≤ (1486429 / 20000000) := by
  have h := checkLog_sound (w := (77153 / 2077153)) (n := 12)
    (lo := (74321449 / 1000000000)) (hi := (1486429 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077153 / 1000000) = 1/(1000000 / 1077153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_507 : Bounds (74321449 / 1000000000) (1486429 / 20000000) (Real.log (1077153 / 1000000)) := by
  have h := reflection_log_507_neg
  have he : Real.log (1077153 / 1000000) = -Real.log (1000000 / 1077153) := by
    rw [show ((1077153 / 1000000) : ℝ) = ((1000000 / 1077153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_508_neg : (40145911 / 500000000) ≤ -Real.log (922847 / 1000000) ∧
    -Real.log (922847 / 1000000) ≤ (80291823 / 1000000000) := by
  have h := checkLog_sound (w := (77153 / 1922847)) (n := 12)
    (lo := (40145911 / 500000000)) (hi := (80291823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922847) = 1/(922847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_508 : Bounds (-80291823 / 1000000000) (-40145911 / 500000000) (Real.log (922847 / 1000000)) := by
  have h := reflection_log_508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_509_neg : (74511747 / 1000000000) ≤ -Real.log (500000 / 538679) ∧
    -Real.log (500000 / 538679) ≤ (18627937 / 250000000) := by
  have h := checkLog_sound (w := (38679 / 1038679)) (n := 12)
    (lo := (74511747 / 1000000000)) (hi := (18627937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538679 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538679 / 500000) = 1/(500000 / 538679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_509 : Bounds (74511747 / 1000000000) (18627937 / 250000000) (Real.log (538679 / 500000)) := by
  have h := reflection_log_509_neg
  have he : Real.log (538679 / 500000) = -Real.log (500000 / 538679) := by
    rw [show ((538679 / 500000) : ℝ) = ((500000 / 538679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_510_neg : (16102797 / 200000000) ≤ -Real.log (461321 / 500000) ∧
    -Real.log (461321 / 500000) ≤ (40256993 / 500000000) := by
  have h := checkLog_sound (w := (38679 / 961321)) (n := 12)
    (lo := (16102797 / 200000000)) (hi := (40256993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461321) = 1/(461321 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_510 : Bounds (-40256993 / 500000000) (-16102797 / 200000000) (Real.log (461321 / 500000)) := by
  have h := reflection_log_510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_511_neg : (6002237 / 1000000000) ≤ -Real.log (248503934959 / 250000000000) ∧
    -Real.log (248503934959 / 250000000000) ≤ (3001119 / 500000000) := by
  have h := checkLog_sound (w := (1496065041 / 498503934959)) (n := 12)
    (lo := (6002237 / 1000000000)) (hi := (3001119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248503934959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248503934959) = 1/(248503934959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_511 : Bounds (-3001119 / 500000000) (-6002237 / 1000000000) (Real.log (248503934959 / 250000000000)) := by
  have h := reflection_log_511_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


