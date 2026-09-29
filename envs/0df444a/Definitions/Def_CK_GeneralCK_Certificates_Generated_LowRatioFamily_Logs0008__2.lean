-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0008__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0008__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T20:43:49.520237+00:00
-- url     : https://prove2.me/theorems/46f907d1-1df2-4d83-ba15-5c2d73450831
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0008 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0009)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0008 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0009)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0008 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0009)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0008 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0009) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0008 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0009).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0008 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_512_neg : (1492593 / 250000000) ≤ -Real.log (994047414591 / 1000000000000) ∧
    -Real.log (994047414591 / 1000000000000) ≤ (5970373 / 1000000000) := by
  have h := checkLog_sound (w := (5952585409 / 1994047414591)) (n := 12)
    (lo := (1492593 / 250000000)) (hi := (5970373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994047414591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994047414591) = 1/(994047414591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_512 : Bounds (-5970373 / 1000000000) (-1492593 / 250000000) (Real.log (994047414591 / 1000000000000)) := by
  have h := reflection_log_512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_513_neg : (154613271 / 1000000000) ≤ -Real.log (12500000000 / 14590081021) ∧
    -Real.log (12500000000 / 14590081021) ≤ (19326659 / 125000000) := by
  have h := checkLog_sound (w := (2090081021 / 27090081021)) (n := 12)
    (lo := (154613271 / 1000000000)) (hi := (19326659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14590081021 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14590081021 / 12500000000) = 1/(12500000000 / 14590081021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_513 : Bounds (154613271 / 1000000000) (19326659 / 125000000) (Real.log (14590081021 / 12500000000)) := by
  have h := reflection_log_513_neg
  have he : Real.log (14590081021 / 12500000000) = -Real.log (12500000000 / 14590081021) := by
    rw [show ((14590081021 / 12500000000) : ℝ) = ((12500000000 / 14590081021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_514_neg : (155025733 / 1000000000) ≤ -Real.log (500000000000 / 583844004501) ∧
    -Real.log (500000000000 / 583844004501) ≤ (77512867 / 500000000) := by
  have h := checkLog_sound (w := (83844004501 / 1083844004501)) (n := 12)
    (lo := (155025733 / 1000000000)) (hi := (77512867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583844004501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583844004501 / 500000000000) = 1/(500000000000 / 583844004501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_514 : Bounds (155025733 / 1000000000) (77512867 / 500000000) (Real.log (583844004501 / 500000000000)) := by
  have h := reflection_log_514_neg
  have he : Real.log (583844004501 / 500000000000) = -Real.log (500000000000 / 583844004501) := by
    rw [show ((583844004501 / 500000000000) : ℝ) = ((500000000000 / 583844004501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_515_neg : (310060383 / 1000000000) ≤ -Real.log (125000000000 / 170438430631) ∧
    -Real.log (125000000000 / 170438430631) ≤ (9689387 / 31250000) := by
  have h := checkLog_sound (w := (45438430631 / 295438430631)) (n := 12)
    (lo := (310060383 / 1000000000)) (hi := (9689387 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170438430631 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170438430631 / 125000000000) = 1/(125000000000 / 170438430631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_515 : Bounds (310060383 / 1000000000) (9689387 / 31250000) (Real.log (170438430631 / 125000000000)) := by
  have h := reflection_log_515_neg
  have he : Real.log (170438430631 / 125000000000) = -Real.log (125000000000 / 170438430631) := by
    rw [show ((170438430631 / 125000000000) : ℝ) = ((125000000000 / 170438430631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_516_neg : (19391577 / 62500000) ≤ -Real.log (7812500000 / 10654584269) ∧
    -Real.log (7812500000 / 10654584269) ≤ (310265233 / 1000000000) := by
  have h := checkLog_sound (w := (2842084269 / 18467084269)) (n := 12)
    (lo := (19391577 / 62500000)) (hi := (310265233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10654584269 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10654584269 / 7812500000) = 1/(7812500000 / 10654584269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_516 : Bounds (19391577 / 62500000) (310265233 / 1000000000) (Real.log (10654584269 / 7812500000)) := by
  have h := reflection_log_516_neg
  have he : Real.log (10654584269 / 7812500000) = -Real.log (7812500000 / 10654584269) := by
    rw [show ((10654584269 / 7812500000) : ℝ) = ((7812500000 / 10654584269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_517_neg : (17904271 / 125000000) ≤ -Real.log (500 / 577) ∧
    -Real.log (500 / 577) ≤ (143234169 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 1077)) (n := 12)
    (lo := (17904271 / 125000000)) (hi := (143234169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577 / 500) = 1/(500 / 577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_517 : Bounds (17904271 / 125000000) (143234169 / 1000000000) (Real.log (577 / 500)) := by
  have h := reflection_log_517_neg
  have he : Real.log (577 / 500) = -Real.log (500 / 577) := by
    rw [show ((577 / 500) : ℝ) = ((500 / 577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_518_neg : (167235919 / 1000000000) ≤ -Real.log (423 / 500) ∧
    -Real.log (423 / 500) ≤ (2090449 / 12500000) := by
  have h := checkLog_sound (w := (77 / 923)) (n := 12)
    (lo := (167235919 / 1000000000)) (hi := (2090449 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 423) = 1/(423 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_518 : Bounds (-2090449 / 12500000) (-167235919 / 1000000000) (Real.log (423 / 500)) := by
  have h := reflection_log_518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_519_neg : (38497 / 250000000) ≤ -Real.log (500000 / 500077) ∧
    -Real.log (500000 / 500077) ≤ (153989 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 1000077)) (n := 12)
    (lo := (38497 / 250000000)) (hi := (153989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500077 / 500000) = 1/(500000 / 500077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_519 : Bounds (38497 / 250000000) (153989 / 1000000000) (Real.log (500077 / 500000)) := by
  have h := reflection_log_519_neg
  have he : Real.log (500077 / 500000) = -Real.log (500000 / 500077) := by
    rw [show ((500077 / 500000) : ℝ) = ((500000 / 500077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_520_neg : (154011 / 1000000000) ≤ -Real.log (499923 / 500000) ∧
    -Real.log (499923 / 500000) ≤ (38503 / 250000000) := by
  have h := checkLog_sound (w := (77 / 999923)) (n := 12)
    (lo := (154011 / 1000000000)) (hi := (38503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499923) = 1/(499923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_520 : Bounds (-38503 / 250000000) (-154011 / 1000000000) (Real.log (499923 / 500000)) := by
  have h := reflection_log_520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_521_neg : (14873759 / 200000000) ≤ -Real.log (250000 / 269301) ∧
    -Real.log (250000 / 269301) ≤ (18592199 / 250000000) := by
  have h := checkLog_sound (w := (19301 / 519301)) (n := 12)
    (lo := (14873759 / 200000000)) (hi := (18592199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269301 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269301 / 250000) = 1/(250000 / 269301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_521 : Bounds (14873759 / 200000000) (18592199 / 250000000) (Real.log (269301 / 250000)) := by
  have h := reflection_log_521_neg
  have he : Real.log (269301 / 250000) = -Real.log (250000 / 269301) := by
    rw [show ((269301 / 250000) : ℝ) = ((250000 / 269301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_522_neg : (80347087 / 1000000000) ≤ -Real.log (230699 / 250000) ∧
    -Real.log (230699 / 250000) ≤ (5021693 / 62500000) := by
  have h := checkLog_sound (w := (19301 / 480699)) (n := 12)
    (lo := (80347087 / 1000000000)) (hi := (5021693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230699) = 1/(230699 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_522 : Bounds (-5021693 / 62500000) (-80347087 / 1000000000) (Real.log (230699 / 250000)) := by
  have h := reflection_log_522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_523_neg : (18639771 / 250000000) ≤ -Real.log (1000000 / 1077409) ∧
    -Real.log (1000000 / 1077409) ≤ (14911817 / 200000000) := by
  have h := checkLog_sound (w := (77409 / 2077409)) (n := 12)
    (lo := (18639771 / 250000000)) (hi := (14911817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077409 / 1000000) = 1/(1000000 / 1077409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_523 : Bounds (18639771 / 250000000) (14911817 / 200000000) (Real.log (1077409 / 1000000)) := by
  have h := reflection_log_523_neg
  have he : Real.log (1077409 / 1000000) = -Real.log (1000000 / 1077409) := by
    rw [show ((1077409 / 1000000) : ℝ) = ((1000000 / 1077409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_524_neg : (40284631 / 500000000) ≤ -Real.log (922591 / 1000000) ∧
    -Real.log (922591 / 1000000) ≤ (80569263 / 1000000000) := by
  have h := checkLog_sound (w := (77409 / 1922591)) (n := 12)
    (lo := (40284631 / 500000000)) (hi := (80569263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922591) = 1/(922591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_524 : Bounds (-80569263 / 1000000000) (-40284631 / 500000000) (Real.log (922591 / 1000000)) := by
  have h := reflection_log_524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_525_neg : (3005089 / 500000000) ≤ -Real.log (994007846719 / 1000000000000) ∧
    -Real.log (994007846719 / 1000000000000) ≤ (6010179 / 1000000000) := by
  have h := checkLog_sound (w := (5992153281 / 1994007846719)) (n := 12)
    (lo := (3005089 / 500000000)) (hi := (6010179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994007846719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994007846719) = 1/(994007846719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_525 : Bounds (-6010179 / 1000000000) (-3005089 / 500000000) (Real.log (994007846719 / 1000000000000)) := by
  have h := reflection_log_525_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_526_neg : (1494573 / 250000000) ≤ -Real.log (62127471399 / 62500000000) ∧
    -Real.log (62127471399 / 62500000000) ≤ (5978293 / 1000000000) := by
  have h := checkLog_sound (w := (372528601 / 124627471399)) (n := 12)
    (lo := (1494573 / 250000000)) (hi := (5978293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62127471399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62127471399) = 1/(62127471399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_526 : Bounds (-5978293 / 1000000000) (-1494573 / 250000000) (Real.log (62127471399 / 62500000000)) := by
  have h := reflection_log_526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_527_neg : (77357941 / 500000000) ≤ -Real.log (100000000000 / 116732625629) ∧
    -Real.log (100000000000 / 116732625629) ≤ (154715883 / 1000000000) := by
  have h := checkLog_sound (w := (16732625629 / 216732625629)) (n := 12)
    (lo := (77357941 / 500000000)) (hi := (154715883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116732625629 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116732625629 / 100000000000) = 1/(100000000000 / 116732625629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_527 : Bounds (77357941 / 500000000) (154715883 / 1000000000) (Real.log (116732625629 / 100000000000)) := by
  have h := reflection_log_527_neg
  have he : Real.log (116732625629 / 100000000000) = -Real.log (100000000000 / 116732625629) := by
    rw [show ((116732625629 / 100000000000) : ℝ) = ((100000000000 / 116732625629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_528_neg : (155128347 / 1000000000) ≤ -Real.log (250000000000 / 291951959211) ∧
    -Real.log (250000000000 / 291951959211) ≤ (38782087 / 250000000) := by
  have h := checkLog_sound (w := (41951959211 / 541951959211)) (n := 12)
    (lo := (155128347 / 1000000000)) (hi := (38782087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291951959211 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291951959211 / 250000000000) = 1/(250000000000 / 291951959211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_528 : Bounds (155128347 / 1000000000) (38782087 / 250000000) (Real.log (291951959211 / 250000000000)) := by
  have h := reflection_log_528_neg
  have he : Real.log (291951959211 / 250000000000) = -Real.log (250000000000 / 291951959211) := by
    rw [show ((291951959211 / 250000000000) : ℝ) = ((250000000000 / 291951959211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_529_neg : (19391577 / 62500000) ≤ -Real.log (100000000000 / 136378678643) ∧
    -Real.log (100000000000 / 136378678643) ≤ (310265233 / 1000000000) := by
  have h := checkLog_sound (w := (36378678643 / 236378678643)) (n := 12)
    (lo := (19391577 / 62500000)) (hi := (310265233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136378678643 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136378678643 / 100000000000) = 1/(100000000000 / 136378678643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_529 : Bounds (19391577 / 62500000) (310265233 / 1000000000) (Real.log (136378678643 / 100000000000)) := by
  have h := reflection_log_529_neg
  have he : Real.log (136378678643 / 100000000000) = -Real.log (100000000000 / 136378678643) := by
    rw [show ((136378678643 / 100000000000) : ℝ) = ((100000000000 / 136378678643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_530_neg : (310470087 / 1000000000) ≤ -Real.log (500000000000 / 682033096927) ∧
    -Real.log (500000000000 / 682033096927) ≤ (38808761 / 125000000) := by
  have h := checkLog_sound (w := (182033096927 / 1182033096927)) (n := 12)
    (lo := (310470087 / 1000000000)) (hi := (38808761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682033096927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682033096927 / 500000000000) = 1/(500000000000 / 682033096927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_530 : Bounds (310470087 / 1000000000) (38808761 / 125000000) (Real.log (682033096927 / 500000000000)) := by
  have h := reflection_log_530_neg
  have he : Real.log (682033096927 / 500000000000) = -Real.log (500000000000 / 682033096927) := by
    rw [show ((682033096927 / 500000000000) : ℝ) = ((500000000000 / 682033096927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_531_neg : (143320819 / 1000000000) ≤ -Real.log (10000 / 11541) ∧
    -Real.log (10000 / 11541) ≤ (7166041 / 50000000) := by
  have h := checkLog_sound (w := (1541 / 21541)) (n := 12)
    (lo := (143320819 / 1000000000)) (hi := (7166041 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11541 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11541 / 10000) = 1/(10000 / 11541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_531 : Bounds (143320819 / 1000000000) (7166041 / 50000000) (Real.log (11541 / 10000)) := by
  have h := reflection_log_531_neg
  have he : Real.log (11541 / 10000) = -Real.log (10000 / 11541) := by
    rw [show ((11541 / 10000) : ℝ) = ((10000 / 11541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_532_neg : (167354129 / 1000000000) ≤ -Real.log (8459 / 10000) ∧
    -Real.log (8459 / 10000) ≤ (16735413 / 100000000) := by
  have h := checkLog_sound (w := (1541 / 18459)) (n := 12)
    (lo := (167354129 / 1000000000)) (hi := (16735413 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8459) = 1/(8459 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_532 : Bounds (-16735413 / 100000000) (-167354129 / 1000000000) (Real.log (8459 / 10000)) := by
  have h := reflection_log_532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_533_neg : (19261 / 125000000) ≤ -Real.log (10000000 / 10001541) ∧
    -Real.log (10000000 / 10001541) ≤ (154089 / 1000000000) := by
  have h := checkLog_sound (w := (1541 / 20001541)) (n := 12)
    (lo := (19261 / 125000000)) (hi := (154089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001541 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001541 / 10000000) = 1/(10000000 / 10001541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_533 : Bounds (19261 / 125000000) (154089 / 1000000000) (Real.log (10001541 / 10000000)) := by
  have h := reflection_log_533_neg
  have he : Real.log (10001541 / 10000000) = -Real.log (10000000 / 10001541) := by
    rw [show ((10001541 / 10000000) : ℝ) = ((10000000 / 10001541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_534_neg : (154111 / 1000000000) ≤ -Real.log (9998459 / 10000000) ∧
    -Real.log (9998459 / 10000000) ≤ (301 / 1953125) := by
  have h := checkLog_sound (w := (1541 / 19998459)) (n := 12)
    (lo := (154111 / 1000000000)) (hi := (301 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998459) = 1/(9998459 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_534 : Bounds (-301 / 1953125) (-154111 / 1000000000) (Real.log (9998459 / 10000000)) := by
  have h := reflection_log_534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_535_neg : (7441521 / 100000000) ≤ -Real.log (500000 / 538627) ∧
    -Real.log (500000 / 538627) ≤ (74415211 / 1000000000) := by
  have h := checkLog_sound (w := (38627 / 1038627)) (n := 12)
    (lo := (7441521 / 100000000)) (hi := (74415211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538627 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538627 / 500000) = 1/(500000 / 538627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_535 : Bounds (7441521 / 100000000) (74415211 / 1000000000) (Real.log (538627 / 500000)) := by
  have h := reflection_log_535_neg
  have he : Real.log (538627 / 500000) = -Real.log (500000 / 538627) := by
    rw [show ((538627 / 500000) : ℝ) = ((500000 / 538627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_536_neg : (80401271 / 1000000000) ≤ -Real.log (461373 / 500000) ∧
    -Real.log (461373 / 500000) ≤ (10050159 / 125000000) := by
  have h := checkLog_sound (w := (38627 / 961373)) (n := 12)
    (lo := (80401271 / 1000000000)) (hi := (10050159 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461373) = 1/(461373 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_536 : Bounds (-10050159 / 125000000) (-80401271 / 1000000000) (Real.log (461373 / 500000)) := by
  have h := reflection_log_536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_537_neg : (74605491 / 1000000000) ≤ -Real.log (1000000 / 1077459) ∧
    -Real.log (1000000 / 1077459) ≤ (18651373 / 250000000) := by
  have h := checkLog_sound (w := (77459 / 2077459)) (n := 12)
    (lo := (74605491 / 1000000000)) (hi := (18651373 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077459 / 1000000) = 1/(1000000 / 1077459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_537 : Bounds (74605491 / 1000000000) (18651373 / 250000000) (Real.log (1077459 / 1000000)) := by
  have h := reflection_log_537_neg
  have he : Real.log (1077459 / 1000000) = -Real.log (1000000 / 1077459) := by
    rw [show ((1077459 / 1000000) : ℝ) = ((1000000 / 1077459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_538_neg : (80623459 / 1000000000) ≤ -Real.log (922541 / 1000000) ∧
    -Real.log (922541 / 1000000) ≤ (4031173 / 50000000) := by
  have h := checkLog_sound (w := (77459 / 1922541)) (n := 12)
    (lo := (80623459 / 1000000000)) (hi := (4031173 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922541) = 1/(922541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_538 : Bounds (-4031173 / 50000000) (-80623459 / 1000000000) (Real.log (922541 / 1000000)) := by
  have h := reflection_log_538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_539_neg : (376123 / 62500000) ≤ -Real.log (994000103319 / 1000000000000) ∧
    -Real.log (994000103319 / 1000000000000) ≤ (6017969 / 1000000000) := by
  have h := checkLog_sound (w := (5999896681 / 1994000103319)) (n := 12)
    (lo := (376123 / 62500000)) (hi := (6017969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994000103319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994000103319) = 1/(994000103319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_539 : Bounds (-6017969 / 1000000000) (-376123 / 62500000) (Real.log (994000103319 / 1000000000000)) := by
  have h := reflection_log_539_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_540_neg : (5986061 / 1000000000) ≤ -Real.log (248507954871 / 250000000000) ∧
    -Real.log (248507954871 / 250000000000) ≤ (2993031 / 500000000) := by
  have h := checkLog_sound (w := (1492045129 / 498507954871)) (n := 12)
    (lo := (5986061 / 1000000000)) (hi := (2993031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248507954871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248507954871) = 1/(248507954871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_540 : Bounds (-2993031 / 500000000) (-5986061 / 1000000000) (Real.log (248507954871 / 250000000000)) := by
  have h := reflection_log_540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_541_neg : (77408241 / 500000000) ≤ -Real.log (100000000000 / 116744369523) ∧
    -Real.log (100000000000 / 116744369523) ≤ (154816483 / 1000000000) := by
  have h := checkLog_sound (w := (16744369523 / 216744369523)) (n := 12)
    (lo := (77408241 / 500000000)) (hi := (154816483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116744369523 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116744369523 / 100000000000) = 1/(100000000000 / 116744369523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_541 : Bounds (77408241 / 500000000) (154816483 / 1000000000) (Real.log (116744369523 / 100000000000)) := by
  have h := reflection_log_541_neg
  have he : Real.log (116744369523 / 100000000000) = -Real.log (100000000000 / 116744369523) := by
    rw [show ((116744369523 / 100000000000) : ℝ) = ((100000000000 / 116744369523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_542_neg : (3104579 / 20000000) ≤ -Real.log (500000000000 / 583962663991) ∧
    -Real.log (500000000000 / 583962663991) ≤ (155228951 / 1000000000) := by
  have h := checkLog_sound (w := (83962663991 / 1083962663991)) (n := 12)
    (lo := (3104579 / 20000000)) (hi := (155228951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583962663991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583962663991 / 500000000000) = 1/(500000000000 / 583962663991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_542 : Bounds (3104579 / 20000000) (155228951 / 1000000000) (Real.log (583962663991 / 500000000000)) := by
  have h := reflection_log_542_neg
  have he : Real.log (583962663991 / 500000000000) = -Real.log (500000000000 / 583962663991) := by
    rw [show ((583962663991 / 500000000000) : ℝ) = ((500000000000 / 583962663991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_543_neg : (310470087 / 1000000000) ≤ -Real.log (250000000000 / 341016548463) ∧
    -Real.log (250000000000 / 341016548463) ≤ (38808761 / 125000000) := by
  have h := checkLog_sound (w := (91016548463 / 591016548463)) (n := 12)
    (lo := (310470087 / 1000000000)) (hi := (38808761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341016548463 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341016548463 / 250000000000) = 1/(250000000000 / 341016548463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_543 : Bounds (310470087 / 1000000000) (38808761 / 125000000) (Real.log (341016548463 / 250000000000)) := by
  have h := reflection_log_543_neg
  have he : Real.log (341016548463 / 250000000000) = -Real.log (250000000000 / 341016548463) := by
    rw [show ((341016548463 / 250000000000) : ℝ) = ((250000000000 / 341016548463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_544_neg : (310674949 / 1000000000) ≤ -Real.log (500000000000 / 682172833669) ∧
    -Real.log (500000000000 / 682172833669) ≤ (6213499 / 20000000) := by
  have h := checkLog_sound (w := (182172833669 / 1182172833669)) (n := 12)
    (lo := (310674949 / 1000000000)) (hi := (6213499 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682172833669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682172833669 / 500000000000) = 1/(500000000000 / 682172833669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_544 : Bounds (310674949 / 1000000000) (6213499 / 20000000) (Real.log (682172833669 / 500000000000)) := by
  have h := reflection_log_544_neg
  have he : Real.log (682172833669 / 500000000000) = -Real.log (500000000000 / 682172833669) := by
    rw [show ((682172833669 / 500000000000) : ℝ) = ((500000000000 / 682172833669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_545_neg : (143407463 / 1000000000) ≤ -Real.log (5000 / 5771) ∧
    -Real.log (5000 / 5771) ≤ (17925933 / 125000000) := by
  have h := checkLog_sound (w := (771 / 10771)) (n := 12)
    (lo := (143407463 / 1000000000)) (hi := (17925933 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5771 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5771 / 5000) = 1/(5000 / 5771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_545 : Bounds (143407463 / 1000000000) (17925933 / 125000000) (Real.log (5771 / 5000)) := by
  have h := reflection_log_545_neg
  have he : Real.log (5771 / 5000) = -Real.log (5000 / 5771) := by
    rw [show ((5771 / 5000) : ℝ) = ((5000 / 5771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_546_neg : (167472353 / 1000000000) ≤ -Real.log (4229 / 5000) ∧
    -Real.log (4229 / 5000) ≤ (83736177 / 500000000) := by
  have h := checkLog_sound (w := (771 / 9229)) (n := 12)
    (lo := (167472353 / 1000000000)) (hi := (83736177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4229) = 1/(4229 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_546 : Bounds (-83736177 / 500000000) (-167472353 / 1000000000) (Real.log (4229 / 5000)) := by
  have h := reflection_log_546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_547_neg : (38547 / 250000000) ≤ -Real.log (5000000 / 5000771) ∧
    -Real.log (5000000 / 5000771) ≤ (154189 / 1000000000) := by
  have h := checkLog_sound (w := (771 / 10000771)) (n := 12)
    (lo := (38547 / 250000000)) (hi := (154189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000771 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000771 / 5000000) = 1/(5000000 / 5000771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_547 : Bounds (38547 / 250000000) (154189 / 1000000000) (Real.log (5000771 / 5000000)) := by
  have h := reflection_log_547_neg
  have he : Real.log (5000771 / 5000000) = -Real.log (5000000 / 5000771) := by
    rw [show ((5000771 / 5000000) : ℝ) = ((5000000 / 5000771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_548_neg : (154211 / 1000000000) ≤ -Real.log (4999229 / 5000000) ∧
    -Real.log (4999229 / 5000000) ≤ (38553 / 250000000) := by
  have h := checkLog_sound (w := (771 / 9999229)) (n := 12)
    (lo := (154211 / 1000000000)) (hi := (38553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999229) = 1/(4999229 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_548 : Bounds (-38553 / 250000000) (-154211 / 1000000000) (Real.log (4999229 / 5000000)) := by
  have h := reflection_log_548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_549_neg : (9307819 / 125000000) ≤ -Real.log (200000 / 215461) ∧
    -Real.log (200000 / 215461) ≤ (74462553 / 1000000000) := by
  have h := checkLog_sound (w := (15461 / 415461)) (n := 12)
    (lo := (9307819 / 125000000)) (hi := (74462553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215461 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215461 / 200000) = 1/(200000 / 215461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_549 : Bounds (9307819 / 125000000) (74462553 / 1000000000) (Real.log (215461 / 200000)) := by
  have h := reflection_log_549_neg
  have he : Real.log (215461 / 200000) = -Real.log (200000 / 215461) := by
    rw [show ((215461 / 200000) : ℝ) = ((200000 / 215461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_550_neg : (80456543 / 1000000000) ≤ -Real.log (184539 / 200000) ∧
    -Real.log (184539 / 200000) ≤ (2514267 / 31250000) := by
  have h := checkLog_sound (w := (15461 / 384539)) (n := 12)
    (lo := (80456543 / 1000000000)) (hi := (2514267 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184539) = 1/(184539 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_550 : Bounds (-2514267 / 31250000) (-80456543 / 1000000000) (Real.log (184539 / 200000)) := by
  have h := reflection_log_550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_551_neg : (74652823 / 1000000000) ≤ -Real.log (100000 / 107751) ∧
    -Real.log (100000 / 107751) ≤ (9331603 / 125000000) := by
  have h := checkLog_sound (w := (7751 / 207751)) (n := 12)
    (lo := (74652823 / 1000000000)) (hi := (9331603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107751 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107751 / 100000) = 1/(100000 / 107751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_551 : Bounds (74652823 / 1000000000) (9331603 / 125000000) (Real.log (107751 / 100000)) := by
  have h := reflection_log_551_neg
  have he : Real.log (107751 / 100000) = -Real.log (100000 / 107751) := by
    rw [show ((107751 / 100000) : ℝ) = ((100000 / 107751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_552_neg : (80678743 / 1000000000) ≤ -Real.log (92249 / 100000) ∧
    -Real.log (92249 / 100000) ≤ (10084843 / 125000000) := by
  have h := checkLog_sound (w := (7751 / 192249)) (n := 12)
    (lo := (80678743 / 1000000000)) (hi := (10084843 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92249) = 1/(92249 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_552 : Bounds (-10084843 / 125000000) (-80678743 / 1000000000) (Real.log (92249 / 100000)) := by
  have h := reflection_log_552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_553_neg : (6025919 / 1000000000) ≤ -Real.log (9939921999 / 10000000000) ∧
    -Real.log (9939921999 / 10000000000) ≤ (18831 / 3125000) := by
  have h := checkLog_sound (w := (60078001 / 19939921999)) (n := 12)
    (lo := (6025919 / 1000000000)) (hi := (18831 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9939921999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9939921999) = 1/(9939921999 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_553 : Bounds (-18831 / 3125000) (-6025919 / 1000000000) (Real.log (9939921999 / 10000000000)) := by
  have h := reflection_log_553_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_554_neg : (5993991 / 1000000000) ≤ -Real.log (39760957479 / 40000000000) ∧
    -Real.log (39760957479 / 40000000000) ≤ (749249 / 125000000) := by
  have h := checkLog_sound (w := (239042521 / 79760957479)) (n := 12)
    (lo := (5993991 / 1000000000)) (hi := (749249 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39760957479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39760957479) = 1/(39760957479 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_554 : Bounds (-749249 / 125000000) (-5993991 / 1000000000) (Real.log (39760957479 / 40000000000)) := by
  have h := reflection_log_554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_555_neg : (30983819 / 200000000) ≤ -Real.log (500000000000 / 583781748031) ∧
    -Real.log (500000000000 / 583781748031) ≤ (19364887 / 125000000) := by
  have h := checkLog_sound (w := (83781748031 / 1083781748031)) (n := 12)
    (lo := (30983819 / 200000000)) (hi := (19364887 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583781748031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583781748031 / 500000000000) = 1/(500000000000 / 583781748031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_555 : Bounds (30983819 / 200000000) (19364887 / 125000000) (Real.log (583781748031 / 500000000000)) := by
  have h := reflection_log_555_neg
  have he : Real.log (583781748031 / 500000000000) = -Real.log (500000000000 / 583781748031) := by
    rw [show ((583781748031 / 500000000000) : ℝ) = ((500000000000 / 583781748031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_556_neg : (77665783 / 500000000) ≤ -Real.log (500000000000 / 584022591031) ∧
    -Real.log (500000000000 / 584022591031) ≤ (155331567 / 1000000000) := by
  have h := checkLog_sound (w := (84022591031 / 1084022591031)) (n := 12)
    (lo := (77665783 / 500000000)) (hi := (155331567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584022591031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584022591031 / 500000000000) = 1/(500000000000 / 584022591031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_556 : Bounds (77665783 / 500000000) (155331567 / 1000000000) (Real.log (584022591031 / 500000000000)) := by
  have h := reflection_log_556_neg
  have he : Real.log (584022591031 / 500000000000) = -Real.log (500000000000 / 584022591031) := by
    rw [show ((584022591031 / 500000000000) : ℝ) = ((500000000000 / 584022591031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_557_neg : (310674949 / 1000000000) ≤ -Real.log (125000000000 / 170543208417) ∧
    -Real.log (125000000000 / 170543208417) ≤ (6213499 / 20000000) := by
  have h := checkLog_sound (w := (45543208417 / 295543208417)) (n := 12)
    (lo := (310674949 / 1000000000)) (hi := (6213499 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170543208417 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170543208417 / 125000000000) = 1/(125000000000 / 170543208417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_557 : Bounds (310674949 / 1000000000) (6213499 / 20000000) (Real.log (170543208417 / 125000000000)) := by
  have h := reflection_log_557_neg
  have he : Real.log (170543208417 / 125000000000) = -Real.log (125000000000 / 170543208417) := by
    rw [show ((170543208417 / 125000000000) : ℝ) = ((125000000000 / 170543208417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_558_neg : (310879817 / 1000000000) ≤ -Real.log (500000000000 / 682312603453) ∧
    -Real.log (500000000000 / 682312603453) ≤ (155439909 / 500000000) := by
  have h := checkLog_sound (w := (182312603453 / 1182312603453)) (n := 12)
    (lo := (310879817 / 1000000000)) (hi := (155439909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682312603453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682312603453 / 500000000000) = 1/(500000000000 / 682312603453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_558 : Bounds (310879817 / 1000000000) (155439909 / 500000000) (Real.log (682312603453 / 500000000000)) := by
  have h := reflection_log_558_neg
  have he : Real.log (682312603453 / 500000000000) = -Real.log (500000000000 / 682312603453) := by
    rw [show ((682312603453 / 500000000000) : ℝ) = ((500000000000 / 682312603453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_559_neg : (143494099 / 1000000000) ≤ -Real.log (10000 / 11543) ∧
    -Real.log (10000 / 11543) ≤ (1434941 / 10000000) := by
  have h := checkLog_sound (w := (1543 / 21543)) (n := 12)
    (lo := (143494099 / 1000000000)) (hi := (1434941 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11543 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11543 / 10000) = 1/(10000 / 11543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_559 : Bounds (143494099 / 1000000000) (1434941 / 10000000) (Real.log (11543 / 10000)) := by
  have h := reflection_log_559_neg
  have he : Real.log (11543 / 10000) = -Real.log (10000 / 11543) := by
    rw [show ((11543 / 10000) : ℝ) = ((10000 / 11543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_560_neg : (2618603 / 15625000) ≤ -Real.log (8457 / 10000) ∧
    -Real.log (8457 / 10000) ≤ (167590593 / 1000000000) := by
  have h := checkLog_sound (w := (1543 / 18457)) (n := 12)
    (lo := (2618603 / 15625000)) (hi := (167590593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8457) = 1/(8457 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_560 : Bounds (-167590593 / 1000000000) (-2618603 / 15625000) (Real.log (8457 / 10000)) := by
  have h := reflection_log_560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_561_neg : (9643 / 62500000) ≤ -Real.log (10000000 / 10001543) ∧
    -Real.log (10000000 / 10001543) ≤ (154289 / 1000000000) := by
  have h := checkLog_sound (w := (1543 / 20001543)) (n := 12)
    (lo := (9643 / 62500000)) (hi := (154289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001543 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001543 / 10000000) = 1/(10000000 / 10001543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_561 : Bounds (9643 / 62500000) (154289 / 1000000000) (Real.log (10001543 / 10000000)) := by
  have h := reflection_log_561_neg
  have he : Real.log (10001543 / 10000000) = -Real.log (10000000 / 10001543) := by
    rw [show ((10001543 / 10000000) : ℝ) = ((10000000 / 10001543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_562_neg : (154311 / 1000000000) ≤ -Real.log (9998457 / 10000000) ∧
    -Real.log (9998457 / 10000000) ≤ (19289 / 125000000) := by
  have h := checkLog_sound (w := (1543 / 19998457)) (n := 12)
    (lo := (154311 / 1000000000)) (hi := (19289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998457) = 1/(9998457 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_562 : Bounds (-19289 / 125000000) (-154311 / 1000000000) (Real.log (9998457 / 10000000)) := by
  have h := reflection_log_562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_563_neg : (74509891 / 1000000000) ≤ -Real.log (250000 / 269339) ∧
    -Real.log (250000 / 269339) ≤ (18627473 / 250000000) := by
  have h := checkLog_sound (w := (19339 / 519339)) (n := 12)
    (lo := (74509891 / 1000000000)) (hi := (18627473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269339 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269339 / 250000) = 1/(250000 / 269339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_563 : Bounds (74509891 / 1000000000) (18627473 / 250000000) (Real.log (269339 / 250000)) := by
  have h := reflection_log_563_neg
  have he : Real.log (269339 / 250000) = -Real.log (250000 / 269339) := by
    rw [show ((269339 / 250000) : ℝ) = ((250000 / 269339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_564_neg : (80511817 / 1000000000) ≤ -Real.log (230661 / 250000) ∧
    -Real.log (230661 / 250000) ≤ (40255909 / 500000000) := by
  have h := checkLog_sound (w := (19339 / 480661)) (n := 12)
    (lo := (80511817 / 1000000000)) (hi := (40255909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230661) = 1/(230661 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_564 : Bounds (-40255909 / 500000000) (-80511817 / 1000000000) (Real.log (230661 / 250000)) := by
  have h := reflection_log_564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_565_neg : (74700153 / 1000000000) ≤ -Real.log (1000000 / 1077561) ∧
    -Real.log (1000000 / 1077561) ≤ (37350077 / 500000000) := by
  have h := checkLog_sound (w := (77561 / 2077561)) (n := 12)
    (lo := (74700153 / 1000000000)) (hi := (37350077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077561 / 1000000) = 1/(1000000 / 1077561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_565 : Bounds (74700153 / 1000000000) (37350077 / 500000000) (Real.log (1077561 / 1000000)) := by
  have h := reflection_log_565_neg
  have he : Real.log (1077561 / 1000000) = -Real.log (1000000 / 1077561) := by
    rw [show ((1077561 / 1000000) : ℝ) = ((1000000 / 1077561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_566_neg : (80734029 / 1000000000) ≤ -Real.log (922439 / 1000000) ∧
    -Real.log (922439 / 1000000) ≤ (8073403 / 100000000) := by
  have h := checkLog_sound (w := (77561 / 1922439)) (n := 12)
    (lo := (80734029 / 1000000000)) (hi := (8073403 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922439) = 1/(922439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_566 : Bounds (-8073403 / 100000000) (-80734029 / 1000000000) (Real.log (922439 / 1000000)) := by
  have h := reflection_log_566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_567_neg : (48271 / 8000000) ≤ -Real.log (993984291279 / 1000000000000) ∧
    -Real.log (993984291279 / 1000000000000) ≤ (1508469 / 250000000) := by
  have h := checkLog_sound (w := (6015708721 / 1993984291279)) (n := 12)
    (lo := (48271 / 8000000)) (hi := (1508469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993984291279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993984291279) = 1/(993984291279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_567 : Bounds (-1508469 / 250000000) (-48271 / 8000000) (Real.log (993984291279 / 1000000000000)) := by
  have h := reflection_log_567_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_568_neg : (3000963 / 500000000) ≤ -Real.log (62126003079 / 62500000000) ∧
    -Real.log (62126003079 / 62500000000) ≤ (6001927 / 1000000000) := by
  have h := checkLog_sound (w := (373996921 / 124626003079)) (n := 12)
    (lo := (3000963 / 500000000)) (hi := (6001927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62126003079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62126003079) = 1/(62126003079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_568 : Bounds (-6001927 / 1000000000) (-3000963 / 500000000) (Real.log (62126003079 / 62500000000)) := by
  have h := reflection_log_568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_569_neg : (155021709 / 1000000000) ≤ -Real.log (500000000000 / 583841655069) ∧
    -Real.log (500000000000 / 583841655069) ≤ (15502171 / 100000000) := by
  have h := checkLog_sound (w := (83841655069 / 1083841655069)) (n := 12)
    (lo := (155021709 / 1000000000)) (hi := (15502171 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583841655069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583841655069 / 500000000000) = 1/(500000000000 / 583841655069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_569 : Bounds (155021709 / 1000000000) (15502171 / 100000000) (Real.log (583841655069 / 500000000000)) := by
  have h := reflection_log_569_neg
  have he : Real.log (583841655069 / 500000000000) = -Real.log (500000000000 / 583841655069) := by
    rw [show ((583841655069 / 500000000000) : ℝ) = ((500000000000 / 583841655069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_570_neg : (155434183 / 1000000000) ≤ -Real.log (500000000000 / 584082524699) ∧
    -Real.log (500000000000 / 584082524699) ≤ (19429273 / 125000000) := by
  have h := checkLog_sound (w := (84082524699 / 1084082524699)) (n := 12)
    (lo := (155434183 / 1000000000)) (hi := (19429273 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584082524699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584082524699 / 500000000000) = 1/(500000000000 / 584082524699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_570 : Bounds (155434183 / 1000000000) (19429273 / 125000000) (Real.log (584082524699 / 500000000000)) := by
  have h := reflection_log_570_neg
  have he : Real.log (584082524699 / 500000000000) = -Real.log (500000000000 / 584082524699) := by
    rw [show ((584082524699 / 500000000000) : ℝ) = ((500000000000 / 584082524699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_571_neg : (310879817 / 1000000000) ≤ -Real.log (125000000000 / 170578150863) ∧
    -Real.log (125000000000 / 170578150863) ≤ (155439909 / 500000000) := by
  have h := checkLog_sound (w := (45578150863 / 295578150863)) (n := 12)
    (lo := (310879817 / 1000000000)) (hi := (155439909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170578150863 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170578150863 / 125000000000) = 1/(125000000000 / 170578150863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_571 : Bounds (310879817 / 1000000000) (155439909 / 500000000) (Real.log (170578150863 / 125000000000)) := by
  have h := reflection_log_571_neg
  have he : Real.log (170578150863 / 125000000000) = -Real.log (125000000000 / 170578150863) := by
    rw [show ((170578150863 / 125000000000) : ℝ) = ((125000000000 / 170578150863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_572_neg : (311084691 / 1000000000) ≤ -Real.log (500000000000 / 682452406291) ∧
    -Real.log (500000000000 / 682452406291) ≤ (77771173 / 250000000) := by
  have h := checkLog_sound (w := (182452406291 / 1182452406291)) (n := 12)
    (lo := (311084691 / 1000000000)) (hi := (77771173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682452406291 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682452406291 / 500000000000) = 1/(500000000000 / 682452406291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_572 : Bounds (311084691 / 1000000000) (77771173 / 250000000) (Real.log (682452406291 / 500000000000)) := by
  have h := reflection_log_572_neg
  have he : Real.log (682452406291 / 500000000000) = -Real.log (500000000000 / 682452406291) := by
    rw [show ((682452406291 / 500000000000) : ℝ) = ((500000000000 / 682452406291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_573_neg : (17947591 / 125000000) ≤ -Real.log (1250 / 1443) ∧
    -Real.log (1250 / 1443) ≤ (143580729 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 2693)) (n := 12)
    (lo := (17947591 / 125000000)) (hi := (143580729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1443 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1443 / 1250) = 1/(1250 / 1443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_573 : Bounds (17947591 / 125000000) (143580729 / 1000000000) (Real.log (1443 / 1250)) := by
  have h := reflection_log_573_neg
  have he : Real.log (1443 / 1250) = -Real.log (1250 / 1443) := by
    rw [show ((1443 / 1250) : ℝ) = ((1250 / 1443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_574_neg : (41927211 / 250000000) ≤ -Real.log (1057 / 1250) ∧
    -Real.log (1057 / 1250) ≤ (33541769 / 200000000) := by
  have h := checkLog_sound (w := (193 / 2307)) (n := 12)
    (lo := (41927211 / 250000000)) (hi := (33541769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1057) = 1/(1057 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_574 : Bounds (-33541769 / 200000000) (-41927211 / 250000000) (Real.log (1057 / 1250)) := by
  have h := reflection_log_574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_575_neg : (38597 / 250000000) ≤ -Real.log (1250000 / 1250193) ∧
    -Real.log (1250000 / 1250193) ≤ (154389 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 2500193)) (n := 12)
    (lo := (38597 / 250000000)) (hi := (154389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250193 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250193 / 1250000) = 1/(1250000 / 1250193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_575 : Bounds (38597 / 250000000) (154389 / 1000000000) (Real.log (1250193 / 1250000)) := by
  have h := reflection_log_575_neg
  have he : Real.log (1250193 / 1250000) = -Real.log (1250000 / 1250193) := by
    rw [show ((1250193 / 1250000) : ℝ) = ((1250000 / 1250193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0009 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_576_neg : (154411 / 1000000000) ≤ -Real.log (1249807 / 1250000) ∧
    -Real.log (1249807 / 1250000) ≤ (38603 / 250000000) := by
  have h := checkLog_sound (w := (193 / 2499807)) (n := 12)
    (lo := (154411 / 1000000000)) (hi := (38603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249807) = 1/(1249807 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_576 : Bounds (-38603 / 250000000) (-154411 / 1000000000) (Real.log (1249807 / 1250000)) := by
  have h := reflection_log_576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_577_neg : (745563 / 10000000) ≤ -Real.log (500000 / 538703) ∧
    -Real.log (500000 / 538703) ≤ (74556301 / 1000000000) := by
  have h := checkLog_sound (w := (38703 / 1038703)) (n := 12)
    (lo := (745563 / 10000000)) (hi := (74556301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538703 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538703 / 500000) = 1/(500000 / 538703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_577 : Bounds (745563 / 10000000) (74556301 / 1000000000) (Real.log (538703 / 500000)) := by
  have h := reflection_log_577_neg
  have he : Real.log (538703 / 500000) = -Real.log (500000 / 538703) := by
    rw [show ((538703 / 500000) : ℝ) = ((500000 / 538703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_578_neg : (80566011 / 1000000000) ≤ -Real.log (461297 / 500000) ∧
    -Real.log (461297 / 500000) ≤ (20141503 / 250000000) := by
  have h := checkLog_sound (w := (38703 / 961297)) (n := 12)
    (lo := (80566011 / 1000000000)) (hi := (20141503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461297) = 1/(461297 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_578 : Bounds (-20141503 / 250000000) (-80566011 / 1000000000) (Real.log (461297 / 500000)) := by
  have h := reflection_log_578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_579_neg : (74747481 / 1000000000) ≤ -Real.log (250000 / 269403) ∧
    -Real.log (250000 / 269403) ≤ (37373741 / 500000000) := by
  have h := checkLog_sound (w := (19403 / 519403)) (n := 12)
    (lo := (74747481 / 1000000000)) (hi := (37373741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269403 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269403 / 250000) = 1/(250000 / 269403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_579 : Bounds (74747481 / 1000000000) (37373741 / 500000000) (Real.log (269403 / 250000)) := by
  have h := reflection_log_579_neg
  have he : Real.log (269403 / 250000) = -Real.log (250000 / 269403) := by
    rw [show ((269403 / 250000) : ℝ) = ((250000 / 269403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_580_neg : (80789319 / 1000000000) ≤ -Real.log (230597 / 250000) ∧
    -Real.log (230597 / 250000) ≤ (2019733 / 25000000) := by
  have h := checkLog_sound (w := (19403 / 480597)) (n := 12)
    (lo := (80789319 / 1000000000)) (hi := (2019733 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230597) = 1/(230597 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_580 : Bounds (-2019733 / 25000000) (-80789319 / 1000000000) (Real.log (230597 / 250000)) := by
  have h := reflection_log_580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_581_neg : (6041837 / 1000000000) ≤ -Real.log (62123523591 / 62500000000) ∧
    -Real.log (62123523591 / 62500000000) ≤ (3020919 / 500000000) := by
  have h := checkLog_sound (w := (376476409 / 124623523591)) (n := 12)
    (lo := (6041837 / 1000000000)) (hi := (3020919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62123523591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62123523591) = 1/(62123523591 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_581 : Bounds (-3020919 / 500000000) (-6041837 / 1000000000) (Real.log (62123523591 / 62500000000)) := by
  have h := reflection_log_581_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_582_neg : (6009711 / 1000000000) ≤ -Real.log (248502077791 / 250000000000) ∧
    -Real.log (248502077791 / 250000000000) ≤ (375607 / 62500000) := by
  have h := checkLog_sound (w := (1497922209 / 498502077791)) (n := 12)
    (lo := (6009711 / 1000000000)) (hi := (375607 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248502077791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248502077791) = 1/(248502077791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_582 : Bounds (-375607 / 62500000) (-6009711 / 1000000000) (Real.log (248502077791 / 250000000000)) := by
  have h := reflection_log_582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_583_neg : (155122311 / 1000000000) ≤ -Real.log (500000000000 / 583900393889) ∧
    -Real.log (500000000000 / 583900393889) ≤ (19390289 / 125000000) := by
  have h := checkLog_sound (w := (83900393889 / 1083900393889)) (n := 12)
    (lo := (155122311 / 1000000000)) (hi := (19390289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583900393889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583900393889 / 500000000000) = 1/(500000000000 / 583900393889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_583 : Bounds (155122311 / 1000000000) (19390289 / 125000000) (Real.log (583900393889 / 500000000000)) := by
  have h := reflection_log_583_neg
  have he : Real.log (583900393889 / 500000000000) = -Real.log (500000000000 / 583900393889) := by
    rw [show ((583900393889 / 500000000000) : ℝ) = ((500000000000 / 583900393889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_584_neg : (155536801 / 1000000000) ≤ -Real.log (250000000000 / 292071232497) ∧
    -Real.log (250000000000 / 292071232497) ≤ (77768401 / 500000000) := by
  have h := checkLog_sound (w := (42071232497 / 542071232497)) (n := 12)
    (lo := (155536801 / 1000000000)) (hi := (77768401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292071232497 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292071232497 / 250000000000) = 1/(250000000000 / 292071232497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_584 : Bounds (155536801 / 1000000000) (77768401 / 500000000) (Real.log (292071232497 / 250000000000)) := by
  have h := reflection_log_584_neg
  have he : Real.log (292071232497 / 250000000000) = -Real.log (250000000000 / 292071232497) := by
    rw [show ((292071232497 / 250000000000) : ℝ) = ((250000000000 / 292071232497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_585_neg : (311084691 / 1000000000) ≤ -Real.log (50000000000 / 68245240629) ∧
    -Real.log (50000000000 / 68245240629) ≤ (77771173 / 250000000) := by
  have h := checkLog_sound (w := (18245240629 / 118245240629)) (n := 12)
    (lo := (311084691 / 1000000000)) (hi := (77771173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68245240629 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68245240629 / 50000000000) = 1/(50000000000 / 68245240629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_585 : Bounds (311084691 / 1000000000) (77771173 / 250000000) (Real.log (68245240629 / 50000000000)) := by
  have h := reflection_log_585_neg
  have he : Real.log (68245240629 / 50000000000) = -Real.log (50000000000 / 68245240629) := by
    rw [show ((68245240629 / 50000000000) : ℝ) = ((50000000000 / 68245240629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_586_neg : (77822393 / 250000000) ≤ -Real.log (100000000000 / 136518448439) ∧
    -Real.log (100000000000 / 136518448439) ≤ (311289573 / 1000000000) := by
  have h := checkLog_sound (w := (36518448439 / 236518448439)) (n := 12)
    (lo := (77822393 / 250000000)) (hi := (311289573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136518448439 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136518448439 / 100000000000) = 1/(100000000000 / 136518448439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_586 : Bounds (77822393 / 250000000) (311289573 / 1000000000) (Real.log (136518448439 / 100000000000)) := by
  have h := reflection_log_586_neg
  have he : Real.log (136518448439 / 100000000000) = -Real.log (100000000000 / 136518448439) := by
    rw [show ((136518448439 / 100000000000) : ℝ) = ((100000000000 / 136518448439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_587_neg : (143667349 / 1000000000) ≤ -Real.log (2000 / 2309) ∧
    -Real.log (2000 / 2309) ≤ (2873347 / 20000000) := by
  have h := checkLog_sound (w := (309 / 4309)) (n := 12)
    (lo := (143667349 / 1000000000)) (hi := (2873347 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2309 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2309 / 2000) = 1/(2000 / 2309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_587 : Bounds (143667349 / 1000000000) (2873347 / 20000000) (Real.log (2309 / 2000)) := by
  have h := reflection_log_587_neg
  have he : Real.log (2309 / 2000) = -Real.log (2000 / 2309) := by
    rw [show ((2309 / 2000) : ℝ) = ((2000 / 2309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_588_neg : (16782711 / 100000000) ≤ -Real.log (1691 / 2000) ∧
    -Real.log (1691 / 2000) ≤ (167827111 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 3691)) (n := 12)
    (lo := (16782711 / 100000000)) (hi := (167827111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1691) = 1/(1691 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_588 : Bounds (-167827111 / 1000000000) (-16782711 / 100000000) (Real.log (1691 / 2000)) := by
  have h := reflection_log_588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_589_neg : (19311 / 125000000) ≤ -Real.log (2000000 / 2000309) ∧
    -Real.log (2000000 / 2000309) ≤ (154489 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 4000309)) (n := 12)
    (lo := (19311 / 125000000)) (hi := (154489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000309 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000309 / 2000000) = 1/(2000000 / 2000309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_589 : Bounds (19311 / 125000000) (154489 / 1000000000) (Real.log (2000309 / 2000000)) := by
  have h := reflection_log_589_neg
  have he : Real.log (2000309 / 2000000) = -Real.log (2000000 / 2000309) := by
    rw [show ((2000309 / 2000000) : ℝ) = ((2000000 / 2000309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_590_neg : (154511 / 1000000000) ≤ -Real.log (1999691 / 2000000) ∧
    -Real.log (1999691 / 2000000) ≤ (9657 / 62500000) := by
  have h := checkLog_sound (w := (309 / 3999691)) (n := 12)
    (lo := (154511 / 1000000000)) (hi := (9657 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999691) = 1/(1999691 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_590 : Bounds (-9657 / 62500000) (-154511 / 1000000000) (Real.log (1999691 / 2000000)) := by
  have h := reflection_log_590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_591_neg : (14920727 / 200000000) ≤ -Real.log (1000000 / 1077457) ∧
    -Real.log (1000000 / 1077457) ≤ (18650909 / 250000000) := by
  have h := checkLog_sound (w := (77457 / 2077457)) (n := 12)
    (lo := (14920727 / 200000000)) (hi := (18650909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077457 / 1000000) = 1/(1000000 / 1077457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_591 : Bounds (14920727 / 200000000) (18650909 / 250000000) (Real.log (1077457 / 1000000)) := by
  have h := reflection_log_591_neg
  have he : Real.log (1077457 / 1000000) = -Real.log (1000000 / 1077457) := by
    rw [show ((1077457 / 1000000) : ℝ) = ((1000000 / 1077457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_592_neg : (80621291 / 1000000000) ≤ -Real.log (922543 / 1000000) ∧
    -Real.log (922543 / 1000000) ≤ (20155323 / 250000000) := by
  have h := checkLog_sound (w := (77457 / 1922543)) (n := 12)
    (lo := (80621291 / 1000000000)) (hi := (20155323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922543) = 1/(922543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_592 : Bounds (-20155323 / 250000000) (-80621291 / 1000000000) (Real.log (922543 / 1000000)) := by
  have h := reflection_log_592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_593_neg : (74793879 / 1000000000) ≤ -Real.log (500000 / 538831) ∧
    -Real.log (500000 / 538831) ≤ (1869847 / 25000000) := by
  have h := checkLog_sound (w := (38831 / 1038831)) (n := 12)
    (lo := (74793879 / 1000000000)) (hi := (1869847 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538831 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538831 / 500000) = 1/(500000 / 538831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_593 : Bounds (74793879 / 1000000000) (1869847 / 25000000) (Real.log (538831 / 500000)) := by
  have h := reflection_log_593_neg
  have he : Real.log (538831 / 500000) = -Real.log (500000 / 538831) := by
    rw [show ((538831 / 500000) : ℝ) = ((500000 / 538831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_594_neg : (10105441 / 125000000) ≤ -Real.log (461169 / 500000) ∧
    -Real.log (461169 / 500000) ≤ (80843529 / 1000000000) := by
  have h := checkLog_sound (w := (38831 / 961169)) (n := 12)
    (lo := (10105441 / 125000000)) (hi := (80843529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461169) = 1/(461169 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_594 : Bounds (-80843529 / 1000000000) (-10105441 / 125000000) (Real.log (461169 / 500000)) := by
  have h := reflection_log_594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_595_neg : (378103 / 62500000) ≤ -Real.log (248492153439 / 250000000000) ∧
    -Real.log (248492153439 / 250000000000) ≤ (6049649 / 1000000000) := by
  have h := checkLog_sound (w := (1507846561 / 498492153439)) (n := 12)
    (lo := (378103 / 62500000)) (hi := (6049649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248492153439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248492153439) = 1/(248492153439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_595 : Bounds (-6049649 / 1000000000) (-378103 / 62500000) (Real.log (248492153439 / 250000000000)) := by
  have h := reflection_log_595_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_596_neg : (752207 / 125000000) ≤ -Real.log (994000413151 / 1000000000000) ∧
    -Real.log (994000413151 / 1000000000000) ≤ (6017657 / 1000000000) := by
  have h := checkLog_sound (w := (5999586849 / 1994000413151)) (n := 12)
    (lo := (752207 / 125000000)) (hi := (6017657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994000413151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994000413151) = 1/(994000413151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_596 : Bounds (-6017657 / 1000000000) (-752207 / 125000000) (Real.log (994000413151 / 1000000000000)) := by
  have h := reflection_log_596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_597_neg : (77612463 / 500000000) ≤ -Real.log (125000000000 / 145990078511) ∧
    -Real.log (125000000000 / 145990078511) ≤ (155224927 / 1000000000) := by
  have h := checkLog_sound (w := (20990078511 / 270990078511)) (n := 12)
    (lo := (77612463 / 500000000)) (hi := (155224927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145990078511 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145990078511 / 125000000000) = 1/(125000000000 / 145990078511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_597 : Bounds (77612463 / 500000000) (155224927 / 1000000000) (Real.log (145990078511 / 125000000000)) := by
  have h := reflection_log_597_neg
  have he : Real.log (145990078511 / 125000000000) = -Real.log (125000000000 / 145990078511) := by
    rw [show ((145990078511 / 125000000000) : ℝ) = ((125000000000 / 145990078511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_598_neg : (155637407 / 1000000000) ≤ -Real.log (62500000000 / 73025154553) ∧
    -Real.log (62500000000 / 73025154553) ≤ (4863669 / 31250000) := by
  have h := checkLog_sound (w := (10525154553 / 135525154553)) (n := 12)
    (lo := (155637407 / 1000000000)) (hi := (4863669 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73025154553 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73025154553 / 62500000000) = 1/(62500000000 / 73025154553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_598 : Bounds (155637407 / 1000000000) (4863669 / 31250000) (Real.log (73025154553 / 62500000000)) := by
  have h := reflection_log_598_neg
  have he : Real.log (73025154553 / 62500000000) = -Real.log (62500000000 / 73025154553) := by
    rw [show ((73025154553 / 62500000000) : ℝ) = ((62500000000 / 73025154553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_599_neg : (77822393 / 250000000) ≤ -Real.log (250000000000 / 341296121097) ∧
    -Real.log (250000000000 / 341296121097) ≤ (311289573 / 1000000000) := by
  have h := checkLog_sound (w := (91296121097 / 591296121097)) (n := 12)
    (lo := (77822393 / 250000000)) (hi := (311289573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341296121097 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341296121097 / 250000000000) = 1/(250000000000 / 341296121097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_599 : Bounds (77822393 / 250000000) (311289573 / 1000000000) (Real.log (341296121097 / 250000000000)) := by
  have h := reflection_log_599_neg
  have he : Real.log (341296121097 / 250000000000) = -Real.log (250000000000 / 341296121097) := by
    rw [show ((341296121097 / 250000000000) : ℝ) = ((250000000000 / 341296121097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_600_neg : (15574723 / 50000000) ≤ -Real.log (500000000000 / 682732111177) ∧
    -Real.log (500000000000 / 682732111177) ≤ (311494461 / 1000000000) := by
  have h := checkLog_sound (w := (182732111177 / 1182732111177)) (n := 12)
    (lo := (15574723 / 50000000)) (hi := (311494461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682732111177 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682732111177 / 500000000000) = 1/(500000000000 / 682732111177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_600 : Bounds (15574723 / 50000000) (311494461 / 1000000000) (Real.log (682732111177 / 500000000000)) := by
  have h := reflection_log_600_neg
  have he : Real.log (682732111177 / 500000000000) = -Real.log (500000000000 / 682732111177) := by
    rw [show ((682732111177 / 500000000000) : ℝ) = ((500000000000 / 682732111177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_601_neg : (143753963 / 1000000000) ≤ -Real.log (5000 / 5773) ∧
    -Real.log (5000 / 5773) ≤ (35938491 / 250000000) := by
  have h := checkLog_sound (w := (773 / 10773)) (n := 12)
    (lo := (143753963 / 1000000000)) (hi := (35938491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5773 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5773 / 5000) = 1/(5000 / 5773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_601 : Bounds (143753963 / 1000000000) (35938491 / 250000000) (Real.log (5773 / 5000)) := by
  have h := reflection_log_601_neg
  have he : Real.log (5773 / 5000) = -Real.log (5000 / 5773) := by
    rw [show ((5773 / 5000) : ℝ) = ((5000 / 5773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_602_neg : (16794539 / 100000000) ≤ -Real.log (4227 / 5000) ∧
    -Real.log (4227 / 5000) ≤ (167945391 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 9227)) (n := 12)
    (lo := (16794539 / 100000000)) (hi := (167945391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4227) = 1/(4227 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_602 : Bounds (-167945391 / 1000000000) (-16794539 / 100000000) (Real.log (4227 / 5000)) := by
  have h := reflection_log_602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_603_neg : (38647 / 250000000) ≤ -Real.log (5000000 / 5000773) ∧
    -Real.log (5000000 / 5000773) ≤ (154589 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 10000773)) (n := 12)
    (lo := (38647 / 250000000)) (hi := (154589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000773 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000773 / 5000000) = 1/(5000000 / 5000773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_603 : Bounds (38647 / 250000000) (154589 / 1000000000) (Real.log (5000773 / 5000000)) := by
  have h := reflection_log_603_neg
  have he : Real.log (5000773 / 5000000) = -Real.log (5000000 / 5000773) := by
    rw [show ((5000773 / 5000000) : ℝ) = ((5000000 / 5000773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_604_neg : (154611 / 1000000000) ≤ -Real.log (4999227 / 5000000) ∧
    -Real.log (4999227 / 5000000) ≤ (38653 / 250000000) := by
  have h := checkLog_sound (w := (773 / 9999227)) (n := 12)
    (lo := (154611 / 1000000000)) (hi := (38653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999227) = 1/(4999227 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_604 : Bounds (-38653 / 250000000) (-154611 / 1000000000) (Real.log (4999227 / 5000000)) := by
  have h := reflection_log_604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_605_neg : (74650039 / 1000000000) ≤ -Real.log (1000000 / 1077507) ∧
    -Real.log (1000000 / 1077507) ≤ (1866251 / 25000000) := by
  have h := checkLog_sound (w := (77507 / 2077507)) (n := 12)
    (lo := (74650039 / 1000000000)) (hi := (1866251 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077507 / 1000000) = 1/(1000000 / 1077507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_605 : Bounds (74650039 / 1000000000) (1866251 / 25000000) (Real.log (1077507 / 1000000)) := by
  have h := reflection_log_605_neg
  have he : Real.log (1077507 / 1000000) = -Real.log (1000000 / 1077507) := by
    rw [show ((1077507 / 1000000) : ℝ) = ((1000000 / 1077507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_606_neg : (80675491 / 1000000000) ≤ -Real.log (922493 / 1000000) ∧
    -Real.log (922493 / 1000000) ≤ (20168873 / 250000000) := by
  have h := checkLog_sound (w := (77507 / 1922493)) (n := 12)
    (lo := (80675491 / 1000000000)) (hi := (20168873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922493) = 1/(922493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_606 : Bounds (-20168873 / 250000000) (-80675491 / 1000000000) (Real.log (922493 / 1000000)) := by
  have h := reflection_log_606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_607_neg : (74841203 / 1000000000) ≤ -Real.log (1000000 / 1077713) ∧
    -Real.log (1000000 / 1077713) ≤ (18710301 / 250000000) := by
  have h := checkLog_sound (w := (77713 / 2077713)) (n := 12)
    (lo := (74841203 / 1000000000)) (hi := (18710301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077713 / 1000000) = 1/(1000000 / 1077713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_607 : Bounds (74841203 / 1000000000) (18710301 / 250000000) (Real.log (1077713 / 1000000)) := by
  have h := reflection_log_607_neg
  have he : Real.log (1077713 / 1000000) = -Real.log (1000000 / 1077713) := by
    rw [show ((1077713 / 1000000) : ℝ) = ((1000000 / 1077713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_608_neg : (10112353 / 125000000) ≤ -Real.log (922287 / 1000000) ∧
    -Real.log (922287 / 1000000) ≤ (3235953 / 40000000) := by
  have h := checkLog_sound (w := (77713 / 1922287)) (n := 12)
    (lo := (10112353 / 125000000)) (hi := (3235953 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922287) = 1/(922287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_608 : Bounds (-3235953 / 40000000) (-10112353 / 125000000) (Real.log (922287 / 1000000)) := by
  have h := reflection_log_608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_609_neg : (302881 / 50000000) ≤ -Real.log (993960689631 / 1000000000000) ∧
    -Real.log (993960689631 / 1000000000000) ≤ (6057621 / 1000000000) := by
  have h := checkLog_sound (w := (6039310369 / 1993960689631)) (n := 12)
    (lo := (302881 / 50000000)) (hi := (6057621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993960689631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993960689631) = 1/(993960689631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_609 : Bounds (-6057621 / 1000000000) (-302881 / 50000000) (Real.log (993960689631 / 1000000000000)) := by
  have h := reflection_log_609_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_610_neg : (6025451 / 1000000000) ≤ -Real.log (993992664951 / 1000000000000) ∧
    -Real.log (993992664951 / 1000000000000) ≤ (1506363 / 250000000) := by
  have h := checkLog_sound (w := (6007335049 / 1993992664951)) (n := 12)
    (lo := (6025451 / 1000000000)) (hi := (1506363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993992664951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993992664951) = 1/(993992664951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_610 : Bounds (-1506363 / 250000000) (-6025451 / 1000000000) (Real.log (993992664951 / 1000000000000)) := by
  have h := reflection_log_610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_611_neg : (15532553 / 100000000) ≤ -Real.log (500000000000 / 584019065727) ∧
    -Real.log (500000000000 / 584019065727) ≤ (155325531 / 1000000000) := by
  have h := checkLog_sound (w := (84019065727 / 1084019065727)) (n := 12)
    (lo := (15532553 / 100000000)) (hi := (155325531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584019065727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584019065727 / 500000000000) = 1/(500000000000 / 584019065727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_611 : Bounds (15532553 / 100000000) (155325531 / 1000000000) (Real.log (584019065727 / 500000000000)) := by
  have h := reflection_log_611_neg
  have he : Real.log (584019065727 / 500000000000) = -Real.log (500000000000 / 584019065727) := by
    rw [show ((584019065727 / 500000000000) : ℝ) = ((500000000000 / 584019065727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_612_neg : (155740027 / 1000000000) ≤ -Real.log (500000000000 / 584261189847) ∧
    -Real.log (500000000000 / 584261189847) ≤ (38935007 / 250000000) := by
  have h := checkLog_sound (w := (84261189847 / 1084261189847)) (n := 12)
    (lo := (155740027 / 1000000000)) (hi := (38935007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584261189847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584261189847 / 500000000000) = 1/(500000000000 / 584261189847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_612 : Bounds (155740027 / 1000000000) (38935007 / 250000000) (Real.log (584261189847 / 500000000000)) := by
  have h := reflection_log_612_neg
  have he : Real.log (584261189847 / 500000000000) = -Real.log (500000000000 / 584261189847) := by
    rw [show ((584261189847 / 500000000000) : ℝ) = ((500000000000 / 584261189847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_613_neg : (15574723 / 50000000) ≤ -Real.log (62500000000 / 85341513897) ∧
    -Real.log (62500000000 / 85341513897) ≤ (311494461 / 1000000000) := by
  have h := checkLog_sound (w := (22841513897 / 147841513897)) (n := 12)
    (lo := (15574723 / 50000000)) (hi := (311494461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85341513897 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85341513897 / 62500000000) = 1/(62500000000 / 85341513897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_613 : Bounds (15574723 / 50000000) (311494461 / 1000000000) (Real.log (85341513897 / 62500000000)) := by
  have h := reflection_log_613_neg
  have he : Real.log (85341513897 / 62500000000) = -Real.log (62500000000 / 85341513897) := by
    rw [show ((85341513897 / 62500000000) : ℝ) = ((62500000000 / 85341513897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_614_neg : (155849677 / 500000000) ≤ -Real.log (500000000000 / 682872013249) ∧
    -Real.log (500000000000 / 682872013249) ≤ (62339871 / 200000000) := by
  have h := checkLog_sound (w := (182872013249 / 1182872013249)) (n := 12)
    (lo := (155849677 / 500000000)) (hi := (62339871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682872013249 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682872013249 / 500000000000) = 1/(500000000000 / 682872013249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_614 : Bounds (155849677 / 500000000) (62339871 / 200000000) (Real.log (682872013249 / 500000000000)) := by
  have h := reflection_log_614_neg
  have he : Real.log (682872013249 / 500000000000) = -Real.log (500000000000 / 682872013249) := by
    rw [show ((682872013249 / 500000000000) : ℝ) = ((500000000000 / 682872013249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_615_neg : (143840569 / 1000000000) ≤ -Real.log (10000 / 11547) ∧
    -Real.log (10000 / 11547) ≤ (14384057 / 100000000) := by
  have h := checkLog_sound (w := (1547 / 21547)) (n := 12)
    (lo := (143840569 / 1000000000)) (hi := (14384057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11547 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11547 / 10000) = 1/(10000 / 11547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_615 : Bounds (143840569 / 1000000000) (14384057 / 100000000) (Real.log (11547 / 10000)) := by
  have h := reflection_log_615_neg
  have he : Real.log (11547 / 10000) = -Real.log (10000 / 11547) := by
    rw [show ((11547 / 10000) : ℝ) = ((10000 / 11547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_616_neg : (33612737 / 200000000) ≤ -Real.log (8453 / 10000) ∧
    -Real.log (8453 / 10000) ≤ (84031843 / 500000000) := by
  have h := checkLog_sound (w := (1547 / 18453)) (n := 12)
    (lo := (33612737 / 200000000)) (hi := (84031843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8453) = 1/(8453 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_616 : Bounds (-84031843 / 500000000) (-33612737 / 200000000) (Real.log (8453 / 10000)) := by
  have h := reflection_log_616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_617_neg : (2417 / 15625000) ≤ -Real.log (10000000 / 10001547) ∧
    -Real.log (10000000 / 10001547) ≤ (154689 / 1000000000) := by
  have h := checkLog_sound (w := (1547 / 20001547)) (n := 12)
    (lo := (2417 / 15625000)) (hi := (154689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001547 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001547 / 10000000) = 1/(10000000 / 10001547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_617 : Bounds (2417 / 15625000) (154689 / 1000000000) (Real.log (10001547 / 10000000)) := by
  have h := reflection_log_617_neg
  have he : Real.log (10001547 / 10000000) = -Real.log (10000000 / 10001547) := by
    rw [show ((10001547 / 10000000) : ℝ) = ((10000000 / 10001547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_618_neg : (154711 / 1000000000) ≤ -Real.log (9998453 / 10000000) ∧
    -Real.log (9998453 / 10000000) ≤ (19339 / 125000000) := by
  have h := checkLog_sound (w := (1547 / 19998453)) (n := 12)
    (lo := (154711 / 1000000000)) (hi := (19339 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998453) = 1/(9998453 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_618 : Bounds (-19339 / 125000000) (-154711 / 1000000000) (Real.log (9998453 / 10000000)) := by
  have h := reflection_log_618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_619_neg : (74697369 / 1000000000) ≤ -Real.log (500000 / 538779) ∧
    -Real.log (500000 / 538779) ≤ (7469737 / 100000000) := by
  have h := checkLog_sound (w := (38779 / 1038779)) (n := 12)
    (lo := (74697369 / 1000000000)) (hi := (7469737 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538779 / 500000) = 1/(500000 / 538779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_619 : Bounds (74697369 / 1000000000) (7469737 / 100000000) (Real.log (538779 / 500000)) := by
  have h := reflection_log_619_neg
  have he : Real.log (538779 / 500000) = -Real.log (500000 / 538779) := by
    rw [show ((538779 / 500000) : ℝ) = ((500000 / 538779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_620_neg : (80730777 / 1000000000) ≤ -Real.log (461221 / 500000) ∧
    -Real.log (461221 / 500000) ≤ (40365389 / 500000000) := by
  have h := checkLog_sound (w := (38779 / 961221)) (n := 12)
    (lo := (80730777 / 1000000000)) (hi := (40365389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461221) = 1/(461221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_620 : Bounds (-40365389 / 500000000) (-80730777 / 1000000000) (Real.log (461221 / 500000)) := by
  have h := reflection_log_620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_621_neg : (18722131 / 250000000) ≤ -Real.log (250000 / 269441) ∧
    -Real.log (250000 / 269441) ≤ (2995541 / 40000000) := by
  have h := checkLog_sound (w := (19441 / 519441)) (n := 12)
    (lo := (18722131 / 250000000)) (hi := (2995541 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269441 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269441 / 250000) = 1/(250000 / 269441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_621 : Bounds (18722131 / 250000000) (2995541 / 40000000) (Real.log (269441 / 250000)) := by
  have h := reflection_log_621_neg
  have he : Real.log (269441 / 250000) = -Real.log (250000 / 269441) := by
    rw [show ((269441 / 250000) : ℝ) = ((250000 / 269441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_622_neg : (40477061 / 500000000) ≤ -Real.log (230559 / 250000) ∧
    -Real.log (230559 / 250000) ≤ (80954123 / 1000000000) := by
  have h := checkLog_sound (w := (19441 / 480559)) (n := 12)
    (lo := (40477061 / 500000000)) (hi := (80954123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230559) = 1/(230559 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_622 : Bounds (-80954123 / 1000000000) (-40477061 / 500000000) (Real.log (230559 / 250000)) := by
  have h := reflection_log_622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_623_neg : (3032799 / 500000000) ≤ -Real.log (62122047519 / 62500000000) ∧
    -Real.log (62122047519 / 62500000000) ≤ (6065599 / 1000000000) := by
  have h := checkLog_sound (w := (377952481 / 124622047519)) (n := 12)
    (lo := (3032799 / 500000000)) (hi := (6065599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62122047519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62122047519) = 1/(62122047519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_623 : Bounds (-6065599 / 1000000000) (-3032799 / 500000000) (Real.log (62122047519 / 62500000000)) := by
  have h := reflection_log_623_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_624_neg : (6033407 / 1000000000) ≤ -Real.log (248496189159 / 250000000000) ∧
    -Real.log (248496189159 / 250000000000) ≤ (11784 / 1953125) := by
  have h := checkLog_sound (w := (1503810841 / 498496189159)) (n := 12)
    (lo := (6033407 / 1000000000)) (hi := (11784 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248496189159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248496189159) = 1/(248496189159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_624 : Bounds (-11784 / 1953125) (-6033407 / 1000000000) (Real.log (248496189159 / 250000000000)) := by
  have h := reflection_log_624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_625_neg : (155428147 / 1000000000) ≤ -Real.log (125000000000 / 146019749751) ∧
    -Real.log (125000000000 / 146019749751) ≤ (38857037 / 250000000) := by
  have h := checkLog_sound (w := (21019749751 / 271019749751)) (n := 12)
    (lo := (155428147 / 1000000000)) (hi := (38857037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146019749751 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146019749751 / 125000000000) = 1/(125000000000 / 146019749751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_625 : Bounds (155428147 / 1000000000) (38857037 / 250000000) (Real.log (146019749751 / 125000000000)) := by
  have h := reflection_log_625_neg
  have he : Real.log (146019749751 / 125000000000) = -Real.log (125000000000 / 146019749751) := by
    rw [show ((146019749751 / 125000000000) : ℝ) = ((125000000000 / 146019749751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_626_neg : (155842647 / 1000000000) ≤ -Real.log (500000000000 / 584321149901) ∧
    -Real.log (500000000000 / 584321149901) ≤ (19480331 / 125000000) := by
  have h := checkLog_sound (w := (84321149901 / 1084321149901)) (n := 12)
    (lo := (155842647 / 1000000000)) (hi := (19480331 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584321149901 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584321149901 / 500000000000) = 1/(500000000000 / 584321149901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_626 : Bounds (155842647 / 1000000000) (19480331 / 125000000) (Real.log (584321149901 / 500000000000)) := by
  have h := reflection_log_626_neg
  have he : Real.log (584321149901 / 500000000000) = -Real.log (500000000000 / 584321149901) := by
    rw [show ((584321149901 / 500000000000) : ℝ) = ((500000000000 / 584321149901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_627_neg : (155849677 / 500000000) ≤ -Real.log (7812500000 / 10669875207) ∧
    -Real.log (7812500000 / 10669875207) ≤ (62339871 / 200000000) := by
  have h := checkLog_sound (w := (2857375207 / 18482375207)) (n := 12)
    (lo := (155849677 / 500000000)) (hi := (62339871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10669875207 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10669875207 / 7812500000) = 1/(7812500000 / 10669875207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_627 : Bounds (155849677 / 500000000) (62339871 / 200000000) (Real.log (10669875207 / 7812500000)) := by
  have h := reflection_log_627_neg
  have he : Real.log (10669875207 / 7812500000) = -Real.log (7812500000 / 10669875207) := by
    rw [show ((10669875207 / 7812500000) : ℝ) = ((7812500000 / 10669875207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_628_neg : (62380851 / 200000000) ≤ -Real.log (500000000000 / 683011948421) ∧
    -Real.log (500000000000 / 683011948421) ≤ (609188 / 1953125) := by
  have h := checkLog_sound (w := (183011948421 / 1183011948421)) (n := 12)
    (lo := (62380851 / 200000000)) (hi := (609188 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683011948421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683011948421 / 500000000000) = 1/(500000000000 / 683011948421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_628 : Bounds (62380851 / 200000000) (609188 / 1953125) (Real.log (683011948421 / 500000000000)) := by
  have h := reflection_log_628_neg
  have he : Real.log (683011948421 / 500000000000) = -Real.log (500000000000 / 683011948421) := by
    rw [show ((683011948421 / 500000000000) : ℝ) = ((500000000000 / 683011948421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_629_neg : (1124431 / 7812500) ≤ -Real.log (2500 / 2887) ∧
    -Real.log (2500 / 2887) ≤ (143927169 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 5387)) (n := 12)
    (lo := (1124431 / 7812500)) (hi := (143927169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2887 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2887 / 2500) = 1/(2500 / 2887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_629 : Bounds (1124431 / 7812500) (143927169 / 1000000000) (Real.log (2887 / 2500)) := by
  have h := reflection_log_629_neg
  have he : Real.log (2887 / 2500) = -Real.log (2500 / 2887) := by
    rw [show ((2887 / 2500) : ℝ) = ((2500 / 2887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_630_neg : (168181993 / 1000000000) ≤ -Real.log (2113 / 2500) ∧
    -Real.log (2113 / 2500) ≤ (84090997 / 500000000) := by
  have h := checkLog_sound (w := (387 / 4613)) (n := 12)
    (lo := (168181993 / 1000000000)) (hi := (84090997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2113) = 1/(2113 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_630 : Bounds (-84090997 / 500000000) (-168181993 / 1000000000) (Real.log (2113 / 2500)) := by
  have h := reflection_log_630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_631_neg : (38697 / 250000000) ≤ -Real.log (2500000 / 2500387) ∧
    -Real.log (2500000 / 2500387) ≤ (154789 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 5000387)) (n := 12)
    (lo := (38697 / 250000000)) (hi := (154789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500387 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500387 / 2500000) = 1/(2500000 / 2500387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_631 : Bounds (38697 / 250000000) (154789 / 1000000000) (Real.log (2500387 / 2500000)) := by
  have h := reflection_log_631_neg
  have he : Real.log (2500387 / 2500000) = -Real.log (2500000 / 2500387) := by
    rw [show ((2500387 / 2500000) : ℝ) = ((2500000 / 2500387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_632_neg : (154811 / 1000000000) ≤ -Real.log (2499613 / 2500000) ∧
    -Real.log (2499613 / 2500000) ≤ (38703 / 250000000) := by
  have h := checkLog_sound (w := (387 / 4999613)) (n := 12)
    (lo := (154811 / 1000000000)) (hi := (38703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499613) = 1/(2499613 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_632 : Bounds (-38703 / 250000000) (-154811 / 1000000000) (Real.log (2499613 / 2500000)) := by
  have h := reflection_log_632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_633_neg : (74744697 / 1000000000) ≤ -Real.log (1000000 / 1077609) ∧
    -Real.log (1000000 / 1077609) ≤ (37372349 / 500000000) := by
  have h := checkLog_sound (w := (77609 / 2077609)) (n := 12)
    (lo := (74744697 / 1000000000)) (hi := (37372349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077609 / 1000000) = 1/(1000000 / 1077609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_633 : Bounds (74744697 / 1000000000) (37372349 / 500000000) (Real.log (1077609 / 1000000)) := by
  have h := reflection_log_633_neg
  have he : Real.log (1077609 / 1000000) = -Real.log (1000000 / 1077609) := by
    rw [show ((1077609 / 1000000) : ℝ) = ((1000000 / 1077609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_634_neg : (80786067 / 1000000000) ≤ -Real.log (922391 / 1000000) ∧
    -Real.log (922391 / 1000000) ≤ (20196517 / 250000000) := by
  have h := checkLog_sound (w := (77609 / 1922391)) (n := 12)
    (lo := (80786067 / 1000000000)) (hi := (20196517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922391) = 1/(922391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_634 : Bounds (-20196517 / 250000000) (-80786067 / 1000000000) (Real.log (922391 / 1000000)) := by
  have h := reflection_log_634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_635_neg : (14986983 / 200000000) ≤ -Real.log (500000 / 538907) ∧
    -Real.log (500000 / 538907) ≤ (18733729 / 250000000) := by
  have h := checkLog_sound (w := (38907 / 1038907)) (n := 12)
    (lo := (14986983 / 200000000)) (hi := (18733729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538907 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538907 / 500000) = 1/(500000 / 538907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_635 : Bounds (14986983 / 200000000) (18733729 / 250000000) (Real.log (538907 / 500000)) := by
  have h := reflection_log_635_neg
  have he : Real.log (538907 / 500000) = -Real.log (500000 / 538907) := by
    rw [show ((538907 / 500000) : ℝ) = ((500000 / 538907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_636_neg : (4050417 / 50000000) ≤ -Real.log (461093 / 500000) ∧
    -Real.log (461093 / 500000) ≤ (81008341 / 1000000000) := by
  have h := checkLog_sound (w := (38907 / 961093)) (n := 12)
    (lo := (4050417 / 50000000)) (hi := (81008341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461093) = 1/(461093 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_636 : Bounds (-81008341 / 1000000000) (-4050417 / 50000000) (Real.log (461093 / 500000)) := by
  have h := reflection_log_636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_637_neg : (379589 / 62500000) ≤ -Real.log (248486245351 / 250000000000) ∧
    -Real.log (248486245351 / 250000000000) ≤ (242937 / 40000000) := by
  have h := checkLog_sound (w := (1513754649 / 498486245351)) (n := 12)
    (lo := (379589 / 62500000)) (hi := (242937 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248486245351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248486245351) = 1/(248486245351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_637 : Bounds (-242937 / 40000000) (-379589 / 62500000) (Real.log (248486245351 / 250000000000)) := by
  have h := reflection_log_637_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_638_neg : (6041369 / 1000000000) ≤ -Real.log (993976843119 / 1000000000000) ∧
    -Real.log (993976843119 / 1000000000000) ≤ (604137 / 100000000) := by
  have h := checkLog_sound (w := (6023156881 / 1993976843119)) (n := 12)
    (lo := (6041369 / 1000000000)) (hi := (604137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993976843119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993976843119) = 1/(993976843119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_638 : Bounds (-604137 / 100000000) (-6041369 / 1000000000) (Real.log (993976843119 / 1000000000000)) := by
  have h := reflection_log_638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_639_neg : (31106153 / 200000000) ≤ -Real.log (500000000000 / 584138938909) ∧
    -Real.log (500000000000 / 584138938909) ≤ (77765383 / 500000000) := by
  have h := checkLog_sound (w := (84138938909 / 1084138938909)) (n := 12)
    (lo := (31106153 / 200000000)) (hi := (77765383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584138938909 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584138938909 / 500000000000) = 1/(500000000000 / 584138938909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_639 : Bounds (31106153 / 200000000) (77765383 / 500000000) (Real.log (584138938909 / 500000000000)) := by
  have h := reflection_log_639_neg
  have he : Real.log (584138938909 / 500000000000) = -Real.log (500000000000 / 584138938909) := by
    rw [show ((584138938909 / 500000000000) : ℝ) = ((500000000000 / 584138938909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


