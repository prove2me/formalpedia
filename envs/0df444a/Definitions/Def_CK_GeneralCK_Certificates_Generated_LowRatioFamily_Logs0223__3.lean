-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0223__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0223__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T00:31:46.034603+00:00
-- url     : https://prove2.me/theorems/b657188a-50b3-4002-a15d-bea821ccb3a2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0223 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0224, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0223 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0224, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0225)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0223 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0224, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0225)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0223 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0224, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0225) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0223 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0224, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0225).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0223 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14272_neg : (313503689 / 500000000) ≤ -Real.log (125 / 234) ∧
    -Real.log (125 / 234) ≤ (627007379 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 359)) (n := 12)
    (lo := (313503689 / 500000000)) (hi := (627007379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234 / 125) = 1/(125 / 234) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14272 : Bounds (313503689 / 500000000) (627007379 / 1000000000) (Real.log (234 / 125)) := by
  have h := reflection_log_14272_neg
  have he : Real.log (234 / 125) = -Real.log (125 / 234) := by
    rw [show ((234 / 125) : ℝ) = ((125 / 234) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14273_neg : (2055725013 / 1000000000) ≤ -Real.log (16 / 125) ∧
    -Real.log (16 / 125) ≤ (256965627 / 125000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 64) = 1/(16 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14273 : Bounds (-256965627 / 125000000) (-2055725013 / 1000000000) (Real.log (16 / 125)) := by
  have h := reflection_log_14273_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14274_neg : (43581 / 50000000) ≤ -Real.log (125000 / 125109) ∧
    -Real.log (125000 / 125109) ≤ (871621 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 250109)) (n := 12)
    (lo := (43581 / 50000000)) (hi := (871621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125109 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125109 / 125000) = 1/(125000 / 125109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14274 : Bounds (43581 / 50000000) (871621 / 1000000000) (Real.log (125109 / 125000)) := by
  have h := reflection_log_14274_neg
  have he : Real.log (125109 / 125000) = -Real.log (125000 / 125109) := by
    rw [show ((125109 / 125000) : ℝ) = ((125000 / 125109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14275_neg : (43619 / 50000000) ≤ -Real.log (124891 / 125000) ∧
    -Real.log (124891 / 125000) ≤ (872381 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 249891)) (n := 12)
    (lo := (43619 / 50000000)) (hi := (872381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124891) = 1/(124891 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14275 : Bounds (-872381 / 1000000000) (-43619 / 50000000) (Real.log (124891 / 125000)) := by
  have h := reflection_log_14275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14276_neg : (51890951 / 125000000) ≤ -Real.log (250000 / 378641) ∧
    -Real.log (250000 / 378641) ≤ (415127609 / 1000000000) := by
  have h := checkLog_sound (w := (128641 / 628641)) (n := 12)
    (lo := (51890951 / 125000000)) (hi := (415127609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((378641 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(378641 / 250000) = 1/(250000 / 378641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14276 : Bounds (51890951 / 125000000) (415127609 / 1000000000) (Real.log (378641 / 250000)) := by
  have h := reflection_log_14276_neg
  have he : Real.log (378641 / 250000) = -Real.log (250000 / 378641) := by
    rw [show ((378641 / 250000) : ℝ) = ((250000 / 378641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14277_neg : (361353911 / 500000000) ≤ -Real.log (121359 / 250000) ∧
    -Real.log (121359 / 250000) ≤ (45169239 / 62500000) := by
  have h := checkLog_sound (w := (3641 / 246359)) (n := 12)
    (lo := (14780321 / 500000000)) (hi := (29560643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 121359) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 121359) = 1/(121359 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14277 : Bounds (-45169239 / 62500000) (-361353911 / 500000000) (Real.log (121359 / 250000)) := by
  have h := reflection_log_14277_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14278_neg : (83458313 / 200000000) ≤ -Real.log (200000 / 303569) ∧
    -Real.log (200000 / 303569) ≤ (208645783 / 500000000) := by
  have h := checkLog_sound (w := (103569 / 503569)) (n := 12)
    (lo := (83458313 / 200000000)) (hi := (208645783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303569 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303569 / 200000) = 1/(200000 / 303569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14278 : Bounds (83458313 / 200000000) (208645783 / 500000000) (Real.log (303569 / 200000)) := by
  have h := reflection_log_14278_neg
  have he : Real.log (303569 / 200000) = -Real.log (200000 / 303569) := by
    rw [show ((303569 / 200000) : ℝ) = ((200000 / 303569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14279_neg : (729489639 / 1000000000) ≤ -Real.log (96431 / 200000) ∧
    -Real.log (96431 / 200000) ≤ (729489641 / 1000000000) := by
  have h := checkLog_sound (w := (3569 / 196431)) (n := 12)
    (lo := (36342459 / 1000000000)) (hi := (1817123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 96431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 96431) = 1/(96431 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14279 : Bounds (-729489641 / 1000000000) (-729489639 / 1000000000) (Real.log (96431 / 200000)) := by
  have h := reflection_log_14279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14280_neg : (156099037 / 500000000) ≤ -Real.log (29273462239 / 40000000000) ∧
    -Real.log (29273462239 / 40000000000) ≤ (12487923 / 40000000) := by
  have h := checkLog_sound (w := (10726537761 / 69273462239)) (n := 12)
    (lo := (156099037 / 500000000)) (hi := (12487923 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 29273462239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 29273462239) = 1/(29273462239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14280 : Bounds (-12487923 / 40000000) (-156099037 / 500000000) (Real.log (29273462239 / 40000000000)) := by
  have h := reflection_log_14280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14281_neg : (153790107 / 500000000) ≤ -Real.log (45951493119 / 62500000000) ∧
    -Real.log (45951493119 / 62500000000) ≤ (61516043 / 200000000) := by
  have h := checkLog_sound (w := (16548506881 / 108451493119)) (n := 12)
    (lo := (153790107 / 500000000)) (hi := (61516043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 45951493119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 45951493119) = 1/(45951493119 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14281 : Bounds (-61516043 / 200000000) (-153790107 / 500000000) (Real.log (45951493119 / 62500000000)) := by
  have h := reflection_log_14281_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14282_neg : (1137835431 / 1000000000) ≤ -Real.log (250000000000 / 780001895203) ∧
    -Real.log (250000000000 / 780001895203) ≤ (1137835433 / 1000000000) := by
  have h := checkLog_sound (w := (280001895203 / 1280001895203)) (n := 12)
    (lo := (444688251 / 1000000000)) (hi := (111172063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780001895203 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(780001895203 / 500000000000) = 1/(250000000000 / 780001895203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14282 : Bounds (1137835431 / 1000000000) (1137835433 / 1000000000) (Real.log (780001895203 / 250000000000)) := by
  have h := reflection_log_14282_neg
  have he : Real.log (780001895203 / 250000000000) = -Real.log (250000000000 / 780001895203) := by
    rw [show ((780001895203 / 250000000000) : ℝ) = ((250000000000 / 780001895203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14283_neg : (229356241 / 200000000) ≤ -Real.log (10000000000 / 31480436789) ∧
    -Real.log (10000000000 / 31480436789) ≤ (1146781207 / 1000000000) := by
  have h := checkLog_sound (w := (11480436789 / 51480436789)) (n := 12)
    (lo := (18145361 / 40000000)) (hi := (226817013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31480436789 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31480436789 / 20000000000) = 1/(10000000000 / 31480436789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14283 : Bounds (229356241 / 200000000) (1146781207 / 1000000000) (Real.log (31480436789 / 10000000000)) := by
  have h := reflection_log_14283_neg
  have he : Real.log (31480436789 / 10000000000) = -Real.log (10000000000 / 31480436789) := by
    rw [show ((31480436789 / 10000000000) : ℝ) = ((10000000000 / 31480436789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14284_neg : (1328980741 / 500000000) ≤ -Real.log (500000000000 / 7133587786259) ∧
    -Real.log (500000000000 / 7133587786259) ≤ (1328980743 / 500000000) := by
  have h := checkLog_sound (w := (3133587786259 / 11133587786259)) (n := 12)
    (lo := (289259971 / 500000000)) (hi := (578519943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7133587786259 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7133587786259 / 4000000000000) = 1/(500000000000 / 7133587786259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14284 : Bounds (1328980741 / 500000000) (1328980743 / 500000000) (Real.log (7133587786259 / 500000000000)) := by
  have h := reflection_log_14284_neg
  have he : Real.log (7133587786259 / 500000000000) = -Real.log (500000000000 / 7133587786259) := by
    rw [show ((7133587786259 / 500000000000) : ℝ) = ((500000000000 / 7133587786259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14285_neg : (2682732391 / 1000000000) ≤ -Real.log (8 / 117) ∧
    -Real.log (8 / 117) ≤ (536546479 / 200000000) := by
  have h := checkLog_sound (w := (53 / 181)) (n := 12)
    (lo := (603290851 / 1000000000)) (hi := (150822713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117 / 64) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(117 / 64) = 1/(8 / 117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14285 : Bounds (2682732391 / 1000000000) (536546479 / 200000000) (Real.log (117 / 8)) := by
  have h := reflection_log_14285_neg
  have he : Real.log (117 / 8) = -Real.log (8 / 117) := by
    rw [show ((117 / 8) : ℝ) = ((8 / 117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14286_neg : (628608659 / 1000000000) ≤ -Real.log (8 / 15) ∧
    -Real.log (8 / 15) ≤ (31430433 / 50000000) := by
  have h := checkLog_sound (w := (7 / 23)) (n := 12)
    (lo := (628608659 / 1000000000)) (hi := (31430433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15 / 8) = 1/(8 / 15) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14286 : Bounds (628608659 / 1000000000) (31430433 / 50000000) (Real.log (15 / 8)) := by
  have h := reflection_log_14286_neg
  have he : Real.log (15 / 8) = -Real.log (8 / 15) := by
    rw [show ((15 / 8) : ℝ) = ((8 / 15) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14287_neg : (103972077 / 50000000) ≤ -Real.log (1 / 8) ∧
    -Real.log (1 / 8) ≤ (2079441543 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2 / 1) = 1/(1 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14287 : Bounds (-2079441543 / 1000000000) (-103972077 / 50000000) (Real.log (1 / 8)) := by
  have h := reflection_log_14287_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14288_neg : (874617 / 1000000000) ≤ -Real.log (8000 / 8007) ∧
    -Real.log (8000 / 8007) ≤ (437309 / 500000000) := by
  have h := checkLog_sound (w := (7 / 16007)) (n := 12)
    (lo := (874617 / 1000000000)) (hi := (437309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8007 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8007 / 8000) = 1/(8000 / 8007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14288 : Bounds (874617 / 1000000000) (437309 / 500000000) (Real.log (8007 / 8000)) := by
  have h := reflection_log_14288_neg
  have he : Real.log (8007 / 8000) = -Real.log (8000 / 8007) := by
    rw [show ((8007 / 8000) : ℝ) = ((8000 / 8007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14289_neg : (875383 / 1000000000) ≤ -Real.log (7993 / 8000) ∧
    -Real.log (7993 / 8000) ≤ (109423 / 125000000) := by
  have h := checkLog_sound (w := (7 / 15993)) (n := 12)
    (lo := (875383 / 1000000000)) (hi := (109423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 7993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 7993) = 1/(7993 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14289 : Bounds (-109423 / 125000000) (-875383 / 1000000000) (Real.log (7993 / 8000)) := by
  have h := reflection_log_14289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14290_neg : (416846757 / 1000000000) ≤ -Real.log (100000 / 151717) ∧
    -Real.log (100000 / 151717) ≤ (208423379 / 500000000) := by
  have h := checkLog_sound (w := (51717 / 251717)) (n := 12)
    (lo := (416846757 / 1000000000)) (hi := (208423379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151717 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151717 / 100000) = 1/(100000 / 151717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14290 : Bounds (416846757 / 1000000000) (208423379 / 500000000) (Real.log (151717 / 100000)) := by
  have h := reflection_log_14290_neg
  have he : Real.log (151717 / 100000) = -Real.log (100000 / 151717) := by
    rw [show ((151717 / 100000) : ℝ) = ((100000 / 151717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14291_neg : (728090653 / 1000000000) ≤ -Real.log (48283 / 100000) ∧
    -Real.log (48283 / 100000) ≤ (145618131 / 200000000) := by
  have h := checkLog_sound (w := (1717 / 98283)) (n := 12)
    (lo := (34943473 / 1000000000)) (hi := (17471737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 48283) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 48283) = 1/(48283 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14291 : Bounds (-145618131 / 200000000) (-728090653 / 1000000000) (Real.log (48283 / 100000)) := by
  have h := reflection_log_14291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14292_neg : (209509091 / 500000000) ≤ -Real.log (250000 / 380117) ∧
    -Real.log (250000 / 380117) ≤ (419018183 / 1000000000) := by
  have h := checkLog_sound (w := (130117 / 630117)) (n := 12)
    (lo := (209509091 / 500000000)) (hi := (419018183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380117 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380117 / 250000) = 1/(250000 / 380117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14292 : Bounds (209509091 / 500000000) (419018183 / 1000000000) (Real.log (380117 / 250000)) := by
  have h := reflection_log_14292_neg
  have he : Real.log (380117 / 250000) = -Real.log (250000 / 380117) := by
    rw [show ((380117 / 250000) : ℝ) = ((250000 / 380117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14293_neg : (14698893 / 20000000) ≤ -Real.log (119883 / 250000) ∧
    -Real.log (119883 / 250000) ≤ (183736163 / 250000000) := by
  have h := checkLog_sound (w := (5117 / 244883)) (n := 12)
    (lo := (4179747 / 100000000)) (hi := (41797471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 119883) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 119883) = 1/(119883 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14293 : Bounds (-183736163 / 250000000) (-14698893 / 20000000) (Real.log (119883 / 250000)) := by
  have h := reflection_log_14293_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14294_neg : (78981617 / 250000000) ≤ -Real.log (45569566311 / 62500000000) ∧
    -Real.log (45569566311 / 62500000000) ≤ (315926469 / 1000000000) := by
  have h := checkLog_sound (w := (16930433689 / 108069566311)) (n := 12)
    (lo := (78981617 / 250000000)) (hi := (315926469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 45569566311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 45569566311) = 1/(45569566311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14294 : Bounds (-315926469 / 1000000000) (-78981617 / 250000000) (Real.log (45569566311 / 62500000000)) := by
  have h := reflection_log_14294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14295_neg : (38905487 / 125000000) ≤ -Real.log (7325351911 / 10000000000) ∧
    -Real.log (7325351911 / 10000000000) ≤ (311243897 / 1000000000) := by
  have h := checkLog_sound (w := (2674648089 / 17325351911)) (n := 12)
    (lo := (38905487 / 125000000)) (hi := (311243897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 7325351911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 7325351911) = 1/(7325351911 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14295 : Bounds (-311243897 / 1000000000) (-38905487 / 125000000) (Real.log (7325351911 / 10000000000)) := by
  have h := reflection_log_14295_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14296_neg : (114493741 / 100000000) ≤ -Real.log (125000000000 / 392780585299) ∧
    -Real.log (125000000000 / 392780585299) ≤ (286234353 / 250000000) := by
  have h := checkLog_sound (w := (142780585299 / 642780585299)) (n := 12)
    (lo := (45179023 / 100000000)) (hi := (451790231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392780585299 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(392780585299 / 250000000000) = 1/(125000000000 / 392780585299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14296 : Bounds (114493741 / 100000000) (286234353 / 250000000) (Real.log (392780585299 / 125000000000)) := by
  have h := reflection_log_14296_neg
  have he : Real.log (392780585299 / 125000000000) = -Real.log (125000000000 / 392780585299) := by
    rw [show ((392780585299 / 125000000000) : ℝ) = ((125000000000 / 392780585299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14297_neg : (72122677 / 62500000) ≤ -Real.log (100000000000 / 317073313147) ∧
    -Real.log (100000000000 / 317073313147) ≤ (576981417 / 500000000) := by
  have h := checkLog_sound (w := (117073313147 / 517073313147)) (n := 12)
    (lo := (115203913 / 250000000)) (hi := (460815653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317073313147 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(317073313147 / 200000000000) = 1/(100000000000 / 317073313147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14297 : Bounds (72122677 / 62500000) (576981417 / 500000000) (Real.log (317073313147 / 100000000000)) := by
  have h := reflection_log_14297_neg
  have he : Real.log (317073313147 / 100000000000) = -Real.log (100000000000 / 317073313147) := by
    rw [show ((317073313147 / 100000000000) : ℝ) = ((100000000000 / 317073313147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14298_neg : (2708050199 / 1000000000) ≤ -Real.log (1 / 15) ∧
    -Real.log (1 / 15) ≤ (2708050203 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 23)) (n := 12)
    (lo := (628608659 / 1000000000)) (hi := (31430433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15 / 8) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15 / 8) = 1/(1 / 15) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14298 : Bounds (2708050199 / 1000000000) (2708050203 / 1000000000) (Real.log (15 / 1)) := by
  have h := reflection_log_14298_neg
  have he : Real.log (15 / 1) = -Real.log (1 / 15) := by
    rw [show ((15 / 1) : ℝ) = ((1 / 15) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14299_neg : (31510369 / 50000000) ≤ -Real.log (500 / 939) ∧
    -Real.log (500 / 939) ≤ (630207381 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1439)) (n := 12)
    (lo := (31510369 / 50000000)) (hi := (630207381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939 / 500) = 1/(500 / 939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14299 : Bounds (31510369 / 50000000) (630207381 / 1000000000) (Real.log (939 / 500)) := by
  have h := reflection_log_14299_neg
  have he : Real.log (939 / 500) = -Real.log (500 / 939) := by
    rw [show ((939 / 500) : ℝ) = ((500 / 939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14300_neg : (262966779 / 125000000) ≤ -Real.log (61 / 500) ∧
    -Real.log (61 / 500) ≤ (525933559 / 250000000) := by
  have h := checkLog_sound (w := (3 / 247)) (n := 12)
    (lo := (6073173 / 250000000)) (hi := (24292693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 122) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 122) = 1/(61 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14300 : Bounds (-525933559 / 250000000) (-262966779 / 125000000) (Real.log (61 / 500)) := by
  have h := reflection_log_14300_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14301_neg : (438807 / 500000000) ≤ -Real.log (500000 / 500439) ∧
    -Real.log (500000 / 500439) ≤ (175523 / 200000000) := by
  have h := checkLog_sound (w := (439 / 1000439)) (n := 12)
    (lo := (438807 / 500000000)) (hi := (175523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500439 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500439 / 500000) = 1/(500000 / 500439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14301 : Bounds (438807 / 500000000) (175523 / 200000000) (Real.log (500439 / 500000)) := by
  have h := reflection_log_14301_neg
  have he : Real.log (500439 / 500000) = -Real.log (500000 / 500439) := by
    rw [show ((500439 / 500000) : ℝ) = ((500000 / 500439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14302_neg : (175677 / 200000000) ≤ -Real.log (499561 / 500000) ∧
    -Real.log (499561 / 500000) ≤ (439193 / 500000000) := by
  have h := checkLog_sound (w := (439 / 999561)) (n := 12)
    (lo := (175677 / 200000000)) (hi := (439193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499561) = 1/(499561 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14302 : Bounds (-439193 / 500000000) (-175677 / 200000000) (Real.log (499561 / 500000)) := by
  have h := reflection_log_14302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14303_neg : (418574141 / 1000000000) ≤ -Real.log (1000000 / 1519793) ∧
    -Real.log (1000000 / 1519793) ≤ (209287071 / 500000000) := by
  have h := checkLog_sound (w := (519793 / 2519793)) (n := 12)
    (lo := (418574141 / 1000000000)) (hi := (209287071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1519793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1519793 / 1000000) = 1/(1000000 / 1519793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14303 : Bounds (418574141 / 1000000000) (209287071 / 500000000) (Real.log (1519793 / 1000000)) := by
  have h := reflection_log_14303_neg
  have he : Real.log (1519793 / 1000000) = -Real.log (1000000 / 1519793) := by
    rw [show ((1519793 / 1000000) : ℝ) = ((1000000 / 1519793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14304_neg : (733538017 / 1000000000) ≤ -Real.log (480207 / 1000000) ∧
    -Real.log (480207 / 1000000) ≤ (733538019 / 1000000000) := by
  have h := checkLog_sound (w := (19793 / 980207)) (n := 12)
    (lo := (40390837 / 1000000000)) (hi := (20195419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 480207) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 480207) = 1/(480207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14304 : Bounds (-733538019 / 1000000000) (-733538017 / 1000000000) (Real.log (480207 / 1000000)) := by
  have h := reflection_log_14304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14305_neg : (420752327 / 1000000000) ≤ -Real.log (1000000 / 1523107) ∧
    -Real.log (1000000 / 1523107) ≤ (52594041 / 125000000) := by
  have h := checkLog_sound (w := (523107 / 2523107)) (n := 12)
    (lo := (420752327 / 1000000000)) (hi := (52594041 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1523107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1523107 / 1000000) = 1/(1000000 / 1523107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14305 : Bounds (420752327 / 1000000000) (52594041 / 125000000) (Real.log (1523107 / 1000000)) := by
  have h := reflection_log_14305_neg
  have he : Real.log (1523107 / 1000000) = -Real.log (1000000 / 1523107) := by
    rw [show ((1523107 / 1000000) : ℝ) = ((1000000 / 1523107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14306_neg : (740463131 / 1000000000) ≤ -Real.log (476893 / 1000000) ∧
    -Real.log (476893 / 1000000) ≤ (740463133 / 1000000000) := by
  have h := checkLog_sound (w := (23107 / 976893)) (n := 12)
    (lo := (47315951 / 1000000000)) (hi := (2957247 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 476893) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 476893) = 1/(476893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14306 : Bounds (-740463133 / 1000000000) (-740463131 / 1000000000) (Real.log (476893 / 1000000)) := by
  have h := reflection_log_14306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14307_neg : (79927701 / 250000000) ≤ -Real.log (726359066551 / 1000000000000) ∧
    -Real.log (726359066551 / 1000000000000) ≤ (63942161 / 200000000) := by
  have h := checkLog_sound (w := (273640933449 / 1726359066551)) (n := 12)
    (lo := (79927701 / 250000000)) (hi := (63942161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 726359066551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 726359066551) = 1/(726359066551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14307 : Bounds (-63942161 / 200000000) (-79927701 / 250000000) (Real.log (726359066551 / 1000000000000)) := by
  have h := reflection_log_14307_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14308_neg : (78740969 / 250000000) ≤ -Real.log (729815237151 / 1000000000000) ∧
    -Real.log (729815237151 / 1000000000000) ≤ (314963877 / 1000000000) := by
  have h := checkLog_sound (w := (270184762849 / 1729815237151)) (n := 12)
    (lo := (78740969 / 250000000)) (hi := (314963877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 729815237151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 729815237151) = 1/(729815237151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14308 : Bounds (-314963877 / 1000000000) (-78740969 / 250000000) (Real.log (729815237151 / 1000000000000)) := by
  have h := reflection_log_14308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14309_neg : (576056079 / 500000000) ≤ -Real.log (500000000000 / 1582435283117) ∧
    -Real.log (500000000000 / 1582435283117) ≤ (7200701 / 6250000) := by
  have h := checkLog_sound (w := (582435283117 / 2582435283117)) (n := 12)
    (lo := (229482489 / 500000000)) (hi := (458964979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1582435283117 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1582435283117 / 1000000000000) = 1/(500000000000 / 1582435283117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14309 : Bounds (576056079 / 500000000) (7200701 / 6250000) (Real.log (1582435283117 / 500000000000)) := by
  have h := reflection_log_14309_neg
  have he : Real.log (1582435283117 / 500000000000) = -Real.log (500000000000 / 1582435283117) := by
    rw [show ((1582435283117 / 500000000000) : ℝ) = ((500000000000 / 1582435283117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14310_neg : (580607729 / 500000000) ≤ -Real.log (500000000000 / 1596906433939) ∧
    -Real.log (500000000000 / 1596906433939) ≤ (58060773 / 50000000) := by
  have h := checkLog_sound (w := (596906433939 / 2596906433939)) (n := 12)
    (lo := (234034139 / 500000000)) (hi := (468068279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1596906433939 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1596906433939 / 1000000000000) = 1/(500000000000 / 1596906433939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14310 : Bounds (580607729 / 500000000) (58060773 / 50000000) (Real.log (1596906433939 / 500000000000)) := by
  have h := reflection_log_14310_neg
  have he : Real.log (1596906433939 / 500000000000) = -Real.log (500000000000 / 1596906433939) := by
    rw [show ((1596906433939 / 500000000000) : ℝ) = ((500000000000 / 1596906433939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14311_neg : (2733941613 / 1000000000) ≤ -Real.log (125000000000 / 1924180327869) ∧
    -Real.log (125000000000 / 1924180327869) ≤ (2733941617 / 1000000000) := by
  have h := checkLog_sound (w := (924180327869 / 2924180327869)) (n := 12)
    (lo := (654500073 / 1000000000)) (hi := (327250037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1924180327869 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1924180327869 / 1000000000000) = 1/(125000000000 / 1924180327869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14311 : Bounds (2733941613 / 1000000000) (2733941617 / 1000000000) (Real.log (1924180327869 / 125000000000)) := by
  have h := reflection_log_14311_neg
  have he : Real.log (1924180327869 / 125000000000) = -Real.log (125000000000 / 1924180327869) := by
    rw [show ((1924180327869 / 125000000000) : ℝ) = ((125000000000 / 1924180327869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14312_neg : (12636071 / 20000000) ≤ -Real.log (1000 / 1881) ∧
    -Real.log (1000 / 1881) ≤ (631803551 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 2881)) (n := 12)
    (lo := (12636071 / 20000000)) (hi := (631803551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1881 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1881 / 1000) = 1/(1000 / 1881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14312 : Bounds (12636071 / 20000000) (631803551 / 1000000000) (Real.log (1881 / 1000)) := by
  have h := reflection_log_14312_neg
  have he : Real.log (1881 / 1000) = -Real.log (1000 / 1881) := by
    rw [show ((1881 / 1000) : ℝ) = ((1000 / 1881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14313_neg : (266078973 / 125000000) ≤ -Real.log (119 / 1000) ∧
    -Real.log (119 / 1000) ≤ (532157947 / 250000000) := by
  have h := checkLog_sound (w := (3 / 122)) (n := 12)
    (lo := (12297561 / 250000000)) (hi := (9838049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 119) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 119) = 1/(119 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14313 : Bounds (-532157947 / 250000000) (-266078973 / 125000000) (Real.log (119 / 1000)) := by
  have h := reflection_log_14313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14314_neg : (220153 / 250000000) ≤ -Real.log (1000000 / 1000881) ∧
    -Real.log (1000000 / 1000881) ≤ (880613 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 2000881)) (n := 12)
    (lo := (220153 / 250000000)) (hi := (880613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000881 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000881 / 1000000) = 1/(1000000 / 1000881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14314 : Bounds (220153 / 250000000) (880613 / 1000000000) (Real.log (1000881 / 1000000)) := by
  have h := reflection_log_14314_neg
  have he : Real.log (1000881 / 1000000) = -Real.log (1000000 / 1000881) := by
    rw [show ((1000881 / 1000000) : ℝ) = ((1000000 / 1000881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14315_neg : (220347 / 250000000) ≤ -Real.log (999119 / 1000000) ∧
    -Real.log (999119 / 1000000) ≤ (881389 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 1999119)) (n := 12)
    (lo := (220347 / 250000000)) (hi := (881389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999119) = 1/(999119 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14315 : Bounds (-881389 / 1000000000) (-220347 / 250000000) (Real.log (999119 / 1000000)) := by
  have h := reflection_log_14315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14316_neg : (6567329 / 15625000) ≤ -Real.log (15625 / 23788) ∧
    -Real.log (15625 / 23788) ≤ (420309057 / 1000000000) := by
  have h := checkLog_sound (w := (8163 / 39413)) (n := 12)
    (lo := (6567329 / 15625000)) (hi := (420309057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23788 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23788 / 15625) = 1/(15625 / 23788) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14316 : Bounds (6567329 / 15625000) (420309057 / 1000000000) (Real.log (23788 / 15625)) := by
  have h := reflection_log_14316_neg
  have he : Real.log (23788 / 15625) = -Real.log (15625 / 23788) := by
    rw [show ((23788 / 15625) : ℝ) = ((15625 / 23788) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14317_neg : (9238109 / 12500000) ≤ -Real.log (7462 / 15625) ∧
    -Real.log (7462 / 15625) ≤ (369524361 / 500000000) := by
  have h := checkLog_sound (w := (701 / 30549)) (n := 12)
    (lo := (2295077 / 50000000)) (hi := (45901541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14924) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 14924) = 1/(7462 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14317 : Bounds (-369524361 / 500000000) (-9238109 / 12500000) (Real.log (7462 / 15625)) := by
  have h := reflection_log_14317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14318_neg : (105623817 / 250000000) ≤ -Real.log (250000 / 381441) ∧
    -Real.log (250000 / 381441) ≤ (422495269 / 1000000000) := by
  have h := checkLog_sound (w := (131441 / 631441)) (n := 12)
    (lo := (105623817 / 250000000)) (hi := (422495269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381441 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381441 / 250000) = 1/(250000 / 381441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14318 : Bounds (105623817 / 250000000) (422495269 / 1000000000) (Real.log (381441 / 250000)) := by
  have h := reflection_log_14318_neg
  have he : Real.log (381441 / 250000) = -Real.log (250000 / 381441) := by
    rw [show ((381441 / 250000) : ℝ) = ((250000 / 381441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14319_neg : (74605019 / 100000000) ≤ -Real.log (118559 / 250000) ∧
    -Real.log (118559 / 250000) ≤ (46628137 / 62500000) := by
  have h := checkLog_sound (w := (6441 / 243559)) (n := 12)
    (lo := (5290301 / 100000000)) (hi := (52903011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 118559) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 118559) = 1/(118559 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14319 : Bounds (-46628137 / 62500000) (-74605019 / 100000000) (Real.log (118559 / 250000)) := by
  have h := reflection_log_14319_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14320_neg : (161777461 / 500000000) ≤ -Real.log (45223263519 / 62500000000) ∧
    -Real.log (45223263519 / 62500000000) ≤ (323554923 / 1000000000) := by
  have h := checkLog_sound (w := (17276736481 / 107723263519)) (n := 12)
    (lo := (161777461 / 500000000)) (hi := (323554923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 45223263519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 45223263519) = 1/(45223263519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14320 : Bounds (-323554923 / 1000000000) (-161777461 / 500000000) (Real.log (45223263519 / 62500000000)) := by
  have h := reflection_log_14320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14321_neg : (19921229 / 62500000) ≤ -Real.log (177506056 / 244140625) ∧
    -Real.log (177506056 / 244140625) ≤ (63747933 / 200000000) := by
  have h := checkLog_sound (w := (66634569 / 421646681)) (n := 12)
    (lo := (19921229 / 62500000)) (hi := (63747933 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 177506056) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 177506056) = 1/(177506056 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14321 : Bounds (-63747933 / 200000000) (-19921229 / 62500000) (Real.log (177506056 / 244140625)) := by
  have h := reflection_log_14321_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14322_neg : (72459861 / 62500000) ≤ -Real.log (500000000000 / 1593942642723) ∧
    -Real.log (500000000000 / 1593942642723) ≤ (579678889 / 500000000) := by
  have h := checkLog_sound (w := (593942642723 / 2593942642723)) (n := 12)
    (lo := (116552649 / 250000000)) (hi := (466210597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593942642723 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1593942642723 / 1000000000000) = 1/(500000000000 / 1593942642723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14322 : Bounds (72459861 / 62500000) (579678889 / 500000000) (Real.log (1593942642723 / 500000000000)) := by
  have h := reflection_log_14322_neg
  have he : Real.log (1593942642723 / 500000000000) = -Real.log (500000000000 / 1593942642723) := by
    rw [show ((1593942642723 / 500000000000) : ℝ) = ((500000000000 / 1593942642723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14323_neg : (584272729 / 500000000) ≤ -Real.log (31250000000 / 100540922663) ∧
    -Real.log (31250000000 / 100540922663) ≤ (58427273 / 50000000) := by
  have h := checkLog_sound (w := (38040922663 / 163040922663)) (n := 12)
    (lo := (237699139 / 500000000)) (hi := (475398279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100540922663 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100540922663 / 62500000000) = 1/(31250000000 / 100540922663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14323 : Bounds (584272729 / 500000000) (58427273 / 50000000) (Real.log (100540922663 / 31250000000)) := by
  have h := reflection_log_14323_neg
  have he : Real.log (100540922663 / 31250000000) = -Real.log (31250000000 / 100540922663) := by
    rw [show ((100540922663 / 31250000000) : ℝ) = ((31250000000 / 100540922663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14324_neg : (2733941613 / 1000000000) ≤ -Real.log (20000000000 / 307868852459) ∧
    -Real.log (20000000000 / 307868852459) ≤ (2733941617 / 1000000000) := by
  have h := checkLog_sound (w := (147868852459 / 467868852459)) (n := 12)
    (lo := (654500073 / 1000000000)) (hi := (327250037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307868852459 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(307868852459 / 160000000000) = 1/(20000000000 / 307868852459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14324 : Bounds (2733941613 / 1000000000) (2733941617 / 1000000000) (Real.log (307868852459 / 20000000000)) := by
  have h := reflection_log_14324_neg
  have he : Real.log (307868852459 / 20000000000) = -Real.log (20000000000 / 307868852459) := by
    rw [show ((307868852459 / 20000000000) : ℝ) = ((20000000000 / 307868852459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14325_neg : (1380217667 / 500000000) ≤ -Real.log (250000000000 / 3951680672269) ∧
    -Real.log (250000000000 / 3951680672269) ≤ (1380217669 / 500000000) := by
  have h := checkLog_sound (w := (1951680672269 / 5951680672269)) (n := 12)
    (lo := (340496897 / 500000000)) (hi := (136198759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3951680672269 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3951680672269 / 2000000000000) = 1/(250000000000 / 3951680672269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14325 : Bounds (1380217667 / 500000000) (1380217669 / 500000000) (Real.log (3951680672269 / 250000000000)) := by
  have h := reflection_log_14325_neg
  have he : Real.log (3951680672269 / 250000000000) = -Real.log (250000000000 / 3951680672269) := by
    rw [show ((3951680672269 / 250000000000) : ℝ) = ((250000000000 / 3951680672269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14326_neg : (79174647 / 125000000) ≤ -Real.log (250 / 471) ∧
    -Real.log (250 / 471) ≤ (633397177 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 721)) (n := 12)
    (lo := (79174647 / 125000000)) (hi := (633397177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471 / 250) = 1/(250 / 471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14326 : Bounds (79174647 / 125000000) (633397177 / 1000000000) (Real.log (471 / 250)) := by
  have h := reflection_log_14326_neg
  have he : Real.log (471 / 250) = -Real.log (250 / 471) := by
    rw [show ((471 / 250) : ℝ) = ((250 / 471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14327_neg : (1077082543 / 500000000) ≤ -Real.log (29 / 250) ∧
    -Real.log (29 / 250) ≤ (215416509 / 100000000) := by
  have h := checkLog_sound (w := (9 / 241)) (n := 12)
    (lo := (37361773 / 500000000)) (hi := (74723547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 116) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 116) = 1/(29 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14327 : Bounds (-215416509 / 100000000) (-1077082543 / 500000000) (Real.log (29 / 250)) := by
  have h := reflection_log_14327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14328_neg : (883609 / 1000000000) ≤ -Real.log (250000 / 250221) ∧
    -Real.log (250000 / 250221) ≤ (88361 / 100000000) := by
  have h := checkLog_sound (w := (221 / 500221)) (n := 12)
    (lo := (883609 / 1000000000)) (hi := (88361 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250221 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250221 / 250000) = 1/(250000 / 250221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14328 : Bounds (883609 / 1000000000) (88361 / 100000000) (Real.log (250221 / 250000)) := by
  have h := reflection_log_14328_neg
  have he : Real.log (250221 / 250000) = -Real.log (250000 / 250221) := by
    rw [show ((250221 / 250000) : ℝ) = ((250000 / 250221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14329_neg : (88439 / 100000000) ≤ -Real.log (249779 / 250000) ∧
    -Real.log (249779 / 250000) ≤ (884391 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 499779)) (n := 12)
    (lo := (88439 / 100000000)) (hi := (884391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249779) = 1/(249779 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14329 : Bounds (-884391 / 1000000000) (-88439 / 100000000) (Real.log (249779 / 250000)) := by
  have h := reflection_log_14329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14330_neg : (422052769 / 1000000000) ≤ -Real.log (1000000 / 1525089) ∧
    -Real.log (1000000 / 1525089) ≤ (42205277 / 100000000) := by
  have h := checkLog_sound (w := (525089 / 2525089)) (n := 12)
    (lo := (422052769 / 1000000000)) (hi := (42205277 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1525089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1525089 / 1000000) = 1/(1000000 / 1525089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14330 : Bounds (422052769 / 1000000000) (42205277 / 100000000) (Real.log (1525089 / 1000000)) := by
  have h := reflection_log_14330_neg
  have he : Real.log (1525089 / 1000000) = -Real.log (1000000 / 1525089) := by
    rw [show ((1525089 / 1000000) : ℝ) = ((1000000 / 1525089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14331_neg : (37231393 / 50000000) ≤ -Real.log (474911 / 1000000) ∧
    -Real.log (474911 / 1000000) ≤ (372313931 / 500000000) := by
  have h := checkLog_sound (w := (25089 / 974911)) (n := 12)
    (lo := (1287017 / 25000000)) (hi := (51480681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 474911) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 474911) = 1/(474911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14331 : Bounds (-372313931 / 500000000) (-37231393 / 50000000) (Real.log (474911 / 1000000)) := by
  have h := reflection_log_14331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14332_neg : (212123149 / 500000000) ≤ -Real.log (500000 / 764219) ∧
    -Real.log (500000 / 764219) ≤ (424246299 / 1000000000) := by
  have h := checkLog_sound (w := (264219 / 1264219)) (n := 12)
    (lo := (212123149 / 500000000)) (hi := (424246299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764219 / 500000) = 1/(500000 / 764219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14332 : Bounds (212123149 / 500000000) (424246299 / 1000000000) (Real.log (764219 / 500000)) := by
  have h := reflection_log_14332_neg
  have he : Real.log (764219 / 500000) = -Real.log (500000 / 764219) := by
    rw [show ((764219 / 500000) : ℝ) = ((500000 / 764219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14333_neg : (751704689 / 1000000000) ≤ -Real.log (235781 / 500000) ∧
    -Real.log (235781 / 500000) ≤ (751704691 / 1000000000) := by
  have h := checkLog_sound (w := (14219 / 485781)) (n := 12)
    (lo := (58557509 / 1000000000)) (hi := (5855751 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 235781) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 235781) = 1/(235781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14333 : Bounds (-751704691 / 1000000000) (-751704689 / 1000000000) (Real.log (235781 / 500000)) := by
  have h := reflection_log_14333_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14334_neg : (327458391 / 1000000000) ≤ -Real.log (180188320039 / 250000000000) ∧
    -Real.log (180188320039 / 250000000000) ≤ (40932299 / 125000000) := by
  have h := checkLog_sound (w := (69811679961 / 430188320039)) (n := 12)
    (lo := (327458391 / 1000000000)) (hi := (40932299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 180188320039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 180188320039) = 1/(180188320039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14334 : Bounds (-40932299 / 125000000) (-327458391 / 1000000000) (Real.log (180188320039 / 250000000000)) := by
  have h := reflection_log_14334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14335_neg : (322575091 / 1000000000) ≤ -Real.log (724281542079 / 1000000000000) ∧
    -Real.log (724281542079 / 1000000000000) ≤ (80643773 / 250000000) := by
  have h := checkLog_sound (w := (275718457921 / 1724281542079)) (n := 12)
    (lo := (322575091 / 1000000000)) (hi := (80643773 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 724281542079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 724281542079) = 1/(724281542079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14335 : Bounds (-80643773 / 250000000) (-322575091 / 1000000000) (Real.log (724281542079 / 1000000000000)) := by
  have h := reflection_log_14335_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0224 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14336_neg : (1166680629 / 1000000000) ≤ -Real.log (500000000000 / 1605657691651) ∧
    -Real.log (500000000000 / 1605657691651) ≤ (1166680631 / 1000000000) := by
  have h := checkLog_sound (w := (605657691651 / 2605657691651)) (n := 12)
    (lo := (473533449 / 1000000000)) (hi := (9470669 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1605657691651 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1605657691651 / 1000000000000) = 1/(500000000000 / 1605657691651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14336 : Bounds (1166680629 / 1000000000) (1166680631 / 1000000000) (Real.log (1605657691651 / 500000000000)) := by
  have h := reflection_log_14336_neg
  have he : Real.log (1605657691651 / 500000000000) = -Real.log (500000000000 / 1605657691651) := by
    rw [show ((1605657691651 / 500000000000) : ℝ) = ((500000000000 / 1605657691651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14337_neg : (293987747 / 250000000) ≤ -Real.log (500000000000 / 1620611923777) ∧
    -Real.log (500000000000 / 1620611923777) ≤ (117595099 / 100000000) := by
  have h := checkLog_sound (w := (620611923777 / 2620611923777)) (n := 12)
    (lo := (15087619 / 31250000)) (hi := (482803809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1620611923777 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1620611923777 / 1000000000000) = 1/(500000000000 / 1620611923777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14337 : Bounds (293987747 / 250000000) (117595099 / 100000000) (Real.log (1620611923777 / 500000000000)) := by
  have h := reflection_log_14337_neg
  have he : Real.log (1620611923777 / 500000000000) = -Real.log (500000000000 / 1620611923777) := by
    rw [show ((1620611923777 / 500000000000) : ℝ) = ((500000000000 / 1620611923777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14338_neg : (1380217667 / 500000000) ≤ -Real.log (500000000000 / 7903361344537) ∧
    -Real.log (500000000000 / 7903361344537) ≤ (1380217669 / 500000000) := by
  have h := checkLog_sound (w := (3903361344537 / 11903361344537)) (n := 12)
    (lo := (340496897 / 500000000)) (hi := (136198759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7903361344537 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7903361344537 / 4000000000000) = 1/(500000000000 / 7903361344537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14338 : Bounds (1380217667 / 500000000) (1380217669 / 500000000) (Real.log (7903361344537 / 500000000000)) := by
  have h := reflection_log_14338_neg
  have he : Real.log (7903361344537 / 500000000000) = -Real.log (500000000000 / 7903361344537) := by
    rw [show ((7903361344537 / 500000000000) : ℝ) = ((500000000000 / 7903361344537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14339_neg : (2787562261 / 1000000000) ≤ -Real.log (500000000000 / 8120689655173) ∧
    -Real.log (500000000000 / 8120689655173) ≤ (1393781133 / 500000000) := by
  have h := checkLog_sound (w := (120689655173 / 16120689655173)) (n := 12)
    (lo := (14973541 / 1000000000)) (hi := (7486771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8120689655173 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8120689655173 / 8000000000000) = 1/(500000000000 / 8120689655173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14339 : Bounds (2787562261 / 1000000000) (1393781133 / 500000000) (Real.log (8120689655173 / 500000000000)) := by
  have h := reflection_log_14339_neg
  have he : Real.log (8120689655173 / 500000000000) = -Real.log (500000000000 / 8120689655173) := by
    rw [show ((8120689655173 / 500000000000) : ℝ) = ((500000000000 / 8120689655173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14340_neg : (317494133 / 500000000) ≤ -Real.log (1000 / 1887) ∧
    -Real.log (1000 / 1887) ≤ (634988267 / 1000000000) := by
  have h := checkLog_sound (w := (887 / 2887)) (n := 12)
    (lo := (317494133 / 500000000)) (hi := (634988267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1887 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1887 / 1000) = 1/(1000 / 1887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14340 : Bounds (317494133 / 500000000) (634988267 / 1000000000) (Real.log (1887 / 1000)) := by
  have h := reflection_log_14340_neg
  have he : Real.log (1887 / 1000) = -Real.log (1000 / 1887) := by
    rw [show ((1887 / 1000) : ℝ) = ((1000 / 1887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14341_neg : (1090183729 / 500000000) ≤ -Real.log (113 / 1000) ∧
    -Real.log (113 / 1000) ≤ (1090183731 / 500000000) := by
  have h := checkLog_sound (w := (6 / 119)) (n := 12)
    (lo := (50462959 / 500000000)) (hi := (100925919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 113) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 113) = 1/(113 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14341 : Bounds (-1090183731 / 500000000) (-1090183729 / 500000000) (Real.log (113 / 1000)) := by
  have h := reflection_log_14341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14342_neg : (443303 / 500000000) ≤ -Real.log (1000000 / 1000887) ∧
    -Real.log (1000000 / 1000887) ≤ (886607 / 1000000000) := by
  have h := checkLog_sound (w := (887 / 2000887)) (n := 12)
    (lo := (443303 / 500000000)) (hi := (886607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000887 / 1000000) = 1/(1000000 / 1000887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14342 : Bounds (443303 / 500000000) (886607 / 1000000000) (Real.log (1000887 / 1000000)) := by
  have h := reflection_log_14342_neg
  have he : Real.log (1000887 / 1000000) = -Real.log (1000000 / 1000887) := by
    rw [show ((1000887 / 1000000) : ℝ) = ((1000000 / 1000887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14343_neg : (887393 / 1000000000) ≤ -Real.log (999113 / 1000000) ∧
    -Real.log (999113 / 1000000) ≤ (443697 / 500000000) := by
  have h := checkLog_sound (w := (887 / 1999113)) (n := 12)
    (lo := (887393 / 1000000000)) (hi := (443697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999113) = 1/(999113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14343 : Bounds (-443697 / 500000000) (-887393 / 1000000000) (Real.log (999113 / 1000000)) := by
  have h := reflection_log_14343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14344_neg : (211902287 / 500000000) ≤ -Real.log (1000000 / 1527763) ∧
    -Real.log (1000000 / 1527763) ≤ (16952183 / 40000000) := by
  have h := checkLog_sound (w := (527763 / 2527763)) (n := 12)
    (lo := (211902287 / 500000000)) (hi := (16952183 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1527763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1527763 / 1000000) = 1/(1000000 / 1527763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14344 : Bounds (211902287 / 500000000) (16952183 / 40000000) (Real.log (1527763 / 1000000)) := by
  have h := reflection_log_14344_neg
  have he : Real.log (1527763 / 1000000) = -Real.log (1000000 / 1527763) := by
    rw [show ((1527763 / 1000000) : ℝ) = ((1000000 / 1527763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14345_neg : (7502743 / 10000000) ≤ -Real.log (472237 / 1000000) ∧
    -Real.log (472237 / 1000000) ≤ (375137151 / 500000000) := by
  have h := checkLog_sound (w := (27763 / 972237)) (n := 12)
    (lo := (714089 / 12500000)) (hi := (57127121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 472237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 472237) = 1/(472237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14345 : Bounds (-375137151 / 500000000) (-7502743 / 10000000) (Real.log (472237 / 1000000)) := by
  have h := reflection_log_14345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14346_neg : (53250753 / 125000000) ≤ -Real.log (100000 / 153113) ∧
    -Real.log (100000 / 153113) ≤ (17040241 / 40000000) := by
  have h := checkLog_sound (w := (53113 / 253113)) (n := 12)
    (lo := (53250753 / 125000000)) (hi := (17040241 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153113 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153113 / 100000) = 1/(100000 / 153113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14346 : Bounds (53250753 / 125000000) (17040241 / 40000000) (Real.log (153113 / 100000)) := by
  have h := reflection_log_14346_neg
  have he : Real.log (153113 / 100000) = -Real.log (100000 / 153113) := by
    rw [show ((153113 / 100000) : ℝ) = ((100000 / 153113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14347_neg : (757429733 / 1000000000) ≤ -Real.log (46887 / 100000) ∧
    -Real.log (46887 / 100000) ≤ (151485947 / 200000000) := by
  have h := checkLog_sound (w := (3113 / 96887)) (n := 12)
    (lo := (64282553 / 1000000000)) (hi := (32141277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 46887) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 46887) = 1/(46887 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14347 : Bounds (-151485947 / 200000000) (-757429733 / 1000000000) (Real.log (46887 / 100000)) := by
  have h := reflection_log_14347_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14348_neg : (331423709 / 1000000000) ≤ -Real.log (7179009231 / 10000000000) ∧
    -Real.log (7179009231 / 10000000000) ≤ (33142371 / 100000000) := by
  have h := checkLog_sound (w := (2820990769 / 17179009231)) (n := 12)
    (lo := (331423709 / 1000000000)) (hi := (33142371 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 7179009231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 7179009231) = 1/(7179009231 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14348 : Bounds (-33142371 / 100000000) (-331423709 / 1000000000) (Real.log (7179009231 / 10000000000)) := by
  have h := reflection_log_14348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14349_neg : (163234863 / 500000000) ≤ -Real.log (721466215831 / 1000000000000) ∧
    -Real.log (721466215831 / 1000000000000) ≤ (326469727 / 1000000000) := by
  have h := checkLog_sound (w := (278533784169 / 1721466215831)) (n := 12)
    (lo := (163234863 / 500000000)) (hi := (326469727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 721466215831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 721466215831) = 1/(721466215831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14349 : Bounds (-326469727 / 1000000000) (-163234863 / 500000000) (Real.log (721466215831 / 1000000000000)) := by
  have h := reflection_log_14349_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14350_neg : (587039437 / 500000000) ≤ -Real.log (500000000000 / 1617580791001) ∧
    -Real.log (500000000000 / 1617580791001) ≤ (293519719 / 250000000) := by
  have h := checkLog_sound (w := (617580791001 / 2617580791001)) (n := 12)
    (lo := (240465847 / 500000000)) (hi := (96186339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1617580791001 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1617580791001 / 1000000000000) = 1/(500000000000 / 1617580791001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14350 : Bounds (587039437 / 500000000) (293519719 / 250000000) (Real.log (1617580791001 / 500000000000)) := by
  have h := reflection_log_14350_neg
  have he : Real.log (1617580791001 / 500000000000) = -Real.log (500000000000 / 1617580791001) := by
    rw [show ((1617580791001 / 500000000000) : ℝ) = ((500000000000 / 1617580791001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14351_neg : (591717879 / 500000000) ≤ -Real.log (20000000000 / 65311493591) ∧
    -Real.log (20000000000 / 65311493591) ≤ (14792947 / 12500000) := by
  have h := checkLog_sound (w := (25311493591 / 105311493591)) (n := 12)
    (lo := (245144289 / 500000000)) (hi := (490288579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65311493591 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65311493591 / 40000000000) = 1/(20000000000 / 65311493591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14351 : Bounds (591717879 / 500000000) (14792947 / 12500000) (Real.log (65311493591 / 20000000000)) := by
  have h := reflection_log_14351_neg
  have he : Real.log (65311493591 / 20000000000) = -Real.log (20000000000 / 65311493591) := by
    rw [show ((65311493591 / 20000000000) : ℝ) = ((20000000000 / 65311493591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14352_neg : (2787562261 / 1000000000) ≤ -Real.log (125000000000 / 2030172413793) ∧
    -Real.log (125000000000 / 2030172413793) ≤ (1393781133 / 500000000) := by
  have h := checkLog_sound (w := (30172413793 / 4030172413793)) (n := 12)
    (lo := (14973541 / 1000000000)) (hi := (7486771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2030172413793 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2030172413793 / 2000000000000) = 1/(125000000000 / 2030172413793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14352 : Bounds (2787562261 / 1000000000) (1393781133 / 500000000) (Real.log (2030172413793 / 125000000000)) := by
  have h := reflection_log_14352_neg
  have he : Real.log (2030172413793 / 125000000000) = -Real.log (125000000000 / 2030172413793) := by
    rw [show ((2030172413793 / 125000000000) : ℝ) = ((125000000000 / 2030172413793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14353_neg : (703838931 / 250000000) ≤ -Real.log (125000000000 / 2087389380531) ∧
    -Real.log (125000000000 / 2087389380531) ≤ (2815355729 / 1000000000) := by
  have h := checkLog_sound (w := (87389380531 / 4087389380531)) (n := 12)
    (lo := (10691751 / 250000000)) (hi := (8553401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2087389380531 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2087389380531 / 2000000000000) = 1/(125000000000 / 2087389380531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14353 : Bounds (703838931 / 250000000) (2815355729 / 1000000000) (Real.log (2087389380531 / 125000000000)) := by
  have h := reflection_log_14353_neg
  have he : Real.log (2087389380531 / 125000000000) = -Real.log (125000000000 / 2087389380531) := by
    rw [show ((2087389380531 / 125000000000) : ℝ) = ((125000000000 / 2087389380531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14354_neg : (636576829 / 1000000000) ≤ -Real.log (100 / 189) ∧
    -Real.log (100 / 189) ≤ (63657683 / 100000000) := by
  have h := checkLog_sound (w := (89 / 289)) (n := 12)
    (lo := (636576829 / 1000000000)) (hi := (63657683 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189 / 100) = 1/(100 / 189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14354 : Bounds (636576829 / 1000000000) (63657683 / 100000000) (Real.log (189 / 100)) := by
  have h := reflection_log_14354_neg
  have he : Real.log (189 / 100) = -Real.log (100 / 189) := by
    rw [show ((189 / 100) : ℝ) = ((100 / 189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14355_neg : (2207274911 / 1000000000) ≤ -Real.log (11 / 100) ∧
    -Real.log (11 / 100) ≤ (441454983 / 200000000) := by
  have h := checkLog_sound (w := (3 / 47)) (n := 12)
    (lo := (127833371 / 1000000000)) (hi := (31958343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 22) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 22) = 1/(11 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14355 : Bounds (-441454983 / 200000000) (-2207274911 / 1000000000) (Real.log (11 / 100)) := by
  have h := reflection_log_14355_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14356_neg : (222401 / 250000000) ≤ -Real.log (100000 / 100089) ∧
    -Real.log (100000 / 100089) ≤ (177921 / 200000000) := by
  have h := checkLog_sound (w := (89 / 200089)) (n := 12)
    (lo := (222401 / 250000000)) (hi := (177921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100089 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100089 / 100000) = 1/(100000 / 100089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14356 : Bounds (222401 / 250000000) (177921 / 200000000) (Real.log (100089 / 100000)) := by
  have h := reflection_log_14356_neg
  have he : Real.log (100089 / 100000) = -Real.log (100000 / 100089) := by
    rw [show ((100089 / 100000) : ℝ) = ((100000 / 100089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14357_neg : (222599 / 250000000) ≤ -Real.log (99911 / 100000) ∧
    -Real.log (99911 / 100000) ≤ (890397 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 199911)) (n := 12)
    (lo := (222599 / 250000000)) (hi := (890397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99911) = 1/(99911 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14357 : Bounds (-890397 / 1000000000) (-222599 / 250000000) (Real.log (99911 / 100000)) := by
  have h := reflection_log_14357_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14358_neg : (106391269 / 250000000) ≤ -Real.log (200000 / 306091) ∧
    -Real.log (200000 / 306091) ≤ (425565077 / 1000000000) := by
  have h := checkLog_sound (w := (106091 / 506091)) (n := 12)
    (lo := (106391269 / 250000000)) (hi := (425565077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306091 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306091 / 200000) = 1/(200000 / 306091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14358 : Bounds (106391269 / 250000000) (425565077 / 1000000000) (Real.log (306091 / 200000)) := by
  have h := reflection_log_14358_neg
  have he : Real.log (306091 / 200000) = -Real.log (200000 / 306091) := by
    rw [show ((306091 / 200000) : ℝ) = ((200000 / 306091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14359_neg : (755991137 / 1000000000) ≤ -Real.log (93909 / 200000) ∧
    -Real.log (93909 / 200000) ≤ (755991139 / 1000000000) := by
  have h := checkLog_sound (w := (6091 / 193909)) (n := 12)
    (lo := (62843957 / 1000000000)) (hi := (31421979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 93909) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 93909) = 1/(93909 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14359 : Bounds (-755991139 / 1000000000) (-755991137 / 1000000000) (Real.log (93909 / 200000)) := by
  have h := reflection_log_14359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14360_neg : (85554879 / 200000000) ≤ -Real.log (12500 / 19173) ∧
    -Real.log (12500 / 19173) ≤ (106943599 / 250000000) := by
  have h := checkLog_sound (w := (6673 / 31673)) (n := 12)
    (lo := (85554879 / 200000000)) (hi := (106943599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19173 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19173 / 12500) = 1/(12500 / 19173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14360 : Bounds (85554879 / 200000000) (106943599 / 250000000) (Real.log (19173 / 12500)) := by
  have h := reflection_log_14360_neg
  have he : Real.log (19173 / 12500) = -Real.log (12500 / 19173) := by
    rw [show ((19173 / 12500) : ℝ) = ((12500 / 19173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14361_neg : (152645271 / 200000000) ≤ -Real.log (5827 / 12500) ∧
    -Real.log (5827 / 12500) ≤ (763226357 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 12077)) (n := 12)
    (lo := (2803167 / 40000000)) (hi := (8759897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5827) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6250 / 5827) = 1/(5827 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14361 : Bounds (-763226357 / 1000000000) (-152645271 / 200000000) (Real.log (5827 / 12500)) := by
  have h := reflection_log_14361_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14362_neg : (335451961 / 1000000000) ≤ -Real.log (111721071 / 156250000) ∧
    -Real.log (111721071 / 156250000) ≤ (167725981 / 500000000) := by
  have h := checkLog_sound (w := (44528929 / 267971071)) (n := 12)
    (lo := (335451961 / 1000000000)) (hi := (167725981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 111721071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 111721071) = 1/(111721071 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14362 : Bounds (-167725981 / 500000000) (-335451961 / 1000000000) (Real.log (111721071 / 156250000)) := by
  have h := reflection_log_14362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14363_neg : (330426061 / 1000000000) ≤ -Real.log (28744699719 / 40000000000) ∧
    -Real.log (28744699719 / 40000000000) ≤ (165213031 / 500000000) := by
  have h := checkLog_sound (w := (11255300281 / 68744699719)) (n := 12)
    (lo := (330426061 / 1000000000)) (hi := (165213031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 28744699719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 28744699719) = 1/(28744699719 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14363 : Bounds (-165213031 / 500000000) (-330426061 / 1000000000) (Real.log (28744699719 / 40000000000)) := by
  have h := reflection_log_14363_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14364_neg : (590778107 / 500000000) ≤ -Real.log (125000000000 / 407430331491) ∧
    -Real.log (125000000000 / 407430331491) ≤ (147694527 / 125000000) := by
  have h := checkLog_sound (w := (157430331491 / 657430331491)) (n := 12)
    (lo := (244204517 / 500000000)) (hi := (97681807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407430331491 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(407430331491 / 250000000000) = 1/(125000000000 / 407430331491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14364 : Bounds (590778107 / 500000000) (147694527 / 125000000) (Real.log (407430331491 / 125000000000)) := by
  have h := reflection_log_14364_neg
  have he : Real.log (407430331491 / 125000000000) = -Real.log (125000000000 / 407430331491) := by
    rw [show ((407430331491 / 125000000000) : ℝ) = ((125000000000 / 407430331491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14365_neg : (4764003 / 4000000) ≤ -Real.log (500000000000 / 1645186202163) ∧
    -Real.log (500000000000 / 1645186202163) ≤ (74437547 / 62500000) := by
  have h := checkLog_sound (w := (645186202163 / 2645186202163)) (n := 12)
    (lo := (49785357 / 100000000)) (hi := (497853571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1645186202163 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1645186202163 / 1000000000000) = 1/(500000000000 / 1645186202163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14365 : Bounds (4764003 / 4000000) (74437547 / 62500000) (Real.log (1645186202163 / 500000000000)) := by
  have h := reflection_log_14365_neg
  have he : Real.log (1645186202163 / 500000000000) = -Real.log (500000000000 / 1645186202163) := by
    rw [show ((1645186202163 / 500000000000) : ℝ) = ((500000000000 / 1645186202163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14366_neg : (703838931 / 250000000) ≤ -Real.log (500000000000 / 8349557522123) ∧
    -Real.log (500000000000 / 8349557522123) ≤ (2815355729 / 1000000000) := by
  have h := checkLog_sound (w := (349557522123 / 16349557522123)) (n := 12)
    (lo := (10691751 / 250000000)) (hi := (8553401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8349557522123 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8349557522123 / 8000000000000) = 1/(500000000000 / 8349557522123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14366 : Bounds (703838931 / 250000000) (2815355729 / 1000000000) (Real.log (8349557522123 / 500000000000)) := by
  have h := reflection_log_14366_neg
  have he : Real.log (8349557522123 / 500000000000) = -Real.log (500000000000 / 8349557522123) := by
    rw [show ((8349557522123 / 500000000000) : ℝ) = ((500000000000 / 8349557522123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14367_neg : (142192587 / 50000000) ≤ -Real.log (50000000000 / 859090909091) ∧
    -Real.log (50000000000 / 859090909091) ≤ (568770349 / 200000000) := by
  have h := checkLog_sound (w := (59090909091 / 1659090909091)) (n := 12)
    (lo := (3563151 / 50000000)) (hi := (71263021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859090909091 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(859090909091 / 800000000000) = 1/(50000000000 / 859090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14367 : Bounds (142192587 / 50000000) (568770349 / 200000000) (Real.log (859090909091 / 50000000000)) := by
  have h := reflection_log_14367_neg
  have he : Real.log (859090909091 / 50000000000) = -Real.log (50000000000 / 859090909091) := by
    rw [show ((859090909091 / 50000000000) : ℝ) = ((50000000000 / 859090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14368_neg : (79770359 / 125000000) ≤ -Real.log (1000 / 1893) ∧
    -Real.log (1000 / 1893) ≤ (638162873 / 1000000000) := by
  have h := checkLog_sound (w := (893 / 2893)) (n := 12)
    (lo := (79770359 / 125000000)) (hi := (638162873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1893 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1893 / 1000) = 1/(1000 / 1893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14368 : Bounds (79770359 / 125000000) (638162873 / 1000000000) (Real.log (1893 / 1000)) := by
  have h := reflection_log_14368_neg
  have he : Real.log (1893 / 1000) = -Real.log (1000 / 1893) := by
    rw [show ((1893 / 1000) : ℝ) = ((1000 / 1893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14369_neg : (1117463221 / 500000000) ≤ -Real.log (107 / 1000) ∧
    -Real.log (107 / 1000) ≤ (1117463223 / 500000000) := by
  have h := checkLog_sound (w := (9 / 116)) (n := 12)
    (lo := (77742451 / 500000000)) (hi := (155484903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 107) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 107) = 1/(107 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14369 : Bounds (-1117463223 / 500000000) (-1117463221 / 500000000) (Real.log (107 / 1000)) := by
  have h := reflection_log_14369_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14370_neg : (892601 / 1000000000) ≤ -Real.log (1000000 / 1000893) ∧
    -Real.log (1000000 / 1000893) ≤ (446301 / 500000000) := by
  have h := checkLog_sound (w := (893 / 2000893)) (n := 12)
    (lo := (892601 / 1000000000)) (hi := (446301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000893 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000893 / 1000000) = 1/(1000000 / 1000893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14370 : Bounds (892601 / 1000000000) (446301 / 500000000) (Real.log (1000893 / 1000000)) := by
  have h := reflection_log_14370_neg
  have he : Real.log (1000893 / 1000000) = -Real.log (1000000 / 1000893) := by
    rw [show ((1000893 / 1000000) : ℝ) = ((1000000 / 1000893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14371_neg : (446699 / 500000000) ≤ -Real.log (999107 / 1000000) ∧
    -Real.log (999107 / 1000000) ≤ (893399 / 1000000000) := by
  have h := checkLog_sound (w := (893 / 1999107)) (n := 12)
    (lo := (446699 / 500000000)) (hi := (893399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999107) = 1/(999107 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14371 : Bounds (-893399 / 1000000000) (-446699 / 500000000) (Real.log (999107 / 1000000)) := by
  have h := reflection_log_14371_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14372_neg : (213667439 / 500000000) ≤ -Real.log (500000 / 766583) ∧
    -Real.log (500000 / 766583) ≤ (427334879 / 1000000000) := by
  have h := checkLog_sound (w := (266583 / 1266583)) (n := 12)
    (lo := (213667439 / 500000000)) (hi := (427334879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((766583 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(766583 / 500000) = 1/(500000 / 766583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14372 : Bounds (213667439 / 500000000) (427334879 / 1000000000) (Real.log (766583 / 500000)) := by
  have h := reflection_log_14372_neg
  have he : Real.log (766583 / 500000) = -Real.log (500000 / 766583) := by
    rw [show ((766583 / 500000) : ℝ) = ((500000 / 766583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14373_neg : (95222693 / 125000000) ≤ -Real.log (233417 / 500000) ∧
    -Real.log (233417 / 500000) ≤ (380890773 / 500000000) := by
  have h := checkLog_sound (w := (16583 / 483417)) (n := 12)
    (lo := (17158591 / 250000000)) (hi := (13726873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 233417) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 233417) = 1/(233417 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14373 : Bounds (-380890773 / 500000000) (-95222693 / 125000000) (Real.log (233417 / 500000)) := by
  have h := reflection_log_14373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14374_neg : (429552659 / 1000000000) ≤ -Real.log (100000 / 153657) ∧
    -Real.log (100000 / 153657) ≤ (21477633 / 50000000) := by
  have h := checkLog_sound (w := (53657 / 253657)) (n := 12)
    (lo := (429552659 / 1000000000)) (hi := (21477633 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153657 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153657 / 100000) = 1/(100000 / 153657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14374 : Bounds (429552659 / 1000000000) (21477633 / 50000000) (Real.log (153657 / 100000)) := by
  have h := reflection_log_14374_neg
  have he : Real.log (153657 / 100000) = -Real.log (100000 / 153657) := by
    rw [show ((153657 / 100000) : ℝ) = ((100000 / 153657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14375_neg : (769099929 / 1000000000) ≤ -Real.log (46343 / 100000) ∧
    -Real.log (46343 / 100000) ≤ (769099931 / 1000000000) := by
  have h := checkLog_sound (w := (3657 / 96343)) (n := 12)
    (lo := (75952749 / 1000000000)) (hi := (303811 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 46343) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 46343) = 1/(46343 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14375 : Bounds (-769099931 / 1000000000) (-769099929 / 1000000000) (Real.log (46343 / 100000)) := by
  have h := reflection_log_14375_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14376_neg : (33954727 / 100000000) ≤ -Real.log (7120926351 / 10000000000) ∧
    -Real.log (7120926351 / 10000000000) ≤ (339547271 / 1000000000) := by
  have h := checkLog_sound (w := (2879073649 / 17120926351)) (n := 12)
    (lo := (33954727 / 100000000)) (hi := (339547271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 7120926351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 7120926351) = 1/(7120926351 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14376 : Bounds (-339547271 / 1000000000) (-33954727 / 100000000) (Real.log (7120926351 / 10000000000)) := by
  have h := reflection_log_14376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14377_neg : (167223333 / 500000000) ≤ -Real.log (178933504111 / 250000000000) ∧
    -Real.log (178933504111 / 250000000000) ≤ (334446667 / 1000000000) := by
  have h := checkLog_sound (w := (71066495889 / 428933504111)) (n := 12)
    (lo := (167223333 / 500000000)) (hi := (334446667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 178933504111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 178933504111) = 1/(178933504111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14377 : Bounds (-334446667 / 1000000000) (-167223333 / 500000000) (Real.log (178933504111 / 250000000000)) := by
  have h := reflection_log_14377_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14378_neg : (594558211 / 500000000) ≤ -Real.log (250000000000 / 821044525463) ∧
    -Real.log (250000000000 / 821044525463) ≤ (148639553 / 125000000) := by
  have h := checkLog_sound (w := (321044525463 / 1321044525463)) (n := 12)
    (lo := (247984621 / 500000000)) (hi := (495969243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821044525463 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(821044525463 / 500000000000) = 1/(250000000000 / 821044525463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14378 : Bounds (594558211 / 500000000) (148639553 / 125000000) (Real.log (821044525463 / 250000000000)) := by
  have h := reflection_log_14378_neg
  have he : Real.log (821044525463 / 250000000000) = -Real.log (250000000000 / 821044525463) := by
    rw [show ((821044525463 / 250000000000) : ℝ) = ((250000000000 / 821044525463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14379_neg : (1198652589 / 1000000000) ≤ -Real.log (488281250 / 1618967957) ∧
    -Real.log (488281250 / 1618967957) ≤ (1198652591 / 1000000000) := by
  have h := checkLog_sound (w := (642405457 / 2595530457)) (n := 12)
    (lo := (505505409 / 1000000000)) (hi := (50550541 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1618967957 / 976562500) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1618967957 / 976562500) = 1/(488281250 / 1618967957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14379 : Bounds (1198652589 / 1000000000) (1198652591 / 1000000000) (Real.log (1618967957 / 488281250)) := by
  have h := reflection_log_14379_neg
  have he : Real.log (1618967957 / 488281250) = -Real.log (488281250 / 1618967957) := by
    rw [show ((1618967957 / 488281250) : ℝ) = ((488281250 / 1618967957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14380_neg : (142192587 / 50000000) ≤ -Real.log (500000000000 / 8590909090909) ∧
    -Real.log (500000000000 / 8590909090909) ≤ (568770349 / 200000000) := by
  have h := checkLog_sound (w := (590909090909 / 16590909090909)) (n := 12)
    (lo := (3563151 / 50000000)) (hi := (71263021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8590909090909 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8590909090909 / 8000000000000) = 1/(500000000000 / 8590909090909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14380 : Bounds (142192587 / 50000000) (568770349 / 200000000) (Real.log (8590909090909 / 500000000000)) := by
  have h := reflection_log_14380_neg
  have he : Real.log (8590909090909 / 500000000000) = -Real.log (500000000000 / 8590909090909) := by
    rw [show ((8590909090909 / 500000000000) : ℝ) = ((500000000000 / 8590909090909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14381_neg : (1436544657 / 500000000) ≤ -Real.log (125000000000 / 2211448598131) ∧
    -Real.log (125000000000 / 2211448598131) ≤ (2873089319 / 1000000000) := by
  have h := checkLog_sound (w := (211448598131 / 4211448598131)) (n := 12)
    (lo := (50250297 / 500000000)) (hi := (20100119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2211448598131 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2211448598131 / 2000000000000) = 1/(125000000000 / 2211448598131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14381 : Bounds (1436544657 / 500000000) (2873089319 / 1000000000) (Real.log (2211448598131 / 125000000000)) := by
  have h := reflection_log_14381_neg
  have he : Real.log (2211448598131 / 125000000000) = -Real.log (125000000000 / 2211448598131) := by
    rw [show ((2211448598131 / 125000000000) : ℝ) = ((125000000000 / 2211448598131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14382_neg : (639746403 / 1000000000) ≤ -Real.log (125 / 237) ∧
    -Real.log (125 / 237) ≤ (159936601 / 250000000) := by
  have h := checkLog_sound (w := (56 / 181)) (n := 12)
    (lo := (639746403 / 1000000000)) (hi := (159936601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237 / 125) = 1/(125 / 237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14382 : Bounds (639746403 / 1000000000) (159936601 / 250000000) (Real.log (237 / 125)) := by
  have h := reflection_log_14382_neg
  have he : Real.log (237 / 125) = -Real.log (125 / 237) := by
    rw [show ((237 / 125) : ℝ) = ((125 / 237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14383_neg : (1131682189 / 500000000) ≤ -Real.log (13 / 125) ∧
    -Real.log (13 / 125) ≤ (1131682191 / 500000000) := by
  have h := checkLog_sound (w := (21 / 229)) (n := 12)
    (lo := (91961419 / 500000000)) (hi := (183922839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 104) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 104) = 1/(13 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14383 : Bounds (-1131682191 / 500000000) (-1131682189 / 500000000) (Real.log (13 / 125)) := by
  have h := reflection_log_14383_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14384_neg : (447799 / 500000000) ≤ -Real.log (15625 / 15639) ∧
    -Real.log (15625 / 15639) ≤ (895599 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 15632)) (n := 12)
    (lo := (447799 / 500000000)) (hi := (895599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15639 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15639 / 15625) = 1/(15625 / 15639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14384 : Bounds (447799 / 500000000) (895599 / 1000000000) (Real.log (15639 / 15625)) := by
  have h := reflection_log_14384_neg
  have he : Real.log (15639 / 15625) = -Real.log (15625 / 15639) := by
    rw [show ((15639 / 15625) : ℝ) = ((15625 / 15639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14385_neg : (896401 / 1000000000) ≤ -Real.log (15611 / 15625) ∧
    -Real.log (15611 / 15625) ≤ (448201 / 500000000) := by
  have h := checkLog_sound (w := (7 / 15618)) (n := 12)
    (lo := (896401 / 1000000000)) (hi := (448201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15611) = 1/(15611 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14385 : Bounds (-448201 / 500000000) (-896401 / 1000000000) (Real.log (15611 / 15625)) := by
  have h := reflection_log_14385_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14386_neg : (107278481 / 250000000) ≤ -Real.log (125000 / 191987) ∧
    -Real.log (125000 / 191987) ≤ (17164557 / 40000000) := by
  have h := checkLog_sound (w := (66987 / 316987)) (n := 12)
    (lo := (107278481 / 250000000)) (hi := (17164557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191987 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191987 / 125000) = 1/(125000 / 191987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14386 : Bounds (107278481 / 250000000) (17164557 / 40000000) (Real.log (191987 / 125000)) := by
  have h := reflection_log_14386_neg
  have he : Real.log (191987 / 125000) = -Real.log (125000 / 191987) := by
    rw [show ((191987 / 125000) : ℝ) = ((125000 / 191987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14387_neg : (767646613 / 1000000000) ≤ -Real.log (58013 / 125000) ∧
    -Real.log (58013 / 125000) ≤ (153529323 / 200000000) := by
  have h := checkLog_sound (w := (4487 / 120513)) (n := 12)
    (lo := (74499433 / 1000000000)) (hi := (37249717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 58013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 58013) = 1/(58013 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14387 : Bounds (-153529323 / 200000000) (-767646613 / 1000000000) (Real.log (58013 / 125000)) := by
  have h := reflection_log_14387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14388_neg : (43134011 / 100000000) ≤ -Real.log (1000000 / 1539319) ∧
    -Real.log (1000000 / 1539319) ≤ (431340111 / 1000000000) := by
  have h := checkLog_sound (w := (539319 / 2539319)) (n := 12)
    (lo := (43134011 / 100000000)) (hi := (431340111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1539319 / 1000000) = 1/(1000000 / 1539319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14388 : Bounds (43134011 / 100000000) (431340111 / 1000000000) (Real.log (1539319 / 1000000)) := by
  have h := reflection_log_14388_neg
  have he : Real.log (1539319 / 1000000) = -Real.log (1000000 / 1539319) := by
    rw [show ((1539319 / 1000000) : ℝ) = ((1000000 / 1539319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14389_neg : (96881181 / 125000000) ≤ -Real.log (460681 / 1000000) ∧
    -Real.log (460681 / 1000000) ≤ (15500989 / 20000000) := by
  have h := checkLog_sound (w := (39319 / 960681)) (n := 12)
    (lo := (20475567 / 250000000)) (hi := (81902269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460681) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 460681) = 1/(460681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14389 : Bounds (-15500989 / 20000000) (-96881181 / 125000000) (Real.log (460681 / 1000000)) := by
  have h := reflection_log_14389_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14390_neg : (171854669 / 500000000) ≤ -Real.log (709135016239 / 1000000000000) ∧
    -Real.log (709135016239 / 1000000000000) ≤ (343709339 / 1000000000) := by
  have h := checkLog_sound (w := (290864983761 / 1709135016239)) (n := 12)
    (lo := (171854669 / 500000000)) (hi := (343709339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 709135016239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 709135016239) = 1/(709135016239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14390 : Bounds (-343709339 / 1000000000) (-171854669 / 500000000) (Real.log (709135016239 / 1000000000000)) := by
  have h := reflection_log_14390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14391_neg : (338532689 / 1000000000) ≤ -Real.log (11137741831 / 15625000000) ∧
    -Real.log (11137741831 / 15625000000) ≤ (33853269 / 100000000) := by
  have h := checkLog_sound (w := (4487258169 / 26762741831)) (n := 12)
    (lo := (338532689 / 1000000000)) (hi := (33853269 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 11137741831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 11137741831) = 1/(11137741831 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14391 : Bounds (-33853269 / 100000000) (-338532689 / 1000000000) (Real.log (11137741831 / 15625000000)) := by
  have h := reflection_log_14391_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14392_neg : (1196760537 / 1000000000) ≤ -Real.log (250000000000 / 827344733077) ∧
    -Real.log (250000000000 / 827344733077) ≤ (1196760539 / 1000000000) := by
  have h := checkLog_sound (w := (327344733077 / 1327344733077)) (n := 12)
    (lo := (503613357 / 1000000000)) (hi := (251806679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827344733077 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(827344733077 / 500000000000) = 1/(250000000000 / 827344733077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14392 : Bounds (1196760537 / 1000000000) (1196760539 / 1000000000) (Real.log (827344733077 / 250000000000)) := by
  have h := reflection_log_14392_neg
  have he : Real.log (827344733077 / 250000000000) = -Real.log (250000000000 / 827344733077) := by
    rw [show ((827344733077 / 250000000000) : ℝ) = ((250000000000 / 827344733077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14393_neg : (1206389559 / 1000000000) ≤ -Real.log (500000000000 / 1670699464489) ∧
    -Real.log (500000000000 / 1670699464489) ≤ (1206389561 / 1000000000) := by
  have h := checkLog_sound (w := (670699464489 / 2670699464489)) (n := 12)
    (lo := (513242379 / 1000000000)) (hi := (25662119 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1670699464489 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1670699464489 / 1000000000000) = 1/(500000000000 / 1670699464489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14393 : Bounds (1206389559 / 1000000000) (1206389561 / 1000000000) (Real.log (1670699464489 / 500000000000)) := by
  have h := reflection_log_14393_neg
  have he : Real.log (1670699464489 / 500000000000) = -Real.log (500000000000 / 1670699464489) := by
    rw [show ((1670699464489 / 500000000000) : ℝ) = ((500000000000 / 1670699464489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14394_neg : (1436544657 / 500000000) ≤ -Real.log (500000000000 / 8845794392523) ∧
    -Real.log (500000000000 / 8845794392523) ≤ (2873089319 / 1000000000) := by
  have h := checkLog_sound (w := (845794392523 / 16845794392523)) (n := 12)
    (lo := (50250297 / 500000000)) (hi := (20100119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8845794392523 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8845794392523 / 8000000000000) = 1/(500000000000 / 8845794392523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14394 : Bounds (1436544657 / 500000000) (2873089319 / 1000000000) (Real.log (8845794392523 / 500000000000)) := by
  have h := reflection_log_14394_neg
  have he : Real.log (8845794392523 / 500000000000) = -Real.log (500000000000 / 8845794392523) := by
    rw [show ((8845794392523 / 500000000000) : ℝ) = ((500000000000 / 8845794392523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14395_neg : (2903110781 / 1000000000) ≤ -Real.log (100000000000 / 1823076923077) ∧
    -Real.log (100000000000 / 1823076923077) ≤ (1451555393 / 500000000) := by
  have h := checkLog_sound (w := (223076923077 / 3423076923077)) (n := 12)
    (lo := (130522061 / 1000000000)) (hi := (65261031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1823076923077 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1823076923077 / 1600000000000) = 1/(100000000000 / 1823076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14395 : Bounds (2903110781 / 1000000000) (1451555393 / 500000000) (Real.log (1823076923077 / 100000000000)) := by
  have h := reflection_log_14395_neg
  have he : Real.log (1823076923077 / 100000000000) = -Real.log (100000000000 / 1823076923077) := by
    rw [show ((1823076923077 / 100000000000) : ℝ) = ((100000000000 / 1823076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14396_neg : (641327431 / 1000000000) ≤ -Real.log (1000 / 1899) ∧
    -Real.log (1000 / 1899) ≤ (80165929 / 125000000) := by
  have h := checkLog_sound (w := (899 / 2899)) (n := 12)
    (lo := (641327431 / 1000000000)) (hi := (80165929 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899 / 1000) = 1/(1000 / 1899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14396 : Bounds (641327431 / 1000000000) (80165929 / 125000000) (Real.log (1899 / 1000)) := by
  have h := reflection_log_14396_neg
  have he : Real.log (1899 / 1000) = -Real.log (1000 / 1899) := by
    rw [show ((1899 / 1000) : ℝ) = ((1000 / 1899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14397_neg : (57315869 / 25000000) ≤ -Real.log (101 / 1000) ∧
    -Real.log (101 / 1000) ≤ (573158691 / 250000000) := by
  have h := checkLog_sound (w := (12 / 113)) (n := 12)
    (lo := (10659661 / 50000000)) (hi := (213193221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 101) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 101) = 1/(101 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14397 : Bounds (-573158691 / 250000000) (-57315869 / 25000000) (Real.log (101 / 1000)) := by
  have h := reflection_log_14397_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14398_neg : (224649 / 250000000) ≤ -Real.log (1000000 / 1000899) ∧
    -Real.log (1000000 / 1000899) ≤ (898597 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 2000899)) (n := 12)
    (lo := (224649 / 250000000)) (hi := (898597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000899 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000899 / 1000000) = 1/(1000000 / 1000899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14398 : Bounds (224649 / 250000000) (898597 / 1000000000) (Real.log (1000899 / 1000000)) := by
  have h := reflection_log_14398_neg
  have he : Real.log (1000899 / 1000000) = -Real.log (1000000 / 1000899) := by
    rw [show ((1000899 / 1000000) : ℝ) = ((1000000 / 1000899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14399_neg : (224851 / 250000000) ≤ -Real.log (999101 / 1000000) ∧
    -Real.log (999101 / 1000000) ≤ (179881 / 200000000) := by
  have h := checkLog_sound (w := (899 / 1999101)) (n := 12)
    (lo := (224851 / 250000000)) (hi := (179881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999101) = 1/(999101 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14399 : Bounds (-179881 / 200000000) (-224851 / 250000000) (Real.log (999101 / 1000000)) := by
  have h := reflection_log_14399_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0225 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14400_neg : (215451079 / 500000000) ≤ -Real.log (200000 / 307729) ∧
    -Real.log (200000 / 307729) ≤ (430902159 / 1000000000) := by
  have h := checkLog_sound (w := (107729 / 507729)) (n := 12)
    (lo := (215451079 / 500000000)) (hi := (430902159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307729 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307729 / 200000) = 1/(200000 / 307729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14400 : Bounds (215451079 / 500000000) (430902159 / 1000000000) (Real.log (307729 / 200000)) := by
  have h := reflection_log_14400_neg
  have he : Real.log (307729 / 200000) = -Real.log (200000 / 307729) := by
    rw [show ((307729 / 200000) : ℝ) = ((200000 / 307729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14401_neg : (386793733 / 500000000) ≤ -Real.log (92271 / 200000) ∧
    -Real.log (92271 / 200000) ≤ (193396867 / 250000000) := by
  have h := checkLog_sound (w := (7729 / 192271)) (n := 12)
    (lo := (40220143 / 500000000)) (hi := (80440287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92271) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 92271) = 1/(92271 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14401 : Bounds (-193396867 / 250000000) (-386793733 / 500000000) (Real.log (92271 / 200000)) := by
  have h := reflection_log_14401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14402_neg : (43313799 / 100000000) ≤ -Real.log (1000000 / 1542089) ∧
    -Real.log (1000000 / 1542089) ≤ (433137991 / 1000000000) := by
  have h := checkLog_sound (w := (542089 / 2542089)) (n := 12)
    (lo := (43313799 / 100000000)) (hi := (433137991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1542089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1542089 / 1000000) = 1/(1000000 / 1542089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14402 : Bounds (43313799 / 100000000) (433137991 / 1000000000) (Real.log (1542089 / 1000000)) := by
  have h := reflection_log_14402_neg
  have he : Real.log (1542089 / 1000000) = -Real.log (1000000 / 1542089) := by
    rw [show ((1542089 / 1000000) : ℝ) = ((1000000 / 1542089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14403_neg : (195270109 / 250000000) ≤ -Real.log (457911 / 1000000) ∧
    -Real.log (457911 / 1000000) ≤ (390540219 / 500000000) := by
  have h := checkLog_sound (w := (42089 / 957911)) (n := 12)
    (lo := (10991657 / 125000000)) (hi := (87933257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457911) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 457911) = 1/(457911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14403 : Bounds (-390540219 / 500000000) (-195270109 / 250000000) (Real.log (457911 / 1000000)) := by
  have h := reflection_log_14403_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14404_neg : (173971223 / 500000000) ≤ -Real.log (706139516079 / 1000000000000) ∧
    -Real.log (706139516079 / 1000000000000) ≤ (347942447 / 1000000000) := by
  have h := checkLog_sound (w := (293860483921 / 1706139516079)) (n := 12)
    (lo := (173971223 / 500000000)) (hi := (347942447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 706139516079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 706139516079) = 1/(706139516079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14404 : Bounds (-347942447 / 1000000000) (-173971223 / 500000000) (Real.log (706139516079 / 1000000000000)) := by
  have h := reflection_log_14404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14405_neg : (85671327 / 250000000) ≤ -Real.log (28394462559 / 40000000000) ∧
    -Real.log (28394462559 / 40000000000) ≤ (342685309 / 1000000000) := by
  have h := checkLog_sound (w := (11605537441 / 68394462559)) (n := 12)
    (lo := (85671327 / 250000000)) (hi := (342685309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 28394462559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 28394462559) = 1/(28394462559 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14405 : Bounds (-342685309 / 1000000000) (-85671327 / 250000000) (Real.log (28394462559 / 40000000000)) := by
  have h := reflection_log_14405_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14406_neg : (9635917 / 8000000) ≤ -Real.log (500000000000 / 1667528259149) ∧
    -Real.log (500000000000 / 1667528259149) ≤ (1204489627 / 1000000000) := by
  have h := checkLog_sound (w := (667528259149 / 2667528259149)) (n := 12)
    (lo := (102268489 / 200000000)) (hi := (255671223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1667528259149 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1667528259149 / 1000000000000) = 1/(500000000000 / 1667528259149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14406 : Bounds (9635917 / 8000000) (1204489627 / 1000000000) (Real.log (1667528259149 / 500000000000)) := by
  have h := reflection_log_14406_neg
  have he : Real.log (1667528259149 / 500000000000) = -Real.log (500000000000 / 1667528259149) := by
    rw [show ((1667528259149 / 500000000000) : ℝ) = ((500000000000 / 1667528259149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14407_neg : (1214218427 / 1000000000) ≤ -Real.log (500000000000 / 1683830482343) ∧
    -Real.log (500000000000 / 1683830482343) ≤ (1214218429 / 1000000000) := by
  have h := checkLog_sound (w := (683830482343 / 2683830482343)) (n := 12)
    (lo := (521071247 / 1000000000)) (hi := (32566953 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683830482343 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1683830482343 / 1000000000000) = 1/(500000000000 / 1683830482343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14407 : Bounds (1214218427 / 1000000000) (1214218429 / 1000000000) (Real.log (1683830482343 / 500000000000)) := by
  have h := reflection_log_14407_neg
  have he : Real.log (1683830482343 / 500000000000) = -Real.log (500000000000 / 1683830482343) := by
    rw [show ((1683830482343 / 500000000000) : ℝ) = ((500000000000 / 1683830482343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14408_neg : (2903110781 / 1000000000) ≤ -Real.log (62500000000 / 1139423076923) ∧
    -Real.log (62500000000 / 1139423076923) ≤ (1451555393 / 500000000) := by
  have h := checkLog_sound (w := (139423076923 / 2139423076923)) (n := 12)
    (lo := (130522061 / 1000000000)) (hi := (65261031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139423076923 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1139423076923 / 1000000000000) = 1/(62500000000 / 1139423076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14408 : Bounds (2903110781 / 1000000000) (1451555393 / 500000000) (Real.log (1139423076923 / 62500000000)) := by
  have h := reflection_log_14408_neg
  have he : Real.log (1139423076923 / 62500000000) = -Real.log (62500000000 / 1139423076923) := by
    rw [show ((1139423076923 / 62500000000) : ℝ) = ((62500000000 / 1139423076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14409_neg : (2933962191 / 1000000000) ≤ -Real.log (50000000000 / 940099009901) ∧
    -Real.log (50000000000 / 940099009901) ≤ (733490549 / 250000000) := by
  have h := checkLog_sound (w := (140099009901 / 1740099009901)) (n := 12)
    (lo := (161373471 / 1000000000)) (hi := (5042921 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940099009901 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(940099009901 / 800000000000) = 1/(50000000000 / 940099009901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14409 : Bounds (2933962191 / 1000000000) (733490549 / 250000000) (Real.log (940099009901 / 50000000000)) := by
  have h := reflection_log_14409_neg
  have he : Real.log (940099009901 / 50000000000) = -Real.log (50000000000 / 940099009901) := by
    rw [show ((940099009901 / 50000000000) : ℝ) = ((50000000000 / 940099009901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14410_neg : (160726491 / 250000000) ≤ -Real.log (500 / 951) ∧
    -Real.log (500 / 951) ≤ (128581193 / 200000000) := by
  have h := checkLog_sound (w := (451 / 1451)) (n := 12)
    (lo := (160726491 / 250000000)) (hi := (128581193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(951 / 500) = 1/(500 / 951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14410 : Bounds (160726491 / 250000000) (128581193 / 200000000) (Real.log (951 / 500)) := by
  have h := reflection_log_14410_neg
  have he : Real.log (951 / 500) = -Real.log (500 / 951) := by
    rw [show ((951 / 500) : ℝ) = ((500 / 951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14411_neg : (1161393899 / 500000000) ≤ -Real.log (49 / 500) ∧
    -Real.log (49 / 500) ≤ (1161393901 / 500000000) := by
  have h := checkLog_sound (w := (27 / 223)) (n := 12)
    (lo := (121673129 / 500000000)) (hi := (243346259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 98) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 98) = 1/(49 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14411 : Bounds (-1161393901 / 500000000) (-1161393899 / 500000000) (Real.log (49 / 500)) := by
  have h := reflection_log_14411_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14412_neg : (901593 / 1000000000) ≤ -Real.log (500000 / 500451) ∧
    -Real.log (500000 / 500451) ≤ (450797 / 500000000) := by
  have h := checkLog_sound (w := (451 / 1000451)) (n := 12)
    (lo := (901593 / 1000000000)) (hi := (450797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500451 / 500000) = 1/(500000 / 500451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14412 : Bounds (901593 / 1000000000) (450797 / 500000000) (Real.log (500451 / 500000)) := by
  have h := reflection_log_14412_neg
  have he : Real.log (500451 / 500000) = -Real.log (500000 / 500451) := by
    rw [show ((500451 / 500000) : ℝ) = ((500000 / 500451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14413_neg : (902407 / 1000000000) ≤ -Real.log (499549 / 500000) ∧
    -Real.log (499549 / 500000) ≤ (112801 / 125000000) := by
  have h := checkLog_sound (w := (451 / 999549)) (n := 12)
    (lo := (902407 / 1000000000)) (hi := (112801 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499549) = 1/(499549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14413 : Bounds (-112801 / 125000000) (-902407 / 1000000000) (Real.log (499549 / 500000)) := by
  have h := reflection_log_14413_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14414_neg : (17308033 / 40000000) ≤ -Real.log (200000 / 308283) ∧
    -Real.log (200000 / 308283) ≤ (216350413 / 500000000) := by
  have h := checkLog_sound (w := (108283 / 508283)) (n := 12)
    (lo := (17308033 / 40000000)) (hi := (216350413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308283 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308283 / 200000) = 1/(200000 / 308283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14414 : Bounds (17308033 / 40000000) (216350413 / 500000000) (Real.log (308283 / 200000)) := by
  have h := reflection_log_14414_neg
  have he : Real.log (308283 / 200000) = -Real.log (200000 / 308283) := by
    rw [show ((308283 / 200000) : ℝ) = ((200000 / 308283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14415_neg : (48725601 / 62500000) ≤ -Real.log (91717 / 200000) ∧
    -Real.log (91717 / 200000) ≤ (389804809 / 500000000) := by
  have h := checkLog_sound (w := (8283 / 191717)) (n := 12)
    (lo := (21615609 / 250000000)) (hi := (86462437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91717) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 91717) = 1/(91717 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14415 : Bounds (-389804809 / 500000000) (-48725601 / 62500000) (Real.log (91717 / 200000)) := by
  have h := reflection_log_14415_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14416_neg : (43494559 / 100000000) ≤ -Real.log (1000000 / 1544879) ∧
    -Real.log (1000000 / 1544879) ≤ (434945591 / 1000000000) := by
  have h := checkLog_sound (w := (544879 / 2544879)) (n := 12)
    (lo := (43494559 / 100000000)) (hi := (434945591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1544879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1544879 / 1000000) = 1/(1000000 / 1544879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14416 : Bounds (43494559 / 100000000) (434945591 / 1000000000) (Real.log (1544879 / 1000000)) := by
  have h := reflection_log_14416_neg
  have he : Real.log (1544879 / 1000000) = -Real.log (1000000 / 1544879) := by
    rw [show ((1544879 / 1000000) : ℝ) = ((1000000 / 1544879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14417_neg : (19679799 / 25000000) ≤ -Real.log (455121 / 1000000) ∧
    -Real.log (455121 / 1000000) ≤ (393595981 / 500000000) := by
  have h := checkLog_sound (w := (44879 / 955121)) (n := 12)
    (lo := (4702239 / 50000000)) (hi := (94044781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455121) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 455121) = 1/(455121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14417 : Bounds (-393595981 / 500000000) (-19679799 / 25000000) (Real.log (455121 / 1000000)) := by
  have h := reflection_log_14417_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14418_neg : (352246371 / 1000000000) ≤ -Real.log (703106875359 / 1000000000000) ∧
    -Real.log (703106875359 / 1000000000000) ≤ (88061593 / 250000000) := by
  have h := checkLog_sound (w := (296893124641 / 1703106875359)) (n := 12)
    (lo := (352246371 / 1000000000)) (hi := (88061593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 703106875359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 703106875359) = 1/(703106875359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14418 : Bounds (-88061593 / 250000000) (-352246371 / 1000000000) (Real.log (703106875359 / 1000000000000)) := by
  have h := reflection_log_14418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14419_neg : (346908791 / 1000000000) ≤ -Real.log (28274791911 / 40000000000) ∧
    -Real.log (28274791911 / 40000000000) ≤ (43363599 / 125000000) := by
  have h := checkLog_sound (w := (11725208089 / 68274791911)) (n := 12)
    (lo := (346908791 / 1000000000)) (hi := (43363599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 28274791911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 28274791911) = 1/(28274791911 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14419 : Bounds (-43363599 / 125000000) (-346908791 / 1000000000) (Real.log (28274791911 / 40000000000)) := by
  have h := reflection_log_14419_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14420_neg : (606155221 / 500000000) ≤ -Real.log (125000000000 / 420155205687) ∧
    -Real.log (125000000000 / 420155205687) ≤ (303077611 / 250000000) := by
  have h := checkLog_sound (w := (170155205687 / 670155205687)) (n := 12)
    (lo := (259581631 / 500000000)) (hi := (519163263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420155205687 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(420155205687 / 250000000000) = 1/(125000000000 / 420155205687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14420 : Bounds (606155221 / 500000000) (303077611 / 250000000) (Real.log (420155205687 / 125000000000)) := by
  have h := reflection_log_14420_neg
  have he : Real.log (420155205687 / 125000000000) = -Real.log (125000000000 / 420155205687) := by
    rw [show ((420155205687 / 125000000000) : ℝ) = ((125000000000 / 420155205687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14421_neg : (24442751 / 20000000) ≤ -Real.log (500000000000 / 1697217882717) ∧
    -Real.log (500000000000 / 1697217882717) ≤ (76383597 / 62500000) := by
  have h := checkLog_sound (w := (697217882717 / 2697217882717)) (n := 12)
    (lo := (52899037 / 100000000)) (hi := (528990371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1697217882717 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1697217882717 / 1000000000000) = 1/(500000000000 / 1697217882717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14421 : Bounds (24442751 / 20000000) (76383597 / 62500000) (Real.log (1697217882717 / 500000000000)) := by
  have h := reflection_log_14421_neg
  have he : Real.log (1697217882717 / 500000000000) = -Real.log (500000000000 / 1697217882717) := by
    rw [show ((1697217882717 / 500000000000) : ℝ) = ((500000000000 / 1697217882717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14422_neg : (2933962191 / 1000000000) ≤ -Real.log (500000000000 / 9400990099009) ∧
    -Real.log (500000000000 / 9400990099009) ≤ (733490549 / 250000000) := by
  have h := checkLog_sound (w := (1400990099009 / 17400990099009)) (n := 12)
    (lo := (161373471 / 1000000000)) (hi := (5042921 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9400990099009 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9400990099009 / 8000000000000) = 1/(500000000000 / 9400990099009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14422 : Bounds (2933962191 / 1000000000) (733490549 / 250000000) (Real.log (9400990099009 / 500000000000)) := by
  have h := reflection_log_14422_neg
  have he : Real.log (9400990099009 / 500000000000) = -Real.log (500000000000 / 9400990099009) := by
    rw [show ((9400990099009 / 500000000000) : ℝ) = ((500000000000 / 9400990099009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14423_neg : (1482846881 / 500000000) ≤ -Real.log (250000000000 / 4852040816327) ∧
    -Real.log (250000000000 / 4852040816327) ≤ (2965693767 / 1000000000) := by
  have h := checkLog_sound (w := (852040816327 / 8852040816327)) (n := 12)
    (lo := (96552521 / 500000000)) (hi := (193105043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4852040816327 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4852040816327 / 4000000000000) = 1/(250000000000 / 4852040816327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14423 : Bounds (1482846881 / 500000000) (2965693767 / 1000000000) (Real.log (4852040816327 / 250000000000)) := by
  have h := reflection_log_14423_neg
  have he : Real.log (4852040816327 / 250000000000) = -Real.log (250000000000 / 4852040816327) := by
    rw [show ((4852040816327 / 250000000000) : ℝ) = ((250000000000 / 4852040816327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14424_neg : (80560251 / 125000000) ≤ -Real.log (200 / 381) ∧
    -Real.log (200 / 381) ≤ (644482009 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 581)) (n := 12)
    (lo := (80560251 / 125000000)) (hi := (644482009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381 / 200) = 1/(200 / 381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14424 : Bounds (80560251 / 125000000) (644482009 / 1000000000) (Real.log (381 / 200)) := by
  have h := reflection_log_14424_neg
  have he : Real.log (381 / 200) = -Real.log (200 / 381) := by
    rw [show ((381 / 200) : ℝ) = ((200 / 381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14425_neg : (470775677 / 200000000) ≤ -Real.log (19 / 200) ∧
    -Real.log (19 / 200) ≤ (2353878389 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 22)) (n := 12)
    (lo := (54887369 / 200000000)) (hi := (137218423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 19) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 19) = 1/(19 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14425 : Bounds (-2353878389 / 1000000000) (-470775677 / 200000000) (Real.log (19 / 200)) := by
  have h := reflection_log_14425_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14426_neg : (90459 / 100000000) ≤ -Real.log (200000 / 200181) ∧
    -Real.log (200000 / 200181) ≤ (904591 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 400181)) (n := 12)
    (lo := (90459 / 100000000)) (hi := (904591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200181 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200181 / 200000) = 1/(200000 / 200181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14426 : Bounds (90459 / 100000000) (904591 / 1000000000) (Real.log (200181 / 200000)) := by
  have h := reflection_log_14426_neg
  have he : Real.log (200181 / 200000) = -Real.log (200000 / 200181) := by
    rw [show ((200181 / 200000) : ℝ) = ((200000 / 200181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14427_neg : (905409 / 1000000000) ≤ -Real.log (199819 / 200000) ∧
    -Real.log (199819 / 200000) ≤ (90541 / 100000000) := by
  have h := checkLog_sound (w := (181 / 399819)) (n := 12)
    (lo := (905409 / 1000000000)) (hi := (90541 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199819) = 1/(199819 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14427 : Bounds (-90541 / 100000000) (-905409 / 1000000000) (Real.log (199819 / 200000)) := by
  have h := reflection_log_14427_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14428_neg : (217254607 / 500000000) ≤ -Real.log (200000 / 308841) ∧
    -Real.log (200000 / 308841) ≤ (86901843 / 200000000) := by
  have h := checkLog_sound (w := (108841 / 508841)) (n := 12)
    (lo := (217254607 / 500000000)) (hi := (86901843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308841 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308841 / 200000) = 1/(200000 / 308841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14428 : Bounds (217254607 / 500000000) (86901843 / 200000000) (Real.log (308841 / 200000)) := by
  have h := reflection_log_14428_neg
  have he : Real.log (308841 / 200000) = -Real.log (200000 / 308841) := by
    rw [show ((308841 / 200000) : ℝ) = ((200000 / 308841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14429_neg : (785712131 / 1000000000) ≤ -Real.log (91159 / 200000) ∧
    -Real.log (91159 / 200000) ≤ (785712133 / 1000000000) := by
  have h := checkLog_sound (w := (8841 / 191159)) (n := 12)
    (lo := (92564951 / 1000000000)) (hi := (11570619 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91159) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 91159) = 1/(91159 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14429 : Bounds (-785712133 / 1000000000) (-785712131 / 1000000000) (Real.log (91159 / 200000)) := by
  have h := reflection_log_14429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14430_neg : (218382071 / 500000000) ≤ -Real.log (1000000 / 1547691) ∧
    -Real.log (1000000 / 1547691) ≤ (436764143 / 1000000000) := by
  have h := checkLog_sound (w := (547691 / 2547691)) (n := 12)
    (lo := (218382071 / 500000000)) (hi := (436764143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1547691 / 1000000) = 1/(1000000 / 1547691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14430 : Bounds (218382071 / 500000000) (436764143 / 1000000000) (Real.log (1547691 / 1000000)) := by
  have h := reflection_log_14430_neg
  have he : Real.log (1547691 / 1000000) = -Real.log (1000000 / 1547691) := by
    rw [show ((1547691 / 1000000) : ℝ) = ((1000000 / 1547691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14431_neg : (793389703 / 1000000000) ≤ -Real.log (452309 / 1000000) ∧
    -Real.log (452309 / 1000000) ≤ (158677941 / 200000000) := by
  have h := checkLog_sound (w := (47691 / 952309)) (n := 12)
    (lo := (100242523 / 1000000000)) (hi := (25060631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 452309) = 1/(452309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14431 : Bounds (-158677941 / 200000000) (-793389703 / 1000000000) (Real.log (452309 / 1000000)) := by
  have h := reflection_log_14431_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14432_neg : (356625561 / 1000000000) ≤ -Real.log (700034568519 / 1000000000000) ∧
    -Real.log (700034568519 / 1000000000000) ≤ (178312781 / 500000000) := by
  have h := checkLog_sound (w := (299965431481 / 1700034568519)) (n := 12)
    (lo := (356625561 / 1000000000)) (hi := (178312781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 700034568519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 700034568519) = 1/(700034568519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14432 : Bounds (-178312781 / 500000000) (-356625561 / 1000000000) (Real.log (700034568519 / 1000000000000)) := by
  have h := reflection_log_14432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14433_neg : (351202917 / 1000000000) ≤ -Real.log (28153636719 / 40000000000) ∧
    -Real.log (28153636719 / 40000000000) ≤ (175601459 / 500000000) := by
  have h := checkLog_sound (w := (11846363281 / 68153636719)) (n := 12)
    (lo := (351202917 / 1000000000)) (hi := (175601459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 28153636719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 28153636719) = 1/(28153636719 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14433 : Bounds (-175601459 / 500000000) (-351202917 / 1000000000) (Real.log (28153636719 / 40000000000)) := by
  have h := reflection_log_14433_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14434_neg : (610110673 / 500000000) ≤ -Real.log (31250000000 / 105873048739) ∧
    -Real.log (31250000000 / 105873048739) ≤ (305055337 / 250000000) := by
  have h := checkLog_sound (w := (43373048739 / 168373048739)) (n := 12)
    (lo := (263537083 / 500000000)) (hi := (527074167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105873048739 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(105873048739 / 62500000000) = 1/(31250000000 / 105873048739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14434 : Bounds (610110673 / 500000000) (305055337 / 250000000) (Real.log (105873048739 / 31250000000)) := by
  have h := reflection_log_14434_neg
  have he : Real.log (105873048739 / 31250000000) = -Real.log (31250000000 / 105873048739) := by
    rw [show ((105873048739 / 31250000000) : ℝ) = ((31250000000 / 105873048739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14435_neg : (615076923 / 500000000) ≤ -Real.log (125000000000 / 427719490437) ∧
    -Real.log (125000000000 / 427719490437) ≤ (153769231 / 125000000) := by
  have h := checkLog_sound (w := (177719490437 / 677719490437)) (n := 12)
    (lo := (268503333 / 500000000)) (hi := (537006667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427719490437 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(427719490437 / 250000000000) = 1/(125000000000 / 427719490437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14435 : Bounds (615076923 / 500000000) (153769231 / 125000000) (Real.log (427719490437 / 125000000000)) := by
  have h := reflection_log_14435_neg
  have he : Real.log (427719490437 / 125000000000) = -Real.log (125000000000 / 427719490437) := by
    rw [show ((427719490437 / 125000000000) : ℝ) = ((125000000000 / 427719490437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14436_neg : (1482846881 / 500000000) ≤ -Real.log (500000000000 / 9704081632653) ∧
    -Real.log (500000000000 / 9704081632653) ≤ (2965693767 / 1000000000) := by
  have h := checkLog_sound (w := (1704081632653 / 17704081632653)) (n := 12)
    (lo := (96552521 / 500000000)) (hi := (193105043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9704081632653 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9704081632653 / 8000000000000) = 1/(500000000000 / 9704081632653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14436 : Bounds (1482846881 / 500000000) (2965693767 / 1000000000) (Real.log (9704081632653 / 500000000000)) := by
  have h := reflection_log_14436_neg
  have he : Real.log (9704081632653 / 500000000000) = -Real.log (500000000000 / 9704081632653) := by
    rw [show ((9704081632653 / 500000000000) : ℝ) = ((500000000000 / 9704081632653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14437_neg : (2998360393 / 1000000000) ≤ -Real.log (250000000000 / 5013157894737) ∧
    -Real.log (250000000000 / 5013157894737) ≤ (1499180199 / 500000000) := by
  have h := checkLog_sound (w := (1013157894737 / 9013157894737)) (n := 12)
    (lo := (225771673 / 1000000000)) (hi := (112885837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5013157894737 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5013157894737 / 4000000000000) = 1/(250000000000 / 5013157894737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14437 : Bounds (2998360393 / 1000000000) (1499180199 / 500000000) (Real.log (5013157894737 / 250000000000)) := by
  have h := reflection_log_14437_neg
  have he : Real.log (5013157894737 / 250000000000) = -Real.log (250000000000 / 5013157894737) := by
    rw [show ((5013157894737 / 250000000000) : ℝ) = ((250000000000 / 5013157894737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14438_neg : (646055573 / 1000000000) ≤ -Real.log (250 / 477) ∧
    -Real.log (250 / 477) ≤ (323027787 / 500000000) := by
  have h := checkLog_sound (w := (227 / 727)) (n := 12)
    (lo := (646055573 / 1000000000)) (hi := (323027787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477 / 250) = 1/(250 / 477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14438 : Bounds (646055573 / 1000000000) (323027787 / 500000000) (Real.log (477 / 250)) := by
  have h := reflection_log_14438_neg
  have he : Real.log (477 / 250) = -Real.log (250 / 477) := by
    rw [show ((477 / 250) : ℝ) = ((250 / 477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14439_neg : (23859667 / 10000000) ≤ -Real.log (23 / 250) ∧
    -Real.log (23 / 250) ≤ (149122919 / 62500000) := by
  have h := checkLog_sound (w := (33 / 217)) (n := 12)
    (lo := (7663129 / 25000000)) (hi := (306525161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 92) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 92) = 1/(23 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14439 : Bounds (-149122919 / 62500000) (-23859667 / 10000000) (Real.log (23 / 250)) := by
  have h := reflection_log_14439_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14440_neg : (226897 / 250000000) ≤ -Real.log (250000 / 250227) ∧
    -Real.log (250000 / 250227) ≤ (907589 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 500227)) (n := 12)
    (lo := (226897 / 250000000)) (hi := (907589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250227 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250227 / 250000) = 1/(250000 / 250227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14440 : Bounds (226897 / 250000000) (907589 / 1000000000) (Real.log (250227 / 250000)) := by
  have h := reflection_log_14440_neg
  have he : Real.log (250227 / 250000) = -Real.log (250000 / 250227) := by
    rw [show ((250227 / 250000) : ℝ) = ((250000 / 250227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14441_neg : (227103 / 250000000) ≤ -Real.log (249773 / 250000) ∧
    -Real.log (249773 / 250000) ≤ (908413 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 499773)) (n := 12)
    (lo := (227103 / 250000000)) (hi := (908413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249773) = 1/(249773 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14441 : Bounds (-908413 / 1000000000) (-227103 / 250000000) (Real.log (249773 / 250000)) := by
  have h := reflection_log_14441_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14442_neg : (5454107 / 12500000) ≤ -Real.log (1000000 / 1547017) ∧
    -Real.log (1000000 / 1547017) ≤ (436328561 / 1000000000) := by
  have h := checkLog_sound (w := (547017 / 2547017)) (n := 12)
    (lo := (5454107 / 12500000)) (hi := (436328561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1547017 / 1000000) = 1/(1000000 / 1547017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14442 : Bounds (5454107 / 12500000) (436328561 / 1000000000) (Real.log (1547017 / 1000000)) := by
  have h := reflection_log_14442_neg
  have he : Real.log (1547017 / 1000000) = -Real.log (1000000 / 1547017) := by
    rw [show ((1547017 / 1000000) : ℝ) = ((1000000 / 1547017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14443_neg : (791900681 / 1000000000) ≤ -Real.log (452983 / 1000000) ∧
    -Real.log (452983 / 1000000) ≤ (791900683 / 1000000000) := by
  have h := checkLog_sound (w := (47017 / 952983)) (n := 12)
    (lo := (98753501 / 1000000000)) (hi := (49376751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452983) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 452983) = 1/(452983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14443 : Bounds (-791900683 / 1000000000) (-791900681 / 1000000000) (Real.log (452983 / 1000000)) := by
  have h := reflection_log_14443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14444_neg : (219296469 / 500000000) ≤ -Real.log (250000 / 387631) ∧
    -Real.log (250000 / 387631) ≤ (438592939 / 1000000000) := by
  have h := checkLog_sound (w := (137631 / 637631)) (n := 12)
    (lo := (219296469 / 500000000)) (hi := (438592939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387631 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387631 / 250000) = 1/(250000 / 387631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14444 : Bounds (219296469 / 500000000) (438592939 / 1000000000) (Real.log (387631 / 250000)) := by
  have h := reflection_log_14444_neg
  have he : Real.log (387631 / 250000) = -Real.log (250000 / 387631) := by
    rw [show ((387631 / 250000) : ℝ) = ((250000 / 387631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14445_neg : (399836409 / 500000000) ≤ -Real.log (112369 / 250000) ∧
    -Real.log (112369 / 250000) ≤ (39983641 / 50000000) := by
  have h := checkLog_sound (w := (12631 / 237369)) (n := 12)
    (lo := (53262819 / 500000000)) (hi := (106525639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 112369) = 1/(112369 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14445 : Bounds (-39983641 / 50000000) (-399836409 / 500000000) (Real.log (112369 / 250000)) := by
  have h := reflection_log_14445_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14446_neg : (9026997 / 25000000) ≤ -Real.log (43557707839 / 62500000000) ∧
    -Real.log (43557707839 / 62500000000) ≤ (361079881 / 1000000000) := by
  have h := checkLog_sound (w := (18942292161 / 106057707839)) (n := 12)
    (lo := (9026997 / 25000000)) (hi := (361079881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 43557707839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 43557707839) = 1/(43557707839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14446 : Bounds (-361079881 / 1000000000) (-9026997 / 25000000) (Real.log (43557707839 / 62500000000)) := by
  have h := reflection_log_14446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14447_neg : (355572121 / 1000000000) ≤ -Real.log (700772401711 / 1000000000000) ∧
    -Real.log (700772401711 / 1000000000000) ≤ (177786061 / 500000000) := by
  have h := checkLog_sound (w := (299227598289 / 1700772401711)) (n := 12)
    (lo := (355572121 / 1000000000)) (hi := (177786061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 700772401711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 700772401711) = 1/(700772401711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14447 : Bounds (-177786061 / 500000000) (-355572121 / 1000000000) (Real.log (700772401711 / 1000000000000)) := by
  have h := reflection_log_14447_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14448_neg : (1228229241 / 1000000000) ≤ -Real.log (500000000000 / 1707588364243) ∧
    -Real.log (500000000000 / 1707588364243) ≤ (1228229243 / 1000000000) := by
  have h := checkLog_sound (w := (707588364243 / 2707588364243)) (n := 12)
    (lo := (535082061 / 1000000000)) (hi := (267541031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1707588364243 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1707588364243 / 1000000000000) = 1/(500000000000 / 1707588364243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14448 : Bounds (1228229241 / 1000000000) (1228229243 / 1000000000) (Real.log (1707588364243 / 500000000000)) := by
  have h := reflection_log_14448_neg
  have he : Real.log (1707588364243 / 500000000000) = -Real.log (500000000000 / 1707588364243) := by
    rw [show ((1707588364243 / 500000000000) : ℝ) = ((500000000000 / 1707588364243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14449_neg : (309566439 / 250000000) ≤ -Real.log (125000000000 / 431203223309) ∧
    -Real.log (125000000000 / 431203223309) ≤ (619132879 / 500000000) := by
  have h := checkLog_sound (w := (181203223309 / 681203223309)) (n := 12)
    (lo := (34069911 / 62500000)) (hi := (545118577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431203223309 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(431203223309 / 250000000000) = 1/(125000000000 / 431203223309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14449 : Bounds (309566439 / 250000000) (619132879 / 500000000) (Real.log (431203223309 / 125000000000)) := by
  have h := reflection_log_14449_neg
  have he : Real.log (431203223309 / 125000000000) = -Real.log (125000000000 / 431203223309) := by
    rw [show ((431203223309 / 125000000000) : ℝ) = ((125000000000 / 431203223309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14450_neg : (2998360393 / 1000000000) ≤ -Real.log (500000000000 / 10026315789473) ∧
    -Real.log (500000000000 / 10026315789473) ≤ (1499180199 / 500000000) := by
  have h := checkLog_sound (w := (2026315789473 / 18026315789473)) (n := 12)
    (lo := (225771673 / 1000000000)) (hi := (112885837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10026315789473 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10026315789473 / 8000000000000) = 1/(500000000000 / 10026315789473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14450 : Bounds (2998360393 / 1000000000) (1499180199 / 500000000) (Real.log (10026315789473 / 500000000000)) := by
  have h := reflection_log_14450_neg
  have he : Real.log (10026315789473 / 500000000000) = -Real.log (500000000000 / 10026315789473) := by
    rw [show ((10026315789473 / 500000000000) : ℝ) = ((500000000000 / 10026315789473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14451_neg : (11843837 / 3906250) ≤ -Real.log (31250000000 / 648097826087) ∧
    -Real.log (31250000000 / 648097826087) ≤ (3032022277 / 1000000000) := by
  have h := checkLog_sound (w := (148097826087 / 1148097826087)) (n := 12)
    (lo := (16214597 / 62500000)) (hi := (259433553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648097826087 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(648097826087 / 500000000000) = 1/(31250000000 / 648097826087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14451 : Bounds (11843837 / 3906250) (3032022277 / 1000000000) (Real.log (648097826087 / 31250000000)) := by
  have h := reflection_log_14451_neg
  have he : Real.log (648097826087 / 31250000000) = -Real.log (31250000000 / 648097826087) := by
    rw [show ((648097826087 / 31250000000) : ℝ) = ((31250000000 / 648097826087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14452_neg : (129525333 / 200000000) ≤ -Real.log (1000 / 1911) ∧
    -Real.log (1000 / 1911) ≤ (323813333 / 500000000) := by
  have h := checkLog_sound (w := (911 / 2911)) (n := 12)
    (lo := (129525333 / 200000000)) (hi := (323813333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1911 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1911 / 1000) = 1/(1000 / 1911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14452 : Bounds (129525333 / 200000000) (323813333 / 500000000) (Real.log (1911 / 1000)) := by
  have h := reflection_log_14452_neg
  have he : Real.log (1911 / 1000) = -Real.log (1000 / 1911) := by
    rw [show ((1911 / 1000) : ℝ) = ((1000 / 1911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14453_neg : (2419118907 / 1000000000) ≤ -Real.log (89 / 1000) ∧
    -Real.log (89 / 1000) ≤ (2419118911 / 1000000000) := by
  have h := checkLog_sound (w := (18 / 107)) (n := 12)
    (lo := (339677367 / 1000000000)) (hi := (42459671 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 89) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 89) = 1/(89 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14453 : Bounds (-2419118911 / 1000000000) (-2419118907 / 1000000000) (Real.log (89 / 1000)) := by
  have h := reflection_log_14453_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14454_neg : (182117 / 200000000) ≤ -Real.log (1000000 / 1000911) ∧
    -Real.log (1000000 / 1000911) ≤ (455293 / 500000000) := by
  have h := checkLog_sound (w := (911 / 2000911)) (n := 12)
    (lo := (182117 / 200000000)) (hi := (455293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000911 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000911 / 1000000) = 1/(1000000 / 1000911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14454 : Bounds (182117 / 200000000) (455293 / 500000000) (Real.log (1000911 / 1000000)) := by
  have h := reflection_log_14454_neg
  have he : Real.log (1000911 / 1000000) = -Real.log (1000000 / 1000911) := by
    rw [show ((1000911 / 1000000) : ℝ) = ((1000000 / 1000911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14455_neg : (182283 / 200000000) ≤ -Real.log (999089 / 1000000) ∧
    -Real.log (999089 / 1000000) ≤ (113927 / 125000000) := by
  have h := checkLog_sound (w := (911 / 1999089)) (n := 12)
    (lo := (182283 / 200000000)) (hi := (113927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999089) = 1/(999089 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14455 : Bounds (-113927 / 125000000) (-182283 / 200000000) (Real.log (999089 / 1000000)) := by
  have h := reflection_log_14455_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14456_neg : (219079721 / 500000000) ≤ -Real.log (250000 / 387463) ∧
    -Real.log (250000 / 387463) ≤ (438159443 / 1000000000) := by
  have h := checkLog_sound (w := (137463 / 637463)) (n := 12)
    (lo := (219079721 / 500000000)) (hi := (438159443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387463 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387463 / 250000) = 1/(250000 / 387463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14456 : Bounds (219079721 / 500000000) (438159443 / 1000000000) (Real.log (387463 / 250000)) := by
  have h := reflection_log_14456_neg
  have he : Real.log (387463 / 250000) = -Real.log (250000 / 387463) := by
    rw [show ((387463 / 250000) : ℝ) = ((250000 / 387463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14457_neg : (39908943 / 50000000) ≤ -Real.log (112537 / 250000) ∧
    -Real.log (112537 / 250000) ≤ (399089431 / 500000000) := by
  have h := checkLog_sound (w := (12463 / 237537)) (n := 12)
    (lo := (41028 / 390625)) (hi := (105031681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112537) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 112537) = 1/(112537 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14457 : Bounds (-399089431 / 500000000) (-39908943 / 50000000) (Real.log (112537 / 250000)) := by
  have h := reflection_log_14457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14458_neg : (88086769 / 200000000) ≤ -Real.log (1000000 / 1553381) ∧
    -Real.log (1000000 / 1553381) ≤ (220216923 / 500000000) := by
  have h := checkLog_sound (w := (553381 / 2553381)) (n := 12)
    (lo := (88086769 / 200000000)) (hi := (220216923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1553381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1553381 / 1000000) = 1/(1000000 / 1553381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14458 : Bounds (88086769 / 200000000) (220216923 / 500000000) (Real.log (1553381 / 1000000)) := by
  have h := reflection_log_14458_neg
  have he : Real.log (1553381 / 1000000) = -Real.log (1000000 / 1553381) := by
    rw [show ((1553381 / 1000000) : ℝ) = ((1000000 / 1553381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14459_neg : (201512349 / 250000000) ≤ -Real.log (446619 / 1000000) ∧
    -Real.log (446619 / 1000000) ≤ (403024699 / 500000000) := by
  have h := checkLog_sound (w := (53381 / 946619)) (n := 12)
    (lo := (14112777 / 125000000)) (hi := (112902217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 446619) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 446619) = 1/(446619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14459 : Bounds (-403024699 / 500000000) (-201512349 / 250000000) (Real.log (446619 / 1000000)) := by
  have h := reflection_log_14459_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14460_neg : (365615551 / 1000000000) ≤ -Real.log (693769468839 / 1000000000000) ∧
    -Real.log (693769468839 / 1000000000000) ≤ (5712743 / 15625000) := by
  have h := checkLog_sound (w := (306230531161 / 1693769468839)) (n := 12)
    (lo := (365615551 / 1000000000)) (hi := (5712743 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 693769468839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 693769468839) = 1/(693769468839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14460 : Bounds (-5712743 / 15625000) (-365615551 / 1000000000) (Real.log (693769468839 / 1000000000000)) := by
  have h := reflection_log_14460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14461_neg : (180009709 / 500000000) ≤ -Real.log (43603923631 / 62500000000) ∧
    -Real.log (43603923631 / 62500000000) ≤ (360019419 / 1000000000) := by
  have h := checkLog_sound (w := (18896076369 / 106103923631)) (n := 12)
    (lo := (180009709 / 500000000)) (hi := (360019419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 43603923631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 43603923631) = 1/(43603923631 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14461 : Bounds (-360019419 / 1000000000) (-180009709 / 500000000) (Real.log (43603923631 / 62500000000)) := by
  have h := reflection_log_14461_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14462_neg : (1236338303 / 1000000000) ≤ -Real.log (250000000000 / 860745799159) ∧
    -Real.log (250000000000 / 860745799159) ≤ (247267661 / 200000000) := by
  have h := checkLog_sound (w := (360745799159 / 1360745799159)) (n := 12)
    (lo := (543191123 / 1000000000)) (hi := (135797781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((860745799159 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(860745799159 / 500000000000) = 1/(250000000000 / 860745799159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14462 : Bounds (1236338303 / 1000000000) (247267661 / 200000000) (Real.log (860745799159 / 250000000000)) := by
  have h := reflection_log_14462_neg
  have he : Real.log (860745799159 / 250000000000) = -Real.log (250000000000 / 860745799159) := by
    rw [show ((860745799159 / 250000000000) : ℝ) = ((250000000000 / 860745799159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14463_neg : (1246483241 / 1000000000) ≤ -Real.log (250000000000 / 869522456501) ∧
    -Real.log (250000000000 / 869522456501) ≤ (1246483243 / 1000000000) := by
  have h := checkLog_sound (w := (369522456501 / 1369522456501)) (n := 12)
    (lo := (553336061 / 1000000000)) (hi := (276668031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869522456501 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(869522456501 / 500000000000) = 1/(250000000000 / 869522456501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14463 : Bounds (1246483241 / 1000000000) (1246483243 / 1000000000) (Real.log (869522456501 / 250000000000)) := by
  have h := reflection_log_14463_neg
  have he : Real.log (869522456501 / 250000000000) = -Real.log (250000000000 / 869522456501) := by
    rw [show ((869522456501 / 250000000000) : ℝ) = ((250000000000 / 869522456501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


