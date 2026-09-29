-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0175__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0175__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T07:38:34.183438+00:00
-- url     : https://prove2.me/theorems/2234bdd3-db61-40e5-a4ba-3eb048e4f722
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0175 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0176, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0175 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0176, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0177)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0175 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0176, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0177)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0175 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0176, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0177) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0175 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0176, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0177).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0175 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11200_neg : (404081 / 1000000000) ≤ -Real.log (249899 / 250000) ∧
    -Real.log (249899 / 250000) ≤ (202041 / 500000000) := by
  have h := checkLog_sound (w := (101 / 499899)) (n := 12)
    (lo := (404081 / 1000000000)) (hi := (202041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249899) = 1/(249899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11200 : Bounds (-202041 / 500000000) (-404081 / 1000000000) (Real.log (249899 / 250000)) := by
  have h := reflection_log_11200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11201_neg : (188557903 / 1000000000) ≤ -Real.log (1000000 / 1207507) ∧
    -Real.log (1000000 / 1207507) ≤ (11784869 / 62500000) := by
  have h := checkLog_sound (w := (207507 / 2207507)) (n := 12)
    (lo := (188557903 / 1000000000)) (hi := (11784869 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207507 / 1000000) = 1/(1000000 / 1207507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11201 : Bounds (188557903 / 1000000000) (11784869 / 62500000) (Real.log (1207507 / 1000000)) := by
  have h := reflection_log_11201_neg
  have he : Real.log (1207507 / 1000000) = -Real.log (1000000 / 1207507) := by
    rw [show ((1207507 / 1000000) : ℝ) = ((1000000 / 1207507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11202_neg : (116285803 / 500000000) ≤ -Real.log (792493 / 1000000) ∧
    -Real.log (792493 / 1000000) ≤ (232571607 / 1000000000) := by
  have h := checkLog_sound (w := (207507 / 1792493)) (n := 12)
    (lo := (116285803 / 500000000)) (hi := (232571607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792493) = 1/(792493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11202 : Bounds (-232571607 / 1000000000) (-116285803 / 500000000) (Real.log (792493 / 1000000)) := by
  have h := reflection_log_11202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11203_neg : (369797 / 1953125) ≤ -Real.log (1000000 / 1208447) ∧
    -Real.log (1000000 / 1208447) ≤ (37867213 / 200000000) := by
  have h := checkLog_sound (w := (208447 / 2208447)) (n := 12)
    (lo := (369797 / 1953125)) (hi := (37867213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208447 / 1000000) = 1/(1000000 / 1208447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11203 : Bounds (369797 / 1953125) (37867213 / 200000000) (Real.log (1208447 / 1000000)) := by
  have h := reflection_log_11203_neg
  have he : Real.log (1208447 / 1000000) = -Real.log (1000000 / 1208447) := by
    rw [show ((1208447 / 1000000) : ℝ) = ((1000000 / 1208447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11204_neg : (5843961 / 25000000) ≤ -Real.log (791553 / 1000000) ∧
    -Real.log (791553 / 1000000) ≤ (233758441 / 1000000000) := by
  have h := checkLog_sound (w := (208447 / 1791553)) (n := 12)
    (lo := (5843961 / 25000000)) (hi := (233758441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791553) = 1/(791553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11204 : Bounds (-233758441 / 1000000000) (-5843961 / 25000000) (Real.log (791553 / 1000000)) := by
  have h := reflection_log_11204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11205_neg : (5552797 / 125000000) ≤ -Real.log (956549848191 / 1000000000000) ∧
    -Real.log (956549848191 / 1000000000000) ≤ (44422377 / 1000000000) := by
  have h := checkLog_sound (w := (43450151809 / 1956549848191)) (n := 12)
    (lo := (5552797 / 125000000)) (hi := (44422377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956549848191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956549848191) = 1/(956549848191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11205 : Bounds (-44422377 / 1000000000) (-5552797 / 125000000) (Real.log (956549848191 / 1000000000000)) := by
  have h := reflection_log_11205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11206_neg : (22006851 / 500000000) ≤ -Real.log (956940844951 / 1000000000000) ∧
    -Real.log (956940844951 / 1000000000000) ≤ (44013703 / 1000000000) := by
  have h := checkLog_sound (w := (43059155049 / 1956940844951)) (n := 12)
    (lo := (22006851 / 500000000)) (hi := (44013703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956940844951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956940844951) = 1/(956940844951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11206 : Bounds (-44013703 / 1000000000) (-22006851 / 500000000) (Real.log (956940844951 / 1000000000000)) := by
  have h := reflection_log_11206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11207_neg : (421129509 / 1000000000) ≤ -Real.log (500000000000 / 761840798593) ∧
    -Real.log (500000000000 / 761840798593) ≤ (42112951 / 100000000) := by
  have h := checkLog_sound (w := (261840798593 / 1261840798593)) (n := 12)
    (lo := (421129509 / 1000000000)) (hi := (42112951 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761840798593 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761840798593 / 500000000000) = 1/(500000000000 / 761840798593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11207 : Bounds (421129509 / 1000000000) (42112951 / 100000000) (Real.log (761840798593 / 500000000000)) := by
  have h := reflection_log_11207_neg
  have he : Real.log (761840798593 / 500000000000) = -Real.log (500000000000 / 761840798593) := by
    rw [show ((761840798593 / 500000000000) : ℝ) = ((500000000000 / 761840798593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11208_neg : (52886813 / 125000000) ≤ -Real.log (250000000000 / 381669641831) ∧
    -Real.log (250000000000 / 381669641831) ≤ (84618901 / 200000000) := by
  have h := checkLog_sound (w := (131669641831 / 631669641831)) (n := 12)
    (lo := (52886813 / 125000000)) (hi := (84618901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381669641831 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381669641831 / 250000000000) = 1/(250000000000 / 381669641831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11208 : Bounds (52886813 / 125000000) (84618901 / 200000000) (Real.log (381669641831 / 250000000000)) := by
  have h := reflection_log_11208_neg
  have he : Real.log (381669641831 / 250000000000) = -Real.log (250000000000 / 381669641831) := by
    rw [show ((381669641831 / 250000000000) : ℝ) = ((250000000000 / 381669641831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11209_neg : (427225483 / 500000000) ≤ -Real.log (250000000000 / 587520938023) ∧
    -Real.log (250000000000 / 587520938023) ≤ (106806371 / 125000000) := by
  have h := checkLog_sound (w := (87520938023 / 1087520938023)) (n := 12)
    (lo := (80651893 / 500000000)) (hi := (161303787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587520938023 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(587520938023 / 500000000000) = 1/(250000000000 / 587520938023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11209 : Bounds (427225483 / 500000000) (106806371 / 125000000) (Real.log (587520938023 / 250000000000)) := by
  have h := reflection_log_11209_neg
  have he : Real.log (587520938023 / 250000000000) = -Real.log (250000000000 / 587520938023) := by
    rw [show ((587520938023 / 250000000000) : ℝ) = ((250000000000 / 587520938023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11210_neg : (214209979 / 250000000) ≤ -Real.log (250000000000 / 588926174497) ∧
    -Real.log (250000000000 / 588926174497) ≤ (428419959 / 500000000) := by
  have h := checkLog_sound (w := (88926174497 / 1088926174497)) (n := 12)
    (lo := (2557699 / 15625000)) (hi := (163692737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588926174497 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(588926174497 / 500000000000) = 1/(250000000000 / 588926174497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11210 : Bounds (214209979 / 250000000) (428419959 / 500000000) (Real.log (588926174497 / 250000000000)) := by
  have h := reflection_log_11210_neg
  have he : Real.log (588926174497 / 250000000000) = -Real.log (250000000000 / 588926174497) := by
    rw [show ((588926174497 / 250000000000) : ℝ) = ((250000000000 / 588926174497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11211_neg : (170018651 / 500000000) ≤ -Real.log (200 / 281) ∧
    -Real.log (200 / 281) ≤ (340037303 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 481)) (n := 12)
    (lo := (170018651 / 500000000)) (hi := (340037303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(281 / 200) = 1/(200 / 281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11211 : Bounds (170018651 / 500000000) (340037303 / 1000000000) (Real.log (281 / 200)) := by
  have h := reflection_log_11211_neg
  have he : Real.log (281 / 200) = -Real.log (200 / 281) := by
    rw [show ((281 / 200) : ℝ) = ((200 / 281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11212_neg : (519193873 / 1000000000) ≤ -Real.log (119 / 200) ∧
    -Real.log (119 / 200) ≤ (259596937 / 500000000) := by
  have h := checkLog_sound (w := (81 / 319)) (n := 12)
    (lo := (519193873 / 1000000000)) (hi := (259596937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 119) = 1/(119 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11212 : Bounds (-259596937 / 500000000) (-519193873 / 1000000000) (Real.log (119 / 200)) := by
  have h := reflection_log_11212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11213_neg : (202459 / 500000000) ≤ -Real.log (200000 / 200081) ∧
    -Real.log (200000 / 200081) ≤ (404919 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 400081)) (n := 12)
    (lo := (202459 / 500000000)) (hi := (404919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200081 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200081 / 200000) = 1/(200000 / 200081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11213 : Bounds (202459 / 500000000) (404919 / 1000000000) (Real.log (200081 / 200000)) := by
  have h := reflection_log_11213_neg
  have he : Real.log (200081 / 200000) = -Real.log (200000 / 200081) := by
    rw [show ((200081 / 200000) : ℝ) = ((200000 / 200081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11214_neg : (202541 / 500000000) ≤ -Real.log (199919 / 200000) ∧
    -Real.log (199919 / 200000) ≤ (405083 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 399919)) (n := 12)
    (lo := (202541 / 500000000)) (hi := (405083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199919) = 1/(199919 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11214 : Bounds (-405083 / 1000000000) (-202541 / 500000000) (Real.log (199919 / 200000)) := by
  have h := reflection_log_11214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11215_neg : (47252907 / 250000000) ≤ -Real.log (200000 / 241611) ∧
    -Real.log (200000 / 241611) ≤ (189011629 / 1000000000) := by
  have h := checkLog_sound (w := (41611 / 441611)) (n := 12)
    (lo := (47252907 / 250000000)) (hi := (189011629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241611 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241611 / 200000) = 1/(200000 / 241611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11215 : Bounds (47252907 / 250000000) (189011629 / 1000000000) (Real.log (241611 / 200000)) := by
  have h := reflection_log_11215_neg
  have he : Real.log (241611 / 200000) = -Real.log (200000 / 241611) := by
    rw [show ((241611 / 200000) : ℝ) = ((200000 / 241611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11216_neg : (116631667 / 500000000) ≤ -Real.log (158389 / 200000) ∧
    -Real.log (158389 / 200000) ≤ (46652667 / 200000000) := by
  have h := checkLog_sound (w := (41611 / 358389)) (n := 12)
    (lo := (116631667 / 500000000)) (hi := (46652667 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158389) = 1/(158389 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11216 : Bounds (-46652667 / 200000000) (-116631667 / 500000000) (Real.log (158389 / 200000)) := by
  have h := reflection_log_11216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11217_neg : (37957887 / 200000000) ≤ -Real.log (200000 / 241799) ∧
    -Real.log (200000 / 241799) ≤ (47447359 / 250000000) := by
  have h := checkLog_sound (w := (41799 / 441799)) (n := 12)
    (lo := (37957887 / 200000000)) (hi := (47447359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241799 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241799 / 200000) = 1/(200000 / 241799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11217 : Bounds (37957887 / 200000000) (47447359 / 250000000) (Real.log (241799 / 200000)) := by
  have h := reflection_log_11217_neg
  have he : Real.log (241799 / 200000) = -Real.log (200000 / 241799) := by
    rw [show ((241799 / 200000) : ℝ) = ((200000 / 241799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11218_neg : (23445099 / 100000000) ≤ -Real.log (158201 / 200000) ∧
    -Real.log (158201 / 200000) ≤ (234450991 / 1000000000) := by
  have h := checkLog_sound (w := (41799 / 358201)) (n := 12)
    (lo := (23445099 / 100000000)) (hi := (234450991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158201) = 1/(158201 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11218 : Bounds (-234450991 / 1000000000) (-23445099 / 100000000) (Real.log (158201 / 200000)) := by
  have h := reflection_log_11218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11219_neg : (22330777 / 500000000) ≤ -Real.log (38252843599 / 40000000000) ∧
    -Real.log (38252843599 / 40000000000) ≤ (8932311 / 200000000) := by
  have h := checkLog_sound (w := (1747156401 / 78252843599)) (n := 12)
    (lo := (22330777 / 500000000)) (hi := (8932311 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38252843599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38252843599) = 1/(38252843599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11219 : Bounds (-8932311 / 200000000) (-22330777 / 500000000) (Real.log (38252843599 / 40000000000)) := by
  have h := reflection_log_11219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11220_neg : (8850341 / 200000000) ≤ -Real.log (38268524679 / 40000000000) ∧
    -Real.log (38268524679 / 40000000000) ≤ (22125853 / 500000000) := by
  have h := checkLog_sound (w := (1731475321 / 78268524679)) (n := 12)
    (lo := (8850341 / 200000000)) (hi := (22125853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38268524679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38268524679) = 1/(38268524679 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11220 : Bounds (-22125853 / 500000000) (-8850341 / 200000000) (Real.log (38268524679 / 40000000000)) := by
  have h := reflection_log_11220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11221_neg : (211137481 / 500000000) ≤ -Real.log (100000000000 / 152542790219) ∧
    -Real.log (100000000000 / 152542790219) ≤ (422274963 / 1000000000) := by
  have h := checkLog_sound (w := (52542790219 / 252542790219)) (n := 12)
    (lo := (211137481 / 500000000)) (hi := (422274963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152542790219 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152542790219 / 100000000000) = 1/(100000000000 / 152542790219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11221 : Bounds (211137481 / 500000000) (422274963 / 1000000000) (Real.log (152542790219 / 100000000000)) := by
  have h := reflection_log_11221_neg
  have he : Real.log (152542790219 / 100000000000) = -Real.log (100000000000 / 152542790219) := by
    rw [show ((152542790219 / 100000000000) : ℝ) = ((100000000000 / 152542790219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11222_neg : (212120213 / 500000000) ≤ -Real.log (500000000000 / 764214511919) ∧
    -Real.log (500000000000 / 764214511919) ≤ (424240427 / 1000000000) := by
  have h := checkLog_sound (w := (264214511919 / 1264214511919)) (n := 12)
    (lo := (212120213 / 500000000)) (hi := (424240427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764214511919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764214511919 / 500000000000) = 1/(500000000000 / 764214511919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11222 : Bounds (212120213 / 500000000) (424240427 / 1000000000) (Real.log (764214511919 / 500000000000)) := by
  have h := reflection_log_11222_neg
  have he : Real.log (764214511919 / 500000000000) = -Real.log (500000000000 / 764214511919) := by
    rw [show ((764214511919 / 500000000000) : ℝ) = ((500000000000 / 764214511919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11223_neg : (214209979 / 250000000) ≤ -Real.log (500000000000 / 1177852348993) ∧
    -Real.log (500000000000 / 1177852348993) ≤ (428419959 / 500000000) := by
  have h := checkLog_sound (w := (177852348993 / 2177852348993)) (n := 12)
    (lo := (2557699 / 15625000)) (hi := (163692737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177852348993 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1177852348993 / 1000000000000) = 1/(500000000000 / 1177852348993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11223 : Bounds (214209979 / 250000000) (428419959 / 500000000) (Real.log (1177852348993 / 500000000000)) := by
  have h := reflection_log_11223_neg
  have he : Real.log (1177852348993 / 500000000000) = -Real.log (500000000000 / 1177852348993) := by
    rw [show ((1177852348993 / 500000000000) : ℝ) = ((500000000000 / 1177852348993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11224_neg : (34369247 / 40000000) ≤ -Real.log (125000000000 / 295168067227) ∧
    -Real.log (125000000000 / 295168067227) ≤ (859231177 / 1000000000) := by
  have h := checkLog_sound (w := (45168067227 / 545168067227)) (n := 12)
    (lo := (33216799 / 200000000)) (hi := (41520999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295168067227 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(295168067227 / 250000000000) = 1/(125000000000 / 295168067227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11224 : Bounds (34369247 / 40000000) (859231177 / 1000000000) (Real.log (295168067227 / 125000000000)) := by
  have h := reflection_log_11224_neg
  have he : Real.log (295168067227 / 125000000000) = -Real.log (125000000000 / 295168067227) := by
    rw [show ((295168067227 / 125000000000) : ℝ) = ((125000000000 / 295168067227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11225_neg : (340748793 / 1000000000) ≤ -Real.log (500 / 703) ∧
    -Real.log (500 / 703) ≤ (170374397 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1203)) (n := 12)
    (lo := (340748793 / 1000000000)) (hi := (170374397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703 / 500) = 1/(500 / 703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11225 : Bounds (340748793 / 1000000000) (170374397 / 500000000) (Real.log (703 / 500)) := by
  have h := reflection_log_11225_neg
  have he : Real.log (703 / 500) = -Real.log (500 / 703) := by
    rw [show ((703 / 500) : ℝ) = ((500 / 703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11226_neg : (520875959 / 1000000000) ≤ -Real.log (297 / 500) ∧
    -Real.log (297 / 500) ≤ (13021899 / 25000000) := by
  have h := checkLog_sound (w := (203 / 797)) (n := 12)
    (lo := (520875959 / 1000000000)) (hi := (13021899 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 297) = 1/(297 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11226 : Bounds (-13021899 / 25000000) (-520875959 / 1000000000) (Real.log (297 / 500)) := by
  have h := reflection_log_11226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11227_neg : (405917 / 1000000000) ≤ -Real.log (500000 / 500203) ∧
    -Real.log (500000 / 500203) ≤ (202959 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1000203)) (n := 12)
    (lo := (405917 / 1000000000)) (hi := (202959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500203 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500203 / 500000) = 1/(500000 / 500203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11227 : Bounds (405917 / 1000000000) (202959 / 500000000) (Real.log (500203 / 500000)) := by
  have h := reflection_log_11227_neg
  have he : Real.log (500203 / 500000) = -Real.log (500000 / 500203) := by
    rw [show ((500203 / 500000) : ℝ) = ((500000 / 500203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11228_neg : (203041 / 500000000) ≤ -Real.log (499797 / 500000) ∧
    -Real.log (499797 / 500000) ≤ (406083 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 999797)) (n := 12)
    (lo := (203041 / 500000000)) (hi := (406083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499797) = 1/(499797 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11228 : Bounds (-406083 / 1000000000) (-203041 / 500000000) (Real.log (499797 / 500000)) := by
  have h := reflection_log_11228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11229_neg : (189465147 / 1000000000) ≤ -Real.log (1000000 / 1208603) ∧
    -Real.log (1000000 / 1208603) ≤ (47366287 / 250000000) := by
  have h := checkLog_sound (w := (208603 / 2208603)) (n := 12)
    (lo := (189465147 / 1000000000)) (hi := (47366287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208603 / 1000000) = 1/(1000000 / 1208603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11229 : Bounds (189465147 / 1000000000) (47366287 / 250000000) (Real.log (1208603 / 1000000)) := by
  have h := reflection_log_11229_neg
  have he : Real.log (1208603 / 1000000) = -Real.log (1000000 / 1208603) := by
    rw [show ((1208603 / 1000000) : ℝ) = ((1000000 / 1208603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11230_neg : (11697777 / 50000000) ≤ -Real.log (791397 / 1000000) ∧
    -Real.log (791397 / 1000000) ≤ (233955541 / 1000000000) := by
  have h := checkLog_sound (w := (208603 / 1791397)) (n := 12)
    (lo := (11697777 / 50000000)) (hi := (233955541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791397) = 1/(791397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11230 : Bounds (-233955541 / 1000000000) (-11697777 / 50000000) (Real.log (791397 / 1000000)) := by
  have h := reflection_log_11230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11231_neg : (190243429 / 1000000000) ≤ -Real.log (125000 / 151193) ∧
    -Real.log (125000 / 151193) ≤ (19024343 / 100000000) := by
  have h := checkLog_sound (w := (26193 / 276193)) (n := 12)
    (lo := (190243429 / 1000000000)) (hi := (19024343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151193 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151193 / 125000) = 1/(125000 / 151193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11231 : Bounds (190243429 / 1000000000) (19024343 / 100000000) (Real.log (151193 / 125000)) := by
  have h := reflection_log_11231_neg
  have he : Real.log (151193 / 125000) = -Real.log (125000 / 151193) := by
    rw [show ((151193 / 125000) : ℝ) = ((125000 / 151193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11232_neg : (58786321 / 250000000) ≤ -Real.log (98807 / 125000) ∧
    -Real.log (98807 / 125000) ≤ (47029057 / 200000000) := by
  have h := checkLog_sound (w := (26193 / 223807)) (n := 12)
    (lo := (58786321 / 250000000)) (hi := (47029057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98807) = 1/(98807 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11232 : Bounds (-47029057 / 200000000) (-58786321 / 250000000) (Real.log (98807 / 125000)) := by
  have h := reflection_log_11232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11233_neg : (8980371 / 200000000) ≤ -Real.log (14938926751 / 15625000000) ∧
    -Real.log (14938926751 / 15625000000) ≤ (1403183 / 31250000) := by
  have h := checkLog_sound (w := (686073249 / 30563926751)) (n := 12)
    (lo := (8980371 / 200000000)) (hi := (1403183 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14938926751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14938926751) = 1/(14938926751 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11233 : Bounds (-1403183 / 31250000) (-8980371 / 200000000) (Real.log (14938926751 / 15625000000)) := by
  have h := reflection_log_11233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11234_neg : (44490393 / 1000000000) ≤ -Real.log (956484788391 / 1000000000000) ∧
    -Real.log (956484788391 / 1000000000000) ≤ (22245197 / 500000000) := by
  have h := checkLog_sound (w := (43515211609 / 1956484788391)) (n := 12)
    (lo := (44490393 / 1000000000)) (hi := (22245197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956484788391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956484788391) = 1/(956484788391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11234 : Bounds (-22245197 / 500000000) (-44490393 / 1000000000) (Real.log (956484788391 / 1000000000000)) := by
  have h := reflection_log_11234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11235_neg : (423420687 / 1000000000) ≤ -Real.log (250000000000 / 381794156409) ∧
    -Real.log (250000000000 / 381794156409) ≤ (26463793 / 62500000) := by
  have h := checkLog_sound (w := (131794156409 / 631794156409)) (n := 12)
    (lo := (423420687 / 1000000000)) (hi := (26463793 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381794156409 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381794156409 / 250000000000) = 1/(250000000000 / 381794156409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11235 : Bounds (423420687 / 1000000000) (26463793 / 62500000) (Real.log (381794156409 / 250000000000)) := by
  have h := reflection_log_11235_neg
  have he : Real.log (381794156409 / 250000000000) = -Real.log (250000000000 / 381794156409) := by
    rw [show ((381794156409 / 250000000000) : ℝ) = ((250000000000 / 381794156409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11236_neg : (425388713 / 1000000000) ≤ -Real.log (125000000000 / 191273138543) ∧
    -Real.log (125000000000 / 191273138543) ≤ (212694357 / 500000000) := by
  have h := checkLog_sound (w := (66273138543 / 316273138543)) (n := 12)
    (lo := (425388713 / 1000000000)) (hi := (212694357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191273138543 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191273138543 / 125000000000) = 1/(125000000000 / 191273138543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11236 : Bounds (425388713 / 1000000000) (212694357 / 500000000) (Real.log (191273138543 / 125000000000)) := by
  have h := reflection_log_11236_neg
  have he : Real.log (191273138543 / 125000000000) = -Real.log (125000000000 / 191273138543) := by
    rw [show ((191273138543 / 125000000000) : ℝ) = ((125000000000 / 191273138543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11237_neg : (34369247 / 40000000) ≤ -Real.log (500000000000 / 1180672268907) ∧
    -Real.log (500000000000 / 1180672268907) ≤ (859231177 / 1000000000) := by
  have h := checkLog_sound (w := (180672268907 / 2180672268907)) (n := 12)
    (lo := (33216799 / 200000000)) (hi := (41520999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180672268907 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1180672268907 / 1000000000000) = 1/(500000000000 / 1180672268907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11237 : Bounds (34369247 / 40000000) (859231177 / 1000000000) (Real.log (1180672268907 / 500000000000)) := by
  have h := reflection_log_11237_neg
  have he : Real.log (1180672268907 / 500000000000) = -Real.log (500000000000 / 1180672268907) := by
    rw [show ((1180672268907 / 500000000000) : ℝ) = ((500000000000 / 1180672268907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11238_neg : (53851547 / 62500000) ≤ -Real.log (250000000000 / 591750841751) ∧
    -Real.log (250000000000 / 591750841751) ≤ (430812377 / 500000000) := by
  have h := checkLog_sound (w := (91750841751 / 1091750841751)) (n := 12)
    (lo := (42119393 / 250000000)) (hi := (168477573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591750841751 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(591750841751 / 500000000000) = 1/(250000000000 / 591750841751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11238 : Bounds (53851547 / 62500000) (430812377 / 500000000) (Real.log (591750841751 / 250000000000)) := by
  have h := reflection_log_11238_neg
  have he : Real.log (591750841751 / 250000000000) = -Real.log (250000000000 / 591750841751) := by
    rw [show ((591750841751 / 250000000000) : ℝ) = ((250000000000 / 591750841751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11239_neg : (170729889 / 500000000) ≤ -Real.log (1000 / 1407) ∧
    -Real.log (1000 / 1407) ≤ (341459779 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 2407)) (n := 12)
    (lo := (170729889 / 500000000)) (hi := (341459779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1407 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1407 / 1000) = 1/(1000 / 1407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11239 : Bounds (170729889 / 500000000) (341459779 / 1000000000) (Real.log (1407 / 1000)) := by
  have h := reflection_log_11239_neg
  have he : Real.log (1407 / 1000) = -Real.log (1000 / 1407) := by
    rw [show ((1407 / 1000) : ℝ) = ((1000 / 1407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11240_neg : (522560879 / 1000000000) ≤ -Real.log (593 / 1000) ∧
    -Real.log (593 / 1000) ≤ (6532011 / 12500000) := by
  have h := checkLog_sound (w := (407 / 1593)) (n := 12)
    (lo := (522560879 / 1000000000)) (hi := (6532011 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 593) = 1/(593 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11240 : Bounds (-6532011 / 12500000) (-522560879 / 1000000000) (Real.log (593 / 1000)) := by
  have h := reflection_log_11240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11241_neg : (406917 / 1000000000) ≤ -Real.log (1000000 / 1000407) ∧
    -Real.log (1000000 / 1000407) ≤ (203459 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2000407)) (n := 12)
    (lo := (406917 / 1000000000)) (hi := (203459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000407 / 1000000) = 1/(1000000 / 1000407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11241 : Bounds (406917 / 1000000000) (203459 / 500000000) (Real.log (1000407 / 1000000)) := by
  have h := reflection_log_11241_neg
  have he : Real.log (1000407 / 1000000) = -Real.log (1000000 / 1000407) := by
    rw [show ((1000407 / 1000000) : ℝ) = ((1000000 / 1000407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11242_neg : (203541 / 500000000) ≤ -Real.log (999593 / 1000000) ∧
    -Real.log (999593 / 1000000) ≤ (407083 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 1999593)) (n := 12)
    (lo := (203541 / 500000000)) (hi := (407083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999593) = 1/(999593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11242 : Bounds (-407083 / 1000000000) (-203541 / 500000000) (Real.log (999593 / 1000000)) := by
  have h := reflection_log_11242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11243_neg : (9495923 / 50000000) ≤ -Real.log (1000000 / 1209151) ∧
    -Real.log (1000000 / 1209151) ≤ (189918461 / 1000000000) := by
  have h := checkLog_sound (w := (209151 / 2209151)) (n := 12)
    (lo := (9495923 / 50000000)) (hi := (189918461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209151 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209151 / 1000000) = 1/(1000000 / 1209151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11243 : Bounds (9495923 / 50000000) (189918461 / 1000000000) (Real.log (1209151 / 1000000)) := by
  have h := reflection_log_11243_neg
  have he : Real.log (1209151 / 1000000) = -Real.log (1000000 / 1209151) := by
    rw [show ((1209151 / 1000000) : ℝ) = ((1000000 / 1209151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11244_neg : (234648227 / 1000000000) ≤ -Real.log (790849 / 1000000) ∧
    -Real.log (790849 / 1000000) ≤ (58662057 / 250000000) := by
  have h := checkLog_sound (w := (209151 / 1790849)) (n := 12)
    (lo := (234648227 / 1000000000)) (hi := (58662057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790849) = 1/(790849 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11244 : Bounds (-58662057 / 250000000) (-234648227 / 1000000000) (Real.log (790849 / 1000000)) := by
  have h := reflection_log_11244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11245_neg : (744911 / 3906250) ≤ -Real.log (1000000 / 1210093) ∧
    -Real.log (1000000 / 1210093) ≤ (190697217 / 1000000000) := by
  have h := checkLog_sound (w := (210093 / 2210093)) (n := 12)
    (lo := (744911 / 3906250)) (hi := (190697217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210093 / 1000000) = 1/(1000000 / 1210093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11245 : Bounds (744911 / 3906250) (190697217 / 1000000000) (Real.log (1210093 / 1000000)) := by
  have h := reflection_log_11245_neg
  have he : Real.log (1210093 / 1000000) = -Real.log (1000000 / 1210093) := by
    rw [show ((1210093 / 1000000) : ℝ) = ((1000000 / 1210093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11246_neg : (235840061 / 1000000000) ≤ -Real.log (789907 / 1000000) ∧
    -Real.log (789907 / 1000000) ≤ (117920031 / 500000000) := by
  have h := checkLog_sound (w := (210093 / 1789907)) (n := 12)
    (lo := (235840061 / 1000000000)) (hi := (117920031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789907) = 1/(789907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11246 : Bounds (-117920031 / 500000000) (-235840061 / 1000000000) (Real.log (789907 / 1000000)) := by
  have h := reflection_log_11246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11247_neg : (9028569 / 200000000) ≤ -Real.log (955860931351 / 1000000000000) ∧
    -Real.log (955860931351 / 1000000000000) ≤ (22571423 / 500000000) := by
  have h := checkLog_sound (w := (44139068649 / 1955860931351)) (n := 12)
    (lo := (9028569 / 200000000)) (hi := (22571423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 955860931351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 955860931351) = 1/(955860931351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11247 : Bounds (-22571423 / 500000000) (-9028569 / 200000000) (Real.log (955860931351 / 1000000000000)) := by
  have h := reflection_log_11247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11248_neg : (22364883 / 500000000) ≤ -Real.log (956255859199 / 1000000000000) ∧
    -Real.log (956255859199 / 1000000000000) ≤ (44729767 / 1000000000) := by
  have h := checkLog_sound (w := (43744140801 / 1956255859199)) (n := 12)
    (lo := (22364883 / 500000000)) (hi := (44729767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956255859199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956255859199) = 1/(956255859199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11248 : Bounds (-44729767 / 1000000000) (-22364883 / 500000000) (Real.log (956255859199 / 1000000000000)) := by
  have h := reflection_log_11248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11249_neg : (424566687 / 1000000000) ≤ -Real.log (500000000000 / 764463886279) ∧
    -Real.log (500000000000 / 764463886279) ≤ (13267709 / 31250000) := by
  have h := checkLog_sound (w := (264463886279 / 1264463886279)) (n := 12)
    (lo := (424566687 / 1000000000)) (hi := (13267709 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764463886279 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764463886279 / 500000000000) = 1/(500000000000 / 764463886279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11249 : Bounds (424566687 / 1000000000) (13267709 / 31250000) (Real.log (764463886279 / 500000000000)) := by
  have h := reflection_log_11249_neg
  have he : Real.log (764463886279 / 500000000000) = -Real.log (500000000000 / 764463886279) := by
    rw [show ((764463886279 / 500000000000) : ℝ) = ((500000000000 / 764463886279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11250_neg : (213268639 / 500000000) ≤ -Real.log (62500000000 / 95746477117) ∧
    -Real.log (62500000000 / 95746477117) ≤ (426537279 / 1000000000) := by
  have h := checkLog_sound (w := (33246477117 / 158246477117)) (n := 12)
    (lo := (213268639 / 500000000)) (hi := (426537279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95746477117 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95746477117 / 62500000000) = 1/(62500000000 / 95746477117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11250 : Bounds (213268639 / 500000000) (426537279 / 1000000000) (Real.log (95746477117 / 62500000000)) := by
  have h := reflection_log_11250_neg
  have he : Real.log (95746477117 / 62500000000) = -Real.log (62500000000 / 95746477117) := by
    rw [show ((95746477117 / 62500000000) : ℝ) = ((62500000000 / 95746477117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11251_neg : (53851547 / 62500000) ≤ -Real.log (500000000000 / 1183501683501) ∧
    -Real.log (500000000000 / 1183501683501) ≤ (430812377 / 500000000) := by
  have h := checkLog_sound (w := (183501683501 / 2183501683501)) (n := 12)
    (lo := (42119393 / 250000000)) (hi := (168477573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183501683501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1183501683501 / 1000000000000) = 1/(500000000000 / 1183501683501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11251 : Bounds (53851547 / 62500000) (430812377 / 500000000) (Real.log (1183501683501 / 500000000000)) := by
  have h := reflection_log_11251_neg
  have he : Real.log (1183501683501 / 500000000000) = -Real.log (500000000000 / 1183501683501) := by
    rw [show ((1183501683501 / 500000000000) : ℝ) = ((500000000000 / 1183501683501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11252_neg : (864020657 / 1000000000) ≤ -Real.log (50000000000 / 118634064081) ∧
    -Real.log (50000000000 / 118634064081) ≤ (864020659 / 1000000000) := by
  have h := checkLog_sound (w := (18634064081 / 218634064081)) (n := 12)
    (lo := (170873477 / 1000000000)) (hi := (85436739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118634064081 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(118634064081 / 100000000000) = 1/(50000000000 / 118634064081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11252 : Bounds (864020657 / 1000000000) (864020659 / 1000000000) (Real.log (118634064081 / 50000000000)) := by
  have h := reflection_log_11252_neg
  have he : Real.log (118634064081 / 50000000000) = -Real.log (50000000000 / 118634064081) := by
    rw [show ((118634064081 / 50000000000) : ℝ) = ((50000000000 / 118634064081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11253_neg : (342170257 / 1000000000) ≤ -Real.log (125 / 176) ∧
    -Real.log (125 / 176) ≤ (171085129 / 500000000) := by
  have h := checkLog_sound (w := (51 / 301)) (n := 12)
    (lo := (342170257 / 1000000000)) (hi := (171085129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176 / 125) = 1/(125 / 176) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11253 : Bounds (342170257 / 1000000000) (171085129 / 500000000) (Real.log (176 / 125)) := by
  have h := reflection_log_11253_neg
  have he : Real.log (176 / 125) = -Real.log (125 / 176) := by
    rw [show ((176 / 125) : ℝ) = ((125 / 176) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11254_neg : (131062161 / 250000000) ≤ -Real.log (74 / 125) ∧
    -Real.log (74 / 125) ≤ (104849729 / 200000000) := by
  have h := checkLog_sound (w := (51 / 199)) (n := 12)
    (lo := (131062161 / 250000000)) (hi := (104849729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 74) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 74) = 1/(74 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11254 : Bounds (-104849729 / 200000000) (-131062161 / 250000000) (Real.log (74 / 125)) := by
  have h := reflection_log_11254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11255_neg : (101979 / 250000000) ≤ -Real.log (125000 / 125051) ∧
    -Real.log (125000 / 125051) ≤ (407917 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 250051)) (n := 12)
    (lo := (101979 / 250000000)) (hi := (407917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125051 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125051 / 125000) = 1/(125000 / 125051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11255 : Bounds (101979 / 250000000) (407917 / 1000000000) (Real.log (125051 / 125000)) := by
  have h := reflection_log_11255_neg
  have he : Real.log (125051 / 125000) = -Real.log (125000 / 125051) := by
    rw [show ((125051 / 125000) : ℝ) = ((125000 / 125051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11256_neg : (408083 / 1000000000) ≤ -Real.log (124949 / 125000) ∧
    -Real.log (124949 / 125000) ≤ (102021 / 250000000) := by
  have h := checkLog_sound (w := (51 / 249949)) (n := 12)
    (lo := (408083 / 1000000000)) (hi := (102021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124949) = 1/(124949 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11256 : Bounds (-102021 / 250000000) (-408083 / 1000000000) (Real.log (124949 / 125000)) := by
  have h := reflection_log_11256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11257_neg : (11898223 / 62500000) ≤ -Real.log (1000000 / 1209699) ∧
    -Real.log (1000000 / 1209699) ≤ (190371569 / 1000000000) := by
  have h := checkLog_sound (w := (209699 / 2209699)) (n := 12)
    (lo := (11898223 / 62500000)) (hi := (190371569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209699 / 1000000) = 1/(1000000 / 1209699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11257 : Bounds (11898223 / 62500000) (190371569 / 1000000000) (Real.log (1209699 / 1000000)) := by
  have h := reflection_log_11257_neg
  have he : Real.log (1209699 / 1000000) = -Real.log (1000000 / 1209699) := by
    rw [show ((1209699 / 1000000) : ℝ) = ((1000000 / 1209699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11258_neg : (235341393 / 1000000000) ≤ -Real.log (790301 / 1000000) ∧
    -Real.log (790301 / 1000000) ≤ (117670697 / 500000000) := by
  have h := checkLog_sound (w := (209699 / 1790301)) (n := 12)
    (lo := (235341393 / 1000000000)) (hi := (117670697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790301) = 1/(790301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11258 : Bounds (-117670697 / 500000000) (-235341393 / 1000000000) (Real.log (790301 / 1000000)) := by
  have h := reflection_log_11258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11259_neg : (191151623 / 1000000000) ≤ -Real.log (1000000 / 1210643) ∧
    -Real.log (1000000 / 1210643) ≤ (23893953 / 125000000) := by
  have h := checkLog_sound (w := (210643 / 2210643)) (n := 12)
    (lo := (191151623 / 1000000000)) (hi := (23893953 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210643 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210643 / 1000000) = 1/(1000000 / 1210643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11259 : Bounds (191151623 / 1000000000) (23893953 / 125000000) (Real.log (1210643 / 1000000)) := by
  have h := reflection_log_11259_neg
  have he : Real.log (1210643 / 1000000) = -Real.log (1000000 / 1210643) := by
    rw [show ((1210643 / 1000000) : ℝ) = ((1000000 / 1210643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11260_neg : (59134147 / 250000000) ≤ -Real.log (789357 / 1000000) ∧
    -Real.log (789357 / 1000000) ≤ (236536589 / 1000000000) := by
  have h := checkLog_sound (w := (210643 / 1789357)) (n := 12)
    (lo := (59134147 / 250000000)) (hi := (236536589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789357) = 1/(789357 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11260 : Bounds (-236536589 / 1000000000) (-59134147 / 250000000) (Real.log (789357 / 1000000)) := by
  have h := reflection_log_11260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11261_neg : (9076993 / 200000000) ≤ -Real.log (955629526551 / 1000000000000) ∧
    -Real.log (955629526551 / 1000000000000) ≤ (22692483 / 500000000) := by
  have h := checkLog_sound (w := (44370473449 / 1955629526551)) (n := 12)
    (lo := (9076993 / 200000000)) (hi := (22692483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 955629526551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 955629526551) = 1/(955629526551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11261 : Bounds (-22692483 / 500000000) (-9076993 / 200000000) (Real.log (955629526551 / 1000000000000)) := by
  have h := reflection_log_11261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11262_neg : (1798793 / 40000000) ≤ -Real.log (956026329399 / 1000000000000) ∧
    -Real.log (956026329399 / 1000000000000) ≤ (22484913 / 500000000) := by
  have h := checkLog_sound (w := (43973670601 / 1956026329399)) (n := 12)
    (lo := (1798793 / 40000000)) (hi := (22484913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956026329399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956026329399) = 1/(956026329399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11262 : Bounds (-22484913 / 500000000) (-1798793 / 40000000) (Real.log (956026329399 / 1000000000000)) := by
  have h := reflection_log_11262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11263_neg : (425712961 / 1000000000) ≤ -Real.log (125000000000 / 191335168499) ∧
    -Real.log (125000000000 / 191335168499) ≤ (212856481 / 500000000) := by
  have h := checkLog_sound (w := (66335168499 / 316335168499)) (n := 12)
    (lo := (425712961 / 1000000000)) (hi := (212856481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191335168499 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191335168499 / 125000000000) = 1/(125000000000 / 191335168499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11263 : Bounds (425712961 / 1000000000) (212856481 / 500000000) (Real.log (191335168499 / 125000000000)) := by
  have h := reflection_log_11263_neg
  have he : Real.log (191335168499 / 125000000000) = -Real.log (125000000000 / 191335168499) := by
    rw [show ((191335168499 / 125000000000) : ℝ) = ((125000000000 / 191335168499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0176 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11264_neg : (106922053 / 250000000) ≤ -Real.log (20000000000 / 30674156307) ∧
    -Real.log (20000000000 / 30674156307) ≤ (427688213 / 1000000000) := by
  have h := checkLog_sound (w := (10674156307 / 50674156307)) (n := 12)
    (lo := (106922053 / 250000000)) (hi := (427688213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30674156307 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30674156307 / 20000000000) = 1/(20000000000 / 30674156307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11264 : Bounds (106922053 / 250000000) (427688213 / 1000000000) (Real.log (30674156307 / 20000000000)) := by
  have h := reflection_log_11264_neg
  have he : Real.log (30674156307 / 20000000000) = -Real.log (20000000000 / 30674156307) := by
    rw [show ((30674156307 / 20000000000) : ℝ) = ((20000000000 / 30674156307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11265_neg : (864020657 / 1000000000) ≤ -Real.log (500000000000 / 1186340640809) ∧
    -Real.log (500000000000 / 1186340640809) ≤ (864020659 / 1000000000) := by
  have h := checkLog_sound (w := (186340640809 / 2186340640809)) (n := 12)
    (lo := (170873477 / 1000000000)) (hi := (85436739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186340640809 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1186340640809 / 1000000000000) = 1/(500000000000 / 1186340640809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11265 : Bounds (864020657 / 1000000000) (864020659 / 1000000000) (Real.log (1186340640809 / 500000000000)) := by
  have h := reflection_log_11265_neg
  have he : Real.log (1186340640809 / 500000000000) = -Real.log (500000000000 / 1186340640809) := by
    rw [show ((1186340640809 / 500000000000) : ℝ) = ((500000000000 / 1186340640809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11266_neg : (866418901 / 1000000000) ≤ -Real.log (50000000000 / 118918918919) ∧
    -Real.log (50000000000 / 118918918919) ≤ (866418903 / 1000000000) := by
  have h := checkLog_sound (w := (18918918919 / 218918918919)) (n := 12)
    (lo := (173271721 / 1000000000)) (hi := (86635861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118918918919 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(118918918919 / 100000000000) = 1/(50000000000 / 118918918919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11266 : Bounds (866418901 / 1000000000) (866418903 / 1000000000) (Real.log (118918918919 / 50000000000)) := by
  have h := reflection_log_11266_neg
  have he : Real.log (118918918919 / 50000000000) = -Real.log (50000000000 / 118918918919) := by
    rw [show ((118918918919 / 50000000000) : ℝ) = ((50000000000 / 118918918919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11267_neg : (42860029 / 125000000) ≤ -Real.log (1000 / 1409) ∧
    -Real.log (1000 / 1409) ≤ (342880233 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2409)) (n := 12)
    (lo := (42860029 / 125000000)) (hi := (342880233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409 / 1000) = 1/(1000 / 1409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11267 : Bounds (42860029 / 125000000) (342880233 / 1000000000) (Real.log (1409 / 1000)) := by
  have h := reflection_log_11267_neg
  have he : Real.log (1409 / 1000) = -Real.log (1000 / 1409) := by
    rw [show ((1409 / 1000) : ℝ) = ((1000 / 1409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11268_neg : (525939261 / 1000000000) ≤ -Real.log (591 / 1000) ∧
    -Real.log (591 / 1000) ≤ (262969631 / 500000000) := by
  have h := checkLog_sound (w := (409 / 1591)) (n := 12)
    (lo := (525939261 / 1000000000)) (hi := (262969631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 591) = 1/(591 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11268 : Bounds (-262969631 / 500000000) (-525939261 / 1000000000) (Real.log (591 / 1000)) := by
  have h := reflection_log_11268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11269_neg : (102229 / 250000000) ≤ -Real.log (1000000 / 1000409) ∧
    -Real.log (1000000 / 1000409) ≤ (408917 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2000409)) (n := 12)
    (lo := (102229 / 250000000)) (hi := (408917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000409 / 1000000) = 1/(1000000 / 1000409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11269 : Bounds (102229 / 250000000) (408917 / 1000000000) (Real.log (1000409 / 1000000)) := by
  have h := reflection_log_11269_neg
  have he : Real.log (1000409 / 1000000) = -Real.log (1000000 / 1000409) := by
    rw [show ((1000409 / 1000000) : ℝ) = ((1000000 / 1000409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11270_neg : (409083 / 1000000000) ≤ -Real.log (999591 / 1000000) ∧
    -Real.log (999591 / 1000000) ≤ (102271 / 250000000) := by
  have h := checkLog_sound (w := (409 / 1999591)) (n := 12)
    (lo := (409083 / 1000000000)) (hi := (102271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999591) = 1/(999591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11270 : Bounds (-102271 / 250000000) (-409083 / 1000000000) (Real.log (999591 / 1000000)) := by
  have h := reflection_log_11270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11271_neg : (190824471 / 1000000000) ≤ -Real.log (1000000 / 1210247) ∧
    -Real.log (1000000 / 1210247) ≤ (23853059 / 125000000) := by
  have h := checkLog_sound (w := (210247 / 2210247)) (n := 12)
    (lo := (190824471 / 1000000000)) (hi := (23853059 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210247 / 1000000) = 1/(1000000 / 1210247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11271 : Bounds (190824471 / 1000000000) (23853059 / 125000000) (Real.log (1210247 / 1000000)) := by
  have h := reflection_log_11271_neg
  have he : Real.log (1210247 / 1000000) = -Real.log (1000000 / 1210247) := by
    rw [show ((1210247 / 1000000) : ℝ) = ((1000000 / 1210247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11272_neg : (1475219 / 6250000) ≤ -Real.log (789753 / 1000000) ∧
    -Real.log (789753 / 1000000) ≤ (236035041 / 1000000000) := by
  have h := checkLog_sound (w := (210247 / 1789753)) (n := 12)
    (lo := (1475219 / 6250000)) (hi := (236035041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789753) = 1/(789753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11272 : Bounds (-236035041 / 1000000000) (-1475219 / 6250000) (Real.log (789753 / 1000000)) := by
  have h := reflection_log_11272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11273_neg : (2993841 / 15625000) ≤ -Real.log (1000000 / 1211193) ∧
    -Real.log (1000000 / 1211193) ≤ (7664233 / 40000000) := by
  have h := checkLog_sound (w := (211193 / 2211193)) (n := 12)
    (lo := (2993841 / 15625000)) (hi := (7664233 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211193 / 1000000) = 1/(1000000 / 1211193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11273 : Bounds (2993841 / 15625000) (7664233 / 40000000) (Real.log (1211193 / 1000000)) := by
  have h := reflection_log_11273_neg
  have he : Real.log (1211193 / 1000000) = -Real.log (1000000 / 1211193) := by
    rw [show ((1211193 / 1000000) : ℝ) = ((1000000 / 1211193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11274_neg : (237233601 / 1000000000) ≤ -Real.log (788807 / 1000000) ∧
    -Real.log (788807 / 1000000) ≤ (118616801 / 500000000) := by
  have h := checkLog_sound (w := (211193 / 1788807)) (n := 12)
    (lo := (237233601 / 1000000000)) (hi := (118616801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788807) = 1/(788807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11274 : Bounds (-118616801 / 500000000) (-237233601 / 1000000000) (Real.log (788807 / 1000000)) := by
  have h := reflection_log_11274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11275_neg : (45627777 / 1000000000) ≤ -Real.log (955397516751 / 1000000000000) ∧
    -Real.log (955397516751 / 1000000000000) ≤ (22813889 / 500000000) := by
  have h := checkLog_sound (w := (44602483249 / 1955397516751)) (n := 12)
    (lo := (45627777 / 1000000000)) (hi := (22813889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 955397516751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 955397516751) = 1/(955397516751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11275 : Bounds (-22813889 / 500000000) (-45627777 / 1000000000) (Real.log (955397516751 / 1000000000000)) := by
  have h := reflection_log_11275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11276_neg : (45210569 / 1000000000) ≤ -Real.log (955796198991 / 1000000000000) ∧
    -Real.log (955796198991 / 1000000000000) ≤ (4521057 / 100000000) := by
  have h := checkLog_sound (w := (44203801009 / 1955796198991)) (n := 12)
    (lo := (45210569 / 1000000000)) (hi := (4521057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 955796198991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 955796198991) = 1/(955796198991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11276 : Bounds (-4521057 / 100000000) (-45210569 / 1000000000) (Real.log (955796198991 / 1000000000000)) := by
  have h := reflection_log_11276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11277_neg : (426859511 / 1000000000) ≤ -Real.log (250000000000 / 383109339249) ∧
    -Real.log (250000000000 / 383109339249) ≤ (53357439 / 125000000) := by
  have h := checkLog_sound (w := (133109339249 / 633109339249)) (n := 12)
    (lo := (426859511 / 1000000000)) (hi := (53357439 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383109339249 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383109339249 / 250000000000) = 1/(250000000000 / 383109339249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11277 : Bounds (426859511 / 1000000000) (53357439 / 125000000) (Real.log (383109339249 / 250000000000)) := by
  have h := reflection_log_11277_neg
  have he : Real.log (383109339249 / 250000000000) = -Real.log (250000000000 / 383109339249) := by
    rw [show ((383109339249 / 250000000000) : ℝ) = ((250000000000 / 383109339249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11278_neg : (17153577 / 40000000) ≤ -Real.log (500000000000 / 767737228499) ∧
    -Real.log (500000000000 / 767737228499) ≤ (214419713 / 500000000) := by
  have h := checkLog_sound (w := (267737228499 / 1267737228499)) (n := 12)
    (lo := (17153577 / 40000000)) (hi := (214419713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767737228499 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767737228499 / 500000000000) = 1/(500000000000 / 767737228499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11278 : Bounds (17153577 / 40000000) (214419713 / 500000000) (Real.log (767737228499 / 500000000000)) := by
  have h := reflection_log_11278_neg
  have he : Real.log (767737228499 / 500000000000) = -Real.log (500000000000 / 767737228499) := by
    rw [show ((767737228499 / 500000000000) : ℝ) = ((500000000000 / 767737228499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11279_neg : (866418901 / 1000000000) ≤ -Real.log (500000000000 / 1189189189189) ∧
    -Real.log (500000000000 / 1189189189189) ≤ (866418903 / 1000000000) := by
  have h := checkLog_sound (w := (189189189189 / 2189189189189)) (n := 12)
    (lo := (173271721 / 1000000000)) (hi := (86635861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189189189189 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1189189189189 / 1000000000000) = 1/(500000000000 / 1189189189189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11279 : Bounds (866418901 / 1000000000) (866418903 / 1000000000) (Real.log (1189189189189 / 500000000000)) := by
  have h := reflection_log_11279_neg
  have he : Real.log (1189189189189 / 500000000000) = -Real.log (500000000000 / 1189189189189) := by
    rw [show ((1189189189189 / 500000000000) : ℝ) = ((500000000000 / 1189189189189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11280_neg : (868819493 / 1000000000) ≤ -Real.log (500000000000 / 1192047377327) ∧
    -Real.log (500000000000 / 1192047377327) ≤ (173763899 / 200000000) := by
  have h := checkLog_sound (w := (192047377327 / 2192047377327)) (n := 12)
    (lo := (175672313 / 1000000000)) (hi := (87836157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192047377327 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1192047377327 / 1000000000000) = 1/(500000000000 / 1192047377327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11280 : Bounds (868819493 / 1000000000) (173763899 / 200000000) (Real.log (1192047377327 / 500000000000)) := by
  have h := reflection_log_11280_neg
  have he : Real.log (1192047377327 / 500000000000) = -Real.log (500000000000 / 1192047377327) := by
    rw [show ((1192047377327 / 500000000000) : ℝ) = ((500000000000 / 1192047377327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11281_neg : (42948713 / 125000000) ≤ -Real.log (100 / 141) ∧
    -Real.log (100 / 141) ≤ (68717941 / 200000000) := by
  have h := checkLog_sound (w := (41 / 241)) (n := 12)
    (lo := (42948713 / 125000000)) (hi := (68717941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141 / 100) = 1/(100 / 141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11281 : Bounds (42948713 / 125000000) (68717941 / 200000000) (Real.log (141 / 100)) := by
  have h := reflection_log_11281_neg
  have he : Real.log (141 / 100) = -Real.log (100 / 141) := by
    rw [show ((141 / 100) : ℝ) = ((100 / 141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11282_neg : (263816371 / 500000000) ≤ -Real.log (59 / 100) ∧
    -Real.log (59 / 100) ≤ (527632743 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 159)) (n := 12)
    (lo := (263816371 / 500000000)) (hi := (527632743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 59) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 59) = 1/(59 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11282 : Bounds (-527632743 / 1000000000) (-263816371 / 500000000) (Real.log (59 / 100)) := by
  have h := reflection_log_11282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11283_neg : (81983 / 200000000) ≤ -Real.log (100000 / 100041) ∧
    -Real.log (100000 / 100041) ≤ (102479 / 250000000) := by
  have h := checkLog_sound (w := (41 / 200041)) (n := 12)
    (lo := (81983 / 200000000)) (hi := (102479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100041 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100041 / 100000) = 1/(100000 / 100041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11283 : Bounds (81983 / 200000000) (102479 / 250000000) (Real.log (100041 / 100000)) := by
  have h := reflection_log_11283_neg
  have he : Real.log (100041 / 100000) = -Real.log (100000 / 100041) := by
    rw [show ((100041 / 100000) : ℝ) = ((100000 / 100041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11284_neg : (102521 / 250000000) ≤ -Real.log (99959 / 100000) ∧
    -Real.log (99959 / 100000) ≤ (82017 / 200000000) := by
  have h := checkLog_sound (w := (41 / 199959)) (n := 12)
    (lo := (102521 / 250000000)) (hi := (82017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99959) = 1/(99959 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11284 : Bounds (-82017 / 200000000) (-102521 / 250000000) (Real.log (99959 / 100000)) := by
  have h := reflection_log_11284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11285_neg : (95638997 / 500000000) ≤ -Real.log (250000 / 302699) ∧
    -Real.log (250000 / 302699) ≤ (38255599 / 200000000) := by
  have h := checkLog_sound (w := (52699 / 552699)) (n := 12)
    (lo := (95638997 / 500000000)) (hi := (38255599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302699 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302699 / 250000) = 1/(250000 / 302699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11285 : Bounds (95638997 / 500000000) (38255599 / 200000000) (Real.log (302699 / 250000)) := by
  have h := reflection_log_11285_neg
  have he : Real.log (302699 / 250000) = -Real.log (250000 / 302699) := by
    rw [show ((302699 / 250000) : ℝ) = ((250000 / 302699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11286_neg : (59182609 / 250000000) ≤ -Real.log (197301 / 250000) ∧
    -Real.log (197301 / 250000) ≤ (236730437 / 1000000000) := by
  have h := checkLog_sound (w := (52699 / 447301)) (n := 12)
    (lo := (59182609 / 250000000)) (hi := (236730437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197301) = 1/(197301 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11286 : Bounds (-236730437 / 1000000000) (-59182609 / 250000000) (Real.log (197301 / 250000)) := by
  have h := reflection_log_11286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11287_neg : (192058993 / 1000000000) ≤ -Real.log (500000 / 605871) ∧
    -Real.log (500000 / 605871) ≤ (96029497 / 500000000) := by
  have h := checkLog_sound (w := (105871 / 1105871)) (n := 12)
    (lo := (192058993 / 1000000000)) (hi := (96029497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605871 / 500000) = 1/(500000 / 605871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11287 : Bounds (192058993 / 1000000000) (96029497 / 500000000) (Real.log (605871 / 500000)) := by
  have h := reflection_log_11287_neg
  have he : Real.log (605871 / 500000) = -Real.log (500000 / 605871) := by
    rw [show ((605871 / 500000) : ℝ) = ((500000 / 605871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11288_neg : (237929831 / 1000000000) ≤ -Real.log (394129 / 500000) ∧
    -Real.log (394129 / 500000) ≤ (29741229 / 125000000) := by
  have h := checkLog_sound (w := (105871 / 894129)) (n := 12)
    (lo := (237929831 / 1000000000)) (hi := (29741229 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394129) = 1/(394129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11288 : Bounds (-29741229 / 125000000) (-237929831 / 1000000000) (Real.log (394129 / 500000)) := by
  have h := reflection_log_11288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11289_neg : (45870837 / 1000000000) ≤ -Real.log (238791331359 / 250000000000) ∧
    -Real.log (238791331359 / 250000000000) ≤ (22935419 / 500000000) := by
  have h := checkLog_sound (w := (11208668641 / 488791331359)) (n := 12)
    (lo := (45870837 / 1000000000)) (hi := (22935419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 238791331359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 238791331359) = 1/(238791331359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11289 : Bounds (-22935419 / 500000000) (-45870837 / 1000000000) (Real.log (238791331359 / 250000000000)) := by
  have h := reflection_log_11289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11290_neg : (45452441 / 1000000000) ≤ -Real.log (59722815399 / 62500000000) ∧
    -Real.log (59722815399 / 62500000000) ≤ (22726221 / 500000000) := by
  have h := checkLog_sound (w := (2777184601 / 122222815399)) (n := 12)
    (lo := (45452441 / 1000000000)) (hi := (22726221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59722815399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59722815399) = 1/(59722815399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11290 : Bounds (-22726221 / 500000000) (-45452441 / 1000000000) (Real.log (59722815399 / 62500000000)) := by
  have h := reflection_log_11290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11291_neg : (42800843 / 100000000) ≤ -Real.log (250000000000 / 383549753929) ∧
    -Real.log (250000000000 / 383549753929) ≤ (428008431 / 1000000000) := by
  have h := checkLog_sound (w := (133549753929 / 633549753929)) (n := 12)
    (lo := (42800843 / 100000000)) (hi := (428008431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383549753929 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383549753929 / 250000000000) = 1/(250000000000 / 383549753929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11291 : Bounds (42800843 / 100000000) (428008431 / 1000000000) (Real.log (383549753929 / 250000000000)) := by
  have h := reflection_log_11291_neg
  have he : Real.log (383549753929 / 250000000000) = -Real.log (250000000000 / 383549753929) := by
    rw [show ((383549753929 / 250000000000) : ℝ) = ((250000000000 / 383549753929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11292_neg : (17199553 / 40000000) ≤ -Real.log (62500000000 / 96077521573) ∧
    -Real.log (62500000000 / 96077521573) ≤ (214994413 / 500000000) := by
  have h := checkLog_sound (w := (33577521573 / 158577521573)) (n := 12)
    (lo := (17199553 / 40000000)) (hi := (214994413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96077521573 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96077521573 / 62500000000) = 1/(62500000000 / 96077521573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11292 : Bounds (17199553 / 40000000) (214994413 / 500000000) (Real.log (96077521573 / 62500000000)) := by
  have h := reflection_log_11292_neg
  have he : Real.log (96077521573 / 62500000000) = -Real.log (62500000000 / 96077521573) := by
    rw [show ((96077521573 / 62500000000) : ℝ) = ((62500000000 / 96077521573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11293_neg : (868819493 / 1000000000) ≤ -Real.log (250000000000 / 596023688663) ∧
    -Real.log (250000000000 / 596023688663) ≤ (173763899 / 200000000) := by
  have h := checkLog_sound (w := (96023688663 / 1096023688663)) (n := 12)
    (lo := (175672313 / 1000000000)) (hi := (87836157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596023688663 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(596023688663 / 500000000000) = 1/(250000000000 / 596023688663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11293 : Bounds (868819493 / 1000000000) (173763899 / 200000000) (Real.log (596023688663 / 250000000000)) := by
  have h := reflection_log_11293_neg
  have he : Real.log (596023688663 / 250000000000) = -Real.log (250000000000 / 596023688663) := by
    rw [show ((596023688663 / 250000000000) : ℝ) = ((250000000000 / 596023688663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11294_neg : (174244489 / 200000000) ≤ -Real.log (250000000000 / 597457627119) ∧
    -Real.log (250000000000 / 597457627119) ≤ (871222447 / 1000000000) := by
  have h := checkLog_sound (w := (97457627119 / 1097457627119)) (n := 12)
    (lo := (35615053 / 200000000)) (hi := (89037633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597457627119 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(597457627119 / 500000000000) = 1/(250000000000 / 597457627119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11294 : Bounds (174244489 / 200000000) (871222447 / 1000000000) (Real.log (597457627119 / 250000000000)) := by
  have h := reflection_log_11294_neg
  have he : Real.log (597457627119 / 250000000000) = -Real.log (250000000000 / 597457627119) := by
    rw [show ((597457627119 / 250000000000) : ℝ) = ((250000000000 / 597457627119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11295_neg : (21518667 / 62500000) ≤ -Real.log (1000 / 1411) ∧
    -Real.log (1000 / 1411) ≤ (344298673 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 2411)) (n := 12)
    (lo := (21518667 / 62500000)) (hi := (344298673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1411 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1411 / 1000) = 1/(1000 / 1411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11295 : Bounds (21518667 / 62500000) (344298673 / 1000000000) (Real.log (1411 / 1000)) := by
  have h := reflection_log_11295_neg
  have he : Real.log (1411 / 1000) = -Real.log (1000 / 1411) := by
    rw [show ((1411 / 1000) : ℝ) = ((1000 / 1411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11296_neg : (105865819 / 200000000) ≤ -Real.log (589 / 1000) ∧
    -Real.log (589 / 1000) ≤ (66166137 / 125000000) := by
  have h := checkLog_sound (w := (411 / 1589)) (n := 12)
    (lo := (105865819 / 200000000)) (hi := (66166137 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 589) = 1/(589 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11296 : Bounds (-66166137 / 125000000) (-105865819 / 200000000) (Real.log (589 / 1000)) := by
  have h := reflection_log_11296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11297_neg : (82183 / 200000000) ≤ -Real.log (1000000 / 1000411) ∧
    -Real.log (1000000 / 1000411) ≤ (102729 / 250000000) := by
  have h := checkLog_sound (w := (411 / 2000411)) (n := 12)
    (lo := (82183 / 200000000)) (hi := (102729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000411 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000411 / 1000000) = 1/(1000000 / 1000411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11297 : Bounds (82183 / 200000000) (102729 / 250000000) (Real.log (1000411 / 1000000)) := by
  have h := reflection_log_11297_neg
  have he : Real.log (1000411 / 1000000) = -Real.log (1000000 / 1000411) := by
    rw [show ((1000411 / 1000000) : ℝ) = ((1000000 / 1000411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11298_neg : (102771 / 250000000) ≤ -Real.log (999589 / 1000000) ∧
    -Real.log (999589 / 1000000) ≤ (82217 / 200000000) := by
  have h := checkLog_sound (w := (411 / 1999589)) (n := 12)
    (lo := (102771 / 250000000)) (hi := (82217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999589) = 1/(999589 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11298 : Bounds (-82217 / 200000000) (-102771 / 250000000) (Real.log (999589 / 1000000)) := by
  have h := reflection_log_11298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11299_neg : (11983207 / 62500000) ≤ -Real.log (200000 / 242269) ∧
    -Real.log (200000 / 242269) ≤ (191731313 / 1000000000) := by
  have h := checkLog_sound (w := (42269 / 442269)) (n := 12)
    (lo := (11983207 / 62500000)) (hi := (191731313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242269 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242269 / 200000) = 1/(200000 / 242269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11299 : Bounds (11983207 / 62500000) (191731313 / 1000000000) (Real.log (242269 / 200000)) := by
  have h := reflection_log_11299_neg
  have he : Real.log (242269 / 200000) = -Real.log (200000 / 242269) := by
    rw [show ((242269 / 200000) : ℝ) = ((200000 / 242269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11300_neg : (59356579 / 250000000) ≤ -Real.log (157731 / 200000) ∧
    -Real.log (157731 / 200000) ≤ (237426317 / 1000000000) := by
  have h := checkLog_sound (w := (42269 / 357731)) (n := 12)
    (lo := (59356579 / 250000000)) (hi := (237426317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157731) = 1/(157731 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11300 : Bounds (-237426317 / 1000000000) (-59356579 / 250000000) (Real.log (157731 / 200000)) := by
  have h := reflection_log_11300_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11301_neg : (192513607 / 1000000000) ≤ -Real.log (1000000 / 1212293) ∧
    -Real.log (1000000 / 1212293) ≤ (24064201 / 125000000) := by
  have h := checkLog_sound (w := (212293 / 2212293)) (n := 12)
    (lo := (192513607 / 1000000000)) (hi := (24064201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212293 / 1000000) = 1/(1000000 / 1212293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11301 : Bounds (192513607 / 1000000000) (24064201 / 125000000) (Real.log (1212293 / 1000000)) := by
  have h := reflection_log_11301_neg
  have he : Real.log (1212293 / 1000000) = -Real.log (1000000 / 1212293) := by
    rw [show ((1212293 / 1000000) : ℝ) = ((1000000 / 1212293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11302_neg : (47725817 / 200000000) ≤ -Real.log (787707 / 1000000) ∧
    -Real.log (787707 / 1000000) ≤ (119314543 / 500000000) := by
  have h := checkLog_sound (w := (212293 / 1787707)) (n := 12)
    (lo := (47725817 / 200000000)) (hi := (119314543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787707) = 1/(787707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11302 : Bounds (-119314543 / 500000000) (-47725817 / 200000000) (Real.log (787707 / 1000000)) := by
  have h := reflection_log_11302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11303_neg : (23057739 / 500000000) ≤ -Real.log (954931682151 / 1000000000000) ∧
    -Real.log (954931682151 / 1000000000000) ≤ (46115479 / 1000000000) := by
  have h := checkLog_sound (w := (45068317849 / 1954931682151)) (n := 12)
    (lo := (23057739 / 500000000)) (hi := (46115479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 954931682151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 954931682151) = 1/(954931682151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11303 : Bounds (-46115479 / 1000000000) (-23057739 / 500000000) (Real.log (954931682151 / 1000000000000)) := by
  have h := reflection_log_11303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11304_neg : (45695003 / 1000000000) ≤ -Real.log (38213331639 / 40000000000) ∧
    -Real.log (38213331639 / 40000000000) ≤ (11423751 / 250000000) := by
  have h := checkLog_sound (w := (1786668361 / 78213331639)) (n := 12)
    (lo := (45695003 / 1000000000)) (hi := (11423751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38213331639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38213331639) = 1/(38213331639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11304 : Bounds (-11423751 / 250000000) (-45695003 / 1000000000) (Real.log (38213331639 / 40000000000)) := by
  have h := reflection_log_11304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11305_neg : (107289407 / 250000000) ≤ -Real.log (125000000000 / 191995390887) ∧
    -Real.log (125000000000 / 191995390887) ≤ (429157629 / 1000000000) := by
  have h := checkLog_sound (w := (66995390887 / 316995390887)) (n := 12)
    (lo := (107289407 / 250000000)) (hi := (429157629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191995390887 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191995390887 / 125000000000) = 1/(125000000000 / 191995390887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11305 : Bounds (107289407 / 250000000) (429157629 / 1000000000) (Real.log (191995390887 / 125000000000)) := by
  have h := reflection_log_11305_neg
  have he : Real.log (191995390887 / 125000000000) = -Real.log (125000000000 / 191995390887) := by
    rw [show ((191995390887 / 125000000000) : ℝ) = ((125000000000 / 191995390887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11306_neg : (431142693 / 1000000000) ≤ -Real.log (500000000000 / 769507570709) ∧
    -Real.log (500000000000 / 769507570709) ≤ (215571347 / 500000000) := by
  have h := checkLog_sound (w := (269507570709 / 1269507570709)) (n := 12)
    (lo := (431142693 / 1000000000)) (hi := (215571347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769507570709 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769507570709 / 500000000000) = 1/(500000000000 / 769507570709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11306 : Bounds (431142693 / 1000000000) (215571347 / 500000000) (Real.log (769507570709 / 500000000000)) := by
  have h := reflection_log_11306_neg
  have he : Real.log (769507570709 / 500000000000) = -Real.log (500000000000 / 769507570709) := by
    rw [show ((769507570709 / 500000000000) : ℝ) = ((500000000000 / 769507570709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11307_neg : (174244489 / 200000000) ≤ -Real.log (500000000000 / 1194915254237) ∧
    -Real.log (500000000000 / 1194915254237) ≤ (871222447 / 1000000000) := by
  have h := checkLog_sound (w := (194915254237 / 2194915254237)) (n := 12)
    (lo := (35615053 / 200000000)) (hi := (89037633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194915254237 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1194915254237 / 1000000000000) = 1/(500000000000 / 1194915254237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11307 : Bounds (174244489 / 200000000) (871222447 / 1000000000) (Real.log (1194915254237 / 500000000000)) := by
  have h := reflection_log_11307_neg
  have he : Real.log (1194915254237 / 500000000000) = -Real.log (500000000000 / 1194915254237) := by
    rw [show ((1194915254237 / 500000000000) : ℝ) = ((500000000000 / 1194915254237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11308_neg : (873627767 / 1000000000) ≤ -Real.log (50000000000 / 119779286927) ∧
    -Real.log (50000000000 / 119779286927) ≤ (873627769 / 1000000000) := by
  have h := checkLog_sound (w := (19779286927 / 219779286927)) (n := 12)
    (lo := (180480587 / 1000000000)) (hi := (45120147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119779286927 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(119779286927 / 100000000000) = 1/(50000000000 / 119779286927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11308 : Bounds (873627767 / 1000000000) (873627769 / 1000000000) (Real.log (119779286927 / 50000000000)) := by
  have h := reflection_log_11308_neg
  have he : Real.log (119779286927 / 50000000000) = -Real.log (50000000000 / 119779286927) := by
    rw [show ((119779286927 / 50000000000) : ℝ) = ((50000000000 / 119779286927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11309_neg : (345007139 / 1000000000) ≤ -Real.log (250 / 353) ∧
    -Real.log (250 / 353) ≤ (17250357 / 50000000) := by
  have h := checkLog_sound (w := (103 / 603)) (n := 12)
    (lo := (345007139 / 1000000000)) (hi := (17250357 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353 / 250) = 1/(250 / 353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11309 : Bounds (345007139 / 1000000000) (17250357 / 50000000) (Real.log (353 / 250)) := by
  have h := reflection_log_11309_neg
  have he : Real.log (353 / 250) = -Real.log (250 / 353) := by
    rw [show ((353 / 250) : ℝ) = ((250 / 353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11310_neg : (531028331 / 1000000000) ≤ -Real.log (147 / 250) ∧
    -Real.log (147 / 250) ≤ (132757083 / 250000000) := by
  have h := checkLog_sound (w := (103 / 397)) (n := 12)
    (lo := (531028331 / 1000000000)) (hi := (132757083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 147) = 1/(147 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11310 : Bounds (-132757083 / 250000000) (-531028331 / 1000000000) (Real.log (147 / 250)) := by
  have h := reflection_log_11310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11311_neg : (82383 / 200000000) ≤ -Real.log (250000 / 250103) ∧
    -Real.log (250000 / 250103) ≤ (102979 / 250000000) := by
  have h := checkLog_sound (w := (103 / 500103)) (n := 12)
    (lo := (82383 / 200000000)) (hi := (102979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250103 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250103 / 250000) = 1/(250000 / 250103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11311 : Bounds (82383 / 200000000) (102979 / 250000000) (Real.log (250103 / 250000)) := by
  have h := reflection_log_11311_neg
  have he : Real.log (250103 / 250000) = -Real.log (250000 / 250103) := by
    rw [show ((250103 / 250000) : ℝ) = ((250000 / 250103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11312_neg : (103021 / 250000000) ≤ -Real.log (249897 / 250000) ∧
    -Real.log (249897 / 250000) ≤ (82417 / 200000000) := by
  have h := checkLog_sound (w := (103 / 499897)) (n := 12)
    (lo := (103021 / 250000000)) (hi := (82417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249897) = 1/(249897 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11312 : Bounds (-82417 / 200000000) (-103021 / 250000000) (Real.log (249897 / 250000)) := by
  have h := reflection_log_11312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11313_neg : (768741 / 4000000) ≤ -Real.log (200000 / 242379) ∧
    -Real.log (200000 / 242379) ≤ (192185251 / 1000000000) := by
  have h := checkLog_sound (w := (42379 / 442379)) (n := 12)
    (lo := (768741 / 4000000)) (hi := (192185251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242379 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242379 / 200000) = 1/(200000 / 242379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11313 : Bounds (768741 / 4000000) (192185251 / 1000000000) (Real.log (242379 / 200000)) := by
  have h := reflection_log_11313_neg
  have he : Real.log (242379 / 200000) = -Real.log (200000 / 242379) := by
    rw [show ((242379 / 200000) : ℝ) = ((200000 / 242379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11314_neg : (238123949 / 1000000000) ≤ -Real.log (157621 / 200000) ∧
    -Real.log (157621 / 200000) ≤ (4762479 / 20000000) := by
  have h := checkLog_sound (w := (42379 / 357621)) (n := 12)
    (lo := (238123949 / 1000000000)) (hi := (4762479 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157621) = 1/(157621 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11314 : Bounds (-4762479 / 20000000) (-238123949 / 1000000000) (Real.log (157621 / 200000)) := by
  have h := reflection_log_11314_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11315_neg : (19296719 / 100000000) ≤ -Real.log (1000000 / 1212843) ∧
    -Real.log (1000000 / 1212843) ≤ (192967191 / 1000000000) := by
  have h := checkLog_sound (w := (212843 / 2212843)) (n := 12)
    (lo := (19296719 / 100000000)) (hi := (192967191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212843 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212843 / 1000000) = 1/(1000000 / 1212843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11315 : Bounds (19296719 / 100000000) (192967191 / 1000000000) (Real.log (1212843 / 1000000)) := by
  have h := reflection_log_11315_neg
  have he : Real.log (1212843 / 1000000) = -Real.log (1000000 / 1212843) := by
    rw [show ((1212843 / 1000000) : ℝ) = ((1000000 / 1212843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11316_neg : (119663779 / 500000000) ≤ -Real.log (787157 / 1000000) ∧
    -Real.log (787157 / 1000000) ≤ (239327559 / 1000000000) := by
  have h := checkLog_sound (w := (212843 / 1787157)) (n := 12)
    (lo := (119663779 / 500000000)) (hi := (239327559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787157) = 1/(787157 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11316 : Bounds (-239327559 / 1000000000) (-119663779 / 500000000) (Real.log (787157 / 1000000)) := by
  have h := reflection_log_11316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11317_neg : (2897523 / 62500000) ≤ -Real.log (954697857351 / 1000000000000) ∧
    -Real.log (954697857351 / 1000000000000) ≤ (46360369 / 1000000000) := by
  have h := checkLog_sound (w := (45302142649 / 1954697857351)) (n := 12)
    (lo := (2897523 / 62500000)) (hi := (46360369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 954697857351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 954697857351) = 1/(954697857351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11317 : Bounds (-46360369 / 1000000000) (-2897523 / 62500000) (Real.log (954697857351 / 1000000000000)) := by
  have h := reflection_log_11317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11318_neg : (45938699 / 1000000000) ≤ -Real.log (38204020359 / 40000000000) ∧
    -Real.log (38204020359 / 40000000000) ≤ (459387 / 10000000) := by
  have h := checkLog_sound (w := (1795979641 / 78204020359)) (n := 12)
    (lo := (45938699 / 1000000000)) (hi := (459387 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38204020359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38204020359) = 1/(38204020359 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11318 : Bounds (-459387 / 10000000) (-45938699 / 1000000000) (Real.log (38204020359 / 40000000000)) := by
  have h := reflection_log_11318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11319_neg : (430309199 / 1000000000) ≤ -Real.log (500000000000 / 768866458149) ∧
    -Real.log (500000000000 / 768866458149) ≤ (1075773 / 2500000) := by
  have h := checkLog_sound (w := (268866458149 / 1268866458149)) (n := 12)
    (lo := (430309199 / 1000000000)) (hi := (1075773 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768866458149 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768866458149 / 500000000000) = 1/(500000000000 / 768866458149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11319 : Bounds (430309199 / 1000000000) (1075773 / 2500000) (Real.log (768866458149 / 500000000000)) := by
  have h := reflection_log_11319_neg
  have he : Real.log (768866458149 / 500000000000) = -Real.log (500000000000 / 768866458149) := by
    rw [show ((768866458149 / 500000000000) : ℝ) = ((500000000000 / 768866458149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11320_neg : (432294749 / 1000000000) ≤ -Real.log (250000000000 / 385197298633) ∧
    -Real.log (250000000000 / 385197298633) ≤ (1729179 / 4000000) := by
  have h := checkLog_sound (w := (135197298633 / 635197298633)) (n := 12)
    (lo := (432294749 / 1000000000)) (hi := (1729179 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((385197298633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(385197298633 / 250000000000) = 1/(250000000000 / 385197298633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11320 : Bounds (432294749 / 1000000000) (1729179 / 4000000) (Real.log (385197298633 / 250000000000)) := by
  have h := reflection_log_11320_neg
  have he : Real.log (385197298633 / 250000000000) = -Real.log (250000000000 / 385197298633) := by
    rw [show ((385197298633 / 250000000000) : ℝ) = ((250000000000 / 385197298633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11321_neg : (873627767 / 1000000000) ≤ -Real.log (500000000000 / 1197792869269) ∧
    -Real.log (500000000000 / 1197792869269) ≤ (873627769 / 1000000000) := by
  have h := checkLog_sound (w := (197792869269 / 2197792869269)) (n := 12)
    (lo := (180480587 / 1000000000)) (hi := (45120147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197792869269 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1197792869269 / 1000000000000) = 1/(500000000000 / 1197792869269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11321 : Bounds (873627767 / 1000000000) (873627769 / 1000000000) (Real.log (1197792869269 / 500000000000)) := by
  have h := reflection_log_11321_neg
  have he : Real.log (1197792869269 / 500000000000) = -Real.log (500000000000 / 1197792869269) := by
    rw [show ((1197792869269 / 500000000000) : ℝ) = ((500000000000 / 1197792869269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11322_neg : (876035469 / 1000000000) ≤ -Real.log (500000000000 / 1200680272109) ∧
    -Real.log (500000000000 / 1200680272109) ≤ (876035471 / 1000000000) := by
  have h := checkLog_sound (w := (200680272109 / 2200680272109)) (n := 12)
    (lo := (182888289 / 1000000000)) (hi := (18288829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200680272109 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1200680272109 / 1000000000000) = 1/(500000000000 / 1200680272109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11322 : Bounds (876035469 / 1000000000) (876035471 / 1000000000) (Real.log (1200680272109 / 500000000000)) := by
  have h := reflection_log_11322_neg
  have he : Real.log (1200680272109 / 500000000000) = -Real.log (500000000000 / 1200680272109) := by
    rw [show ((1200680272109 / 500000000000) : ℝ) = ((500000000000 / 1200680272109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11323_neg : (345715103 / 1000000000) ≤ -Real.log (1000 / 1413) ∧
    -Real.log (1000 / 1413) ≤ (10803597 / 31250000) := by
  have h := checkLog_sound (w := (413 / 2413)) (n := 12)
    (lo := (345715103 / 1000000000)) (hi := (10803597 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1413 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1413 / 1000) = 1/(1000 / 1413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11323 : Bounds (345715103 / 1000000000) (10803597 / 31250000) (Real.log (1413 / 1000)) := by
  have h := reflection_log_11323_neg
  have he : Real.log (1413 / 1000) = -Real.log (1000 / 1413) := by
    rw [show ((1413 / 1000) : ℝ) = ((1000 / 1413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11324_neg : (532730459 / 1000000000) ≤ -Real.log (587 / 1000) ∧
    -Real.log (587 / 1000) ≤ (26636523 / 50000000) := by
  have h := checkLog_sound (w := (413 / 1587)) (n := 12)
    (lo := (532730459 / 1000000000)) (hi := (26636523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 587) = 1/(587 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11324 : Bounds (-26636523 / 50000000) (-532730459 / 1000000000) (Real.log (587 / 1000)) := by
  have h := reflection_log_11324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11325_neg : (206457 / 500000000) ≤ -Real.log (1000000 / 1000413) ∧
    -Real.log (1000000 / 1000413) ≤ (82583 / 200000000) := by
  have h := checkLog_sound (w := (413 / 2000413)) (n := 12)
    (lo := (206457 / 500000000)) (hi := (82583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000413 / 1000000) = 1/(1000000 / 1000413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11325 : Bounds (206457 / 500000000) (82583 / 200000000) (Real.log (1000413 / 1000000)) := by
  have h := reflection_log_11325_neg
  have he : Real.log (1000413 / 1000000) = -Real.log (1000000 / 1000413) := by
    rw [show ((1000413 / 1000000) : ℝ) = ((1000000 / 1000413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11326_neg : (82617 / 200000000) ≤ -Real.log (999587 / 1000000) ∧
    -Real.log (999587 / 1000000) ≤ (206543 / 500000000) := by
  have h := checkLog_sound (w := (413 / 1999587)) (n := 12)
    (lo := (82617 / 200000000)) (hi := (206543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999587) = 1/(999587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11326 : Bounds (-206543 / 500000000) (-82617 / 200000000) (Real.log (999587 / 1000000)) := by
  have h := reflection_log_11326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11327_neg : (192638157 / 1000000000) ≤ -Real.log (250000 / 303111) ∧
    -Real.log (250000 / 303111) ≤ (96319079 / 500000000) := by
  have h := checkLog_sound (w := (53111 / 553111)) (n := 12)
    (lo := (192638157 / 1000000000)) (hi := (96319079 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303111 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303111 / 250000) = 1/(250000 / 303111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11327 : Bounds (192638157 / 1000000000) (96319079 / 500000000) (Real.log (303111 / 250000)) := by
  have h := reflection_log_11327_neg
  have he : Real.log (303111 / 250000) = -Real.log (250000 / 303111) := by
    rw [show ((303111 / 250000) : ℝ) = ((250000 / 303111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0177 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11328_neg : (238820799 / 1000000000) ≤ -Real.log (196889 / 250000) ∧
    -Real.log (196889 / 250000) ≤ (149263 / 625000) := by
  have h := checkLog_sound (w := (53111 / 446889)) (n := 12)
    (lo := (238820799 / 1000000000)) (hi := (149263 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196889) = 1/(196889 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11328 : Bounds (-149263 / 625000) (-238820799 / 1000000000) (Real.log (196889 / 250000)) := by
  have h := reflection_log_11328_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11329_neg : (193421391 / 1000000000) ≤ -Real.log (500000 / 606697) ∧
    -Real.log (500000 / 606697) ≤ (12088837 / 62500000) := by
  have h := checkLog_sound (w := (106697 / 1106697)) (n := 12)
    (lo := (193421391 / 1000000000)) (hi := (12088837 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606697 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606697 / 500000) = 1/(500000 / 606697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11329 : Bounds (193421391 / 1000000000) (12088837 / 62500000) (Real.log (606697 / 500000)) := by
  have h := reflection_log_11329_neg
  have he : Real.log (606697 / 500000) = -Real.log (500000 / 606697) := by
    rw [show ((606697 / 500000) : ℝ) = ((500000 / 606697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11330_neg : (240027791 / 1000000000) ≤ -Real.log (393303 / 500000) ∧
    -Real.log (393303 / 500000) ≤ (15001737 / 62500000) := by
  have h := checkLog_sound (w := (106697 / 893303)) (n := 12)
    (lo := (240027791 / 1000000000)) (hi := (15001737 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393303) = 1/(393303 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11330 : Bounds (-15001737 / 62500000) (-240027791 / 1000000000) (Real.log (393303 / 500000)) := by
  have h := reflection_log_11330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11331_neg : (46606399 / 1000000000) ≤ -Real.log (238615750191 / 250000000000) ∧
    -Real.log (238615750191 / 250000000000) ≤ (29129 / 625000) := by
  have h := checkLog_sound (w := (11384249809 / 488615750191)) (n := 12)
    (lo := (46606399 / 1000000000)) (hi := (29129 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 238615750191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 238615750191) = 1/(238615750191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11331 : Bounds (-29129 / 625000) (-46606399 / 1000000000) (Real.log (238615750191 / 250000000000)) := by
  have h := reflection_log_11331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11332_neg : (23091321 / 500000000) ≤ -Real.log (59679221679 / 62500000000) ∧
    -Real.log (59679221679 / 62500000000) ≤ (46182643 / 1000000000) := by
  have h := checkLog_sound (w := (2820778321 / 122179221679)) (n := 12)
    (lo := (23091321 / 500000000)) (hi := (46182643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59679221679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59679221679) = 1/(59679221679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11332 : Bounds (-46182643 / 1000000000) (-23091321 / 500000000) (Real.log (59679221679 / 62500000000)) := by
  have h := reflection_log_11332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11333_neg : (107864739 / 250000000) ≤ -Real.log (250000000000 / 384875488219) ∧
    -Real.log (250000000000 / 384875488219) ≤ (431458957 / 1000000000) := by
  have h := checkLog_sound (w := (134875488219 / 634875488219)) (n := 12)
    (lo := (107864739 / 250000000)) (hi := (431458957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384875488219 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384875488219 / 250000000000) = 1/(250000000000 / 384875488219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11333 : Bounds (107864739 / 250000000) (431458957 / 1000000000) (Real.log (384875488219 / 250000000000)) := by
  have h := reflection_log_11333_neg
  have he : Real.log (384875488219 / 250000000000) = -Real.log (250000000000 / 384875488219) := by
    rw [show ((384875488219 / 250000000000) : ℝ) = ((250000000000 / 384875488219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11334_neg : (216724591 / 500000000) ≤ -Real.log (250000000000 / 385642240207) ∧
    -Real.log (250000000000 / 385642240207) ≤ (433449183 / 1000000000) := by
  have h := checkLog_sound (w := (135642240207 / 635642240207)) (n := 12)
    (lo := (216724591 / 500000000)) (hi := (433449183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((385642240207 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(385642240207 / 250000000000) = 1/(250000000000 / 385642240207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11334 : Bounds (216724591 / 500000000) (433449183 / 1000000000) (Real.log (385642240207 / 250000000000)) := by
  have h := reflection_log_11334_neg
  have he : Real.log (385642240207 / 250000000000) = -Real.log (250000000000 / 385642240207) := by
    rw [show ((385642240207 / 250000000000) : ℝ) = ((250000000000 / 385642240207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11335_neg : (876035469 / 1000000000) ≤ -Real.log (125000000000 / 300170068027) ∧
    -Real.log (125000000000 / 300170068027) ≤ (876035471 / 1000000000) := by
  have h := checkLog_sound (w := (50170068027 / 550170068027)) (n := 12)
    (lo := (182888289 / 1000000000)) (hi := (18288829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300170068027 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(300170068027 / 250000000000) = 1/(125000000000 / 300170068027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11335 : Bounds (876035469 / 1000000000) (876035471 / 1000000000) (Real.log (300170068027 / 125000000000)) := by
  have h := reflection_log_11335_neg
  have he : Real.log (300170068027 / 125000000000) = -Real.log (125000000000 / 300170068027) := by
    rw [show ((300170068027 / 125000000000) : ℝ) = ((125000000000 / 300170068027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11336_neg : (439222781 / 500000000) ≤ -Real.log (500000000000 / 1203577512777) ∧
    -Real.log (500000000000 / 1203577512777) ≤ (219611391 / 250000000) := by
  have h := checkLog_sound (w := (203577512777 / 2203577512777)) (n := 12)
    (lo := (92649191 / 500000000)) (hi := (185298383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203577512777 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1203577512777 / 1000000000000) = 1/(500000000000 / 1203577512777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11336 : Bounds (439222781 / 500000000) (219611391 / 250000000) (Real.log (1203577512777 / 500000000000)) := by
  have h := reflection_log_11336_neg
  have he : Real.log (1203577512777 / 500000000000) = -Real.log (500000000000 / 1203577512777) := by
    rw [show ((1203577512777 / 500000000000) : ℝ) = ((500000000000 / 1203577512777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11337_neg : (346422567 / 1000000000) ≤ -Real.log (500 / 707) ∧
    -Real.log (500 / 707) ≤ (43302821 / 125000000) := by
  have h := checkLog_sound (w := (207 / 1207)) (n := 12)
    (lo := (346422567 / 1000000000)) (hi := (43302821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707 / 500) = 1/(500 / 707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11337 : Bounds (346422567 / 1000000000) (43302821 / 125000000) (Real.log (707 / 500)) := by
  have h := reflection_log_11337_neg
  have he : Real.log (707 / 500) = -Real.log (500 / 707) := by
    rw [show ((707 / 500) : ℝ) = ((500 / 707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11338_neg : (534435489 / 1000000000) ≤ -Real.log (293 / 500) ∧
    -Real.log (293 / 500) ≤ (53443549 / 100000000) := by
  have h := checkLog_sound (w := (207 / 793)) (n := 12)
    (lo := (534435489 / 1000000000)) (hi := (53443549 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 293) = 1/(293 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11338 : Bounds (-53443549 / 100000000) (-534435489 / 1000000000) (Real.log (293 / 500)) := by
  have h := reflection_log_11338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11339_neg : (206957 / 500000000) ≤ -Real.log (500000 / 500207) ∧
    -Real.log (500000 / 500207) ≤ (82783 / 200000000) := by
  have h := checkLog_sound (w := (207 / 1000207)) (n := 12)
    (lo := (206957 / 500000000)) (hi := (82783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500207 / 500000) = 1/(500000 / 500207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11339 : Bounds (206957 / 500000000) (82783 / 200000000) (Real.log (500207 / 500000)) := by
  have h := reflection_log_11339_neg
  have he : Real.log (500207 / 500000) = -Real.log (500000 / 500207) := by
    rw [show ((500207 / 500000) : ℝ) = ((500000 / 500207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11340_neg : (82817 / 200000000) ≤ -Real.log (499793 / 500000) ∧
    -Real.log (499793 / 500000) ≤ (207043 / 500000000) := by
  have h := checkLog_sound (w := (207 / 999793)) (n := 12)
    (lo := (82817 / 200000000)) (hi := (207043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499793) = 1/(499793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11340 : Bounds (-207043 / 500000000) (-82817 / 200000000) (Real.log (499793 / 500000)) := by
  have h := reflection_log_11340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11341_neg : (193091683 / 1000000000) ≤ -Real.log (500000 / 606497) ∧
    -Real.log (500000 / 606497) ≤ (48272921 / 250000000) := by
  have h := checkLog_sound (w := (106497 / 1106497)) (n := 12)
    (lo := (193091683 / 1000000000)) (hi := (48272921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606497 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606497 / 500000) = 1/(500000 / 606497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11341 : Bounds (193091683 / 1000000000) (48272921 / 250000000) (Real.log (606497 / 500000)) := by
  have h := reflection_log_11341_neg
  have he : Real.log (606497 / 500000) = -Real.log (500000 / 606497) := by
    rw [show ((606497 / 500000) : ℝ) = ((500000 / 606497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11342_neg : (119759703 / 500000000) ≤ -Real.log (393503 / 500000) ∧
    -Real.log (393503 / 500000) ≤ (239519407 / 1000000000) := by
  have h := checkLog_sound (w := (106497 / 893503)) (n := 12)
    (lo := (119759703 / 500000000)) (hi := (239519407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393503) = 1/(393503 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11342 : Bounds (-239519407 / 1000000000) (-119759703 / 500000000) (Real.log (393503 / 500000)) := by
  have h := reflection_log_11342_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11343_neg : (96937693 / 500000000) ≤ -Real.log (200000 / 242789) ∧
    -Real.log (200000 / 242789) ≤ (193875387 / 1000000000) := by
  have h := checkLog_sound (w := (42789 / 442789)) (n := 12)
    (lo := (96937693 / 500000000)) (hi := (193875387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242789 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242789 / 200000) = 1/(200000 / 242789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11343 : Bounds (96937693 / 500000000) (193875387 / 1000000000) (Real.log (242789 / 200000)) := by
  have h := reflection_log_11343_neg
  have he : Real.log (242789 / 200000) = -Real.log (200000 / 242789) := by
    rw [show ((242789 / 200000) : ℝ) = ((200000 / 242789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11344_neg : (120364257 / 500000000) ≤ -Real.log (157211 / 200000) ∧
    -Real.log (157211 / 200000) ≤ (48145703 / 200000000) := by
  have h := checkLog_sound (w := (42789 / 357211)) (n := 12)
    (lo := (120364257 / 500000000)) (hi := (48145703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157211) = 1/(157211 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11344 : Bounds (-48145703 / 200000000) (-120364257 / 500000000) (Real.log (157211 / 200000)) := by
  have h := reflection_log_11344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11345_neg : (46853127 / 1000000000) ≤ -Real.log (38169101479 / 40000000000) ∧
    -Real.log (38169101479 / 40000000000) ≤ (5856641 / 125000000) := by
  have h := checkLog_sound (w := (1830898521 / 78169101479)) (n := 12)
    (lo := (46853127 / 1000000000)) (hi := (5856641 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38169101479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38169101479) = 1/(38169101479 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11345 : Bounds (-5856641 / 125000000) (-46853127 / 1000000000) (Real.log (38169101479 / 40000000000)) := by
  have h := reflection_log_11345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11346_neg : (46427723 / 1000000000) ≤ -Real.log (238658388991 / 250000000000) ∧
    -Real.log (238658388991 / 250000000000) ≤ (11606931 / 250000000) := by
  have h := checkLog_sound (w := (11341611009 / 488658388991)) (n := 12)
    (lo := (46427723 / 1000000000)) (hi := (11606931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 238658388991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 238658388991) = 1/(238658388991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11346 : Bounds (-11606931 / 250000000) (-46427723 / 1000000000) (Real.log (238658388991 / 250000000000)) := by
  have h := reflection_log_11346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11347_neg : (43261109 / 100000000) ≤ -Real.log (50000000000 / 77063834329) ∧
    -Real.log (50000000000 / 77063834329) ≤ (432611091 / 1000000000) := by
  have h := checkLog_sound (w := (27063834329 / 127063834329)) (n := 12)
    (lo := (43261109 / 100000000)) (hi := (432611091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77063834329 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77063834329 / 50000000000) = 1/(50000000000 / 77063834329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11347 : Bounds (43261109 / 100000000) (432611091 / 1000000000) (Real.log (77063834329 / 50000000000)) := by
  have h := reflection_log_11347_neg
  have he : Real.log (77063834329 / 50000000000) = -Real.log (50000000000 / 77063834329) := by
    rw [show ((77063834329 / 50000000000) : ℝ) = ((50000000000 / 77063834329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11348_neg : (434603901 / 1000000000) ≤ -Real.log (250000000000 / 386087805561) ∧
    -Real.log (250000000000 / 386087805561) ≤ (217301951 / 500000000) := by
  have h := checkLog_sound (w := (136087805561 / 636087805561)) (n := 12)
    (lo := (434603901 / 1000000000)) (hi := (217301951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386087805561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386087805561 / 250000000000) = 1/(250000000000 / 386087805561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11348 : Bounds (434603901 / 1000000000) (217301951 / 500000000) (Real.log (386087805561 / 250000000000)) := by
  have h := reflection_log_11348_neg
  have he : Real.log (386087805561 / 250000000000) = -Real.log (250000000000 / 386087805561) := by
    rw [show ((386087805561 / 250000000000) : ℝ) = ((250000000000 / 386087805561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11349_neg : (439222781 / 500000000) ≤ -Real.log (62500000000 / 150447189097) ∧
    -Real.log (62500000000 / 150447189097) ≤ (219611391 / 250000000) := by
  have h := checkLog_sound (w := (25447189097 / 275447189097)) (n := 12)
    (lo := (92649191 / 500000000)) (hi := (185298383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150447189097 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(150447189097 / 125000000000) = 1/(62500000000 / 150447189097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11349 : Bounds (439222781 / 500000000) (219611391 / 250000000) (Real.log (150447189097 / 62500000000)) := by
  have h := reflection_log_11349_neg
  have he : Real.log (150447189097 / 62500000000) = -Real.log (62500000000 / 150447189097) := by
    rw [show ((150447189097 / 62500000000) : ℝ) = ((62500000000 / 150447189097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11350_neg : (110107257 / 125000000) ≤ -Real.log (500000000000 / 1206484641639) ∧
    -Real.log (500000000000 / 1206484641639) ≤ (440429029 / 500000000) := by
  have h := checkLog_sound (w := (206484641639 / 2206484641639)) (n := 12)
    (lo := (46927719 / 250000000)) (hi := (187710877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206484641639 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1206484641639 / 1000000000000) = 1/(500000000000 / 1206484641639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11350 : Bounds (110107257 / 125000000) (440429029 / 500000000) (Real.log (1206484641639 / 500000000000)) := by
  have h := reflection_log_11350_neg
  have he : Real.log (1206484641639 / 500000000000) = -Real.log (500000000000 / 1206484641639) := by
    rw [show ((1206484641639 / 500000000000) : ℝ) = ((500000000000 / 1206484641639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11351_neg : (347129531 / 1000000000) ≤ -Real.log (200 / 283) ∧
    -Real.log (200 / 283) ≤ (86782383 / 250000000) := by
  have h := checkLog_sound (w := (83 / 483)) (n := 12)
    (lo := (347129531 / 1000000000)) (hi := (86782383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(283 / 200) = 1/(200 / 283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11351 : Bounds (347129531 / 1000000000) (86782383 / 250000000) (Real.log (283 / 200)) := by
  have h := reflection_log_11351_neg
  have he : Real.log (283 / 200) = -Real.log (200 / 283) := by
    rw [show ((283 / 200) : ℝ) = ((200 / 283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11352_neg : (536143431 / 1000000000) ≤ -Real.log (117 / 200) ∧
    -Real.log (117 / 200) ≤ (67017929 / 125000000) := by
  have h := checkLog_sound (w := (83 / 317)) (n := 12)
    (lo := (536143431 / 1000000000)) (hi := (67017929 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 117) = 1/(117 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11352 : Bounds (-67017929 / 125000000) (-536143431 / 1000000000) (Real.log (117 / 200)) := by
  have h := reflection_log_11352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11353_neg : (414913 / 1000000000) ≤ -Real.log (200000 / 200083) ∧
    -Real.log (200000 / 200083) ≤ (207457 / 500000000) := by
  have h := checkLog_sound (w := (83 / 400083)) (n := 12)
    (lo := (414913 / 1000000000)) (hi := (207457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200083 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200083 / 200000) = 1/(200000 / 200083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11353 : Bounds (414913 / 1000000000) (207457 / 500000000) (Real.log (200083 / 200000)) := by
  have h := reflection_log_11353_neg
  have he : Real.log (200083 / 200000) = -Real.log (200000 / 200083) := by
    rw [show ((200083 / 200000) : ℝ) = ((200000 / 200083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11354_neg : (207543 / 500000000) ≤ -Real.log (199917 / 200000) ∧
    -Real.log (199917 / 200000) ≤ (415087 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 399917)) (n := 12)
    (lo := (207543 / 500000000)) (hi := (415087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199917) = 1/(199917 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11354 : Bounds (-415087 / 1000000000) (-207543 / 500000000) (Real.log (199917 / 200000)) := by
  have h := reflection_log_11354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11355_neg : (48386251 / 250000000) ≤ -Real.log (125000 / 151693) ∧
    -Real.log (125000 / 151693) ≤ (38709001 / 200000000) := by
  have h := checkLog_sound (w := (26693 / 276693)) (n := 12)
    (lo := (48386251 / 250000000)) (hi := (38709001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151693 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151693 / 125000) = 1/(125000 / 151693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11355 : Bounds (48386251 / 250000000) (38709001 / 200000000) (Real.log (151693 / 125000)) := by
  have h := reflection_log_11355_neg
  have he : Real.log (151693 / 125000) = -Real.log (125000 / 151693) := by
    rw [show ((151693 / 125000) : ℝ) = ((125000 / 151693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11356_neg : (120109251 / 500000000) ≤ -Real.log (98307 / 125000) ∧
    -Real.log (98307 / 125000) ≤ (240218503 / 1000000000) := by
  have h := checkLog_sound (w := (26693 / 223307)) (n := 12)
    (lo := (120109251 / 500000000)) (hi := (240218503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98307) = 1/(98307 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11356 : Bounds (-240218503 / 1000000000) (-120109251 / 500000000) (Real.log (98307 / 125000)) := by
  have h := reflection_log_11356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11357_neg : (7773167 / 40000000) ≤ -Real.log (31250 / 37953) ∧
    -Real.log (31250 / 37953) ≤ (24291147 / 125000000) := by
  have h := checkLog_sound (w := (6703 / 69203)) (n := 12)
    (lo := (7773167 / 40000000)) (hi := (24291147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37953 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37953 / 31250) = 1/(31250 / 37953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11357 : Bounds (7773167 / 40000000) (24291147 / 125000000) (Real.log (37953 / 31250)) := by
  have h := reflection_log_11357_neg
  have he : Real.log (37953 / 31250) = -Real.log (31250 / 37953) := by
    rw [show ((37953 / 31250) : ℝ) = ((31250 / 37953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11358_neg : (241429729 / 1000000000) ≤ -Real.log (24547 / 31250) ∧
    -Real.log (24547 / 31250) ≤ (24142973 / 100000000) := by
  have h := checkLog_sound (w := (6703 / 55797)) (n := 12)
    (lo := (241429729 / 1000000000)) (hi := (24142973 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24547) = 1/(24547 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11358 : Bounds (-24142973 / 100000000) (-241429729 / 1000000000) (Real.log (24547 / 31250)) := by
  have h := reflection_log_11358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11359_neg : (47100553 / 1000000000) ≤ -Real.log (931632291 / 976562500) ∧
    -Real.log (931632291 / 976562500) ≤ (23550277 / 500000000) := by
  have h := checkLog_sound (w := (44930209 / 1908194791)) (n := 12)
    (lo := (47100553 / 1000000000)) (hi := (23550277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 931632291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 931632291) = 1/(931632291 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11359 : Bounds (-23550277 / 500000000) (-47100553 / 1000000000) (Real.log (931632291 / 976562500)) := by
  have h := reflection_log_11359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11360_neg : (46673497 / 1000000000) ≤ -Real.log (14912483751 / 15625000000) ∧
    -Real.log (14912483751 / 15625000000) ≤ (23336749 / 500000000) := by
  have h := checkLog_sound (w := (712516249 / 30537483751)) (n := 12)
    (lo := (46673497 / 1000000000)) (hi := (23336749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14912483751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14912483751) = 1/(14912483751 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11360 : Bounds (-23336749 / 500000000) (-46673497 / 1000000000) (Real.log (14912483751 / 15625000000)) := by
  have h := reflection_log_11360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11361_neg : (216881753 / 500000000) ≤ -Real.log (100000000000 / 154305390257) ∧
    -Real.log (100000000000 / 154305390257) ≤ (433763507 / 1000000000) := by
  have h := checkLog_sound (w := (54305390257 / 254305390257)) (n := 12)
    (lo := (216881753 / 500000000)) (hi := (433763507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154305390257 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154305390257 / 100000000000) = 1/(100000000000 / 154305390257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11361 : Bounds (216881753 / 500000000) (433763507 / 1000000000) (Real.log (154305390257 / 100000000000)) := by
  have h := reflection_log_11361_neg
  have he : Real.log (154305390257 / 100000000000) = -Real.log (100000000000 / 154305390257) := by
    rw [show ((154305390257 / 100000000000) : ℝ) = ((100000000000 / 154305390257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11362_neg : (54469863 / 125000000) ≤ -Real.log (31250000000 / 48316749501) ∧
    -Real.log (31250000000 / 48316749501) ≤ (87151781 / 200000000) := by
  have h := checkLog_sound (w := (17066749501 / 79566749501)) (n := 12)
    (lo := (54469863 / 125000000)) (hi := (87151781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48316749501 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48316749501 / 31250000000) = 1/(31250000000 / 48316749501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11362 : Bounds (54469863 / 125000000) (87151781 / 200000000) (Real.log (48316749501 / 31250000000)) := by
  have h := reflection_log_11362_neg
  have he : Real.log (48316749501 / 31250000000) = -Real.log (31250000000 / 48316749501) := by
    rw [show ((48316749501 / 31250000000) : ℝ) = ((31250000000 / 48316749501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11363_neg : (110107257 / 125000000) ≤ -Real.log (250000000000 / 603242320819) ∧
    -Real.log (250000000000 / 603242320819) ≤ (440429029 / 500000000) := by
  have h := checkLog_sound (w := (103242320819 / 1103242320819)) (n := 12)
    (lo := (46927719 / 250000000)) (hi := (187710877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603242320819 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(603242320819 / 500000000000) = 1/(250000000000 / 603242320819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11363 : Bounds (110107257 / 125000000) (440429029 / 500000000) (Real.log (603242320819 / 250000000000)) := by
  have h := reflection_log_11363_neg
  have he : Real.log (603242320819 / 250000000000) = -Real.log (250000000000 / 603242320819) := by
    rw [show ((603242320819 / 250000000000) : ℝ) = ((250000000000 / 603242320819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11364_neg : (441636481 / 500000000) ≤ -Real.log (250000000000 / 604700854701) ∧
    -Real.log (250000000000 / 604700854701) ≤ (220818241 / 250000000) := by
  have h := checkLog_sound (w := (104700854701 / 1104700854701)) (n := 12)
    (lo := (95062891 / 500000000)) (hi := (190125783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604700854701 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(604700854701 / 500000000000) = 1/(250000000000 / 604700854701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11364 : Bounds (441636481 / 500000000) (220818241 / 250000000) (Real.log (604700854701 / 250000000000)) := by
  have h := reflection_log_11364_neg
  have he : Real.log (604700854701 / 250000000000) = -Real.log (250000000000 / 604700854701) := by
    rw [show ((604700854701 / 250000000000) : ℝ) = ((250000000000 / 604700854701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11365_neg : (69567199 / 200000000) ≤ -Real.log (125 / 177) ∧
    -Real.log (125 / 177) ≤ (86958999 / 250000000) := by
  have h := checkLog_sound (w := (26 / 151)) (n := 12)
    (lo := (69567199 / 200000000)) (hi := (86958999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 125) = 1/(125 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11365 : Bounds (69567199 / 200000000) (86958999 / 250000000) (Real.log (177 / 125)) := by
  have h := reflection_log_11365_neg
  have he : Real.log (177 / 125) = -Real.log (125 / 177) := by
    rw [show ((177 / 125) : ℝ) = ((125 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11366_neg : (67231787 / 125000000) ≤ -Real.log (73 / 125) ∧
    -Real.log (73 / 125) ≤ (537854297 / 1000000000) := by
  have h := checkLog_sound (w := (26 / 99)) (n := 12)
    (lo := (67231787 / 125000000)) (hi := (537854297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 73) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 73) = 1/(73 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11366 : Bounds (-537854297 / 1000000000) (-67231787 / 125000000) (Real.log (73 / 125)) := by
  have h := reflection_log_11366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11367_neg : (415913 / 1000000000) ≤ -Real.log (31250 / 31263) ∧
    -Real.log (31250 / 31263) ≤ (207957 / 500000000) := by
  have h := checkLog_sound (w := (13 / 62513)) (n := 12)
    (lo := (415913 / 1000000000)) (hi := (207957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31263 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31263 / 31250) = 1/(31250 / 31263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11367 : Bounds (415913 / 1000000000) (207957 / 500000000) (Real.log (31263 / 31250)) := by
  have h := reflection_log_11367_neg
  have he : Real.log (31263 / 31250) = -Real.log (31250 / 31263) := by
    rw [show ((31263 / 31250) : ℝ) = ((31250 / 31263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11368_neg : (208043 / 500000000) ≤ -Real.log (31237 / 31250) ∧
    -Real.log (31237 / 31250) ≤ (416087 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 62487)) (n := 12)
    (lo := (208043 / 500000000)) (hi := (416087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31237) = 1/(31237 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11368 : Bounds (-416087 / 1000000000) (-208043 / 500000000) (Real.log (31237 / 31250)) := by
  have h := reflection_log_11368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11369_neg : (193998119 / 1000000000) ≤ -Real.log (500000 / 607047) ∧
    -Real.log (500000 / 607047) ≤ (4849953 / 25000000) := by
  have h := checkLog_sound (w := (107047 / 1107047)) (n := 12)
    (lo := (193998119 / 1000000000)) (hi := (4849953 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607047 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607047 / 500000) = 1/(500000 / 607047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11369 : Bounds (193998119 / 1000000000) (4849953 / 25000000) (Real.log (607047 / 500000)) := by
  have h := reflection_log_11369_neg
  have he : Real.log (607047 / 500000) = -Real.log (500000 / 607047) := by
    rw [show ((607047 / 500000) : ℝ) = ((500000 / 607047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11370_neg : (120459043 / 500000000) ≤ -Real.log (392953 / 500000) ∧
    -Real.log (392953 / 500000) ≤ (240918087 / 1000000000) := by
  have h := checkLog_sound (w := (107047 / 892953)) (n := 12)
    (lo := (120459043 / 500000000)) (hi := (240918087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 392953) = 1/(392953 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11370 : Bounds (-240918087 / 1000000000) (-120459043 / 500000000) (Real.log (392953 / 500000)) := by
  have h := reflection_log_11370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11371_neg : (97391791 / 500000000) ≤ -Real.log (125000 / 151881) ∧
    -Real.log (125000 / 151881) ≤ (194783583 / 1000000000) := by
  have h := checkLog_sound (w := (26881 / 276881)) (n := 12)
    (lo := (97391791 / 500000000)) (hi := (194783583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151881 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151881 / 125000) = 1/(125000 / 151881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11371 : Bounds (97391791 / 500000000) (194783583 / 1000000000) (Real.log (151881 / 125000)) := by
  have h := reflection_log_11371_neg
  have he : Real.log (151881 / 125000) = -Real.log (125000 / 151881) := by
    rw [show ((151881 / 125000) : ℝ) = ((125000 / 151881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11372_neg : (242132709 / 1000000000) ≤ -Real.log (98119 / 125000) ∧
    -Real.log (98119 / 125000) ≤ (24213271 / 100000000) := by
  have h := checkLog_sound (w := (26881 / 223119)) (n := 12)
    (lo := (242132709 / 1000000000)) (hi := (24213271 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98119) = 1/(98119 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11372 : Bounds (-24213271 / 100000000) (-242132709 / 1000000000) (Real.log (98119 / 125000)) := by
  have h := reflection_log_11372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11373_neg : (47349127 / 1000000000) ≤ -Real.log (14902411839 / 15625000000) ∧
    -Real.log (14902411839 / 15625000000) ≤ (5918641 / 125000000) := by
  have h := checkLog_sound (w := (722588161 / 30527411839)) (n := 12)
    (lo := (47349127 / 1000000000)) (hi := (5918641 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14902411839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14902411839) = 1/(14902411839 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11373 : Bounds (-5918641 / 125000000) (-47349127 / 1000000000) (Real.log (14902411839 / 15625000000)) := by
  have h := reflection_log_11373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11374_neg : (23459983 / 500000000) ≤ -Real.log (238540939791 / 250000000000) ∧
    -Real.log (238540939791 / 250000000000) ≤ (46919967 / 1000000000) := by
  have h := checkLog_sound (w := (11459060209 / 488540939791)) (n := 12)
    (lo := (23459983 / 500000000)) (hi := (46919967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 238540939791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 238540939791) = 1/(238540939791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11374 : Bounds (-46919967 / 1000000000) (-23459983 / 500000000) (Real.log (238540939791 / 250000000000)) := by
  have h := reflection_log_11374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11375_neg : (217458103 / 500000000) ≤ -Real.log (500000000000 / 772416803027) ∧
    -Real.log (500000000000 / 772416803027) ≤ (434916207 / 1000000000) := by
  have h := checkLog_sound (w := (272416803027 / 1272416803027)) (n := 12)
    (lo := (217458103 / 500000000)) (hi := (434916207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772416803027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772416803027 / 500000000000) = 1/(500000000000 / 772416803027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11375 : Bounds (217458103 / 500000000) (434916207 / 1000000000) (Real.log (772416803027 / 500000000000)) := by
  have h := reflection_log_11375_neg
  have he : Real.log (772416803027 / 500000000000) = -Real.log (500000000000 / 772416803027) := by
    rw [show ((772416803027 / 500000000000) : ℝ) = ((500000000000 / 772416803027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11376_neg : (436916291 / 1000000000) ≤ -Real.log (500000000000 / 773963248709) ∧
    -Real.log (500000000000 / 773963248709) ≤ (109229073 / 250000000) := by
  have h := checkLog_sound (w := (273963248709 / 1273963248709)) (n := 12)
    (lo := (436916291 / 1000000000)) (hi := (109229073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773963248709 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773963248709 / 500000000000) = 1/(500000000000 / 773963248709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11376 : Bounds (436916291 / 1000000000) (109229073 / 250000000) (Real.log (773963248709 / 500000000000)) := by
  have h := reflection_log_11376_neg
  have he : Real.log (773963248709 / 500000000000) = -Real.log (500000000000 / 773963248709) := by
    rw [show ((773963248709 / 500000000000) : ℝ) = ((500000000000 / 773963248709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11377_neg : (441636481 / 500000000) ≤ -Real.log (500000000000 / 1209401709401) ∧
    -Real.log (500000000000 / 1209401709401) ≤ (220818241 / 250000000) := by
  have h := checkLog_sound (w := (209401709401 / 2209401709401)) (n := 12)
    (lo := (95062891 / 500000000)) (hi := (190125783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209401709401 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1209401709401 / 1000000000000) = 1/(500000000000 / 1209401709401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11377 : Bounds (441636481 / 500000000) (220818241 / 250000000) (Real.log (1209401709401 / 500000000000)) := by
  have h := reflection_log_11377_neg
  have he : Real.log (1209401709401 / 500000000000) = -Real.log (500000000000 / 1209401709401) := by
    rw [show ((1209401709401 / 500000000000) : ℝ) = ((500000000000 / 1209401709401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11378_neg : (88569029 / 100000000) ≤ -Real.log (125000000000 / 303082191781) ∧
    -Real.log (125000000000 / 303082191781) ≤ (221422573 / 250000000) := by
  have h := checkLog_sound (w := (53082191781 / 553082191781)) (n := 12)
    (lo := (19254311 / 100000000)) (hi := (192543111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303082191781 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(303082191781 / 250000000000) = 1/(125000000000 / 303082191781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11378 : Bounds (88569029 / 100000000) (221422573 / 250000000) (Real.log (303082191781 / 125000000000)) := by
  have h := reflection_log_11378_neg
  have he : Real.log (303082191781 / 125000000000) = -Real.log (125000000000 / 303082191781) := by
    rw [show ((303082191781 / 125000000000) : ℝ) = ((125000000000 / 303082191781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11379_neg : (8713549 / 25000000) ≤ -Real.log (1000 / 1417) ∧
    -Real.log (1000 / 1417) ≤ (348541961 / 1000000000) := by
  have h := checkLog_sound (w := (417 / 2417)) (n := 12)
    (lo := (8713549 / 25000000)) (hi := (348541961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1417 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1417 / 1000) = 1/(1000 / 1417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11379 : Bounds (8713549 / 25000000) (348541961 / 1000000000) (Real.log (1417 / 1000)) := by
  have h := reflection_log_11379_neg
  have he : Real.log (1417 / 1000) = -Real.log (1000 / 1417) := by
    rw [show ((1417 / 1000) : ℝ) = ((1000 / 1417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11380_neg : (134892023 / 250000000) ≤ -Real.log (583 / 1000) ∧
    -Real.log (583 / 1000) ≤ (539568093 / 1000000000) := by
  have h := checkLog_sound (w := (417 / 1583)) (n := 12)
    (lo := (134892023 / 250000000)) (hi := (539568093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 583) = 1/(583 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11380 : Bounds (-539568093 / 1000000000) (-134892023 / 250000000) (Real.log (583 / 1000)) := by
  have h := reflection_log_11380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11381_neg : (416913 / 1000000000) ≤ -Real.log (1000000 / 1000417) ∧
    -Real.log (1000000 / 1000417) ≤ (208457 / 500000000) := by
  have h := checkLog_sound (w := (417 / 2000417)) (n := 12)
    (lo := (416913 / 1000000000)) (hi := (208457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000417 / 1000000) = 1/(1000000 / 1000417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11381 : Bounds (416913 / 1000000000) (208457 / 500000000) (Real.log (1000417 / 1000000)) := by
  have h := reflection_log_11381_neg
  have he : Real.log (1000417 / 1000000) = -Real.log (1000000 / 1000417) := by
    rw [show ((1000417 / 1000000) : ℝ) = ((1000000 / 1000417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11382_neg : (208543 / 500000000) ≤ -Real.log (999583 / 1000000) ∧
    -Real.log (999583 / 1000000) ≤ (417087 / 1000000000) := by
  have h := checkLog_sound (w := (417 / 1999583)) (n := 12)
    (lo := (208543 / 500000000)) (hi := (417087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999583) = 1/(999583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11382 : Bounds (-417087 / 1000000000) (-208543 / 500000000) (Real.log (999583 / 1000000)) := by
  have h := reflection_log_11382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11383_neg : (194451853 / 1000000000) ≤ -Real.log (200000 / 242929) ∧
    -Real.log (200000 / 242929) ≤ (97225927 / 500000000) := by
  have h := checkLog_sound (w := (42929 / 442929)) (n := 12)
    (lo := (194451853 / 1000000000)) (hi := (97225927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242929 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242929 / 200000) = 1/(200000 / 242929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11383 : Bounds (194451853 / 1000000000) (97225927 / 500000000) (Real.log (242929 / 200000)) := by
  have h := reflection_log_11383_neg
  have he : Real.log (242929 / 200000) = -Real.log (200000 / 242929) := by
    rw [show ((242929 / 200000) : ℝ) = ((200000 / 242929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11384_neg : (120809717 / 500000000) ≤ -Real.log (157071 / 200000) ∧
    -Real.log (157071 / 200000) ≤ (48323887 / 200000000) := by
  have h := checkLog_sound (w := (42929 / 357071)) (n := 12)
    (lo := (120809717 / 500000000)) (hi := (48323887 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157071) = 1/(157071 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11384 : Bounds (-48323887 / 200000000) (-120809717 / 500000000) (Real.log (157071 / 200000)) := by
  have h := reflection_log_11384_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11385_neg : (195236959 / 1000000000) ≤ -Real.log (1000000 / 1215599) ∧
    -Real.log (1000000 / 1215599) ≤ (1220231 / 6250000) := by
  have h := checkLog_sound (w := (215599 / 2215599)) (n := 12)
    (lo := (195236959 / 1000000000)) (hi := (1220231 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1215599 / 1000000) = 1/(1000000 / 1215599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11385 : Bounds (195236959 / 1000000000) (1220231 / 6250000) (Real.log (1215599 / 1000000)) := by
  have h := reflection_log_11385_neg
  have he : Real.log (1215599 / 1000000) = -Real.log (1000000 / 1215599) := by
    rw [show ((1215599 / 1000000) : ℝ) = ((1000000 / 1215599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11386_neg : (242834909 / 1000000000) ≤ -Real.log (784401 / 1000000) ∧
    -Real.log (784401 / 1000000) ≤ (24283491 / 100000000) := by
  have h := checkLog_sound (w := (215599 / 1784401)) (n := 12)
    (lo := (242834909 / 1000000000)) (hi := (24283491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 784401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 784401) = 1/(784401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11386 : Bounds (-24283491 / 100000000) (-242834909 / 1000000000) (Real.log (784401 / 1000000)) := by
  have h := reflection_log_11386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11387_neg : (951959 / 20000000) ≤ -Real.log (953517071199 / 1000000000000) ∧
    -Real.log (953517071199 / 1000000000000) ≤ (47597951 / 1000000000) := by
  have h := checkLog_sound (w := (46482928801 / 1953517071199)) (n := 12)
    (lo := (951959 / 20000000)) (hi := (47597951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 953517071199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 953517071199) = 1/(953517071199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11387 : Bounds (-47597951 / 1000000000) (-951959 / 20000000) (Real.log (953517071199 / 1000000000000)) := by
  have h := reflection_log_11387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11388_neg : (47167581 / 1000000000) ≤ -Real.log (38157100959 / 40000000000) ∧
    -Real.log (38157100959 / 40000000000) ≤ (23583791 / 500000000) := by
  have h := checkLog_sound (w := (1842899041 / 78157100959)) (n := 12)
    (lo := (47167581 / 1000000000)) (hi := (23583791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38157100959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38157100959) = 1/(38157100959 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11388 : Bounds (-23583791 / 500000000) (-47167581 / 1000000000) (Real.log (38157100959 / 40000000000)) := by
  have h := reflection_log_11388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11389_neg : (436071287 / 1000000000) ≤ -Real.log (100000000000 / 154661904489) ∧
    -Real.log (100000000000 / 154661904489) ≤ (54508911 / 125000000) := by
  have h := checkLog_sound (w := (54661904489 / 254661904489)) (n := 12)
    (lo := (436071287 / 1000000000)) (hi := (54508911 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154661904489 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154661904489 / 100000000000) = 1/(100000000000 / 154661904489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11389 : Bounds (436071287 / 1000000000) (54508911 / 125000000) (Real.log (154661904489 / 100000000000)) := by
  have h := reflection_log_11389_neg
  have he : Real.log (154661904489 / 100000000000) = -Real.log (100000000000 / 154661904489) := by
    rw [show ((154661904489 / 100000000000) : ℝ) = ((100000000000 / 154661904489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11390_neg : (438071869 / 1000000000) ≤ -Real.log (500000000000 / 774858140161) ∧
    -Real.log (500000000000 / 774858140161) ≤ (43807187 / 100000000) := by
  have h := checkLog_sound (w := (274858140161 / 1274858140161)) (n := 12)
    (lo := (438071869 / 1000000000)) (hi := (43807187 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774858140161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774858140161 / 500000000000) = 1/(500000000000 / 774858140161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11390 : Bounds (438071869 / 1000000000) (43807187 / 100000000) (Real.log (774858140161 / 500000000000)) := by
  have h := reflection_log_11390_neg
  have he : Real.log (774858140161 / 500000000000) = -Real.log (500000000000 / 774858140161) := by
    rw [show ((774858140161 / 500000000000) : ℝ) = ((500000000000 / 774858140161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11391_neg : (88569029 / 100000000) ≤ -Real.log (500000000000 / 1212328767123) ∧
    -Real.log (500000000000 / 1212328767123) ≤ (221422573 / 250000000) := by
  have h := checkLog_sound (w := (212328767123 / 2212328767123)) (n := 12)
    (lo := (19254311 / 100000000)) (hi := (192543111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212328767123 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1212328767123 / 1000000000000) = 1/(500000000000 / 1212328767123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11391 : Bounds (88569029 / 100000000) (221422573 / 250000000) (Real.log (1212328767123 / 500000000000)) := by
  have h := reflection_log_11391_neg
  have he : Real.log (1212328767123 / 500000000000) = -Real.log (500000000000 / 1212328767123) := by
    rw [show ((1212328767123 / 500000000000) : ℝ) = ((500000000000 / 1212328767123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


