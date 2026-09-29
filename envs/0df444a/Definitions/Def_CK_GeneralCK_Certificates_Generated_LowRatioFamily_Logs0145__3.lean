-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0145__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0145__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T05:23:47.866599+00:00
-- url     : https://prove2.me/theorems/31ad27cc-0783-448c-94bd-2434298f07ae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0147)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0147)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0147) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0145 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0146, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0147).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0145__3_q01

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0147 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9408_neg : (21410339 / 1000000000) ≤ -Real.log (978817235151 / 1000000000000) ∧
    -Real.log (978817235151 / 1000000000000) ≤ (1070517 / 50000000) := by
  have h := checkLog_sound (w := (21182764849 / 1978817235151)) (n := 12)
    (lo := (21410339 / 1000000000)) (hi := (1070517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978817235151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978817235151) = 1/(978817235151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9408 : Bounds (-1070517 / 50000000) (-21410339 / 1000000000) (Real.log (978817235151 / 1000000000000)) := by
  have h := reflection_log_9408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9409_neg : (293167859 / 1000000000) ≤ -Real.log (500000000000 / 670333907967) ∧
    -Real.log (500000000000 / 670333907967) ≤ (14658393 / 50000000) := by
  have h := checkLog_sound (w := (170333907967 / 1170333907967)) (n := 12)
    (lo := (293167859 / 1000000000)) (hi := (14658393 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670333907967 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670333907967 / 500000000000) = 1/(500000000000 / 670333907967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9409 : Bounds (293167859 / 1000000000) (14658393 / 50000000) (Real.log (670333907967 / 500000000000)) := by
  have h := reflection_log_9409_neg
  have he : Real.log (670333907967 / 500000000000) = -Real.log (500000000000 / 670333907967) := by
    rw [show ((670333907967 / 500000000000) : ℝ) = ((500000000000 / 670333907967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9410_neg : (294281539 / 1000000000) ≤ -Real.log (62500000000 / 83885107599) ∧
    -Real.log (62500000000 / 83885107599) ≤ (14714077 / 50000000) := by
  have h := checkLog_sound (w := (21385107599 / 146385107599)) (n := 12)
    (lo := (294281539 / 1000000000)) (hi := (14714077 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83885107599 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83885107599 / 62500000000) = 1/(62500000000 / 83885107599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9410 : Bounds (294281539 / 1000000000) (14714077 / 50000000) (Real.log (83885107599 / 62500000000)) := by
  have h := reflection_log_9410_neg
  have he : Real.log (83885107599 / 62500000000) = -Real.log (62500000000 / 83885107599) := by
    rw [show ((83885107599 / 62500000000) : ℝ) = ((62500000000 / 83885107599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9411_neg : (590587787 / 1000000000) ≤ -Real.log (500000000000 / 902524544179) ∧
    -Real.log (500000000000 / 902524544179) ≤ (147646947 / 250000000) := by
  have h := checkLog_sound (w := (402524544179 / 1402524544179)) (n := 12)
    (lo := (590587787 / 1000000000)) (hi := (147646947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902524544179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(902524544179 / 500000000000) = 1/(500000000000 / 902524544179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9411 : Bounds (590587787 / 1000000000) (147646947 / 250000000) (Real.log (902524544179 / 500000000000)) := by
  have h := reflection_log_9411_neg
  have he : Real.log (902524544179 / 500000000000) = -Real.log (500000000000 / 902524544179) := by
    rw [show ((902524544179 / 500000000000) : ℝ) = ((500000000000 / 902524544179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9412_neg : (14791943 / 25000000) ≤ -Real.log (50000000000 / 90350877193) ∧
    -Real.log (50000000000 / 90350877193) ≤ (591677721 / 1000000000) := by
  have h := checkLog_sound (w := (40350877193 / 140350877193)) (n := 12)
    (lo := (14791943 / 25000000)) (hi := (591677721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90350877193 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90350877193 / 50000000000) = 1/(50000000000 / 90350877193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9412 : Bounds (14791943 / 25000000) (591677721 / 1000000000) (Real.log (90350877193 / 50000000000)) := by
  have h := reflection_log_9412_neg
  have he : Real.log (90350877193 / 50000000000) = -Real.log (50000000000 / 90350877193) := by
    rw [show ((90350877193 / 50000000000) : ℝ) = ((50000000000 / 90350877193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9413_neg : (253090627 / 1000000000) ≤ -Real.log (125 / 161) ∧
    -Real.log (125 / 161) ≤ (63272657 / 250000000) := by
  have h := checkLog_sound (w := (18 / 143)) (n := 12)
    (lo := (253090627 / 1000000000)) (hi := (63272657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161 / 125) = 1/(125 / 161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9413 : Bounds (253090627 / 1000000000) (63272657 / 250000000) (Real.log (161 / 125)) := by
  have h := reflection_log_9413_neg
  have he : Real.log (161 / 125) = -Real.log (125 / 161) := by
    rw [show ((161 / 125) : ℝ) = ((125 / 161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9414_neg : (339677367 / 1000000000) ≤ -Real.log (89 / 125) ∧
    -Real.log (89 / 125) ≤ (42459671 / 125000000) := by
  have h := checkLog_sound (w := (18 / 107)) (n := 12)
    (lo := (339677367 / 1000000000)) (hi := (42459671 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 89) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 89) = 1/(89 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9414 : Bounds (-42459671 / 125000000) (-339677367 / 1000000000) (Real.log (89 / 125)) := by
  have h := reflection_log_9414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9415_neg : (143979 / 500000000) ≤ -Real.log (31250 / 31259) ∧
    -Real.log (31250 / 31259) ≤ (287959 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 62509)) (n := 12)
    (lo := (143979 / 500000000)) (hi := (287959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31259 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31259 / 31250) = 1/(31250 / 31259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9415 : Bounds (143979 / 500000000) (287959 / 1000000000) (Real.log (31259 / 31250)) := by
  have h := reflection_log_9415_neg
  have he : Real.log (31259 / 31250) = -Real.log (31250 / 31259) := by
    rw [show ((31259 / 31250) : ℝ) = ((31250 / 31259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9416_neg : (288041 / 1000000000) ≤ -Real.log (31241 / 31250) ∧
    -Real.log (31241 / 31250) ≤ (144021 / 500000000) := by
  have h := checkLog_sound (w := (9 / 62491)) (n := 12)
    (lo := (288041 / 1000000000)) (hi := (144021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31241) = 1/(31241 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9416 : Bounds (-144021 / 500000000) (-288041 / 1000000000) (Real.log (31241 / 31250)) := by
  have h := reflection_log_9416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9417_neg : (136106573 / 1000000000) ≤ -Real.log (250000 / 286451) ∧
    -Real.log (250000 / 286451) ≤ (68053287 / 500000000) := by
  have h := checkLog_sound (w := (36451 / 536451)) (n := 12)
    (lo := (136106573 / 1000000000)) (hi := (68053287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286451 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286451 / 250000) = 1/(250000 / 286451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9417 : Bounds (136106573 / 1000000000) (68053287 / 500000000) (Real.log (286451 / 250000)) := by
  have h := reflection_log_9417_neg
  have he : Real.log (286451 / 250000) = -Real.log (250000 / 286451) := by
    rw [show ((286451 / 250000) : ℝ) = ((250000 / 286451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9418_neg : (157594603 / 1000000000) ≤ -Real.log (213549 / 250000) ∧
    -Real.log (213549 / 250000) ≤ (39398651 / 250000000) := by
  have h := checkLog_sound (w := (36451 / 463549)) (n := 12)
    (lo := (157594603 / 1000000000)) (hi := (39398651 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 213549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 213549) = 1/(213549 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9418 : Bounds (-39398651 / 250000000) (-157594603 / 1000000000) (Real.log (213549 / 250000)) := by
  have h := reflection_log_9418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9419_neg : (136582981 / 1000000000) ≤ -Real.log (20000 / 22927) ∧
    -Real.log (20000 / 22927) ≤ (68291491 / 500000000) := by
  have h := checkLog_sound (w := (2927 / 42927)) (n := 12)
    (lo := (136582981 / 1000000000)) (hi := (68291491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22927 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22927 / 20000) = 1/(20000 / 22927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9419 : Bounds (136582981 / 1000000000) (68291491 / 500000000) (Real.log (22927 / 20000)) := by
  have h := reflection_log_9419_neg
  have he : Real.log (22927 / 20000) = -Real.log (20000 / 22927) := by
    rw [show ((22927 / 20000) : ℝ) = ((20000 / 22927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9420_neg : (31646801 / 200000000) ≤ -Real.log (17073 / 20000) ∧
    -Real.log (17073 / 20000) ≤ (79117003 / 500000000) := by
  have h := checkLog_sound (w := (2927 / 37073)) (n := 12)
    (lo := (31646801 / 200000000)) (hi := (79117003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 17073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 17073) = 1/(17073 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9420 : Bounds (-79117003 / 500000000) (-31646801 / 200000000) (Real.log (17073 / 20000)) := by
  have h := reflection_log_9420_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9421_neg : (21651023 / 1000000000) ≤ -Real.log (391432671 / 400000000) ∧
    -Real.log (391432671 / 400000000) ≤ (1353189 / 62500000) := by
  have h := checkLog_sound (w := (8567329 / 791432671)) (n := 12)
    (lo := (21651023 / 1000000000)) (hi := (1353189 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 391432671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 391432671) = 1/(391432671 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9421 : Bounds (-1353189 / 62500000) (-21651023 / 1000000000) (Real.log (391432671 / 400000000)) := by
  have h := reflection_log_9421_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9422_neg : (21488029 / 1000000000) ≤ -Real.log (61171324599 / 62500000000) ∧
    -Real.log (61171324599 / 62500000000) ≤ (2148803 / 100000000) := by
  have h := checkLog_sound (w := (1328675401 / 123671324599)) (n := 12)
    (lo := (21488029 / 1000000000)) (hi := (2148803 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61171324599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61171324599) = 1/(61171324599 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9422 : Bounds (-2148803 / 100000000) (-21488029 / 1000000000) (Real.log (61171324599 / 62500000000)) := by
  have h := reflection_log_9422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9423_neg : (293701177 / 1000000000) ≤ -Real.log (500000000000 / 670691504057) ∧
    -Real.log (500000000000 / 670691504057) ≤ (146850589 / 500000000) := by
  have h := checkLog_sound (w := (170691504057 / 1170691504057)) (n := 12)
    (lo := (293701177 / 1000000000)) (hi := (146850589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670691504057 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670691504057 / 500000000000) = 1/(500000000000 / 670691504057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9423 : Bounds (293701177 / 1000000000) (146850589 / 500000000) (Real.log (670691504057 / 500000000000)) := by
  have h := reflection_log_9423_neg
  have he : Real.log (670691504057 / 500000000000) = -Real.log (500000000000 / 670691504057) := by
    rw [show ((670691504057 / 500000000000) : ℝ) = ((500000000000 / 670691504057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9424_neg : (294816987 / 1000000000) ≤ -Real.log (62500000000 / 83930035729) ∧
    -Real.log (62500000000 / 83930035729) ≤ (73704247 / 250000000) := by
  have h := checkLog_sound (w := (21430035729 / 146430035729)) (n := 12)
    (lo := (294816987 / 1000000000)) (hi := (73704247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83930035729 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83930035729 / 62500000000) = 1/(62500000000 / 83930035729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9424 : Bounds (294816987 / 1000000000) (73704247 / 250000000) (Real.log (83930035729 / 62500000000)) := by
  have h := reflection_log_9424_neg
  have he : Real.log (83930035729 / 62500000000) = -Real.log (62500000000 / 83930035729) := by
    rw [show ((83930035729 / 62500000000) : ℝ) = ((62500000000 / 83930035729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9425_neg : (14791943 / 25000000) ≤ -Real.log (500000000000 / 903508771929) ∧
    -Real.log (500000000000 / 903508771929) ≤ (591677721 / 1000000000) := by
  have h := checkLog_sound (w := (403508771929 / 1403508771929)) (n := 12)
    (lo := (14791943 / 25000000)) (hi := (591677721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903508771929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903508771929 / 500000000000) = 1/(500000000000 / 903508771929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9425 : Bounds (14791943 / 25000000) (591677721 / 1000000000) (Real.log (903508771929 / 500000000000)) := by
  have h := reflection_log_9425_neg
  have he : Real.log (903508771929 / 500000000000) = -Real.log (500000000000 / 903508771929) := by
    rw [show ((903508771929 / 500000000000) : ℝ) = ((500000000000 / 903508771929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9426_neg : (118553599 / 200000000) ≤ -Real.log (500000000000 / 904494382023) ∧
    -Real.log (500000000000 / 904494382023) ≤ (148191999 / 250000000) := by
  have h := checkLog_sound (w := (404494382023 / 1404494382023)) (n := 12)
    (lo := (118553599 / 200000000)) (hi := (148191999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904494382023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904494382023 / 500000000000) = 1/(500000000000 / 904494382023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9426 : Bounds (118553599 / 200000000) (148191999 / 250000000) (Real.log (904494382023 / 500000000000)) := by
  have h := reflection_log_9426_neg
  have he : Real.log (904494382023 / 500000000000) = -Real.log (500000000000 / 904494382023) := by
    rw [show ((904494382023 / 500000000000) : ℝ) = ((500000000000 / 904494382023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9427_neg : (253478751 / 1000000000) ≤ -Real.log (2000 / 2577) ∧
    -Real.log (2000 / 2577) ≤ (7921211 / 31250000) := by
  have h := checkLog_sound (w := (577 / 4577)) (n := 12)
    (lo := (253478751 / 1000000000)) (hi := (7921211 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2577 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2577 / 2000) = 1/(2000 / 2577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9427 : Bounds (253478751 / 1000000000) (7921211 / 31250000) (Real.log (2577 / 2000)) := by
  have h := reflection_log_9427_neg
  have he : Real.log (2577 / 2000) = -Real.log (2000 / 2577) := by
    rw [show ((2577 / 2000) : ℝ) = ((2000 / 2577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9428_neg : (340379861 / 1000000000) ≤ -Real.log (1423 / 2000) ∧
    -Real.log (1423 / 2000) ≤ (170189931 / 500000000) := by
  have h := checkLog_sound (w := (577 / 3423)) (n := 12)
    (lo := (340379861 / 1000000000)) (hi := (170189931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1423) = 1/(1423 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9428 : Bounds (-170189931 / 500000000) (-340379861 / 1000000000) (Real.log (1423 / 2000)) := by
  have h := reflection_log_9428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9429_neg : (144229 / 500000000) ≤ -Real.log (2000000 / 2000577) ∧
    -Real.log (2000000 / 2000577) ≤ (288459 / 1000000000) := by
  have h := checkLog_sound (w := (577 / 4000577)) (n := 12)
    (lo := (144229 / 500000000)) (hi := (288459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000577 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000577 / 2000000) = 1/(2000000 / 2000577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9429 : Bounds (144229 / 500000000) (288459 / 1000000000) (Real.log (2000577 / 2000000)) := by
  have h := reflection_log_9429_neg
  have he : Real.log (2000577 / 2000000) = -Real.log (2000000 / 2000577) := by
    rw [show ((2000577 / 2000000) : ℝ) = ((2000000 / 2000577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9430_neg : (288541 / 1000000000) ≤ -Real.log (1999423 / 2000000) ∧
    -Real.log (1999423 / 2000000) ≤ (144271 / 500000000) := by
  have h := checkLog_sound (w := (577 / 3999423)) (n := 12)
    (lo := (288541 / 1000000000)) (hi := (144271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999423) = 1/(1999423 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9430 : Bounds (-144271 / 500000000) (-288541 / 1000000000) (Real.log (1999423 / 2000000)) := by
  have h := reflection_log_9430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9431_neg : (17041901 / 125000000) ≤ -Real.log (500000 / 573033) ∧
    -Real.log (500000 / 573033) ≤ (136335209 / 1000000000) := by
  have h := checkLog_sound (w := (73033 / 1073033)) (n := 12)
    (lo := (17041901 / 125000000)) (hi := (136335209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573033 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(573033 / 500000) = 1/(500000 / 573033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9431 : Bounds (17041901 / 125000000) (136335209 / 1000000000) (Real.log (573033 / 500000)) := by
  have h := reflection_log_9431_neg
  have he : Real.log (573033 / 500000) = -Real.log (500000 / 573033) := by
    rw [show ((573033 / 500000) : ℝ) = ((500000 / 573033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9432_neg : (157901371 / 1000000000) ≤ -Real.log (426967 / 500000) ∧
    -Real.log (426967 / 500000) ≤ (39475343 / 250000000) := by
  have h := checkLog_sound (w := (73033 / 926967)) (n := 12)
    (lo := (157901371 / 1000000000)) (hi := (39475343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 426967) = 1/(426967 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9432 : Bounds (-39475343 / 250000000) (-157901371 / 1000000000) (Real.log (426967 / 500000)) := by
  have h := reflection_log_9432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9433_neg : (136811507 / 1000000000) ≤ -Real.log (250000 / 286653) ∧
    -Real.log (250000 / 286653) ≤ (34202877 / 250000000) := by
  have h := checkLog_sound (w := (36653 / 536653)) (n := 12)
    (lo := (136811507 / 1000000000)) (hi := (34202877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286653 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286653 / 250000) = 1/(250000 / 286653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9433 : Bounds (136811507 / 1000000000) (34202877 / 250000000) (Real.log (286653 / 250000)) := by
  have h := reflection_log_9433_neg
  have he : Real.log (286653 / 250000) = -Real.log (250000 / 286653) := by
    rw [show ((286653 / 250000) : ℝ) = ((250000 / 286653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9434_neg : (158540969 / 1000000000) ≤ -Real.log (213347 / 250000) ∧
    -Real.log (213347 / 250000) ≤ (15854097 / 100000000) := by
  have h := checkLog_sound (w := (36653 / 463347)) (n := 12)
    (lo := (158540969 / 1000000000)) (hi := (15854097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 213347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 213347) = 1/(213347 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9434 : Bounds (-15854097 / 100000000) (-158540969 / 1000000000) (Real.log (213347 / 250000)) := by
  have h := reflection_log_9434_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9435_neg : (10864731 / 500000000) ≤ -Real.log (61156557591 / 62500000000) ∧
    -Real.log (61156557591 / 62500000000) ≤ (21729463 / 1000000000) := by
  have h := checkLog_sound (w := (1343442409 / 123656557591)) (n := 12)
    (lo := (10864731 / 500000000)) (hi := (21729463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61156557591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61156557591) = 1/(61156557591 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9435 : Bounds (-21729463 / 1000000000) (-10864731 / 500000000) (Real.log (61156557591 / 62500000000)) := by
  have h := reflection_log_9435_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9436_neg : (21566163 / 1000000000) ≤ -Real.log (244666180911 / 250000000000) ∧
    -Real.log (244666180911 / 250000000000) ≤ (5391541 / 250000000) := by
  have h := checkLog_sound (w := (5333819089 / 494666180911)) (n := 12)
    (lo := (21566163 / 1000000000)) (hi := (5391541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244666180911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244666180911) = 1/(244666180911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9436 : Bounds (-5391541 / 250000000) (-21566163 / 1000000000) (Real.log (244666180911 / 250000000000)) := by
  have h := reflection_log_9436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9437_neg : (294236579 / 1000000000) ≤ -Real.log (5000000000 / 6710506901) ∧
    -Real.log (5000000000 / 6710506901) ≤ (14711829 / 50000000) := by
  have h := checkLog_sound (w := (1710506901 / 11710506901)) (n := 12)
    (lo := (294236579 / 1000000000)) (hi := (14711829 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6710506901 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6710506901 / 5000000000) = 1/(5000000000 / 6710506901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9437 : Bounds (294236579 / 1000000000) (14711829 / 50000000) (Real.log (6710506901 / 5000000000)) := by
  have h := reflection_log_9437_neg
  have he : Real.log (6710506901 / 5000000000) = -Real.log (5000000000 / 6710506901) := by
    rw [show ((6710506901 / 5000000000) : ℝ) = ((5000000000 / 6710506901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9438_neg : (73838119 / 250000000) ≤ -Real.log (500000000000 / 671799931567) ∧
    -Real.log (500000000000 / 671799931567) ≤ (295352477 / 1000000000) := by
  have h := checkLog_sound (w := (171799931567 / 1171799931567)) (n := 12)
    (lo := (73838119 / 250000000)) (hi := (295352477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671799931567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671799931567 / 500000000000) = 1/(500000000000 / 671799931567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9438 : Bounds (73838119 / 250000000) (295352477 / 1000000000) (Real.log (671799931567 / 500000000000)) := by
  have h := reflection_log_9438_neg
  have he : Real.log (671799931567 / 500000000000) = -Real.log (500000000000 / 671799931567) := by
    rw [show ((671799931567 / 500000000000) : ℝ) = ((500000000000 / 671799931567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9439_neg : (118553599 / 200000000) ≤ -Real.log (250000000000 / 452247191011) ∧
    -Real.log (250000000000 / 452247191011) ≤ (148191999 / 250000000) := by
  have h := checkLog_sound (w := (202247191011 / 702247191011)) (n := 12)
    (lo := (118553599 / 200000000)) (hi := (148191999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((452247191011 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(452247191011 / 250000000000) = 1/(250000000000 / 452247191011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9439 : Bounds (118553599 / 200000000) (148191999 / 250000000) (Real.log (452247191011 / 250000000000)) := by
  have h := reflection_log_9439_neg
  have he : Real.log (452247191011 / 250000000000) = -Real.log (250000000000 / 452247191011) := by
    rw [show ((452247191011 / 250000000000) : ℝ) = ((250000000000 / 452247191011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9440_neg : (148464653 / 250000000) ≤ -Real.log (125000000000 / 226370344343) ∧
    -Real.log (125000000000 / 226370344343) ≤ (593858613 / 1000000000) := by
  have h := checkLog_sound (w := (101370344343 / 351370344343)) (n := 12)
    (lo := (148464653 / 250000000)) (hi := (593858613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226370344343 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226370344343 / 125000000000) = 1/(125000000000 / 226370344343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9440 : Bounds (148464653 / 250000000) (593858613 / 1000000000) (Real.log (226370344343 / 125000000000)) := by
  have h := reflection_log_9440_neg
  have he : Real.log (226370344343 / 125000000000) = -Real.log (125000000000 / 226370344343) := by
    rw [show ((226370344343 / 125000000000) : ℝ) = ((125000000000 / 226370344343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9441_neg : (253866723 / 1000000000) ≤ -Real.log (1000 / 1289) ∧
    -Real.log (1000 / 1289) ≤ (63466681 / 250000000) := by
  have h := checkLog_sound (w := (289 / 2289)) (n := 12)
    (lo := (253866723 / 1000000000)) (hi := (63466681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289 / 1000) = 1/(1000 / 1289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9441 : Bounds (253866723 / 1000000000) (63466681 / 250000000) (Real.log (1289 / 1000)) := by
  have h := reflection_log_9441_neg
  have he : Real.log (1289 / 1000) = -Real.log (1000 / 1289) := by
    rw [show ((1289 / 1000) : ℝ) = ((1000 / 1289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9442_neg : (341082849 / 1000000000) ≤ -Real.log (711 / 1000) ∧
    -Real.log (711 / 1000) ≤ (6821657 / 20000000) := by
  have h := checkLog_sound (w := (289 / 1711)) (n := 12)
    (lo := (341082849 / 1000000000)) (hi := (6821657 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 711) = 1/(711 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9442 : Bounds (-6821657 / 20000000) (-341082849 / 1000000000) (Real.log (711 / 1000)) := by
  have h := reflection_log_9442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9443_neg : (144479 / 500000000) ≤ -Real.log (1000000 / 1000289) ∧
    -Real.log (1000000 / 1000289) ≤ (288959 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 2000289)) (n := 12)
    (lo := (144479 / 500000000)) (hi := (288959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000289 / 1000000) = 1/(1000000 / 1000289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9443 : Bounds (144479 / 500000000) (288959 / 1000000000) (Real.log (1000289 / 1000000)) := by
  have h := reflection_log_9443_neg
  have he : Real.log (1000289 / 1000000) = -Real.log (1000000 / 1000289) := by
    rw [show ((1000289 / 1000000) : ℝ) = ((1000000 / 1000289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9444_neg : (289041 / 1000000000) ≤ -Real.log (999711 / 1000000) ∧
    -Real.log (999711 / 1000000) ≤ (144521 / 500000000) := by
  have h := checkLog_sound (w := (289 / 1999711)) (n := 12)
    (lo := (289041 / 1000000000)) (hi := (144521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999711) = 1/(999711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9444 : Bounds (-144521 / 500000000) (-289041 / 1000000000) (Real.log (999711 / 1000000)) := by
  have h := reflection_log_9444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9445_neg : (136562917 / 1000000000) ≤ -Real.log (1000000 / 1146327) ∧
    -Real.log (1000000 / 1146327) ≤ (68281459 / 500000000) := by
  have h := checkLog_sound (w := (146327 / 2146327)) (n := 12)
    (lo := (136562917 / 1000000000)) (hi := (68281459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1146327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1146327 / 1000000) = 1/(1000000 / 1146327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9445 : Bounds (136562917 / 1000000000) (68281459 / 500000000) (Real.log (1146327 / 1000000)) := by
  have h := reflection_log_9445_neg
  have he : Real.log (1146327 / 1000000) = -Real.log (1000000 / 1146327) := by
    rw [show ((1146327 / 1000000) : ℝ) = ((1000000 / 1146327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9446_neg : (79103531 / 500000000) ≤ -Real.log (853673 / 1000000) ∧
    -Real.log (853673 / 1000000) ≤ (158207063 / 1000000000) := by
  have h := checkLog_sound (w := (146327 / 1853673)) (n := 12)
    (lo := (79103531 / 500000000)) (hi := (158207063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 853673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 853673) = 1/(853673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9446 : Bounds (-158207063 / 1000000000) (-79103531 / 500000000) (Real.log (853673 / 1000000)) := by
  have h := reflection_log_9446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9447_neg : (6851999 / 50000000) ≤ -Real.log (500000 / 573437) ∧
    -Real.log (500000 / 573437) ≤ (137039981 / 1000000000) := by
  have h := checkLog_sound (w := (73437 / 1073437)) (n := 12)
    (lo := (6851999 / 50000000)) (hi := (137039981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573437 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(573437 / 500000) = 1/(500000 / 573437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9447 : Bounds (6851999 / 50000000) (137039981 / 1000000000) (Real.log (573437 / 500000)) := by
  have h := reflection_log_9447_neg
  have he : Real.log (573437 / 500000) = -Real.log (500000 / 573437) := by
    rw [show ((573437 / 500000) : ℝ) = ((500000 / 573437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9448_neg : (39712007 / 250000000) ≤ -Real.log (426563 / 500000) ∧
    -Real.log (426563 / 500000) ≤ (158848029 / 1000000000) := by
  have h := checkLog_sound (w := (73437 / 926563)) (n := 12)
    (lo := (39712007 / 250000000)) (hi := (158848029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 426563) = 1/(426563 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9448 : Bounds (-158848029 / 1000000000) (-39712007 / 250000000) (Real.log (426563 / 500000)) := by
  have h := reflection_log_9448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9449_neg : (1363003 / 62500000) ≤ -Real.log (244607007031 / 250000000000) ∧
    -Real.log (244607007031 / 250000000000) ≤ (21808049 / 1000000000) := by
  have h := checkLog_sound (w := (5392992969 / 494607007031)) (n := 12)
    (lo := (1363003 / 62500000)) (hi := (21808049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244607007031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244607007031) = 1/(244607007031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9449 : Bounds (-21808049 / 1000000000) (-1363003 / 62500000) (Real.log (244607007031 / 250000000000)) := by
  have h := reflection_log_9449_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9450_neg : (1352759 / 62500000) ≤ -Real.log (978588409071 / 1000000000000) ∧
    -Real.log (978588409071 / 1000000000000) ≤ (4328829 / 200000000) := by
  have h := checkLog_sound (w := (21411590929 / 1978588409071)) (n := 12)
    (lo := (1352759 / 62500000)) (hi := (4328829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978588409071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978588409071) = 1/(978588409071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9450 : Bounds (-4328829 / 200000000) (-1352759 / 62500000) (Real.log (978588409071 / 1000000000000)) := by
  have h := reflection_log_9450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9451_neg : (14738499 / 50000000) ≤ -Real.log (500000000000 / 671408724417) ∧
    -Real.log (500000000000 / 671408724417) ≤ (294769981 / 1000000000) := by
  have h := checkLog_sound (w := (171408724417 / 1171408724417)) (n := 12)
    (lo := (14738499 / 50000000)) (hi := (294769981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671408724417 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671408724417 / 500000000000) = 1/(500000000000 / 671408724417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9451 : Bounds (14738499 / 50000000) (294769981 / 1000000000) (Real.log (671408724417 / 500000000000)) := by
  have h := reflection_log_9451_neg
  have he : Real.log (671408724417 / 500000000000) = -Real.log (500000000000 / 671408724417) := by
    rw [show ((671408724417 / 500000000000) : ℝ) = ((500000000000 / 671408724417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9452_neg : (36986001 / 125000000) ≤ -Real.log (500000000000 / 672159798201) ∧
    -Real.log (500000000000 / 672159798201) ≤ (295888009 / 1000000000) := by
  have h := checkLog_sound (w := (172159798201 / 1172159798201)) (n := 12)
    (lo := (36986001 / 125000000)) (hi := (295888009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672159798201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(672159798201 / 500000000000) = 1/(500000000000 / 672159798201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9452 : Bounds (36986001 / 125000000) (295888009 / 1000000000) (Real.log (672159798201 / 500000000000)) := by
  have h := reflection_log_9452_neg
  have he : Real.log (672159798201 / 500000000000) = -Real.log (500000000000 / 672159798201) := by
    rw [show ((672159798201 / 500000000000) : ℝ) = ((500000000000 / 672159798201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9453_neg : (148464653 / 250000000) ≤ -Real.log (500000000000 / 905481377371) ∧
    -Real.log (500000000000 / 905481377371) ≤ (593858613 / 1000000000) := by
  have h := checkLog_sound (w := (405481377371 / 1405481377371)) (n := 12)
    (lo := (148464653 / 250000000)) (hi := (593858613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((905481377371 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(905481377371 / 500000000000) = 1/(500000000000 / 905481377371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9453 : Bounds (148464653 / 250000000) (593858613 / 1000000000) (Real.log (905481377371 / 500000000000)) := by
  have h := reflection_log_9453_neg
  have he : Real.log (905481377371 / 500000000000) = -Real.log (500000000000 / 905481377371) := by
    rw [show ((905481377371 / 500000000000) : ℝ) = ((500000000000 / 905481377371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9454_neg : (594949573 / 1000000000) ≤ -Real.log (500000000000 / 906469760901) ∧
    -Real.log (500000000000 / 906469760901) ≤ (297474787 / 500000000) := by
  have h := checkLog_sound (w := (406469760901 / 1406469760901)) (n := 12)
    (lo := (594949573 / 1000000000)) (hi := (297474787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((906469760901 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(906469760901 / 500000000000) = 1/(500000000000 / 906469760901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9454 : Bounds (594949573 / 1000000000) (297474787 / 500000000) (Real.log (906469760901 / 500000000000)) := by
  have h := reflection_log_9454_neg
  have he : Real.log (906469760901 / 500000000000) = -Real.log (500000000000 / 906469760901) := by
    rw [show ((906469760901 / 500000000000) : ℝ) = ((500000000000 / 906469760901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9455_neg : (127127273 / 500000000) ≤ -Real.log (2000 / 2579) ∧
    -Real.log (2000 / 2579) ≤ (254254547 / 1000000000) := by
  have h := checkLog_sound (w := (579 / 4579)) (n := 12)
    (lo := (127127273 / 500000000)) (hi := (254254547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2579 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2579 / 2000) = 1/(2000 / 2579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9455 : Bounds (127127273 / 500000000) (254254547 / 1000000000) (Real.log (2579 / 2000)) := by
  have h := reflection_log_9455_neg
  have he : Real.log (2579 / 2000) = -Real.log (2000 / 2579) := by
    rw [show ((2579 / 2000) : ℝ) = ((2000 / 2579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9456_neg : (341786331 / 1000000000) ≤ -Real.log (1421 / 2000) ∧
    -Real.log (1421 / 2000) ≤ (85446583 / 250000000) := by
  have h := checkLog_sound (w := (579 / 3421)) (n := 12)
    (lo := (341786331 / 1000000000)) (hi := (85446583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1421) = 1/(1421 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9456 : Bounds (-85446583 / 250000000) (-341786331 / 1000000000) (Real.log (1421 / 2000)) := by
  have h := reflection_log_9456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9457_neg : (144729 / 500000000) ≤ -Real.log (2000000 / 2000579) ∧
    -Real.log (2000000 / 2000579) ≤ (289459 / 1000000000) := by
  have h := checkLog_sound (w := (579 / 4000579)) (n := 12)
    (lo := (144729 / 500000000)) (hi := (289459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000579 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000579 / 2000000) = 1/(2000000 / 2000579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9457 : Bounds (144729 / 500000000) (289459 / 1000000000) (Real.log (2000579 / 2000000)) := by
  have h := reflection_log_9457_neg
  have he : Real.log (2000579 / 2000000) = -Real.log (2000000 / 2000579) := by
    rw [show ((2000579 / 2000000) : ℝ) = ((2000000 / 2000579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9458_neg : (289541 / 1000000000) ≤ -Real.log (1999421 / 2000000) ∧
    -Real.log (1999421 / 2000000) ≤ (144771 / 500000000) := by
  have h := checkLog_sound (w := (579 / 3999421)) (n := 12)
    (lo := (289541 / 1000000000)) (hi := (144771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999421) = 1/(1999421 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9458 : Bounds (-144771 / 500000000) (-289541 / 1000000000) (Real.log (1999421 / 2000000)) := by
  have h := reflection_log_9458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9459_neg : (136791447 / 1000000000) ≤ -Real.log (1000000 / 1146589) ∧
    -Real.log (1000000 / 1146589) ≤ (17098931 / 125000000) := by
  have h := checkLog_sound (w := (146589 / 2146589)) (n := 12)
    (lo := (136791447 / 1000000000)) (hi := (17098931 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1146589 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1146589 / 1000000) = 1/(1000000 / 1146589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9459 : Bounds (136791447 / 1000000000) (17098931 / 125000000) (Real.log (1146589 / 1000000)) := by
  have h := reflection_log_9459_neg
  have he : Real.log (1146589 / 1000000) = -Real.log (1000000 / 1146589) := by
    rw [show ((1146589 / 1000000) : ℝ) = ((1000000 / 1146589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9460_neg : (79257009 / 500000000) ≤ -Real.log (853411 / 1000000) ∧
    -Real.log (853411 / 1000000) ≤ (158514019 / 1000000000) := by
  have h := checkLog_sound (w := (146589 / 1853411)) (n := 12)
    (lo := (79257009 / 500000000)) (hi := (158514019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 853411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 853411) = 1/(853411 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9460 : Bounds (-158514019 / 1000000000) (-79257009 / 500000000) (Real.log (853411 / 1000000)) := by
  have h := reflection_log_9460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9461_neg : (137268401 / 1000000000) ≤ -Real.log (15625 / 17924) ∧
    -Real.log (15625 / 17924) ≤ (68634201 / 500000000) := by
  have h := checkLog_sound (w := (2299 / 33549)) (n := 12)
    (lo := (137268401 / 1000000000)) (hi := (68634201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17924 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17924 / 15625) = 1/(15625 / 17924) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9461 : Bounds (137268401 / 1000000000) (68634201 / 500000000) (Real.log (17924 / 15625)) := by
  have h := reflection_log_9461_neg
  have he : Real.log (17924 / 15625) = -Real.log (15625 / 17924) := by
    rw [show ((17924 / 15625) : ℝ) = ((15625 / 17924) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9462_neg : (159155181 / 1000000000) ≤ -Real.log (13326 / 15625) ∧
    -Real.log (13326 / 15625) ≤ (79577591 / 500000000) := by
  have h := checkLog_sound (w := (2299 / 28951)) (n := 12)
    (lo := (159155181 / 1000000000)) (hi := (79577591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13326) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13326) = 1/(13326 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9462 : Bounds (-79577591 / 500000000) (-159155181 / 1000000000) (Real.log (13326 / 15625)) := by
  have h := reflection_log_9462_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9463_neg : (1094339 / 50000000) ≤ -Real.log (238855224 / 244140625) ∧
    -Real.log (238855224 / 244140625) ≤ (21886781 / 1000000000) := by
  have h := checkLog_sound (w := (5285401 / 482995849)) (n := 12)
    (lo := (1094339 / 50000000)) (hi := (21886781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 238855224) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 238855224) = 1/(238855224 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9463 : Bounds (-21886781 / 1000000000) (-1094339 / 50000000) (Real.log (238855224 / 244140625)) := by
  have h := reflection_log_9463_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9464_neg : (2172257 / 100000000) ≤ -Real.log (978511665079 / 1000000000000) ∧
    -Real.log (978511665079 / 1000000000000) ≤ (21722571 / 1000000000) := by
  have h := checkLog_sound (w := (21488334921 / 1978511665079)) (n := 12)
    (lo := (2172257 / 100000000)) (hi := (21722571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978511665079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978511665079) = 1/(978511665079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9464 : Bounds (-21722571 / 1000000000) (-2172257 / 100000000) (Real.log (978511665079 / 1000000000000)) := by
  have h := reflection_log_9464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9465_neg : (147652733 / 500000000) ≤ -Real.log (500000000000 / 671768350771) ∧
    -Real.log (500000000000 / 671768350771) ≤ (295305467 / 1000000000) := by
  have h := checkLog_sound (w := (171768350771 / 1171768350771)) (n := 12)
    (lo := (147652733 / 500000000)) (hi := (295305467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671768350771 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671768350771 / 500000000000) = 1/(500000000000 / 671768350771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9465 : Bounds (147652733 / 500000000) (295305467 / 1000000000) (Real.log (671768350771 / 500000000000)) := by
  have h := reflection_log_9465_neg
  have he : Real.log (671768350771 / 500000000000) = -Real.log (500000000000 / 671768350771) := by
    rw [show ((671768350771 / 500000000000) : ℝ) = ((500000000000 / 671768350771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9466_neg : (148211791 / 500000000) ≤ -Real.log (250000000000 / 336259942969) ∧
    -Real.log (250000000000 / 336259942969) ≤ (296423583 / 1000000000) := by
  have h := checkLog_sound (w := (86259942969 / 586259942969)) (n := 12)
    (lo := (148211791 / 500000000)) (hi := (296423583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336259942969 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336259942969 / 250000000000) = 1/(250000000000 / 336259942969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9466 : Bounds (148211791 / 500000000) (296423583 / 1000000000) (Real.log (336259942969 / 250000000000)) := by
  have h := reflection_log_9466_neg
  have he : Real.log (336259942969 / 250000000000) = -Real.log (250000000000 / 336259942969) := by
    rw [show ((336259942969 / 250000000000) : ℝ) = ((250000000000 / 336259942969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9467_neg : (594949573 / 1000000000) ≤ -Real.log (5000000000 / 9064697609) ∧
    -Real.log (5000000000 / 9064697609) ≤ (297474787 / 500000000) := by
  have h := checkLog_sound (w := (4064697609 / 14064697609)) (n := 12)
    (lo := (594949573 / 1000000000)) (hi := (297474787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9064697609 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9064697609 / 5000000000) = 1/(5000000000 / 9064697609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9467 : Bounds (594949573 / 1000000000) (297474787 / 500000000) (Real.log (9064697609 / 5000000000)) := by
  have h := reflection_log_9467_neg
  have he : Real.log (9064697609 / 5000000000) = -Real.log (5000000000 / 9064697609) := by
    rw [show ((9064697609 / 5000000000) : ℝ) = ((5000000000 / 9064697609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9468_neg : (596040877 / 1000000000) ≤ -Real.log (500000000000 / 907459535539) ∧
    -Real.log (500000000000 / 907459535539) ≤ (298020439 / 500000000) := by
  have h := checkLog_sound (w := (407459535539 / 1407459535539)) (n := 12)
    (lo := (596040877 / 1000000000)) (hi := (298020439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((907459535539 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(907459535539 / 500000000000) = 1/(500000000000 / 907459535539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9468 : Bounds (596040877 / 1000000000) (298020439 / 500000000) (Real.log (907459535539 / 500000000000)) := by
  have h := reflection_log_9468_neg
  have he : Real.log (907459535539 / 500000000000) = -Real.log (500000000000 / 907459535539) := by
    rw [show ((907459535539 / 500000000000) : ℝ) = ((500000000000 / 907459535539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9469_neg : (127321109 / 500000000) ≤ -Real.log (100 / 129) ∧
    -Real.log (100 / 129) ≤ (254642219 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 229)) (n := 12)
    (lo := (127321109 / 500000000)) (hi := (254642219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(129 / 100) = 1/(100 / 129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9469 : Bounds (127321109 / 500000000) (254642219 / 1000000000) (Real.log (129 / 100)) := by
  have h := reflection_log_9469_neg
  have he : Real.log (129 / 100) = -Real.log (100 / 129) := by
    rw [show ((129 / 100) : ℝ) = ((100 / 129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9470_neg : (85622577 / 250000000) ≤ -Real.log (71 / 100) ∧
    -Real.log (71 / 100) ≤ (342490309 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 171)) (n := 12)
    (lo := (85622577 / 250000000)) (hi := (342490309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 71) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 71) = 1/(71 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9470 : Bounds (-342490309 / 1000000000) (-85622577 / 250000000) (Real.log (71 / 100)) := by
  have h := reflection_log_9470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9471_neg : (289957 / 1000000000) ≤ -Real.log (100000 / 100029) ∧
    -Real.log (100000 / 100029) ≤ (144979 / 500000000) := by
  have h := checkLog_sound (w := (29 / 200029)) (n := 12)
    (lo := (289957 / 1000000000)) (hi := (144979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100029 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100029 / 100000) = 1/(100000 / 100029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9471 : Bounds (289957 / 1000000000) (144979 / 500000000) (Real.log (100029 / 100000)) := by
  have h := reflection_log_9471_neg
  have he : Real.log (100029 / 100000) = -Real.log (100000 / 100029) := by
    rw [show ((100029 / 100000) : ℝ) = ((100000 / 100029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


