-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0048__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0048__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:28:21.198441+00:00
-- url     : https://prove2.me/theorems/77913099-61c9-4417-b794-c5dec933ecc5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0050)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0050)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0050) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0048 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0049, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0050).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0048__3_q01

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0050 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3200_neg : (3788733 / 500000000) ≤ -Real.log (62028198159 / 62500000000) ∧
    -Real.log (62028198159 / 62500000000) ≤ (7577467 / 1000000000) := by
  have h := checkLog_sound (w := (471801841 / 124528198159)) (n := 12)
    (lo := (3788733 / 500000000)) (hi := (7577467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62028198159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62028198159) = 1/(62028198159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3200 : Bounds (-7577467 / 1000000000) (-3788733 / 500000000) (Real.log (62028198159 / 62500000000)) := by
  have h := reflection_log_3200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3201_neg : (174207239 / 1000000000) ≤ -Real.log (10000000000 / 11903022179) ∧
    -Real.log (10000000000 / 11903022179) ≤ (4355181 / 25000000) := by
  have h := checkLog_sound (w := (1903022179 / 21903022179)) (n := 12)
    (lo := (174207239 / 1000000000)) (hi := (4355181 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11903022179 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11903022179 / 10000000000) = 1/(10000000000 / 11903022179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3201 : Bounds (174207239 / 1000000000) (4355181 / 25000000) (Real.log (11903022179 / 10000000000)) := by
  have h := reflection_log_3201_neg
  have he : Real.log (11903022179 / 10000000000) = -Real.log (10000000000 / 11903022179) := by
    rw [show ((11903022179 / 10000000000) : ℝ) = ((10000000000 / 11903022179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3202_neg : (34931731 / 200000000) ≤ -Real.log (100000000000 / 119083966121) ∧
    -Real.log (100000000000 / 119083966121) ≤ (5458083 / 31250000) := by
  have h := checkLog_sound (w := (19083966121 / 219083966121)) (n := 12)
    (lo := (34931731 / 200000000)) (hi := (5458083 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119083966121 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119083966121 / 100000000000) = 1/(100000000000 / 119083966121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3202 : Bounds (34931731 / 200000000) (5458083 / 31250000) (Real.log (119083966121 / 100000000000)) := by
  have h := reflection_log_3202_neg
  have he : Real.log (119083966121 / 100000000000) = -Real.log (100000000000 / 119083966121) := by
    rw [show ((119083966121 / 100000000000) : ℝ) = ((100000000000 / 119083966121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3203_neg : (349515153 / 1000000000) ≤ -Real.log (100000000000 / 141837968561) ∧
    -Real.log (100000000000 / 141837968561) ≤ (174757577 / 500000000) := by
  have h := checkLog_sound (w := (41837968561 / 241837968561)) (n := 12)
    (lo := (349515153 / 1000000000)) (hi := (174757577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141837968561 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141837968561 / 100000000000) = 1/(100000000000 / 141837968561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3203 : Bounds (349515153 / 1000000000) (174757577 / 500000000) (Real.log (141837968561 / 100000000000)) := by
  have h := reflection_log_3203_neg
  have he : Real.log (141837968561 / 100000000000) = -Real.log (100000000000 / 141837968561) := by
    rw [show ((141837968561 / 100000000000) : ℝ) = ((100000000000 / 141837968561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3204_neg : (349721327 / 1000000000) ≤ -Real.log (1953125000 / 2770844041) ∧
    -Real.log (1953125000 / 2770844041) ≤ (21857583 / 62500000) := by
  have h := checkLog_sound (w := (817719041 / 4723969041)) (n := 12)
    (lo := (349721327 / 1000000000)) (hi := (21857583 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2770844041 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2770844041 / 1953125000) = 1/(1953125000 / 2770844041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3204 : Bounds (349721327 / 1000000000) (21857583 / 62500000) (Real.log (2770844041 / 1953125000)) := by
  have h := reflection_log_3204_neg
  have he : Real.log (2770844041 / 1953125000) = -Real.log (1953125000 / 2770844041) := by
    rw [show ((2770844041 / 1953125000) : ℝ) = ((1953125000 / 2770844041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3205_neg : (79867529 / 500000000) ≤ -Real.log (2500 / 2933) ∧
    -Real.log (2500 / 2933) ≤ (159735059 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 5433)) (n := 12)
    (lo := (79867529 / 500000000)) (hi := (159735059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2933 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2933 / 2500) = 1/(2500 / 2933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3205 : Bounds (79867529 / 500000000) (159735059 / 1000000000) (Real.log (2933 / 2500)) := by
  have h := reflection_log_3205_neg
  have he : Real.log (2933 / 2500) = -Real.log (2500 / 2933) := by
    rw [show ((2933 / 2500) : ℝ) = ((2500 / 2933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3206_neg : (190192451 / 1000000000) ≤ -Real.log (2067 / 2500) ∧
    -Real.log (2067 / 2500) ≤ (47548113 / 250000000) := by
  have h := checkLog_sound (w := (433 / 4567)) (n := 12)
    (lo := (190192451 / 1000000000)) (hi := (47548113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2067) = 1/(2067 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3206 : Bounds (-47548113 / 250000000) (-190192451 / 1000000000) (Real.log (2067 / 2500)) := by
  have h := reflection_log_3206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3207_neg : (34637 / 200000000) ≤ -Real.log (2500000 / 2500433) ∧
    -Real.log (2500000 / 2500433) ≤ (86593 / 500000000) := by
  have h := checkLog_sound (w := (433 / 5000433)) (n := 12)
    (lo := (34637 / 200000000)) (hi := (86593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500433 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500433 / 2500000) = 1/(2500000 / 2500433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3207 : Bounds (34637 / 200000000) (86593 / 500000000) (Real.log (2500433 / 2500000)) := by
  have h := reflection_log_3207_neg
  have he : Real.log (2500433 / 2500000) = -Real.log (2500000 / 2500433) := by
    rw [show ((2500433 / 2500000) : ℝ) = ((2500000 / 2500433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3208_neg : (34643 / 200000000) ≤ -Real.log (2499567 / 2500000) ∧
    -Real.log (2499567 / 2500000) ≤ (5413 / 31250000) := by
  have h := checkLog_sound (w := (433 / 4999567)) (n := 12)
    (lo := (34643 / 200000000)) (hi := (5413 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499567) = 1/(2499567 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3208 : Bounds (-5413 / 31250000) (-34643 / 200000000) (Real.log (2499567 / 2500000)) := by
  have h := reflection_log_3208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3209_neg : (5210113 / 62500000) ≤ -Real.log (200000 / 217387) ∧
    -Real.log (200000 / 217387) ≤ (83361809 / 1000000000) := by
  have h := checkLog_sound (w := (17387 / 417387)) (n := 12)
    (lo := (5210113 / 62500000)) (hi := (83361809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217387 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217387 / 200000) = 1/(200000 / 217387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3209 : Bounds (5210113 / 62500000) (83361809 / 1000000000) (Real.log (217387 / 200000)) := by
  have h := reflection_log_3209_neg
  have he : Real.log (217387 / 200000) = -Real.log (200000 / 217387) := by
    rw [show ((217387 / 200000) : ℝ) = ((200000 / 217387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3210_neg : (90948207 / 1000000000) ≤ -Real.log (182613 / 200000) ∧
    -Real.log (182613 / 200000) ≤ (5684263 / 62500000) := by
  have h := checkLog_sound (w := (17387 / 382613)) (n := 12)
    (lo := (90948207 / 1000000000)) (hi := (5684263 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182613) = 1/(182613 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3210 : Bounds (-5684263 / 62500000) (-90948207 / 1000000000) (Real.log (182613 / 200000)) := by
  have h := reflection_log_3210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3211_neg : (83567871 / 1000000000) ≤ -Real.log (1000000 / 1087159) ∧
    -Real.log (1000000 / 1087159) ≤ (326437 / 3906250) := by
  have h := checkLog_sound (w := (87159 / 2087159)) (n := 12)
    (lo := (83567871 / 1000000000)) (hi := (326437 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087159 / 1000000) = 1/(1000000 / 1087159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3211 : Bounds (83567871 / 1000000000) (326437 / 3906250) (Real.log (1087159 / 1000000)) := by
  have h := reflection_log_3211_neg
  have he : Real.log (1087159 / 1000000) = -Real.log (1000000 / 1087159) := by
    rw [show ((1087159 / 1000000) : ℝ) = ((1000000 / 1087159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3212_neg : (22798391 / 250000000) ≤ -Real.log (912841 / 1000000) ∧
    -Real.log (912841 / 1000000) ≤ (18238713 / 200000000) := by
  have h := checkLog_sound (w := (87159 / 1912841)) (n := 12)
    (lo := (22798391 / 250000000)) (hi := (18238713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912841) = 1/(912841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3212 : Bounds (-18238713 / 200000000) (-22798391 / 250000000) (Real.log (912841 / 1000000)) := by
  have h := reflection_log_3212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3213_neg : (7625693 / 1000000000) ≤ -Real.log (992403308719 / 1000000000000) ∧
    -Real.log (992403308719 / 1000000000000) ≤ (3812847 / 500000000) := by
  have h := checkLog_sound (w := (7596691281 / 1992403308719)) (n := 12)
    (lo := (7625693 / 1000000000)) (hi := (3812847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992403308719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992403308719) = 1/(992403308719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3213 : Bounds (-3812847 / 500000000) (-7625693 / 1000000000) (Real.log (992403308719 / 1000000000000)) := by
  have h := reflection_log_3213_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3214_neg : (3793199 / 500000000) ≤ -Real.log (39697692231 / 40000000000) ∧
    -Real.log (39697692231 / 40000000000) ≤ (7586399 / 1000000000) := by
  have h := checkLog_sound (w := (302307769 / 79697692231)) (n := 12)
    (lo := (3793199 / 500000000)) (hi := (7586399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39697692231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39697692231) = 1/(39697692231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3214 : Bounds (-7586399 / 1000000000) (-3793199 / 500000000) (Real.log (39697692231 / 40000000000)) := by
  have h := reflection_log_3214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3215_neg : (34862003 / 200000000) ≤ -Real.log (3125000000 / 3720076747) ∧
    -Real.log (3125000000 / 3720076747) ≤ (1361797 / 7812500) := by
  have h := checkLog_sound (w := (595076747 / 6845076747)) (n := 12)
    (lo := (34862003 / 200000000)) (hi := (1361797 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3720076747 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3720076747 / 3125000000) = 1/(3125000000 / 3720076747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3215 : Bounds (34862003 / 200000000) (1361797 / 7812500) (Real.log (3720076747 / 3125000000)) := by
  have h := reflection_log_3215_neg
  have he : Real.log (3720076747 / 3125000000) = -Real.log (3125000000 / 3720076747) := by
    rw [show ((3720076747 / 3125000000) : ℝ) = ((3125000000 / 3720076747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3216_neg : (43690359 / 250000000) ≤ -Real.log (500000000000 / 595481031199) ∧
    -Real.log (500000000000 / 595481031199) ≤ (174761437 / 1000000000) := by
  have h := checkLog_sound (w := (95481031199 / 1095481031199)) (n := 12)
    (lo := (43690359 / 250000000)) (hi := (174761437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595481031199 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595481031199 / 500000000000) = 1/(500000000000 / 595481031199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3216 : Bounds (43690359 / 250000000) (174761437 / 1000000000) (Real.log (595481031199 / 500000000000)) := by
  have h := reflection_log_3216_neg
  have he : Real.log (595481031199 / 500000000000) = -Real.log (500000000000 / 595481031199) := by
    rw [show ((595481031199 / 500000000000) : ℝ) = ((500000000000 / 595481031199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3217_neg : (349721327 / 1000000000) ≤ -Real.log (100000000000 / 141867214899) ∧
    -Real.log (100000000000 / 141867214899) ≤ (21857583 / 62500000) := by
  have h := checkLog_sound (w := (41867214899 / 241867214899)) (n := 12)
    (lo := (349721327 / 1000000000)) (hi := (21857583 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141867214899 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141867214899 / 100000000000) = 1/(100000000000 / 141867214899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3217 : Bounds (349721327 / 1000000000) (21857583 / 62500000) (Real.log (141867214899 / 100000000000)) := by
  have h := reflection_log_3217_neg
  have he : Real.log (141867214899 / 100000000000) = -Real.log (100000000000 / 141867214899) := by
    rw [show ((141867214899 / 100000000000) : ℝ) = ((100000000000 / 141867214899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3218_neg : (349927509 / 1000000000) ≤ -Real.log (250000000000 / 354741170779) ∧
    -Real.log (250000000000 / 354741170779) ≤ (34992751 / 100000000) := by
  have h := checkLog_sound (w := (104741170779 / 604741170779)) (n := 12)
    (lo := (349927509 / 1000000000)) (hi := (34992751 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354741170779 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354741170779 / 250000000000) = 1/(250000000000 / 354741170779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3218 : Bounds (349927509 / 1000000000) (34992751 / 100000000) (Real.log (354741170779 / 250000000000)) := by
  have h := reflection_log_3218_neg
  have he : Real.log (354741170779 / 250000000000) = -Real.log (250000000000 / 354741170779) := by
    rw [show ((354741170779 / 250000000000) : ℝ) = ((250000000000 / 354741170779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3219_neg : (159820291 / 1000000000) ≤ -Real.log (10000 / 11733) ∧
    -Real.log (10000 / 11733) ≤ (39955073 / 250000000) := by
  have h := checkLog_sound (w := (1733 / 21733)) (n := 12)
    (lo := (159820291 / 1000000000)) (hi := (39955073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11733 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11733 / 10000) = 1/(10000 / 11733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3219 : Bounds (159820291 / 1000000000) (39955073 / 250000000) (Real.log (11733 / 10000)) := by
  have h := reflection_log_3219_neg
  have he : Real.log (11733 / 10000) = -Real.log (10000 / 11733) := by
    rw [show ((11733 / 10000) : ℝ) = ((10000 / 11733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3220_neg : (95156703 / 500000000) ≤ -Real.log (8267 / 10000) ∧
    -Real.log (8267 / 10000) ≤ (190313407 / 1000000000) := by
  have h := checkLog_sound (w := (1733 / 18267)) (n := 12)
    (lo := (95156703 / 500000000)) (hi := (190313407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8267) = 1/(8267 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3220 : Bounds (-190313407 / 1000000000) (-95156703 / 500000000) (Real.log (8267 / 10000)) := by
  have h := reflection_log_3220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3221_neg : (43321 / 250000000) ≤ -Real.log (10000000 / 10001733) ∧
    -Real.log (10000000 / 10001733) ≤ (34657 / 200000000) := by
  have h := checkLog_sound (w := (1733 / 20001733)) (n := 12)
    (lo := (43321 / 250000000)) (hi := (34657 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001733 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001733 / 10000000) = 1/(10000000 / 10001733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3221 : Bounds (43321 / 250000000) (34657 / 200000000) (Real.log (10001733 / 10000000)) := by
  have h := reflection_log_3221_neg
  have he : Real.log (10001733 / 10000000) = -Real.log (10000000 / 10001733) := by
    rw [show ((10001733 / 10000000) : ℝ) = ((10000000 / 10001733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3222_neg : (34663 / 200000000) ≤ -Real.log (9998267 / 10000000) ∧
    -Real.log (9998267 / 10000000) ≤ (43329 / 250000000) := by
  have h := checkLog_sound (w := (1733 / 19998267)) (n := 12)
    (lo := (34663 / 200000000)) (hi := (43329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998267) = 1/(9998267 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3222 : Bounds (-43329 / 250000000) (-34663 / 200000000) (Real.log (9998267 / 10000000)) := by
  have h := reflection_log_3222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3223_neg : (10426091 / 125000000) ≤ -Real.log (500000 / 543493) ∧
    -Real.log (500000 / 543493) ≤ (83408729 / 1000000000) := by
  have h := checkLog_sound (w := (43493 / 1043493)) (n := 12)
    (lo := (10426091 / 125000000)) (hi := (83408729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543493 / 500000) = 1/(500000 / 543493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3223 : Bounds (10426091 / 125000000) (83408729 / 1000000000) (Real.log (543493 / 500000)) := by
  have h := reflection_log_3223_neg
  have he : Real.log (543493 / 500000) = -Real.log (500000 / 543493) := by
    rw [show ((543493 / 500000) : ℝ) = ((500000 / 543493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3224_neg : (2843877 / 31250000) ≤ -Real.log (456507 / 500000) ∧
    -Real.log (456507 / 500000) ≤ (18200813 / 200000000) := by
  have h := checkLog_sound (w := (43493 / 956507)) (n := 12)
    (lo := (2843877 / 31250000)) (hi := (18200813 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456507) = 1/(456507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3224 : Bounds (-18200813 / 200000000) (-2843877 / 31250000) (Real.log (456507 / 500000)) := by
  have h := reflection_log_3224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3225_neg : (83614781 / 1000000000) ≤ -Real.log (100000 / 108721) ∧
    -Real.log (100000 / 108721) ≤ (41807391 / 500000000) := by
  have h := checkLog_sound (w := (8721 / 208721)) (n := 12)
    (lo := (83614781 / 1000000000)) (hi := (41807391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108721 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108721 / 100000) = 1/(100000 / 108721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3225 : Bounds (83614781 / 1000000000) (41807391 / 500000000) (Real.log (108721 / 100000)) := by
  have h := reflection_log_3225_neg
  have he : Real.log (108721 / 100000) = -Real.log (100000 / 108721) := by
    rw [show ((108721 / 100000) : ℝ) = ((100000 / 108721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3226_neg : (18249887 / 200000000) ≤ -Real.log (91279 / 100000) ∧
    -Real.log (91279 / 100000) ≤ (22812359 / 250000000) := by
  have h := checkLog_sound (w := (8721 / 191279)) (n := 12)
    (lo := (18249887 / 200000000)) (hi := (22812359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91279) = 1/(91279 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3226 : Bounds (-22812359 / 250000000) (-18249887 / 200000000) (Real.log (91279 / 100000)) := by
  have h := reflection_log_3226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3227_neg : (3817327 / 500000000) ≤ -Real.log (9923944159 / 10000000000) ∧
    -Real.log (9923944159 / 10000000000) ≤ (1526931 / 200000000) := by
  have h := checkLog_sound (w := (76055841 / 19923944159)) (n := 12)
    (lo := (3817327 / 500000000)) (hi := (1526931 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9923944159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9923944159) = 1/(9923944159 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3227 : Bounds (-1526931 / 200000000) (-3817327 / 500000000) (Real.log (9923944159 / 10000000000)) := by
  have h := reflection_log_3227_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3228_neg : (1519067 / 200000000) ≤ -Real.log (248108358951 / 250000000000) ∧
    -Real.log (248108358951 / 250000000000) ≤ (949417 / 125000000) := by
  have h := checkLog_sound (w := (1891641049 / 498108358951)) (n := 12)
    (lo := (1519067 / 200000000)) (hi := (949417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248108358951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248108358951) = 1/(248108358951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3228 : Bounds (-949417 / 125000000) (-1519067 / 200000000) (Real.log (248108358951 / 250000000000)) := by
  have h := reflection_log_3228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3229_neg : (174412793 / 1000000000) ≤ -Real.log (500000000000 / 595273456923) ∧
    -Real.log (500000000000 / 595273456923) ≤ (87206397 / 500000000) := by
  have h := checkLog_sound (w := (95273456923 / 1095273456923)) (n := 12)
    (lo := (174412793 / 1000000000)) (hi := (87206397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595273456923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595273456923 / 500000000000) = 1/(500000000000 / 595273456923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3229 : Bounds (174412793 / 1000000000) (87206397 / 500000000) (Real.log (595273456923 / 500000000000)) := by
  have h := reflection_log_3229_neg
  have he : Real.log (595273456923 / 500000000000) = -Real.log (500000000000 / 595273456923) := by
    rw [show ((595273456923 / 500000000000) : ℝ) = ((500000000000 / 595273456923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3230_neg : (174864217 / 1000000000) ≤ -Real.log (62500000000 / 74442779829) ∧
    -Real.log (62500000000 / 74442779829) ≤ (87432109 / 500000000) := by
  have h := checkLog_sound (w := (11942779829 / 136942779829)) (n := 12)
    (lo := (174864217 / 1000000000)) (hi := (87432109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74442779829 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74442779829 / 62500000000) = 1/(62500000000 / 74442779829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3230 : Bounds (174864217 / 1000000000) (87432109 / 500000000) (Real.log (74442779829 / 62500000000)) := by
  have h := reflection_log_3230_neg
  have he : Real.log (74442779829 / 62500000000) = -Real.log (62500000000 / 74442779829) := by
    rw [show ((74442779829 / 62500000000) : ℝ) = ((62500000000 / 74442779829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3231_neg : (349927509 / 1000000000) ≤ -Real.log (500000000000 / 709482341557) ∧
    -Real.log (500000000000 / 709482341557) ≤ (34992751 / 100000000) := by
  have h := checkLog_sound (w := (209482341557 / 1209482341557)) (n := 12)
    (lo := (349927509 / 1000000000)) (hi := (34992751 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709482341557 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709482341557 / 500000000000) = 1/(500000000000 / 709482341557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3231 : Bounds (349927509 / 1000000000) (34992751 / 100000000) (Real.log (709482341557 / 500000000000)) := by
  have h := reflection_log_3231_neg
  have he : Real.log (709482341557 / 500000000000) = -Real.log (500000000000 / 709482341557) := by
    rw [show ((709482341557 / 500000000000) : ℝ) = ((500000000000 / 709482341557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3232_neg : (175066849 / 500000000) ≤ -Real.log (500000000000 / 709628644007) ∧
    -Real.log (500000000000 / 709628644007) ≤ (350133699 / 1000000000) := by
  have h := checkLog_sound (w := (209628644007 / 1209628644007)) (n := 12)
    (lo := (175066849 / 500000000)) (hi := (350133699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709628644007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709628644007 / 500000000000) = 1/(500000000000 / 709628644007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3232 : Bounds (175066849 / 500000000) (350133699 / 1000000000) (Real.log (709628644007 / 500000000000)) := by
  have h := reflection_log_3232_neg
  have he : Real.log (709628644007 / 500000000000) = -Real.log (500000000000 / 709628644007) := by
    rw [show ((709628644007 / 500000000000) : ℝ) = ((500000000000 / 709628644007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3233_neg : (159905517 / 1000000000) ≤ -Real.log (5000 / 5867) ∧
    -Real.log (5000 / 5867) ≤ (79952759 / 500000000) := by
  have h := checkLog_sound (w := (867 / 10867)) (n := 12)
    (lo := (159905517 / 1000000000)) (hi := (79952759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5867 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5867 / 5000) = 1/(5000 / 5867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3233 : Bounds (159905517 / 1000000000) (79952759 / 500000000) (Real.log (5867 / 5000)) := by
  have h := reflection_log_3233_neg
  have he : Real.log (5867 / 5000) = -Real.log (5000 / 5867) := by
    rw [show ((5867 / 5000) : ℝ) = ((5000 / 5867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3234_neg : (23804297 / 125000000) ≤ -Real.log (4133 / 5000) ∧
    -Real.log (4133 / 5000) ≤ (190434377 / 1000000000) := by
  have h := checkLog_sound (w := (867 / 9133)) (n := 12)
    (lo := (23804297 / 125000000)) (hi := (190434377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4133) = 1/(4133 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3234 : Bounds (-190434377 / 1000000000) (-23804297 / 125000000) (Real.log (4133 / 5000)) := by
  have h := reflection_log_3234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3235_neg : (21673 / 125000000) ≤ -Real.log (5000000 / 5000867) ∧
    -Real.log (5000000 / 5000867) ≤ (34677 / 200000000) := by
  have h := checkLog_sound (w := (867 / 10000867)) (n := 12)
    (lo := (21673 / 125000000)) (hi := (34677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000867 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000867 / 5000000) = 1/(5000000 / 5000867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3235 : Bounds (21673 / 125000000) (34677 / 200000000) (Real.log (5000867 / 5000000)) := by
  have h := reflection_log_3235_neg
  have he : Real.log (5000867 / 5000000) = -Real.log (5000000 / 5000867) := by
    rw [show ((5000867 / 5000000) : ℝ) = ((5000000 / 5000867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3236_neg : (34683 / 200000000) ≤ -Real.log (4999133 / 5000000) ∧
    -Real.log (4999133 / 5000000) ≤ (21677 / 125000000) := by
  have h := checkLog_sound (w := (867 / 9999133)) (n := 12)
    (lo := (34683 / 200000000)) (hi := (21677 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999133) = 1/(4999133 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3236 : Bounds (-21677 / 125000000) (-34683 / 200000000) (Real.log (4999133 / 5000000)) := by
  have h := reflection_log_3236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3237_neg : (41727823 / 500000000) ≤ -Real.log (1000000 / 1087037) ∧
    -Real.log (1000000 / 1087037) ≤ (83455647 / 1000000000) := by
  have h := checkLog_sound (w := (87037 / 2087037)) (n := 12)
    (lo := (41727823 / 500000000)) (hi := (83455647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087037 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087037 / 1000000) = 1/(1000000 / 1087037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3237 : Bounds (41727823 / 500000000) (83455647 / 1000000000) (Real.log (1087037 / 1000000)) := by
  have h := reflection_log_3237_neg
  have he : Real.log (1087037 / 1000000) = -Real.log (1000000 / 1087037) := by
    rw [show ((1087037 / 1000000) : ℝ) = ((1000000 / 1087037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3238_neg : (22764981 / 250000000) ≤ -Real.log (912963 / 1000000) ∧
    -Real.log (912963 / 1000000) ≤ (3642397 / 40000000) := by
  have h := checkLog_sound (w := (87037 / 1912963)) (n := 12)
    (lo := (22764981 / 250000000)) (hi := (3642397 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912963) = 1/(912963 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3238 : Bounds (-3642397 / 40000000) (-22764981 / 250000000) (Real.log (912963 / 1000000)) := by
  have h := reflection_log_3238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3239_neg : (83661689 / 1000000000) ≤ -Real.log (1000000 / 1087261) ∧
    -Real.log (1000000 / 1087261) ≤ (8366169 / 100000000) := by
  have h := checkLog_sound (w := (87261 / 2087261)) (n := 12)
    (lo := (83661689 / 1000000000)) (hi := (8366169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087261 / 1000000) = 1/(1000000 / 1087261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3239 : Bounds (83661689 / 1000000000) (8366169 / 100000000) (Real.log (1087261 / 1000000)) := by
  have h := reflection_log_3239_neg
  have he : Real.log (1087261 / 1000000) = -Real.log (1000000 / 1087261) := by
    rw [show ((1087261 / 1000000) : ℝ) = ((1000000 / 1087261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3240_neg : (9130531 / 100000000) ≤ -Real.log (912739 / 1000000) ∧
    -Real.log (912739 / 1000000) ≤ (91305311 / 1000000000) := by
  have h := checkLog_sound (w := (87261 / 1912739)) (n := 12)
    (lo := (9130531 / 100000000)) (hi := (91305311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912739) = 1/(912739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3240 : Bounds (-91305311 / 1000000000) (-9130531 / 100000000) (Real.log (912739 / 1000000)) := by
  have h := reflection_log_3240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3241_neg : (382181 / 50000000) ≤ -Real.log (992385517879 / 1000000000000) ∧
    -Real.log (992385517879 / 1000000000000) ≤ (7643621 / 1000000000) := by
  have h := checkLog_sound (w := (7614482121 / 1992385517879)) (n := 12)
    (lo := (382181 / 50000000)) (hi := (7643621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992385517879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992385517879) = 1/(992385517879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3241 : Bounds (-7643621 / 1000000000) (-382181 / 50000000) (Real.log (992385517879 / 1000000000000)) := by
  have h := reflection_log_3241_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3242_neg : (3802139 / 500000000) ≤ -Real.log (992424560631 / 1000000000000) ∧
    -Real.log (992424560631 / 1000000000000) ≤ (7604279 / 1000000000) := by
  have h := checkLog_sound (w := (7575439369 / 1992424560631)) (n := 12)
    (lo := (3802139 / 500000000)) (hi := (7604279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992424560631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992424560631) = 1/(992424560631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3242 : Bounds (-7604279 / 1000000000) (-3802139 / 500000000) (Real.log (992424560631 / 1000000000000)) := by
  have h := reflection_log_3242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3243_neg : (174515571 / 1000000000) ≤ -Real.log (250000000000 / 297667320581) ∧
    -Real.log (250000000000 / 297667320581) ≤ (43628893 / 250000000) := by
  have h := checkLog_sound (w := (47667320581 / 547667320581)) (n := 12)
    (lo := (174515571 / 1000000000)) (hi := (43628893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297667320581 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297667320581 / 250000000000) = 1/(250000000000 / 297667320581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3243 : Bounds (174515571 / 1000000000) (43628893 / 250000000) (Real.log (297667320581 / 250000000000)) := by
  have h := reflection_log_3243_neg
  have he : Real.log (297667320581 / 250000000000) = -Real.log (250000000000 / 297667320581) := by
    rw [show ((297667320581 / 250000000000) : ℝ) = ((250000000000 / 297667320581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3244_neg : (174966999 / 1000000000) ≤ -Real.log (62500000000 / 74450431613) ∧
    -Real.log (62500000000 / 74450431613) ≤ (174967 / 1000000) := by
  have h := checkLog_sound (w := (11950431613 / 136950431613)) (n := 12)
    (lo := (174966999 / 1000000000)) (hi := (174967 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74450431613 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74450431613 / 62500000000) = 1/(62500000000 / 74450431613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3244 : Bounds (174966999 / 1000000000) (174967 / 1000000) (Real.log (74450431613 / 62500000000)) := by
  have h := reflection_log_3244_neg
  have he : Real.log (74450431613 / 62500000000) = -Real.log (62500000000 / 74450431613) := by
    rw [show ((74450431613 / 62500000000) : ℝ) = ((62500000000 / 74450431613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3245_neg : (175066849 / 500000000) ≤ -Real.log (250000000000 / 354814322003) ∧
    -Real.log (250000000000 / 354814322003) ≤ (350133699 / 1000000000) := by
  have h := checkLog_sound (w := (104814322003 / 604814322003)) (n := 12)
    (lo := (175066849 / 500000000)) (hi := (350133699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354814322003 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354814322003 / 250000000000) = 1/(250000000000 / 354814322003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3245 : Bounds (175066849 / 500000000) (350133699 / 1000000000) (Real.log (354814322003 / 250000000000)) := by
  have h := reflection_log_3245_neg
  have he : Real.log (354814322003 / 250000000000) = -Real.log (250000000000 / 354814322003) := by
    rw [show ((354814322003 / 250000000000) : ℝ) = ((250000000000 / 354814322003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3246_neg : (175169947 / 500000000) ≤ -Real.log (250000000000 / 354887490927) ∧
    -Real.log (250000000000 / 354887490927) ≤ (70067979 / 200000000) := by
  have h := checkLog_sound (w := (104887490927 / 604887490927)) (n := 12)
    (lo := (175169947 / 500000000)) (hi := (70067979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354887490927 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354887490927 / 250000000000) = 1/(250000000000 / 354887490927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3246 : Bounds (175169947 / 500000000) (70067979 / 200000000) (Real.log (354887490927 / 250000000000)) := by
  have h := reflection_log_3246_neg
  have he : Real.log (354887490927 / 250000000000) = -Real.log (250000000000 / 354887490927) := by
    rw [show ((354887490927 / 250000000000) : ℝ) = ((250000000000 / 354887490927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3247_neg : (9999421 / 62500000) ≤ -Real.log (2000 / 2347) ∧
    -Real.log (2000 / 2347) ≤ (159990737 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 4347)) (n := 12)
    (lo := (9999421 / 62500000)) (hi := (159990737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2347 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2347 / 2000) = 1/(2000 / 2347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3247 : Bounds (9999421 / 62500000) (159990737 / 1000000000) (Real.log (2347 / 2000)) := by
  have h := reflection_log_3247_neg
  have he : Real.log (2347 / 2000) = -Real.log (2000 / 2347) := by
    rw [show ((2347 / 2000) : ℝ) = ((2000 / 2347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3248_neg : (190555361 / 1000000000) ≤ -Real.log (1653 / 2000) ∧
    -Real.log (1653 / 2000) ≤ (95277681 / 500000000) := by
  have h := checkLog_sound (w := (347 / 3653)) (n := 12)
    (lo := (190555361 / 1000000000)) (hi := (95277681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1653) = 1/(1653 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3248 : Bounds (-95277681 / 500000000) (-190555361 / 1000000000) (Real.log (1653 / 2000)) := by
  have h := reflection_log_3248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3249_neg : (43371 / 250000000) ≤ -Real.log (2000000 / 2000347) ∧
    -Real.log (2000000 / 2000347) ≤ (34697 / 200000000) := by
  have h := checkLog_sound (w := (347 / 4000347)) (n := 12)
    (lo := (43371 / 250000000)) (hi := (34697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000347 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000347 / 2000000) = 1/(2000000 / 2000347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3249 : Bounds (43371 / 250000000) (34697 / 200000000) (Real.log (2000347 / 2000000)) := by
  have h := reflection_log_3249_neg
  have he : Real.log (2000347 / 2000000) = -Real.log (2000000 / 2000347) := by
    rw [show ((2000347 / 2000000) : ℝ) = ((2000000 / 2000347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3250_neg : (34703 / 200000000) ≤ -Real.log (1999653 / 2000000) ∧
    -Real.log (1999653 / 2000000) ≤ (43379 / 250000000) := by
  have h := checkLog_sound (w := (347 / 3999653)) (n := 12)
    (lo := (34703 / 200000000)) (hi := (43379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999653) = 1/(1999653 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3250 : Bounds (-43379 / 250000000) (-34703 / 200000000) (Real.log (1999653 / 2000000)) := by
  have h := reflection_log_3250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3251_neg : (83502561 / 1000000000) ≤ -Real.log (62500 / 67943) ∧
    -Real.log (62500 / 67943) ≤ (41751281 / 500000000) := by
  have h := checkLog_sound (w := (5443 / 130443)) (n := 12)
    (lo := (83502561 / 1000000000)) (hi := (41751281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67943 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67943 / 62500) = 1/(62500 / 67943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3251 : Bounds (83502561 / 1000000000) (41751281 / 500000000) (Real.log (67943 / 62500)) := by
  have h := reflection_log_3251_neg
  have he : Real.log (67943 / 62500) = -Real.log (62500 / 67943) := by
    rw [show ((67943 / 62500) : ℝ) = ((62500 / 67943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3252_neg : (22778947 / 250000000) ≤ -Real.log (57057 / 62500) ∧
    -Real.log (57057 / 62500) ≤ (91115789 / 1000000000) := by
  have h := checkLog_sound (w := (5443 / 119557)) (n := 12)
    (lo := (22778947 / 250000000)) (hi := (91115789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57057) = 1/(57057 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3252 : Bounds (-91115789 / 1000000000) (-22778947 / 250000000) (Real.log (57057 / 62500)) := by
  have h := reflection_log_3252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3253_neg : (16741719 / 200000000) ≤ -Real.log (62500 / 67957) ∧
    -Real.log (62500 / 67957) ≤ (20927149 / 250000000) := by
  have h := checkLog_sound (w := (5457 / 130457)) (n := 12)
    (lo := (16741719 / 200000000)) (hi := (20927149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67957 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67957 / 62500) = 1/(62500 / 67957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3253 : Bounds (16741719 / 200000000) (20927149 / 250000000) (Real.log (67957 / 62500)) := by
  have h := reflection_log_3253_neg
  have he : Real.log (67957 / 62500) = -Real.log (62500 / 67957) := by
    rw [show ((67957 / 62500) : ℝ) = ((62500 / 67957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3254_neg : (91361187 / 1000000000) ≤ -Real.log (57043 / 62500) ∧
    -Real.log (57043 / 62500) ≤ (22840297 / 250000000) := by
  have h := checkLog_sound (w := (5457 / 119543)) (n := 12)
    (lo := (91361187 / 1000000000)) (hi := (22840297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57043) = 1/(57043 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3254 : Bounds (-22840297 / 250000000) (-91361187 / 1000000000) (Real.log (57043 / 62500)) := by
  have h := reflection_log_3254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3255_neg : (7652591 / 1000000000) ≤ -Real.log (3876471151 / 3906250000) ∧
    -Real.log (3876471151 / 3906250000) ≤ (478287 / 62500000) := by
  have h := checkLog_sound (w := (29778849 / 7782721151)) (n := 12)
    (lo := (7652591 / 1000000000)) (hi := (478287 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3876471151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3876471151) = 1/(3876471151 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3255 : Bounds (-478287 / 62500000) (-7652591 / 1000000000) (Real.log (3876471151 / 3906250000)) := by
  have h := reflection_log_3255_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3256_neg : (3806613 / 500000000) ≤ -Real.log (3876623751 / 3906250000) ∧
    -Real.log (3876623751 / 3906250000) ≤ (7613227 / 1000000000) := by
  have h := checkLog_sound (w := (29626249 / 7782873751)) (n := 12)
    (lo := (3806613 / 500000000)) (hi := (7613227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3876623751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3876623751) = 1/(3876623751 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3256 : Bounds (-7613227 / 1000000000) (-3806613 / 500000000) (Real.log (3876623751 / 3906250000)) := by
  have h := reflection_log_3256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3257_neg : (3492367 / 20000000) ≤ -Real.log (500000000000 / 595395832237) ∧
    -Real.log (500000000000 / 595395832237) ≤ (174618351 / 1000000000) := by
  have h := checkLog_sound (w := (95395832237 / 1095395832237)) (n := 12)
    (lo := (3492367 / 20000000)) (hi := (174618351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595395832237 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595395832237 / 500000000000) = 1/(500000000000 / 595395832237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3257 : Bounds (3492367 / 20000000) (174618351 / 1000000000) (Real.log (595395832237 / 500000000000)) := by
  have h := reflection_log_3257_neg
  have he : Real.log (595395832237 / 500000000000) = -Real.log (500000000000 / 595395832237) := by
    rw [show ((595395832237 / 500000000000) : ℝ) = ((500000000000 / 595395832237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3258_neg : (87534891 / 500000000) ≤ -Real.log (250000000000 / 297832337009) ∧
    -Real.log (250000000000 / 297832337009) ≤ (175069783 / 1000000000) := by
  have h := checkLog_sound (w := (47832337009 / 547832337009)) (n := 12)
    (lo := (87534891 / 500000000)) (hi := (175069783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297832337009 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297832337009 / 250000000000) = 1/(250000000000 / 297832337009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3258 : Bounds (87534891 / 500000000) (175069783 / 1000000000) (Real.log (297832337009 / 250000000000)) := by
  have h := reflection_log_3258_neg
  have he : Real.log (297832337009 / 250000000000) = -Real.log (250000000000 / 297832337009) := by
    rw [show ((297832337009 / 250000000000) : ℝ) = ((250000000000 / 297832337009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3259_neg : (175169947 / 500000000) ≤ -Real.log (500000000000 / 709774981853) ∧
    -Real.log (500000000000 / 709774981853) ≤ (70067979 / 200000000) := by
  have h := checkLog_sound (w := (209774981853 / 1209774981853)) (n := 12)
    (lo := (175169947 / 500000000)) (hi := (70067979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709774981853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709774981853 / 500000000000) = 1/(500000000000 / 709774981853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3259 : Bounds (175169947 / 500000000) (70067979 / 200000000) (Real.log (709774981853 / 500000000000)) := by
  have h := reflection_log_3259_neg
  have he : Real.log (709774981853 / 500000000000) = -Real.log (500000000000 / 709774981853) := by
    rw [show ((709774981853 / 500000000000) : ℝ) = ((500000000000 / 709774981853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3260_neg : (175273049 / 500000000) ≤ -Real.log (62500000000 / 88740169389) ∧
    -Real.log (62500000000 / 88740169389) ≤ (350546099 / 1000000000) := by
  have h := checkLog_sound (w := (26240169389 / 151240169389)) (n := 12)
    (lo := (175273049 / 500000000)) (hi := (350546099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88740169389 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88740169389 / 62500000000) = 1/(62500000000 / 88740169389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3260 : Bounds (175273049 / 500000000) (350546099 / 1000000000) (Real.log (88740169389 / 62500000000)) := by
  have h := reflection_log_3260_neg
  have he : Real.log (88740169389 / 62500000000) = -Real.log (62500000000 / 88740169389) := by
    rw [show ((88740169389 / 62500000000) : ℝ) = ((62500000000 / 88740169389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3261_neg : (160075947 / 1000000000) ≤ -Real.log (1250 / 1467) ∧
    -Real.log (1250 / 1467) ≤ (40018987 / 250000000) := by
  have h := checkLog_sound (w := (217 / 2717)) (n := 12)
    (lo := (160075947 / 1000000000)) (hi := (40018987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1467 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1467 / 1250) = 1/(1250 / 1467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3261 : Bounds (160075947 / 1000000000) (40018987 / 250000000) (Real.log (1467 / 1250)) := by
  have h := reflection_log_3261_neg
  have he : Real.log (1467 / 1250) = -Real.log (1250 / 1467) := by
    rw [show ((1467 / 1250) : ℝ) = ((1250 / 1467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3262_neg : (190676361 / 1000000000) ≤ -Real.log (1033 / 1250) ∧
    -Real.log (1033 / 1250) ≤ (95338181 / 500000000) := by
  have h := checkLog_sound (w := (217 / 2283)) (n := 12)
    (lo := (190676361 / 1000000000)) (hi := (95338181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1033) = 1/(1033 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3262 : Bounds (-95338181 / 500000000) (-190676361 / 1000000000) (Real.log (1033 / 1250)) := by
  have h := reflection_log_3262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3263_neg : (10849 / 62500000) ≤ -Real.log (1250000 / 1250217) ∧
    -Real.log (1250000 / 1250217) ≤ (34717 / 200000000) := by
  have h := checkLog_sound (w := (217 / 2500217)) (n := 12)
    (lo := (10849 / 62500000)) (hi := (34717 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250217 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250217 / 1250000) = 1/(1250000 / 1250217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3263 : Bounds (10849 / 62500000) (34717 / 200000000) (Real.log (1250217 / 1250000)) := by
  have h := reflection_log_3263_neg
  have he : Real.log (1250217 / 1250000) = -Real.log (1250000 / 1250217) := by
    rw [show ((1250217 / 1250000) : ℝ) = ((1250000 / 1250217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


