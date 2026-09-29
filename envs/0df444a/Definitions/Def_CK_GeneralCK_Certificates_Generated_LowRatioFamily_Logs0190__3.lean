-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0190__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0190__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T07:34:41.05941+00:00
-- url     : https://prove2.me/theorems/88bbbf91-b63c-4635-977b-c7b7370b50d3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0190 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0191, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0190 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0191, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0192)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0190 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0191, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0192)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0190 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0191, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0192) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0190 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0191, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0192).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0190 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12160_neg : (503135917 / 1000000000) ≤ -Real.log (250000000000 / 413474910033) ∧
    -Real.log (250000000000 / 413474910033) ≤ (251567959 / 500000000) := by
  have h := checkLog_sound (w := (163474910033 / 663474910033)) (n := 12)
    (lo := (503135917 / 1000000000)) (hi := (251567959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413474910033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413474910033 / 250000000000) = 1/(250000000000 / 413474910033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12160 : Bounds (503135917 / 1000000000) (251567959 / 500000000) (Real.log (413474910033 / 250000000000)) := by
  have h := reflection_log_12160_neg
  have he : Real.log (413474910033 / 250000000000) = -Real.log (250000000000 / 413474910033) := by
    rw [show ((413474910033 / 250000000000) : ℝ) = ((250000000000 / 413474910033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12161_neg : (127838661 / 125000000) ≤ -Real.log (500000000000 / 1390359168241) ∧
    -Real.log (500000000000 / 1390359168241) ≤ (102270929 / 100000000) := by
  have h := checkLog_sound (w := (390359168241 / 2390359168241)) (n := 12)
    (lo := (82390527 / 250000000)) (hi := (329562109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1390359168241 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1390359168241 / 1000000000000) = 1/(500000000000 / 1390359168241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12161 : Bounds (127838661 / 125000000) (102270929 / 100000000) (Real.log (1390359168241 / 500000000000)) := by
  have h := reflection_log_12161_neg
  have he : Real.log (1390359168241 / 500000000000) = -Real.log (500000000000 / 1390359168241) := by
    rw [show ((1390359168241 / 500000000000) : ℝ) = ((500000000000 / 1390359168241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12162_neg : (205056203 / 200000000) ≤ -Real.log (25000000000 / 69696969697) ∧
    -Real.log (25000000000 / 69696969697) ≤ (1025281017 / 1000000000) := by
  have h := checkLog_sound (w := (19696969697 / 119696969697)) (n := 12)
    (lo := (66426767 / 200000000)) (hi := (83033459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69696969697 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(69696969697 / 50000000000) = 1/(25000000000 / 69696969697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12162 : Bounds (205056203 / 200000000) (1025281017 / 1000000000) (Real.log (69696969697 / 25000000000)) := by
  have h := reflection_log_12162_neg
  have he : Real.log (69696969697 / 25000000000) = -Real.log (25000000000 / 69696969697) := by
    rw [show ((69696969697 / 25000000000) : ℝ) = ((25000000000 / 69696969697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12163_neg : (387301137 / 1000000000) ≤ -Real.log (1000 / 1473) ∧
    -Real.log (1000 / 1473) ≤ (193650569 / 500000000) := by
  have h := checkLog_sound (w := (473 / 2473)) (n := 12)
    (lo := (387301137 / 1000000000)) (hi := (193650569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1473 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1473 / 1000) = 1/(1000 / 1473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12163 : Bounds (387301137 / 1000000000) (193650569 / 500000000) (Real.log (1473 / 1000)) := by
  have h := reflection_log_12163_neg
  have he : Real.log (1473 / 1000) = -Real.log (1000 / 1473) := by
    rw [show ((1473 / 1000) : ℝ) = ((1000 / 1473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12164_neg : (64055473 / 100000000) ≤ -Real.log (527 / 1000) ∧
    -Real.log (527 / 1000) ≤ (640554731 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 1527)) (n := 12)
    (lo := (64055473 / 100000000)) (hi := (640554731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 527) = 1/(527 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12164 : Bounds (-640554731 / 1000000000) (-64055473 / 100000000) (Real.log (527 / 1000)) := by
  have h := reflection_log_12164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12165_neg : (59111 / 125000000) ≤ -Real.log (1000000 / 1000473) ∧
    -Real.log (1000000 / 1000473) ≤ (472889 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 2000473)) (n := 12)
    (lo := (59111 / 125000000)) (hi := (472889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000473 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000473 / 1000000) = 1/(1000000 / 1000473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12165 : Bounds (59111 / 125000000) (472889 / 1000000000) (Real.log (1000473 / 1000000)) := by
  have h := reflection_log_12165_neg
  have he : Real.log (1000473 / 1000000) = -Real.log (1000000 / 1000473) := by
    rw [show ((1000473 / 1000000) : ℝ) = ((1000000 / 1000473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12166_neg : (473111 / 1000000000) ≤ -Real.log (999527 / 1000000) ∧
    -Real.log (999527 / 1000000) ≤ (59139 / 125000000) := by
  have h := checkLog_sound (w := (473 / 1999527)) (n := 12)
    (lo := (473111 / 1000000000)) (hi := (59139 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999527) = 1/(999527 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12166 : Bounds (-59139 / 125000000) (-473111 / 1000000000) (Real.log (999527 / 1000000)) := by
  have h := reflection_log_12166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12167_neg : (43978053 / 200000000) ≤ -Real.log (50000 / 62297) ∧
    -Real.log (50000 / 62297) ≤ (109945133 / 500000000) := by
  have h := checkLog_sound (w := (12297 / 112297)) (n := 12)
    (lo := (43978053 / 200000000)) (hi := (109945133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62297 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62297 / 50000) = 1/(50000 / 62297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12167 : Bounds (43978053 / 200000000) (109945133 / 500000000) (Real.log (62297 / 50000)) := by
  have h := reflection_log_12167_neg
  have he : Real.log (62297 / 50000) = -Real.log (50000 / 62297) := by
    rw [show ((62297 / 50000) : ℝ) = ((50000 / 62297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12168_neg : (141141669 / 500000000) ≤ -Real.log (37703 / 50000) ∧
    -Real.log (37703 / 50000) ≤ (282283339 / 1000000000) := by
  have h := checkLog_sound (w := (12297 / 87703)) (n := 12)
    (lo := (141141669 / 500000000)) (hi := (282283339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37703) = 1/(37703 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12168 : Bounds (-282283339 / 1000000000) (-141141669 / 500000000) (Real.log (37703 / 50000)) := by
  have h := reflection_log_12168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12169_neg : (220708589 / 1000000000) ≤ -Real.log (12500 / 15587) ∧
    -Real.log (12500 / 15587) ≤ (22070859 / 100000000) := by
  have h := checkLog_sound (w := (3087 / 28087)) (n := 12)
    (lo := (220708589 / 1000000000)) (hi := (22070859 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15587 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15587 / 12500) = 1/(12500 / 15587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12169 : Bounds (220708589 / 1000000000) (22070859 / 100000000) (Real.log (15587 / 12500)) := by
  have h := reflection_log_12169_neg
  have he : Real.log (15587 / 12500) = -Real.log (12500 / 15587) := by
    rw [show ((15587 / 12500) : ℝ) = ((12500 / 15587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12170_neg : (283636931 / 1000000000) ≤ -Real.log (9413 / 12500) ∧
    -Real.log (9413 / 12500) ≤ (70909233 / 250000000) := by
  have h := checkLog_sound (w := (3087 / 21913)) (n := 12)
    (lo := (283636931 / 1000000000)) (hi := (70909233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9413) = 1/(9413 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12170 : Bounds (-70909233 / 250000000) (-283636931 / 1000000000) (Real.log (9413 / 12500)) := by
  have h := reflection_log_12170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12171_neg : (31464171 / 500000000) ≤ -Real.log (146720431 / 156250000) ∧
    -Real.log (146720431 / 156250000) ≤ (62928343 / 1000000000) := by
  have h := checkLog_sound (w := (9529569 / 302970431)) (n := 12)
    (lo := (31464171 / 500000000)) (hi := (62928343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 146720431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 146720431) = 1/(146720431 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12171 : Bounds (-62928343 / 1000000000) (-31464171 / 500000000) (Real.log (146720431 / 156250000)) := by
  have h := reflection_log_12171_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12172_neg : (62393073 / 1000000000) ≤ -Real.log (2348783791 / 2500000000) ∧
    -Real.log (2348783791 / 2500000000) ≤ (31196537 / 500000000) := by
  have h := checkLog_sound (w := (151216209 / 4848783791)) (n := 12)
    (lo := (62393073 / 1000000000)) (hi := (31196537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2348783791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2348783791) = 1/(2348783791 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12172 : Bounds (-31196537 / 500000000) (-62393073 / 1000000000) (Real.log (2348783791 / 2500000000)) := by
  have h := reflection_log_12172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12173_neg : (502173603 / 1000000000) ≤ -Real.log (25000000000 / 41307720871) ∧
    -Real.log (25000000000 / 41307720871) ≤ (125543401 / 250000000) := by
  have h := checkLog_sound (w := (16307720871 / 66307720871)) (n := 12)
    (lo := (502173603 / 1000000000)) (hi := (125543401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41307720871 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41307720871 / 25000000000) = 1/(25000000000 / 41307720871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12173 : Bounds (502173603 / 1000000000) (125543401 / 250000000) (Real.log (41307720871 / 25000000000)) := by
  have h := reflection_log_12173_neg
  have he : Real.log (41307720871 / 25000000000) = -Real.log (25000000000 / 41307720871) := by
    rw [show ((41307720871 / 25000000000) : ℝ) = ((25000000000 / 41307720871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12174_neg : (6304319 / 12500000) ≤ -Real.log (50000000000 / 82795070647) ∧
    -Real.log (50000000000 / 82795070647) ≤ (504345521 / 1000000000) := by
  have h := checkLog_sound (w := (32795070647 / 132795070647)) (n := 12)
    (lo := (6304319 / 12500000)) (hi := (504345521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82795070647 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82795070647 / 50000000000) = 1/(50000000000 / 82795070647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12174 : Bounds (6304319 / 12500000) (504345521 / 1000000000) (Real.log (82795070647 / 50000000000)) := by
  have h := reflection_log_12174_neg
  have he : Real.log (82795070647 / 50000000000) = -Real.log (50000000000 / 82795070647) := by
    rw [show ((82795070647 / 50000000000) : ℝ) = ((50000000000 / 82795070647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12175_neg : (205056203 / 200000000) ≤ -Real.log (500000000000 / 1393939393939) ∧
    -Real.log (500000000000 / 1393939393939) ≤ (1025281017 / 1000000000) := by
  have h := checkLog_sound (w := (393939393939 / 2393939393939)) (n := 12)
    (lo := (66426767 / 200000000)) (hi := (83033459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393939393939 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1393939393939 / 1000000000000) = 1/(500000000000 / 1393939393939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12175 : Bounds (205056203 / 200000000) (1025281017 / 1000000000) (Real.log (1393939393939 / 500000000000)) := by
  have h := reflection_log_12175_neg
  have he : Real.log (1393939393939 / 500000000000) = -Real.log (500000000000 / 1393939393939) := by
    rw [show ((1393939393939 / 500000000000) : ℝ) = ((500000000000 / 1393939393939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12176_neg : (1027855867 / 1000000000) ≤ -Real.log (31250000000 / 87345825427) ∧
    -Real.log (31250000000 / 87345825427) ≤ (1027855869 / 1000000000) := by
  have h := checkLog_sound (w := (24845825427 / 149845825427)) (n := 12)
    (lo := (334708687 / 1000000000)) (hi := (20919293 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87345825427 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(87345825427 / 62500000000) = 1/(31250000000 / 87345825427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12176 : Bounds (1027855867 / 1000000000) (1027855869 / 1000000000) (Real.log (87345825427 / 31250000000)) := by
  have h := reflection_log_12176_neg
  have he : Real.log (87345825427 / 31250000000) = -Real.log (31250000000 / 87345825427) := by
    rw [show ((87345825427 / 31250000000) : ℝ) = ((31250000000 / 87345825427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12177_neg : (387979793 / 1000000000) ≤ -Real.log (500 / 737) ∧
    -Real.log (500 / 737) ≤ (193989897 / 500000000) := by
  have h := checkLog_sound (w := (237 / 1237)) (n := 12)
    (lo := (387979793 / 1000000000)) (hi := (193989897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737 / 500) = 1/(500 / 737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12177 : Bounds (387979793 / 1000000000) (193989897 / 500000000) (Real.log (737 / 500)) := by
  have h := reflection_log_12177_neg
  have he : Real.log (737 / 500) = -Real.log (500 / 737) := by
    rw [show ((737 / 500) : ℝ) = ((500 / 737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12178_neg : (321227033 / 500000000) ≤ -Real.log (263 / 500) ∧
    -Real.log (263 / 500) ≤ (642454067 / 1000000000) := by
  have h := checkLog_sound (w := (237 / 763)) (n := 12)
    (lo := (321227033 / 500000000)) (hi := (642454067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 263) = 1/(263 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12178 : Bounds (-642454067 / 1000000000) (-321227033 / 500000000) (Real.log (263 / 500)) := by
  have h := reflection_log_12178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12179_neg : (473887 / 1000000000) ≤ -Real.log (500000 / 500237) ∧
    -Real.log (500000 / 500237) ≤ (14809 / 31250000) := by
  have h := checkLog_sound (w := (237 / 1000237)) (n := 12)
    (lo := (473887 / 1000000000)) (hi := (14809 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500237 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500237 / 500000) = 1/(500000 / 500237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12179 : Bounds (473887 / 1000000000) (14809 / 31250000) (Real.log (500237 / 500000)) := by
  have h := reflection_log_12179_neg
  have he : Real.log (500237 / 500000) = -Real.log (500000 / 500237) := by
    rw [show ((500237 / 500000) : ℝ) = ((500000 / 500237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12180_neg : (926 / 1953125) ≤ -Real.log (499763 / 500000) ∧
    -Real.log (499763 / 500000) ≤ (474113 / 1000000000) := by
  have h := checkLog_sound (w := (237 / 999763)) (n := 12)
    (lo := (926 / 1953125)) (hi := (474113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499763) = 1/(499763 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12180 : Bounds (-474113 / 1000000000) (-926 / 1953125) (Real.log (499763 / 500000)) := by
  have h := reflection_log_12180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12181_neg : (220346041 / 1000000000) ≤ -Real.log (250000 / 311627) ∧
    -Real.log (250000 / 311627) ≤ (110173021 / 500000000) := by
  have h := checkLog_sound (w := (61627 / 561627)) (n := 12)
    (lo := (220346041 / 1000000000)) (hi := (110173021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311627 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311627 / 250000) = 1/(250000 / 311627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12181 : Bounds (220346041 / 1000000000) (110173021 / 500000000) (Real.log (311627 / 250000)) := by
  have h := reflection_log_12181_neg
  have he : Real.log (311627 / 250000) = -Real.log (250000 / 311627) := by
    rw [show ((311627 / 250000) : ℝ) = ((250000 / 311627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12182_neg : (141518439 / 500000000) ≤ -Real.log (188373 / 250000) ∧
    -Real.log (188373 / 250000) ≤ (283036879 / 1000000000) := by
  have h := checkLog_sound (w := (61627 / 438373)) (n := 12)
    (lo := (141518439 / 500000000)) (hi := (283036879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188373) = 1/(188373 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12182 : Bounds (-283036879 / 1000000000) (-141518439 / 500000000) (Real.log (188373 / 250000)) := by
  have h := reflection_log_12182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12183_neg : (110582397 / 500000000) ≤ -Real.log (1000000 / 1247529) ∧
    -Real.log (1000000 / 1247529) ≤ (44232959 / 200000000) := by
  have h := checkLog_sound (w := (247529 / 2247529)) (n := 12)
    (lo := (110582397 / 500000000)) (hi := (44232959 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247529 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247529 / 1000000) = 1/(1000000 / 1247529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12183 : Bounds (110582397 / 500000000) (44232959 / 200000000) (Real.log (1247529 / 1000000)) := by
  have h := reflection_log_12183_neg
  have he : Real.log (1247529 / 1000000) = -Real.log (1000000 / 1247529) := by
    rw [show ((1247529 / 1000000) : ℝ) = ((1000000 / 1247529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12184_neg : (284392821 / 1000000000) ≤ -Real.log (752471 / 1000000) ∧
    -Real.log (752471 / 1000000) ≤ (142196411 / 500000000) := by
  have h := checkLog_sound (w := (247529 / 1752471)) (n := 12)
    (lo := (284392821 / 1000000000)) (hi := (142196411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 752471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 752471) = 1/(752471 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12184 : Bounds (-142196411 / 500000000) (-284392821 / 1000000000) (Real.log (752471 / 1000000)) := by
  have h := reflection_log_12184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12185_neg : (31614013 / 500000000) ≤ -Real.log (938729394159 / 1000000000000) ∧
    -Real.log (938729394159 / 1000000000000) ≤ (63228027 / 1000000000) := by
  have h := checkLog_sound (w := (61270605841 / 1938729394159)) (n := 12)
    (lo := (31614013 / 500000000)) (hi := (63228027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 938729394159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 938729394159) = 1/(938729394159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12185 : Bounds (-63228027 / 1000000000) (-31614013 / 500000000) (Real.log (938729394159 / 1000000000000)) := by
  have h := reflection_log_12185_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12186_neg : (15672709 / 250000000) ≤ -Real.log (58702112871 / 62500000000) ∧
    -Real.log (58702112871 / 62500000000) ≤ (62690837 / 1000000000) := by
  have h := checkLog_sound (w := (3797887129 / 121202112871)) (n := 12)
    (lo := (15672709 / 250000000)) (hi := (62690837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58702112871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58702112871) = 1/(58702112871 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12186 : Bounds (-62690837 / 1000000000) (-15672709 / 250000000) (Real.log (58702112871 / 62500000000)) := by
  have h := reflection_log_12186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12187_neg : (12584573 / 25000000) ≤ -Real.log (20000000000 / 33086164153) ∧
    -Real.log (20000000000 / 33086164153) ≤ (503382921 / 1000000000) := by
  have h := checkLog_sound (w := (13086164153 / 53086164153)) (n := 12)
    (lo := (12584573 / 25000000)) (hi := (503382921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33086164153 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33086164153 / 20000000000) = 1/(20000000000 / 33086164153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12187 : Bounds (12584573 / 25000000) (503382921 / 1000000000) (Real.log (33086164153 / 20000000000)) := by
  have h := reflection_log_12187_neg
  have he : Real.log (33086164153 / 20000000000) = -Real.log (20000000000 / 33086164153) := by
    rw [show ((33086164153 / 20000000000) : ℝ) = ((20000000000 / 33086164153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12188_neg : (31597351 / 62500000) ≤ -Real.log (250000000000 / 414477435011) ∧
    -Real.log (250000000000 / 414477435011) ≤ (505557617 / 1000000000) := by
  have h := checkLog_sound (w := (164477435011 / 664477435011)) (n := 12)
    (lo := (31597351 / 62500000)) (hi := (505557617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414477435011 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414477435011 / 250000000000) = 1/(250000000000 / 414477435011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12188 : Bounds (31597351 / 62500000) (505557617 / 1000000000) (Real.log (414477435011 / 250000000000)) := by
  have h := reflection_log_12188_neg
  have he : Real.log (414477435011 / 250000000000) = -Real.log (250000000000 / 414477435011) := by
    rw [show ((414477435011 / 250000000000) : ℝ) = ((250000000000 / 414477435011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12189_neg : (1027855867 / 1000000000) ≤ -Real.log (500000000000 / 1397533206831) ∧
    -Real.log (500000000000 / 1397533206831) ≤ (1027855869 / 1000000000) := by
  have h := checkLog_sound (w := (397533206831 / 2397533206831)) (n := 12)
    (lo := (334708687 / 1000000000)) (hi := (20919293 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397533206831 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1397533206831 / 1000000000000) = 1/(500000000000 / 1397533206831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12189 : Bounds (1027855867 / 1000000000) (1027855869 / 1000000000) (Real.log (1397533206831 / 500000000000)) := by
  have h := reflection_log_12189_neg
  have he : Real.log (1397533206831 / 500000000000) = -Real.log (500000000000 / 1397533206831) := by
    rw [show ((1397533206831 / 500000000000) : ℝ) = ((500000000000 / 1397533206831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12190_neg : (1030433859 / 1000000000) ≤ -Real.log (500000000000 / 1401140684411) ∧
    -Real.log (500000000000 / 1401140684411) ≤ (1030433861 / 1000000000) := by
  have h := checkLog_sound (w := (401140684411 / 2401140684411)) (n := 12)
    (lo := (337286679 / 1000000000)) (hi := (8432167 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1401140684411 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1401140684411 / 1000000000000) = 1/(500000000000 / 1401140684411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12190 : Bounds (1030433859 / 1000000000) (1030433861 / 1000000000) (Real.log (1401140684411 / 500000000000)) := by
  have h := reflection_log_12190_neg
  have he : Real.log (1401140684411 / 500000000000) = -Real.log (500000000000 / 1401140684411) := by
    rw [show ((1401140684411 / 500000000000) : ℝ) = ((500000000000 / 1401140684411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12191_neg : (388657989 / 1000000000) ≤ -Real.log (40 / 59) ∧
    -Real.log (40 / 59) ≤ (38865799 / 100000000) := by
  have h := checkLog_sound (w := (19 / 99)) (n := 12)
    (lo := (388657989 / 1000000000)) (hi := (38865799 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59 / 40) = 1/(40 / 59) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12191 : Bounds (388657989 / 1000000000) (38865799 / 100000000) (Real.log (59 / 40)) := by
  have h := reflection_log_12191_neg
  have he : Real.log (59 / 40) = -Real.log (40 / 59) := by
    rw [show ((59 / 40) : ℝ) = ((40 / 59) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12192_neg : (80544627 / 125000000) ≤ -Real.log (21 / 40) ∧
    -Real.log (21 / 40) ≤ (644357017 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 21) = 1/(21 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12192 : Bounds (-644357017 / 1000000000) (-80544627 / 125000000) (Real.log (21 / 40)) := by
  have h := reflection_log_12192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12193_neg : (474887 / 1000000000) ≤ -Real.log (40000 / 40019) ∧
    -Real.log (40000 / 40019) ≤ (59361 / 125000000) := by
  have h := checkLog_sound (w := (19 / 80019)) (n := 12)
    (lo := (474887 / 1000000000)) (hi := (59361 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40019 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40019 / 40000) = 1/(40000 / 40019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12193 : Bounds (474887 / 1000000000) (59361 / 125000000) (Real.log (40019 / 40000)) := by
  have h := reflection_log_12193_neg
  have he : Real.log (40019 / 40000) = -Real.log (40000 / 40019) := by
    rw [show ((40019 / 40000) : ℝ) = ((40000 / 40019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12194_neg : (59389 / 125000000) ≤ -Real.log (39981 / 40000) ∧
    -Real.log (39981 / 40000) ≤ (475113 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 79981)) (n := 12)
    (lo := (59389 / 125000000)) (hi := (475113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39981) = 1/(39981 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12194 : Bounds (-475113 / 1000000000) (-59389 / 125000000) (Real.log (39981 / 40000)) := by
  have h := reflection_log_12194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12195_neg : (220801611 / 1000000000) ≤ -Real.log (250000 / 311769) ∧
    -Real.log (250000 / 311769) ≤ (55200403 / 250000000) := by
  have h := checkLog_sound (w := (61769 / 561769)) (n := 12)
    (lo := (220801611 / 1000000000)) (hi := (55200403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311769 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311769 / 250000) = 1/(250000 / 311769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12195 : Bounds (220801611 / 1000000000) (55200403 / 250000000) (Real.log (311769 / 250000)) := by
  have h := reflection_log_12195_neg
  have he : Real.log (311769 / 250000) = -Real.log (250000 / 311769) := by
    rw [show ((311769 / 250000) : ℝ) = ((250000 / 311769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12196_neg : (56758197 / 200000000) ≤ -Real.log (188231 / 250000) ∧
    -Real.log (188231 / 250000) ≤ (141895493 / 500000000) := by
  have h := checkLog_sound (w := (61769 / 438231)) (n := 12)
    (lo := (56758197 / 200000000)) (hi := (141895493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188231) = 1/(188231 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12196 : Bounds (-141895493 / 500000000) (-56758197 / 200000000) (Real.log (188231 / 250000)) := by
  have h := reflection_log_12196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12197_neg : (27702599 / 125000000) ≤ -Real.log (500000 / 624049) ∧
    -Real.log (500000 / 624049) ≤ (221620793 / 1000000000) := by
  have h := checkLog_sound (w := (124049 / 1124049)) (n := 12)
    (lo := (27702599 / 125000000)) (hi := (221620793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624049 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624049 / 500000) = 1/(500000 / 624049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12197 : Bounds (27702599 / 125000000) (221620793 / 1000000000) (Real.log (624049 / 500000)) := by
  have h := reflection_log_12197_neg
  have he : Real.log (624049 / 500000) = -Real.log (500000 / 624049) := by
    rw [show ((624049 / 500000) : ℝ) = ((500000 / 624049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12198_neg : (142574641 / 500000000) ≤ -Real.log (375951 / 500000) ∧
    -Real.log (375951 / 500000) ≤ (285149283 / 1000000000) := by
  have h := checkLog_sound (w := (124049 / 875951)) (n := 12)
    (lo := (142574641 / 500000000)) (hi := (285149283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375951) = 1/(375951 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12198 : Bounds (-285149283 / 1000000000) (-142574641 / 500000000) (Real.log (375951 / 500000)) := by
  have h := reflection_log_12198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12199_neg : (6352849 / 100000000) ≤ -Real.log (234611845599 / 250000000000) ∧
    -Real.log (234611845599 / 250000000000) ≤ (63528491 / 1000000000) := by
  have h := checkLog_sound (w := (15388154401 / 484611845599)) (n := 12)
    (lo := (6352849 / 100000000)) (hi := (63528491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 234611845599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 234611845599) = 1/(234611845599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12199 : Bounds (-63528491 / 1000000000) (-6352849 / 100000000) (Real.log (234611845599 / 250000000000)) := by
  have h := reflection_log_12199_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12200_neg : (31494687 / 500000000) ≤ -Real.log (58684590639 / 62500000000) ∧
    -Real.log (58684590639 / 62500000000) ≤ (100783 / 1600000) := by
  have h := checkLog_sound (w := (3815409361 / 121184590639)) (n := 12)
    (lo := (31494687 / 500000000)) (hi := (100783 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58684590639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58684590639) = 1/(58684590639 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12200 : Bounds (-100783 / 1600000) (-31494687 / 500000000) (Real.log (58684590639 / 62500000000)) := by
  have h := reflection_log_12200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12201_neg : (504592597 / 1000000000) ≤ -Real.log (250000000000 / 414077649271) ∧
    -Real.log (250000000000 / 414077649271) ≤ (252296299 / 500000000) := by
  have h := checkLog_sound (w := (164077649271 / 664077649271)) (n := 12)
    (lo := (504592597 / 1000000000)) (hi := (252296299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414077649271 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414077649271 / 250000000000) = 1/(250000000000 / 414077649271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12201 : Bounds (504592597 / 1000000000) (252296299 / 500000000) (Real.log (414077649271 / 250000000000)) := by
  have h := reflection_log_12201_neg
  have he : Real.log (414077649271 / 250000000000) = -Real.log (250000000000 / 414077649271) := by
    rw [show ((414077649271 / 250000000000) : ℝ) = ((250000000000 / 414077649271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12202_neg : (20270803 / 40000000) ≤ -Real.log (50000000000 / 82996055337) ∧
    -Real.log (50000000000 / 82996055337) ≤ (126692519 / 250000000) := by
  have h := checkLog_sound (w := (32996055337 / 132996055337)) (n := 12)
    (lo := (20270803 / 40000000)) (hi := (126692519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82996055337 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82996055337 / 50000000000) = 1/(50000000000 / 82996055337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12202 : Bounds (20270803 / 40000000) (126692519 / 250000000) (Real.log (82996055337 / 50000000000)) := by
  have h := reflection_log_12202_neg
  have he : Real.log (82996055337 / 50000000000) = -Real.log (50000000000 / 82996055337) := by
    rw [show ((82996055337 / 50000000000) : ℝ) = ((50000000000 / 82996055337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12203_neg : (1030433859 / 1000000000) ≤ -Real.log (50000000000 / 140114068441) ∧
    -Real.log (50000000000 / 140114068441) ≤ (1030433861 / 1000000000) := by
  have h := checkLog_sound (w := (40114068441 / 240114068441)) (n := 12)
    (lo := (337286679 / 1000000000)) (hi := (8432167 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140114068441 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(140114068441 / 100000000000) = 1/(50000000000 / 140114068441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12203 : Bounds (1030433859 / 1000000000) (1030433861 / 1000000000) (Real.log (140114068441 / 50000000000)) := by
  have h := reflection_log_12203_neg
  have he : Real.log (140114068441 / 50000000000) = -Real.log (50000000000 / 140114068441) := by
    rw [show ((140114068441 / 50000000000) : ℝ) = ((50000000000 / 140114068441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12204_neg : (206603001 / 200000000) ≤ -Real.log (250000000000 / 702380952381) ∧
    -Real.log (250000000000 / 702380952381) ≤ (1033015007 / 1000000000) := by
  have h := checkLog_sound (w := (202380952381 / 1202380952381)) (n := 12)
    (lo := (13594713 / 40000000)) (hi := (169933913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702380952381 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(702380952381 / 500000000000) = 1/(250000000000 / 702380952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12204 : Bounds (206603001 / 200000000) (1033015007 / 1000000000) (Real.log (702380952381 / 250000000000)) := by
  have h := reflection_log_12204_neg
  have he : Real.log (702380952381 / 250000000000) = -Real.log (250000000000 / 702380952381) := by
    rw [show ((702380952381 / 250000000000) : ℝ) = ((250000000000 / 702380952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12205_neg : (194667863 / 500000000) ≤ -Real.log (250 / 369) ∧
    -Real.log (250 / 369) ≤ (389335727 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 619)) (n := 12)
    (lo := (194667863 / 500000000)) (hi := (389335727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369 / 250) = 1/(250 / 369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12205 : Bounds (194667863 / 500000000) (389335727 / 1000000000) (Real.log (369 / 250)) := by
  have h := reflection_log_12205_neg
  have he : Real.log (369 / 250) = -Real.log (250 / 369) := by
    rw [show ((369 / 250) : ℝ) = ((250 / 369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12206_neg : (323131797 / 500000000) ≤ -Real.log (131 / 250) ∧
    -Real.log (131 / 250) ≤ (129252719 / 200000000) := by
  have h := checkLog_sound (w := (119 / 381)) (n := 12)
    (lo := (323131797 / 500000000)) (hi := (129252719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 131) = 1/(131 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12206 : Bounds (-129252719 / 200000000) (-323131797 / 500000000) (Real.log (131 / 250)) := by
  have h := reflection_log_12206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12207_neg : (237943 / 500000000) ≤ -Real.log (250000 / 250119) ∧
    -Real.log (250000 / 250119) ≤ (475887 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 500119)) (n := 12)
    (lo := (237943 / 500000000)) (hi := (475887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250119 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250119 / 250000) = 1/(250000 / 250119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12207 : Bounds (237943 / 500000000) (475887 / 1000000000) (Real.log (250119 / 250000)) := by
  have h := reflection_log_12207_neg
  have he : Real.log (250119 / 250000) = -Real.log (250000 / 250119) := by
    rw [show ((250119 / 250000) : ℝ) = ((250000 / 250119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12208_neg : (476113 / 1000000000) ≤ -Real.log (249881 / 250000) ∧
    -Real.log (249881 / 250000) ≤ (238057 / 500000000) := by
  have h := checkLog_sound (w := (119 / 499881)) (n := 12)
    (lo := (476113 / 1000000000)) (hi := (238057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249881) = 1/(249881 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12208 : Bounds (-238057 / 500000000) (-476113 / 1000000000) (Real.log (249881 / 250000)) := by
  have h := reflection_log_12208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12209_neg : (55314243 / 250000000) ≤ -Real.log (250000 / 311911) ∧
    -Real.log (250000 / 311911) ≤ (221256973 / 1000000000) := by
  have h := checkLog_sound (w := (61911 / 561911)) (n := 12)
    (lo := (55314243 / 250000000)) (hi := (221256973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311911 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311911 / 250000) = 1/(250000 / 311911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12209 : Bounds (55314243 / 250000000) (221256973 / 1000000000) (Real.log (311911 / 250000)) := by
  have h := reflection_log_12209_neg
  have he : Real.log (311911 / 250000) = -Real.log (250000 / 311911) := by
    rw [show ((311911 / 250000) : ℝ) = ((250000 / 311911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12210_neg : (142272831 / 500000000) ≤ -Real.log (188089 / 250000) ∧
    -Real.log (188089 / 250000) ≤ (284545663 / 1000000000) := by
  have h := checkLog_sound (w := (61911 / 438089)) (n := 12)
    (lo := (142272831 / 500000000)) (hi := (284545663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188089) = 1/(188089 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12210 : Bounds (-284545663 / 1000000000) (-142272831 / 500000000) (Real.log (188089 / 250000)) := by
  have h := reflection_log_12210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12211_neg : (222077383 / 1000000000) ≤ -Real.log (250000 / 312167) ∧
    -Real.log (250000 / 312167) ≤ (27759673 / 125000000) := by
  have h := checkLog_sound (w := (62167 / 562167)) (n := 12)
    (lo := (222077383 / 1000000000)) (hi := (27759673 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312167 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312167 / 250000) = 1/(250000 / 312167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12211 : Bounds (222077383 / 1000000000) (27759673 / 125000000) (Real.log (312167 / 250000)) := by
  have h := reflection_log_12211_neg
  have he : Real.log (312167 / 250000) = -Real.log (250000 / 312167) := by
    rw [show ((312167 / 250000) : ℝ) = ((250000 / 312167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12212_neg : (285907647 / 1000000000) ≤ -Real.log (187833 / 250000) ∧
    -Real.log (187833 / 250000) ≤ (4467307 / 15625000) := by
  have h := checkLog_sound (w := (62167 / 437833)) (n := 12)
    (lo := (285907647 / 1000000000)) (hi := (4467307 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187833) = 1/(187833 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12212 : Bounds (-4467307 / 15625000) (-285907647 / 1000000000) (Real.log (187833 / 250000)) := by
  have h := reflection_log_12212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12213_neg : (7978783 / 125000000) ≤ -Real.log (58635264111 / 62500000000) ∧
    -Real.log (58635264111 / 62500000000) ≤ (12766053 / 200000000) := by
  have h := checkLog_sound (w := (3864735889 / 121135264111)) (n := 12)
    (lo := (7978783 / 125000000)) (hi := (12766053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58635264111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58635264111) = 1/(58635264111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12213 : Bounds (-12766053 / 200000000) (-7978783 / 125000000) (Real.log (58635264111 / 62500000000)) := by
  have h := reflection_log_12213_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12214_neg : (63288689 / 1000000000) ≤ -Real.log (58667028079 / 62500000000) ∧
    -Real.log (58667028079 / 62500000000) ≤ (6328869 / 100000000) := by
  have h := checkLog_sound (w := (3832971921 / 121167028079)) (n := 12)
    (lo := (63288689 / 1000000000)) (hi := (6328869 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58667028079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58667028079) = 1/(58667028079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12214 : Bounds (-6328869 / 100000000) (-63288689 / 1000000000) (Real.log (58667028079 / 62500000000)) := by
  have h := reflection_log_12214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12215_neg : (101160527 / 200000000) ≤ -Real.log (500000000000 / 829158004987) ∧
    -Real.log (500000000000 / 829158004987) ≤ (126450659 / 250000000) := by
  have h := checkLog_sound (w := (329158004987 / 1329158004987)) (n := 12)
    (lo := (101160527 / 200000000)) (hi := (126450659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829158004987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829158004987 / 500000000000) = 1/(500000000000 / 829158004987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12215 : Bounds (101160527 / 200000000) (126450659 / 250000000) (Real.log (829158004987 / 500000000000)) := by
  have h := reflection_log_12215_neg
  have he : Real.log (829158004987 / 500000000000) = -Real.log (500000000000 / 829158004987) := by
    rw [show ((829158004987 / 500000000000) : ℝ) = ((500000000000 / 829158004987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12216_neg : (50798503 / 100000000) ≤ -Real.log (250000000000 / 415484765723) ∧
    -Real.log (250000000000 / 415484765723) ≤ (507985031 / 1000000000) := by
  have h := checkLog_sound (w := (165484765723 / 665484765723)) (n := 12)
    (lo := (50798503 / 100000000)) (hi := (507985031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415484765723 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415484765723 / 250000000000) = 1/(250000000000 / 415484765723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12216 : Bounds (50798503 / 100000000) (507985031 / 1000000000) (Real.log (415484765723 / 250000000000)) := by
  have h := reflection_log_12216_neg
  have he : Real.log (415484765723 / 250000000000) = -Real.log (250000000000 / 415484765723) := by
    rw [show ((415484765723 / 250000000000) : ℝ) = ((250000000000 / 415484765723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12217_neg : (206603001 / 200000000) ≤ -Real.log (500000000000 / 1404761904761) ∧
    -Real.log (500000000000 / 1404761904761) ≤ (1033015007 / 1000000000) := by
  have h := checkLog_sound (w := (404761904761 / 2404761904761)) (n := 12)
    (lo := (13594713 / 40000000)) (hi := (169933913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1404761904761 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1404761904761 / 1000000000000) = 1/(500000000000 / 1404761904761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12217 : Bounds (206603001 / 200000000) (1033015007 / 1000000000) (Real.log (1404761904761 / 500000000000)) := by
  have h := reflection_log_12217_neg
  have he : Real.log (1404761904761 / 500000000000) = -Real.log (500000000000 / 1404761904761) := by
    rw [show ((1404761904761 / 500000000000) : ℝ) = ((500000000000 / 1404761904761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12218_neg : (25889983 / 25000000) ≤ -Real.log (100000000000 / 281679389313) ∧
    -Real.log (100000000000 / 281679389313) ≤ (517799661 / 500000000) := by
  have h := checkLog_sound (w := (81679389313 / 481679389313)) (n := 12)
    (lo := (17122607 / 50000000)) (hi := (342452141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281679389313 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(281679389313 / 200000000000) = 1/(100000000000 / 281679389313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12218 : Bounds (25889983 / 25000000) (517799661 / 500000000) (Real.log (281679389313 / 100000000000)) := by
  have h := reflection_log_12218_neg
  have he : Real.log (281679389313 / 100000000000) = -Real.log (100000000000 / 281679389313) := by
    rw [show ((281679389313 / 100000000000) : ℝ) = ((100000000000 / 281679389313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12219_neg : (390013003 / 1000000000) ≤ -Real.log (1000 / 1477) ∧
    -Real.log (1000 / 1477) ≤ (97503251 / 250000000) := by
  have h := checkLog_sound (w := (477 / 2477)) (n := 12)
    (lo := (390013003 / 1000000000)) (hi := (97503251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1477 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1477 / 1000) = 1/(1000 / 1477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12219 : Bounds (390013003 / 1000000000) (97503251 / 250000000) (Real.log (1477 / 1000)) := by
  have h := reflection_log_12219_neg
  have he : Real.log (1477 / 1000) = -Real.log (1000 / 1477) := by
    rw [show ((1477 / 1000) : ℝ) = ((1000 / 1477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12220_neg : (324086907 / 500000000) ≤ -Real.log (523 / 1000) ∧
    -Real.log (523 / 1000) ≤ (129634763 / 200000000) := by
  have h := checkLog_sound (w := (477 / 1523)) (n := 12)
    (lo := (324086907 / 500000000)) (hi := (129634763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 523) = 1/(523 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12220 : Bounds (-129634763 / 200000000) (-324086907 / 500000000) (Real.log (523 / 1000)) := by
  have h := reflection_log_12220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12221_neg : (238443 / 500000000) ≤ -Real.log (1000000 / 1000477) ∧
    -Real.log (1000000 / 1000477) ≤ (476887 / 1000000000) := by
  have h := checkLog_sound (w := (477 / 2000477)) (n := 12)
    (lo := (238443 / 500000000)) (hi := (476887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000477 / 1000000) = 1/(1000000 / 1000477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12221 : Bounds (238443 / 500000000) (476887 / 1000000000) (Real.log (1000477 / 1000000)) := by
  have h := reflection_log_12221_neg
  have he : Real.log (1000477 / 1000000) = -Real.log (1000000 / 1000477) := by
    rw [show ((1000477 / 1000000) : ℝ) = ((1000000 / 1000477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12222_neg : (477113 / 1000000000) ≤ -Real.log (999523 / 1000000) ∧
    -Real.log (999523 / 1000000) ≤ (238557 / 500000000) := by
  have h := checkLog_sound (w := (477 / 1999523)) (n := 12)
    (lo := (477113 / 1000000000)) (hi := (238557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999523) = 1/(999523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12222 : Bounds (-238557 / 500000000) (-477113 / 1000000000) (Real.log (999523 / 1000000)) := by
  have h := reflection_log_12222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12223_neg : (6928529 / 31250000) ≤ -Real.log (1000000 / 1248213) ∧
    -Real.log (1000000 / 1248213) ≤ (221712929 / 1000000000) := by
  have h := checkLog_sound (w := (248213 / 2248213)) (n := 12)
    (lo := (6928529 / 31250000)) (hi := (221712929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248213 / 1000000) = 1/(1000000 / 1248213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12223 : Bounds (6928529 / 31250000) (221712929 / 1000000000) (Real.log (1248213 / 1000000)) := by
  have h := reflection_log_12223_neg
  have he : Real.log (1248213 / 1000000) = -Real.log (1000000 / 1248213) := by
    rw [show ((1248213 / 1000000) : ℝ) = ((1000000 / 1248213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0191 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12224_neg : (285302239 / 1000000000) ≤ -Real.log (751787 / 1000000) ∧
    -Real.log (751787 / 1000000) ≤ (1783139 / 6250000) := by
  have h := checkLog_sound (w := (248213 / 1751787)) (n := 12)
    (lo := (285302239 / 1000000000)) (hi := (1783139 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 751787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 751787) = 1/(751787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12224 : Bounds (-1783139 / 6250000) (-285302239 / 1000000000) (Real.log (751787 / 1000000)) := by
  have h := reflection_log_12224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12225_neg : (55633241 / 250000000) ≤ -Real.log (1000000 / 1249237) ∧
    -Real.log (1000000 / 1249237) ≤ (44506593 / 200000000) := by
  have h := checkLog_sound (w := (249237 / 2249237)) (n := 12)
    (lo := (55633241 / 250000000)) (hi := (44506593 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249237 / 1000000) = 1/(1000000 / 1249237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12225 : Bounds (55633241 / 250000000) (44506593 / 200000000) (Real.log (1249237 / 1000000)) := by
  have h := reflection_log_12225_neg
  have he : Real.log (1249237 / 1000000) = -Real.log (1000000 / 1249237) := by
    rw [show ((1249237 / 1000000) : ℝ) = ((1000000 / 1249237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12226_neg : (35833157 / 125000000) ≤ -Real.log (750763 / 1000000) ∧
    -Real.log (750763 / 1000000) ≤ (286665257 / 1000000000) := by
  have h := checkLog_sound (w := (249237 / 1750763)) (n := 12)
    (lo := (35833157 / 125000000)) (hi := (286665257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750763) = 1/(750763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12226 : Bounds (-286665257 / 1000000000) (-35833157 / 125000000) (Real.log (750763 / 1000000)) := by
  have h := reflection_log_12226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12227_neg : (64132291 / 1000000000) ≤ -Real.log (937880917831 / 1000000000000) ∧
    -Real.log (937880917831 / 1000000000000) ≤ (16033073 / 250000000) := by
  have h := checkLog_sound (w := (62119082169 / 1937880917831)) (n := 12)
    (lo := (64132291 / 1000000000)) (hi := (16033073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 937880917831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 937880917831) = 1/(937880917831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12227 : Bounds (-16033073 / 250000000) (-64132291 / 1000000000) (Real.log (937880917831 / 1000000000000)) := by
  have h := reflection_log_12227_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12228_neg : (63589311 / 1000000000) ≤ -Real.log (938390306631 / 1000000000000) ∧
    -Real.log (938390306631 / 1000000000000) ≤ (993583 / 15625000) := by
  have h := checkLog_sound (w := (61609693369 / 1938390306631)) (n := 12)
    (lo := (63589311 / 1000000000)) (hi := (993583 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 938390306631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 938390306631) = 1/(938390306631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12228 : Bounds (-993583 / 15625000) (-63589311 / 1000000000) (Real.log (938390306631 / 1000000000000)) := by
  have h := reflection_log_12228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12229_neg : (990264 / 1953125) ≤ -Real.log (500000000000 / 830163995919) ∧
    -Real.log (500000000000 / 830163995919) ≤ (507015169 / 1000000000) := by
  have h := checkLog_sound (w := (330163995919 / 1330163995919)) (n := 12)
    (lo := (990264 / 1953125)) (hi := (507015169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((830163995919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(830163995919 / 500000000000) = 1/(500000000000 / 830163995919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12229 : Bounds (990264 / 1953125) (507015169 / 1000000000) (Real.log (830163995919 / 500000000000)) := by
  have h := reflection_log_12229_neg
  have he : Real.log (830163995919 / 500000000000) = -Real.log (500000000000 / 830163995919) := by
    rw [show ((830163995919 / 500000000000) : ℝ) = ((500000000000 / 830163995919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12230_neg : (509198221 / 1000000000) ≤ -Real.log (500000000000 / 831978267443) ∧
    -Real.log (500000000000 / 831978267443) ≤ (254599111 / 500000000) := by
  have h := checkLog_sound (w := (331978267443 / 1331978267443)) (n := 12)
    (lo := (509198221 / 1000000000)) (hi := (254599111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831978267443 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831978267443 / 500000000000) = 1/(500000000000 / 831978267443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12230 : Bounds (509198221 / 1000000000) (254599111 / 500000000) (Real.log (831978267443 / 500000000000)) := by
  have h := reflection_log_12230_neg
  have he : Real.log (831978267443 / 500000000000) = -Real.log (500000000000 / 831978267443) := by
    rw [show ((831978267443 / 500000000000) : ℝ) = ((500000000000 / 831978267443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12231_neg : (25889983 / 25000000) ≤ -Real.log (125000000000 / 352099236641) ∧
    -Real.log (125000000000 / 352099236641) ≤ (517799661 / 500000000) := by
  have h := checkLog_sound (w := (102099236641 / 602099236641)) (n := 12)
    (lo := (17122607 / 50000000)) (hi := (342452141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352099236641 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(352099236641 / 250000000000) = 1/(125000000000 / 352099236641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12231 : Bounds (25889983 / 25000000) (517799661 / 500000000) (Real.log (352099236641 / 125000000000)) := by
  have h := reflection_log_12231_neg
  have he : Real.log (352099236641 / 125000000000) = -Real.log (125000000000 / 352099236641) := by
    rw [show ((352099236641 / 125000000000) : ℝ) = ((125000000000 / 352099236641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12232_neg : (1038186817 / 1000000000) ≤ -Real.log (250000000000 / 706022944551) ∧
    -Real.log (250000000000 / 706022944551) ≤ (1038186819 / 1000000000) := by
  have h := checkLog_sound (w := (206022944551 / 1206022944551)) (n := 12)
    (lo := (345039637 / 1000000000)) (hi := (172519819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706022944551 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(706022944551 / 500000000000) = 1/(250000000000 / 706022944551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12232 : Bounds (1038186817 / 1000000000) (1038186819 / 1000000000) (Real.log (706022944551 / 250000000000)) := by
  have h := reflection_log_12232_neg
  have he : Real.log (706022944551 / 250000000000) = -Real.log (250000000000 / 706022944551) := by
    rw [show ((706022944551 / 250000000000) : ℝ) = ((250000000000 / 706022944551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12233_neg : (195344911 / 500000000) ≤ -Real.log (500 / 739) ∧
    -Real.log (500 / 739) ≤ (390689823 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 1239)) (n := 12)
    (lo := (195344911 / 500000000)) (hi := (390689823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739 / 500) = 1/(500 / 739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12233 : Bounds (195344911 / 500000000) (390689823 / 1000000000) (Real.log (739 / 500)) := by
  have h := reflection_log_12233_neg
  have he : Real.log (739 / 500) = -Real.log (500 / 739) := by
    rw [show ((739 / 500) : ℝ) = ((500 / 739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12234_neg : (650087691 / 1000000000) ≤ -Real.log (261 / 500) ∧
    -Real.log (261 / 500) ≤ (162521923 / 250000000) := by
  have h := checkLog_sound (w := (239 / 761)) (n := 12)
    (lo := (650087691 / 1000000000)) (hi := (162521923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 261) = 1/(261 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12234 : Bounds (-162521923 / 250000000) (-650087691 / 1000000000) (Real.log (261 / 500)) := by
  have h := reflection_log_12234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12235_neg : (95577 / 200000000) ≤ -Real.log (500000 / 500239) ∧
    -Real.log (500000 / 500239) ≤ (238943 / 500000000) := by
  have h := checkLog_sound (w := (239 / 1000239)) (n := 12)
    (lo := (95577 / 200000000)) (hi := (238943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500239 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500239 / 500000) = 1/(500000 / 500239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12235 : Bounds (95577 / 200000000) (238943 / 500000000) (Real.log (500239 / 500000)) := by
  have h := reflection_log_12235_neg
  have he : Real.log (500239 / 500000) = -Real.log (500000 / 500239) := by
    rw [show ((500239 / 500000) : ℝ) = ((500000 / 500239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12236_neg : (239057 / 500000000) ≤ -Real.log (499761 / 500000) ∧
    -Real.log (499761 / 500000) ≤ (95623 / 200000000) := by
  have h := checkLog_sound (w := (239 / 999761)) (n := 12)
    (lo := (239057 / 500000000)) (hi := (95623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499761) = 1/(499761 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12236 : Bounds (-95623 / 200000000) (-239057 / 500000000) (Real.log (499761 / 500000)) := by
  have h := reflection_log_12236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12237_neg : (55542169 / 250000000) ≤ -Real.log (500000 / 624391) ∧
    -Real.log (500000 / 624391) ≤ (222168677 / 1000000000) := by
  have h := checkLog_sound (w := (124391 / 1124391)) (n := 12)
    (lo := (55542169 / 250000000)) (hi := (222168677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624391 / 500000) = 1/(500000 / 624391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12237 : Bounds (55542169 / 250000000) (222168677 / 1000000000) (Real.log (624391 / 500000)) := by
  have h := reflection_log_12237_neg
  have he : Real.log (624391 / 500000) = -Real.log (500000 / 624391) := by
    rw [show ((624391 / 500000) : ℝ) = ((500000 / 624391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12238_neg : (286059389 / 1000000000) ≤ -Real.log (375609 / 500000) ∧
    -Real.log (375609 / 500000) ≤ (28605939 / 100000000) := by
  have h := checkLog_sound (w := (124391 / 875609)) (n := 12)
    (lo := (286059389 / 1000000000)) (hi := (28605939 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375609) = 1/(375609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12238 : Bounds (-28605939 / 100000000) (-286059389 / 1000000000) (Real.log (375609 / 500000)) := by
  have h := reflection_log_12238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12239_neg : (222989139 / 1000000000) ≤ -Real.log (1000000 / 1249807) ∧
    -Real.log (1000000 / 1249807) ≤ (11149457 / 50000000) := by
  have h := checkLog_sound (w := (249807 / 2249807)) (n := 12)
    (lo := (222989139 / 1000000000)) (hi := (11149457 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249807 / 1000000) = 1/(1000000 / 1249807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12239 : Bounds (222989139 / 1000000000) (11149457 / 50000000) (Real.log (1249807 / 1000000)) := by
  have h := reflection_log_12239_neg
  have he : Real.log (1249807 / 1000000) = -Real.log (1000000 / 1249807) := by
    rw [show ((1249807 / 1000000) : ℝ) = ((1000000 / 1249807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12240_neg : (71856193 / 250000000) ≤ -Real.log (750193 / 1000000) ∧
    -Real.log (750193 / 1000000) ≤ (287424773 / 1000000000) := by
  have h := checkLog_sound (w := (249807 / 1750193)) (n := 12)
    (lo := (71856193 / 250000000)) (hi := (287424773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750193) = 1/(750193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12240 : Bounds (-287424773 / 1000000000) (-71856193 / 250000000) (Real.log (750193 / 1000000)) := by
  have h := reflection_log_12240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12241_neg : (4027227 / 62500000) ≤ -Real.log (937596462751 / 1000000000000) ∧
    -Real.log (937596462751 / 1000000000000) ≤ (64435633 / 1000000000) := by
  have h := checkLog_sound (w := (62403537249 / 1937596462751)) (n := 12)
    (lo := (4027227 / 62500000)) (hi := (64435633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 937596462751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 937596462751) = 1/(937596462751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12241 : Bounds (-64435633 / 1000000000) (-4027227 / 62500000) (Real.log (937596462751 / 1000000000000)) := by
  have h := reflection_log_12241_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12242_neg : (63890713 / 1000000000) ≤ -Real.log (234526879119 / 250000000000) ∧
    -Real.log (234526879119 / 250000000000) ≤ (31945357 / 500000000) := by
  have h := checkLog_sound (w := (15473120881 / 484526879119)) (n := 12)
    (lo := (63890713 / 1000000000)) (hi := (31945357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 234526879119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 234526879119) = 1/(234526879119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12242 : Bounds (-31945357 / 500000000) (-63890713 / 1000000000) (Real.log (234526879119 / 250000000000)) := by
  have h := reflection_log_12242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12243_neg : (101645613 / 200000000) ≤ -Real.log (500000000000 / 831171510799) ∧
    -Real.log (500000000000 / 831171510799) ≤ (254114033 / 500000000) := by
  have h := checkLog_sound (w := (331171510799 / 1331171510799)) (n := 12)
    (lo := (101645613 / 200000000)) (hi := (254114033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831171510799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831171510799 / 500000000000) = 1/(500000000000 / 831171510799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12243 : Bounds (101645613 / 200000000) (254114033 / 500000000) (Real.log (831171510799 / 500000000000)) := by
  have h := reflection_log_12243_neg
  have he : Real.log (831171510799 / 500000000000) = -Real.log (500000000000 / 831171510799) := by
    rw [show ((831171510799 / 500000000000) : ℝ) = ((500000000000 / 831171510799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12244_neg : (510413911 / 1000000000) ≤ -Real.log (250000000000 / 416495155247) ∧
    -Real.log (250000000000 / 416495155247) ≤ (63801739 / 125000000) := by
  have h := checkLog_sound (w := (166495155247 / 666495155247)) (n := 12)
    (lo := (510413911 / 1000000000)) (hi := (63801739 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416495155247 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(416495155247 / 250000000000) = 1/(250000000000 / 416495155247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12244 : Bounds (510413911 / 1000000000) (63801739 / 125000000) (Real.log (416495155247 / 250000000000)) := by
  have h := reflection_log_12244_neg
  have he : Real.log (416495155247 / 250000000000) = -Real.log (250000000000 / 416495155247) := by
    rw [show ((416495155247 / 250000000000) : ℝ) = ((250000000000 / 416495155247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12245_neg : (1038186817 / 1000000000) ≤ -Real.log (500000000000 / 1412045889101) ∧
    -Real.log (500000000000 / 1412045889101) ≤ (1038186819 / 1000000000) := by
  have h := checkLog_sound (w := (412045889101 / 2412045889101)) (n := 12)
    (lo := (345039637 / 1000000000)) (hi := (172519819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1412045889101 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1412045889101 / 1000000000000) = 1/(500000000000 / 1412045889101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12245 : Bounds (1038186817 / 1000000000) (1038186819 / 1000000000) (Real.log (1412045889101 / 500000000000)) := by
  have h := reflection_log_12245_neg
  have he : Real.log (1412045889101 / 500000000000) = -Real.log (500000000000 / 1412045889101) := by
    rw [show ((1412045889101 / 500000000000) : ℝ) = ((500000000000 / 1412045889101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12246_neg : (1040777513 / 1000000000) ≤ -Real.log (500000000000 / 1415708812261) ∧
    -Real.log (500000000000 / 1415708812261) ≤ (208155503 / 200000000) := by
  have h := checkLog_sound (w := (415708812261 / 2415708812261)) (n := 12)
    (lo := (347630333 / 1000000000)) (hi := (173815167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415708812261 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1415708812261 / 1000000000000) = 1/(500000000000 / 1415708812261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12246 : Bounds (1040777513 / 1000000000) (208155503 / 200000000) (Real.log (1415708812261 / 500000000000)) := by
  have h := reflection_log_12246_neg
  have he : Real.log (1415708812261 / 500000000000) = -Real.log (500000000000 / 1415708812261) := by
    rw [show ((1415708812261 / 500000000000) : ℝ) = ((500000000000 / 1415708812261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12247_neg : (391366183 / 1000000000) ≤ -Real.log (1000 / 1479) ∧
    -Real.log (1000 / 1479) ≤ (48920773 / 125000000) := by
  have h := checkLog_sound (w := (479 / 2479)) (n := 12)
    (lo := (391366183 / 1000000000)) (hi := (48920773 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1479 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1479 / 1000) = 1/(1000 / 1479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12247 : Bounds (391366183 / 1000000000) (48920773 / 125000000) (Real.log (1479 / 1000)) := by
  have h := reflection_log_12247_neg
  have he : Real.log (1479 / 1000) = -Real.log (1000 / 1479) := by
    rw [show ((1479 / 1000) : ℝ) = ((1000 / 1479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12248_neg : (652005237 / 1000000000) ≤ -Real.log (521 / 1000) ∧
    -Real.log (521 / 1000) ≤ (326002619 / 500000000) := by
  have h := checkLog_sound (w := (479 / 1521)) (n := 12)
    (lo := (652005237 / 1000000000)) (hi := (326002619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 521) = 1/(521 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12248 : Bounds (-326002619 / 500000000) (-652005237 / 1000000000) (Real.log (521 / 1000)) := by
  have h := reflection_log_12248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12249_neg : (95777 / 200000000) ≤ -Real.log (1000000 / 1000479) ∧
    -Real.log (1000000 / 1000479) ≤ (239443 / 500000000) := by
  have h := checkLog_sound (w := (479 / 2000479)) (n := 12)
    (lo := (95777 / 200000000)) (hi := (239443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000479 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000479 / 1000000) = 1/(1000000 / 1000479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12249 : Bounds (95777 / 200000000) (239443 / 500000000) (Real.log (1000479 / 1000000)) := by
  have h := reflection_log_12249_neg
  have he : Real.log (1000479 / 1000000) = -Real.log (1000000 / 1000479) := by
    rw [show ((1000479 / 1000000) : ℝ) = ((1000000 / 1000479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12250_neg : (239557 / 500000000) ≤ -Real.log (999521 / 1000000) ∧
    -Real.log (999521 / 1000000) ≤ (95823 / 200000000) := by
  have h := checkLog_sound (w := (479 / 1999521)) (n := 12)
    (lo := (239557 / 500000000)) (hi := (95823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999521) = 1/(999521 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12250 : Bounds (-95823 / 200000000) (-239557 / 500000000) (Real.log (999521 / 1000000)) := by
  have h := reflection_log_12250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12251_neg : (27828027 / 125000000) ≤ -Real.log (1000000 / 1249351) ∧
    -Real.log (1000000 / 1249351) ≤ (222624217 / 1000000000) := by
  have h := checkLog_sound (w := (249351 / 2249351)) (n := 12)
    (lo := (27828027 / 125000000)) (hi := (222624217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249351 / 1000000) = 1/(1000000 / 1249351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12251 : Bounds (27828027 / 125000000) (222624217 / 1000000000) (Real.log (1249351 / 1000000)) := by
  have h := reflection_log_12251_neg
  have he : Real.log (1249351 / 1000000) = -Real.log (1000000 / 1249351) := by
    rw [show ((1249351 / 1000000) : ℝ) = ((1000000 / 1249351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12252_neg : (286817113 / 1000000000) ≤ -Real.log (750649 / 1000000) ∧
    -Real.log (750649 / 1000000) ≤ (143408557 / 500000000) := by
  have h := checkLog_sound (w := (249351 / 1750649)) (n := 12)
    (lo := (286817113 / 1000000000)) (hi := (143408557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750649) = 1/(750649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12252 : Bounds (-143408557 / 500000000) (-286817113 / 1000000000) (Real.log (750649 / 1000000)) := by
  have h := reflection_log_12252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12253_neg : (44689181 / 200000000) ≤ -Real.log (500000 / 625189) ∧
    -Real.log (500000 / 625189) ≤ (111722953 / 500000000) := by
  have h := checkLog_sound (w := (125189 / 1125189)) (n := 12)
    (lo := (44689181 / 200000000)) (hi := (111722953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625189 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625189 / 500000) = 1/(500000 / 625189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12253 : Bounds (44689181 / 200000000) (111722953 / 500000000) (Real.log (625189 / 500000)) := by
  have h := reflection_log_12253_neg
  have he : Real.log (625189 / 500000) = -Real.log (500000 / 625189) := by
    rw [show ((625189 / 500000) : ℝ) = ((500000 / 625189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12254_neg : (288186199 / 1000000000) ≤ -Real.log (374811 / 500000) ∧
    -Real.log (374811 / 500000) ≤ (1440931 / 5000000) := by
  have h := checkLog_sound (w := (125189 / 874811)) (n := 12)
    (lo := (288186199 / 1000000000)) (hi := (1440931 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 374811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 374811) = 1/(374811 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12254 : Bounds (-1440931 / 5000000) (-288186199 / 1000000000) (Real.log (374811 / 500000)) := by
  have h := reflection_log_12254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12255_neg : (64740293 / 1000000000) ≤ -Real.log (234327714279 / 250000000000) ∧
    -Real.log (234327714279 / 250000000000) ≤ (32370147 / 500000000) := by
  have h := checkLog_sound (w := (15672285721 / 484327714279)) (n := 12)
    (lo := (64740293 / 1000000000)) (hi := (32370147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 234327714279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 234327714279) = 1/(234327714279 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12255 : Bounds (-32370147 / 500000000) (-64740293 / 1000000000) (Real.log (234327714279 / 250000000000)) := by
  have h := reflection_log_12255_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12256_neg : (501507 / 7812500) ≤ -Real.log (937824078799 / 1000000000000) ∧
    -Real.log (937824078799 / 1000000000000) ≤ (64192897 / 1000000000) := by
  have h := checkLog_sound (w := (62175921201 / 1937824078799)) (n := 12)
    (lo := (501507 / 7812500)) (hi := (64192897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 937824078799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 937824078799) = 1/(937824078799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12256 : Bounds (-64192897 / 1000000000) (-501507 / 7812500) (Real.log (937824078799 / 1000000000000)) := by
  have h := reflection_log_12256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12257_neg : (509441329 / 1000000000) ≤ -Real.log (250000000000 / 416090276547) ∧
    -Real.log (250000000000 / 416090276547) ≤ (50944133 / 100000000) := by
  have h := checkLog_sound (w := (166090276547 / 666090276547)) (n := 12)
    (lo := (509441329 / 1000000000)) (hi := (50944133 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416090276547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(416090276547 / 250000000000) = 1/(250000000000 / 416090276547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12257 : Bounds (509441329 / 1000000000) (50944133 / 100000000) (Real.log (416090276547 / 250000000000)) := by
  have h := reflection_log_12257_neg
  have he : Real.log (416090276547 / 250000000000) = -Real.log (250000000000 / 416090276547) := by
    rw [show ((416090276547 / 250000000000) : ℝ) = ((250000000000 / 416090276547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12258_neg : (102326421 / 200000000) ≤ -Real.log (500000000000 / 834005672193) ∧
    -Real.log (500000000000 / 834005672193) ≤ (255816053 / 500000000) := by
  have h := checkLog_sound (w := (334005672193 / 1334005672193)) (n := 12)
    (lo := (102326421 / 200000000)) (hi := (255816053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834005672193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(834005672193 / 500000000000) = 1/(500000000000 / 834005672193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12258 : Bounds (102326421 / 200000000) (255816053 / 500000000) (Real.log (834005672193 / 500000000000)) := by
  have h := reflection_log_12258_neg
  have he : Real.log (834005672193 / 500000000000) = -Real.log (500000000000 / 834005672193) := by
    rw [show ((834005672193 / 500000000000) : ℝ) = ((500000000000 / 834005672193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12259_neg : (1040777513 / 1000000000) ≤ -Real.log (25000000000 / 70785440613) ∧
    -Real.log (25000000000 / 70785440613) ≤ (208155503 / 200000000) := by
  have h := checkLog_sound (w := (20785440613 / 120785440613)) (n := 12)
    (lo := (347630333 / 1000000000)) (hi := (173815167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70785440613 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(70785440613 / 50000000000) = 1/(25000000000 / 70785440613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12259 : Bounds (1040777513 / 1000000000) (208155503 / 200000000) (Real.log (70785440613 / 25000000000)) := by
  have h := reflection_log_12259_neg
  have he : Real.log (70785440613 / 25000000000) = -Real.log (25000000000 / 70785440613) := by
    rw [show ((70785440613 / 25000000000) : ℝ) = ((25000000000 / 70785440613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12260_neg : (52168571 / 50000000) ≤ -Real.log (250000000000 / 709692898273) ∧
    -Real.log (250000000000 / 709692898273) ≤ (521685711 / 500000000) := by
  have h := checkLog_sound (w := (209692898273 / 1209692898273)) (n := 12)
    (lo := (4377803 / 12500000)) (hi := (350224241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709692898273 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(709692898273 / 500000000000) = 1/(250000000000 / 709692898273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12260 : Bounds (52168571 / 50000000) (521685711 / 500000000) (Real.log (709692898273 / 250000000000)) := by
  have h := reflection_log_12260_neg
  have he : Real.log (709692898273 / 250000000000) = -Real.log (250000000000 / 709692898273) := by
    rw [show ((709692898273 / 250000000000) : ℝ) = ((250000000000 / 709692898273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12261_neg : (392042087 / 1000000000) ≤ -Real.log (25 / 37) ∧
    -Real.log (25 / 37) ≤ (49005261 / 125000000) := by
  have h := checkLog_sound (w := (6 / 31)) (n := 12)
    (lo := (392042087 / 1000000000)) (hi := (49005261 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37 / 25) = 1/(25 / 37) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12261 : Bounds (392042087 / 1000000000) (49005261 / 125000000) (Real.log (37 / 25)) := by
  have h := reflection_log_12261_neg
  have he : Real.log (37 / 25) = -Real.log (25 / 37) := by
    rw [show ((37 / 25) : ℝ) = ((25 / 37) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12262_neg : (653926467 / 1000000000) ≤ -Real.log (13 / 25) ∧
    -Real.log (13 / 25) ≤ (163481617 / 250000000) := by
  have h := checkLog_sound (w := (6 / 19)) (n := 12)
    (lo := (653926467 / 1000000000)) (hi := (163481617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 13) = 1/(13 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12262 : Bounds (-163481617 / 250000000) (-653926467 / 1000000000) (Real.log (13 / 25)) := by
  have h := reflection_log_12262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12263_neg : (119971 / 250000000) ≤ -Real.log (6250 / 6253) ∧
    -Real.log (6250 / 6253) ≤ (95977 / 200000000) := by
  have h := checkLog_sound (w := (3 / 12503)) (n := 12)
    (lo := (119971 / 250000000)) (hi := (95977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6253 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6253 / 6250) = 1/(6250 / 6253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12263 : Bounds (119971 / 250000000) (95977 / 200000000) (Real.log (6253 / 6250)) := by
  have h := reflection_log_12263_neg
  have he : Real.log (6253 / 6250) = -Real.log (6250 / 6253) := by
    rw [show ((6253 / 6250) : ℝ) = ((6250 / 6253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12264_neg : (96023 / 200000000) ≤ -Real.log (6247 / 6250) ∧
    -Real.log (6247 / 6250) ≤ (120029 / 250000000) := by
  have h := checkLog_sound (w := (3 / 12497)) (n := 12)
    (lo := (96023 / 200000000)) (hi := (120029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 6247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 6247) = 1/(6247 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12264 : Bounds (-120029 / 250000000) (-96023 / 200000000) (Real.log (6247 / 6250)) := by
  have h := reflection_log_12264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12265_neg : (223080349 / 1000000000) ≤ -Real.log (1000000 / 1249921) ∧
    -Real.log (1000000 / 1249921) ≤ (4461607 / 20000000) := by
  have h := checkLog_sound (w := (249921 / 2249921)) (n := 12)
    (lo := (223080349 / 1000000000)) (hi := (4461607 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249921 / 1000000) = 1/(1000000 / 1249921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12265 : Bounds (223080349 / 1000000000) (4461607 / 20000000) (Real.log (1249921 / 1000000)) := by
  have h := reflection_log_12265_neg
  have he : Real.log (1249921 / 1000000) = -Real.log (1000000 / 1249921) := by
    rw [show ((1249921 / 1000000) : ℝ) = ((1000000 / 1249921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12266_neg : (35947093 / 125000000) ≤ -Real.log (750079 / 1000000) ∧
    -Real.log (750079 / 1000000) ≤ (57515349 / 200000000) := by
  have h := checkLog_sound (w := (249921 / 1750079)) (n := 12)
    (lo := (35947093 / 125000000)) (hi := (57515349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750079) = 1/(750079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12266 : Bounds (-57515349 / 200000000) (-35947093 / 125000000) (Real.log (750079 / 1000000)) := by
  have h := reflection_log_12266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12267_neg : (223901663 / 1000000000) ≤ -Real.log (250000 / 312737) ∧
    -Real.log (250000 / 312737) ≤ (6996927 / 31250000) := by
  have h := checkLog_sound (w := (62737 / 562737)) (n := 12)
    (lo := (223901663 / 1000000000)) (hi := (6996927 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312737 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312737 / 250000) = 1/(250000 / 312737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12267 : Bounds (223901663 / 1000000000) (6996927 / 31250000) (Real.log (312737 / 250000)) := by
  have h := reflection_log_12267_neg
  have he : Real.log (312737 / 250000) = -Real.log (250000 / 312737) := by
    rw [show ((312737 / 250000) : ℝ) = ((250000 / 312737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12268_neg : (288946871 / 1000000000) ≤ -Real.log (187263 / 250000) ∧
    -Real.log (187263 / 250000) ≤ (36118359 / 125000000) := by
  have h := checkLog_sound (w := (62737 / 437263)) (n := 12)
    (lo := (288946871 / 1000000000)) (hi := (36118359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187263) = 1/(187263 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12268 : Bounds (-36118359 / 125000000) (-288946871 / 1000000000) (Real.log (187263 / 250000)) := by
  have h := reflection_log_12268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12269_neg : (8130651 / 125000000) ≤ -Real.log (58564068831 / 62500000000) ∧
    -Real.log (58564068831 / 62500000000) ≤ (65045209 / 1000000000) := by
  have h := checkLog_sound (w := (3935931169 / 121064068831)) (n := 12)
    (lo := (8130651 / 125000000)) (hi := (65045209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58564068831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58564068831) = 1/(58564068831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12269 : Bounds (-65045209 / 1000000000) (-8130651 / 125000000) (Real.log (58564068831 / 62500000000)) := by
  have h := reflection_log_12269_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12270_neg : (12899279 / 200000000) ≤ -Real.log (937539493759 / 1000000000000) ∧
    -Real.log (937539493759 / 1000000000000) ≤ (16124099 / 250000000) := by
  have h := checkLog_sound (w := (62460506241 / 1937539493759)) (n := 12)
    (lo := (12899279 / 200000000)) (hi := (16124099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 937539493759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 937539493759) = 1/(937539493759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12270 : Bounds (-16124099 / 250000000) (-12899279 / 200000000) (Real.log (937539493759 / 1000000000000)) := by
  have h := reflection_log_12270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12271_neg : (510657093 / 1000000000) ≤ -Real.log (97656250 / 162732989) ∧
    -Real.log (97656250 / 162732989) ≤ (255328547 / 500000000) := by
  have h := checkLog_sound (w := (65076739 / 260389239)) (n := 12)
    (lo := (510657093 / 1000000000)) (hi := (255328547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162732989 / 97656250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162732989 / 97656250) = 1/(97656250 / 162732989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12271 : Bounds (510657093 / 1000000000) (255328547 / 500000000) (Real.log (162732989 / 97656250)) := by
  have h := reflection_log_12271_neg
  have he : Real.log (162732989 / 97656250) = -Real.log (97656250 / 162732989) := by
    rw [show ((162732989 / 97656250) : ℝ) = ((97656250 / 162732989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12272_neg : (102569707 / 200000000) ≤ -Real.log (4000000000 / 6680166397) ∧
    -Real.log (4000000000 / 6680166397) ≤ (64106067 / 125000000) := by
  have h := checkLog_sound (w := (2680166397 / 10680166397)) (n := 12)
    (lo := (102569707 / 200000000)) (hi := (64106067 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6680166397 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6680166397 / 4000000000) = 1/(4000000000 / 6680166397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12272 : Bounds (102569707 / 200000000) (64106067 / 125000000) (Real.log (6680166397 / 4000000000)) := by
  have h := reflection_log_12272_neg
  have he : Real.log (6680166397 / 4000000000) = -Real.log (4000000000 / 6680166397) := by
    rw [show ((6680166397 / 4000000000) : ℝ) = ((4000000000 / 6680166397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12273_neg : (52168571 / 50000000) ≤ -Real.log (100000000000 / 283877159309) ∧
    -Real.log (100000000000 / 283877159309) ≤ (521685711 / 500000000) := by
  have h := checkLog_sound (w := (83877159309 / 483877159309)) (n := 12)
    (lo := (4377803 / 12500000)) (hi := (350224241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283877159309 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(283877159309 / 200000000000) = 1/(100000000000 / 283877159309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12273 : Bounds (52168571 / 50000000) (521685711 / 500000000) (Real.log (283877159309 / 100000000000)) := by
  have h := reflection_log_12273_neg
  have he : Real.log (283877159309 / 100000000000) = -Real.log (100000000000 / 283877159309) := by
    rw [show ((283877159309 / 100000000000) : ℝ) = ((100000000000 / 283877159309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12274_neg : (522984277 / 500000000) ≤ -Real.log (500000000000 / 1423076923077) ∧
    -Real.log (500000000000 / 1423076923077) ≤ (261492139 / 250000000) := by
  have h := checkLog_sound (w := (423076923077 / 2423076923077)) (n := 12)
    (lo := (176410687 / 500000000)) (hi := (2822571 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1423076923077 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1423076923077 / 1000000000000) = 1/(500000000000 / 1423076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12274 : Bounds (522984277 / 500000000) (261492139 / 250000000) (Real.log (1423076923077 / 500000000000)) := by
  have h := reflection_log_12274_neg
  have he : Real.log (1423076923077 / 500000000000) = -Real.log (500000000000 / 1423076923077) := by
    rw [show ((1423076923077 / 500000000000) : ℝ) = ((500000000000 / 1423076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12275_neg : (78543507 / 200000000) ≤ -Real.log (1000 / 1481) ∧
    -Real.log (1000 / 1481) ≤ (12272423 / 31250000) := by
  have h := checkLog_sound (w := (481 / 2481)) (n := 12)
    (lo := (78543507 / 200000000)) (hi := (12272423 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1481 / 1000) = 1/(1000 / 1481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12275 : Bounds (78543507 / 200000000) (12272423 / 31250000) (Real.log (1481 / 1000)) := by
  have h := reflection_log_12275_neg
  have he : Real.log (1481 / 1000) = -Real.log (1000 / 1481) := by
    rw [show ((1481 / 1000) : ℝ) = ((1000 / 1481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12276_neg : (131170279 / 200000000) ≤ -Real.log (519 / 1000) ∧
    -Real.log (519 / 1000) ≤ (163962849 / 250000000) := by
  have h := checkLog_sound (w := (481 / 1519)) (n := 12)
    (lo := (131170279 / 200000000)) (hi := (163962849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 519) = 1/(519 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12276 : Bounds (-163962849 / 250000000) (-131170279 / 200000000) (Real.log (519 / 1000)) := by
  have h := reflection_log_12276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12277_neg : (120221 / 250000000) ≤ -Real.log (1000000 / 1000481) ∧
    -Real.log (1000000 / 1000481) ≤ (96177 / 200000000) := by
  have h := checkLog_sound (w := (481 / 2000481)) (n := 12)
    (lo := (120221 / 250000000)) (hi := (96177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000481 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000481 / 1000000) = 1/(1000000 / 1000481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12277 : Bounds (120221 / 250000000) (96177 / 200000000) (Real.log (1000481 / 1000000)) := by
  have h := reflection_log_12277_neg
  have he : Real.log (1000481 / 1000000) = -Real.log (1000000 / 1000481) := by
    rw [show ((1000481 / 1000000) : ℝ) = ((1000000 / 1000481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12278_neg : (96223 / 200000000) ≤ -Real.log (999519 / 1000000) ∧
    -Real.log (999519 / 1000000) ≤ (120279 / 250000000) := by
  have h := checkLog_sound (w := (481 / 1999519)) (n := 12)
    (lo := (96223 / 200000000)) (hi := (120279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999519) = 1/(999519 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12278 : Bounds (-120279 / 250000000) (-96223 / 200000000) (Real.log (999519 / 1000000)) := by
  have h := reflection_log_12278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12279_neg : (111767737 / 500000000) ≤ -Real.log (100000 / 125049) ∧
    -Real.log (100000 / 125049) ≤ (8941419 / 40000000) := by
  have h := checkLog_sound (w := (25049 / 225049)) (n := 12)
    (lo := (111767737 / 500000000)) (hi := (8941419 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125049 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125049 / 100000) = 1/(100000 / 125049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12279 : Bounds (111767737 / 500000000) (8941419 / 40000000) (Real.log (125049 / 100000)) := by
  have h := reflection_log_12279_neg
  have he : Real.log (125049 / 100000) = -Real.log (100000 / 125049) := by
    rw [show ((125049 / 100000) : ℝ) = ((100000 / 125049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12280_neg : (288335619 / 1000000000) ≤ -Real.log (74951 / 100000) ∧
    -Real.log (74951 / 100000) ≤ (14416781 / 50000000) := by
  have h := checkLog_sound (w := (25049 / 174951)) (n := 12)
    (lo := (288335619 / 1000000000)) (hi := (14416781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74951) = 1/(74951 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12280 : Bounds (-14416781 / 50000000) (-288335619 / 1000000000) (Real.log (74951 / 100000)) := by
  have h := reflection_log_12280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12281_neg : (56089703 / 250000000) ≤ -Real.log (3125 / 3911) ∧
    -Real.log (3125 / 3911) ≤ (224358813 / 1000000000) := by
  have h := checkLog_sound (w := (393 / 3518)) (n := 12)
    (lo := (56089703 / 250000000)) (hi := (224358813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3911 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3911 / 3125) = 1/(3125 / 3911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12281 : Bounds (56089703 / 250000000) (224358813 / 1000000000) (Real.log (3911 / 3125)) := by
  have h := reflection_log_12281_neg
  have he : Real.log (3911 / 3125) = -Real.log (3125 / 3911) := by
    rw [show ((3911 / 3125) : ℝ) = ((3125 / 3911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12282_neg : (57942159 / 200000000) ≤ -Real.log (2339 / 3125) ∧
    -Real.log (2339 / 3125) ≤ (72427699 / 250000000) := by
  have h := checkLog_sound (w := (393 / 2732)) (n := 12)
    (lo := (57942159 / 200000000)) (hi := (72427699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2339) = 1/(2339 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12282 : Bounds (-72427699 / 250000000) (-57942159 / 200000000) (Real.log (2339 / 3125)) := by
  have h := reflection_log_12282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12283_neg : (65351983 / 1000000000) ≤ -Real.log (9147829 / 9765625) ∧
    -Real.log (9147829 / 9765625) ≤ (4084499 / 62500000) := by
  have h := checkLog_sound (w := (308898 / 9456727)) (n := 12)
    (lo := (65351983 / 1000000000)) (hi := (4084499 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9147829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9147829) = 1/(9147829 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12283 : Bounds (-4084499 / 62500000) (-65351983 / 1000000000) (Real.log (9147829 / 9765625)) := by
  have h := reflection_log_12283_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12284_neg : (4050009 / 62500000) ≤ -Real.log (9372547599 / 10000000000) ∧
    -Real.log (9372547599 / 10000000000) ≤ (12960029 / 200000000) := by
  have h := checkLog_sound (w := (627452401 / 19372547599)) (n := 12)
    (lo := (4050009 / 62500000)) (hi := (12960029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9372547599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9372547599) = 1/(9372547599 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12284 : Bounds (-12960029 / 200000000) (-4050009 / 62500000) (Real.log (9372547599 / 10000000000)) := by
  have h := reflection_log_12284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12285_neg : (511871093 / 1000000000) ≤ -Real.log (250000000000 / 417102506971) ∧
    -Real.log (250000000000 / 417102506971) ≤ (255935547 / 500000000) := by
  have h := checkLog_sound (w := (167102506971 / 667102506971)) (n := 12)
    (lo := (511871093 / 1000000000)) (hi := (255935547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417102506971 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417102506971 / 250000000000) = 1/(250000000000 / 417102506971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12285 : Bounds (511871093 / 1000000000) (255935547 / 500000000) (Real.log (417102506971 / 250000000000)) := by
  have h := reflection_log_12285_neg
  have he : Real.log (417102506971 / 250000000000) = -Real.log (250000000000 / 417102506971) := by
    rw [show ((417102506971 / 250000000000) : ℝ) = ((250000000000 / 417102506971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12286_neg : (64258701 / 125000000) ≤ -Real.log (500000000000 / 836041043181) ∧
    -Real.log (500000000000 / 836041043181) ≤ (514069609 / 1000000000) := by
  have h := checkLog_sound (w := (336041043181 / 1336041043181)) (n := 12)
    (lo := (64258701 / 125000000)) (hi := (514069609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((836041043181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(836041043181 / 500000000000) = 1/(500000000000 / 836041043181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12286 : Bounds (64258701 / 125000000) (514069609 / 1000000000) (Real.log (836041043181 / 500000000000)) := by
  have h := reflection_log_12286_neg
  have he : Real.log (836041043181 / 500000000000) = -Real.log (500000000000 / 836041043181) := by
    rw [show ((836041043181 / 500000000000) : ℝ) = ((500000000000 / 836041043181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12287_neg : (522984277 / 500000000) ≤ -Real.log (125000000000 / 355769230769) ∧
    -Real.log (125000000000 / 355769230769) ≤ (261492139 / 250000000) := by
  have h := checkLog_sound (w := (105769230769 / 605769230769)) (n := 12)
    (lo := (176410687 / 500000000)) (hi := (2822571 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355769230769 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(355769230769 / 250000000000) = 1/(125000000000 / 355769230769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12287 : Bounds (522984277 / 500000000) (261492139 / 250000000) (Real.log (355769230769 / 125000000000)) := by
  have h := reflection_log_12287_neg
  have he : Real.log (355769230769 / 125000000000) = -Real.log (125000000000 / 355769230769) := by
    rw [show ((355769230769 / 125000000000) : ℝ) = ((125000000000 / 355769230769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0192 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12288_neg : (104856893 / 100000000) ≤ -Real.log (125000000000 / 356695568401) ∧
    -Real.log (125000000000 / 356695568401) ≤ (262142233 / 250000000) := by
  have h := checkLog_sound (w := (106695568401 / 606695568401)) (n := 12)
    (lo := (1421687 / 4000000)) (hi := (355421751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356695568401 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(356695568401 / 250000000000) = 1/(125000000000 / 356695568401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12288 : Bounds (104856893 / 100000000) (262142233 / 250000000) (Real.log (356695568401 / 125000000000)) := by
  have h := reflection_log_12288_neg
  have he : Real.log (356695568401 / 125000000000) = -Real.log (125000000000 / 356695568401) := by
    rw [show ((356695568401 / 125000000000) : ℝ) = ((125000000000 / 356695568401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12289_neg : (196696263 / 500000000) ≤ -Real.log (500 / 741) ∧
    -Real.log (500 / 741) ≤ (393392527 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1241)) (n := 12)
    (lo := (196696263 / 500000000)) (hi := (393392527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741 / 500) = 1/(500 / 741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12289 : Bounds (196696263 / 500000000) (393392527 / 1000000000) (Real.log (741 / 500)) := by
  have h := reflection_log_12289_neg
  have he : Real.log (741 / 500) = -Real.log (500 / 741) := by
    rw [show ((741 / 500) : ℝ) = ((500 / 741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12290_neg : (164445009 / 250000000) ≤ -Real.log (259 / 500) ∧
    -Real.log (259 / 500) ≤ (657780037 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 759)) (n := 12)
    (lo := (164445009 / 250000000)) (hi := (657780037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 259) = 1/(259 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12290 : Bounds (-657780037 / 1000000000) (-164445009 / 250000000) (Real.log (259 / 500)) := by
  have h := reflection_log_12290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12291_neg : (481883 / 1000000000) ≤ -Real.log (500000 / 500241) ∧
    -Real.log (500000 / 500241) ≤ (120471 / 250000000) := by
  have h := checkLog_sound (w := (241 / 1000241)) (n := 12)
    (lo := (481883 / 1000000000)) (hi := (120471 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500241 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500241 / 500000) = 1/(500000 / 500241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12291 : Bounds (481883 / 1000000000) (120471 / 250000000) (Real.log (500241 / 500000)) := by
  have h := reflection_log_12291_neg
  have he : Real.log (500241 / 500000) = -Real.log (500000 / 500241) := by
    rw [show ((500241 / 500000) : ℝ) = ((500000 / 500241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12292_neg : (120529 / 250000000) ≤ -Real.log (499759 / 500000) ∧
    -Real.log (499759 / 500000) ≤ (482117 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 999759)) (n := 12)
    (lo := (120529 / 250000000)) (hi := (482117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499759) = 1/(499759 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12292 : Bounds (-482117 / 1000000000) (-120529 / 250000000) (Real.log (499759 / 500000)) := by
  have h := reflection_log_12292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12293_neg : (223991991 / 1000000000) ≤ -Real.log (1000000 / 1251061) ∧
    -Real.log (1000000 / 1251061) ≤ (27998999 / 125000000) := by
  have h := checkLog_sound (w := (251061 / 2251061)) (n := 12)
    (lo := (223991991 / 1000000000)) (hi := (27998999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251061 / 1000000) = 1/(1000000 / 1251061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12293 : Bounds (223991991 / 1000000000) (27998999 / 125000000) (Real.log (1251061 / 1000000)) := by
  have h := reflection_log_12293_neg
  have he : Real.log (1251061 / 1000000) = -Real.log (1000000 / 1251061) := by
    rw [show ((1251061 / 1000000) : ℝ) = ((1000000 / 1251061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12294_neg : (14454887 / 50000000) ≤ -Real.log (748939 / 1000000) ∧
    -Real.log (748939 / 1000000) ≤ (289097741 / 1000000000) := by
  have h := checkLog_sound (w := (251061 / 1748939)) (n := 12)
    (lo := (14454887 / 50000000)) (hi := (289097741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748939) = 1/(748939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12294 : Bounds (-289097741 / 1000000000) (-14454887 / 50000000) (Real.log (748939 / 1000000)) := by
  have h := reflection_log_12294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12295_neg : (224814953 / 1000000000) ≤ -Real.log (1000000 / 1252091) ∧
    -Real.log (1000000 / 1252091) ≤ (112407477 / 500000000) := by
  have h := checkLog_sound (w := (252091 / 2252091)) (n := 12)
    (lo := (224814953 / 1000000000)) (hi := (112407477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252091 / 1000000) = 1/(1000000 / 1252091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12295 : Bounds (224814953 / 1000000000) (112407477 / 500000000) (Real.log (1252091 / 1000000)) := by
  have h := reflection_log_12295_neg
  have he : Real.log (1252091 / 1000000) = -Real.log (1000000 / 1252091) := by
    rw [show ((1252091 / 1000000) : ℝ) = ((1000000 / 1252091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12296_neg : (145236983 / 500000000) ≤ -Real.log (747909 / 1000000) ∧
    -Real.log (747909 / 1000000) ≤ (290473967 / 1000000000) := by
  have h := checkLog_sound (w := (252091 / 1747909)) (n := 12)
    (lo := (145236983 / 500000000)) (hi := (290473967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747909) = 1/(747909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12296 : Bounds (-290473967 / 1000000000) (-145236983 / 500000000) (Real.log (747909 / 1000000)) := by
  have h := reflection_log_12296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12297_neg : (16414753 / 250000000) ≤ -Real.log (936450127719 / 1000000000000) ∧
    -Real.log (936450127719 / 1000000000000) ≤ (65659013 / 1000000000) := by
  have h := checkLog_sound (w := (63549872281 / 1936450127719)) (n := 12)
    (lo := (16414753 / 250000000)) (hi := (65659013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 936450127719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 936450127719) = 1/(936450127719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12297 : Bounds (-65659013 / 1000000000) (-16414753 / 250000000) (Real.log (936450127719 / 1000000000000)) := by
  have h := reflection_log_12297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12298_neg : (65105749 / 1000000000) ≤ -Real.log (936968374279 / 1000000000000) ∧
    -Real.log (936968374279 / 1000000000000) ≤ (260423 / 4000000) := by
  have h := checkLog_sound (w := (63031625721 / 1936968374279)) (n := 12)
    (lo := (65105749 / 1000000000)) (hi := (260423 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 936968374279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 936968374279) = 1/(936968374279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12298 : Bounds (-260423 / 4000000) (-65105749 / 1000000000) (Real.log (936968374279 / 1000000000000)) := by
  have h := reflection_log_12298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12299_neg : (513089731 / 1000000000) ≤ -Real.log (500000000000 / 835222227711) ∧
    -Real.log (500000000000 / 835222227711) ≤ (128272433 / 250000000) := by
  have h := checkLog_sound (w := (335222227711 / 1335222227711)) (n := 12)
    (lo := (513089731 / 1000000000)) (hi := (128272433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835222227711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835222227711 / 500000000000) = 1/(500000000000 / 835222227711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12299 : Bounds (513089731 / 1000000000) (128272433 / 250000000) (Real.log (835222227711 / 500000000000)) := by
  have h := reflection_log_12299_neg
  have he : Real.log (835222227711 / 500000000000) = -Real.log (500000000000 / 835222227711) := by
    rw [show ((835222227711 / 500000000000) : ℝ) = ((500000000000 / 835222227711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12300_neg : (515288919 / 1000000000) ≤ -Real.log (31250000000 / 52316316223) ∧
    -Real.log (31250000000 / 52316316223) ≤ (12882223 / 25000000) := by
  have h := checkLog_sound (w := (21066316223 / 83566316223)) (n := 12)
    (lo := (515288919 / 1000000000)) (hi := (12882223 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52316316223 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52316316223 / 31250000000) = 1/(31250000000 / 52316316223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12300 : Bounds (515288919 / 1000000000) (12882223 / 25000000) (Real.log (52316316223 / 31250000000)) := by
  have h := reflection_log_12300_neg
  have he : Real.log (52316316223 / 31250000000) = -Real.log (31250000000 / 52316316223) := by
    rw [show ((52316316223 / 31250000000) : ℝ) = ((31250000000 / 52316316223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12301_neg : (104856893 / 100000000) ≤ -Real.log (500000000000 / 1426782273603) ∧
    -Real.log (500000000000 / 1426782273603) ≤ (262142233 / 250000000) := by
  have h := checkLog_sound (w := (426782273603 / 2426782273603)) (n := 12)
    (lo := (1421687 / 4000000)) (hi := (355421751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1426782273603 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1426782273603 / 1000000000000) = 1/(500000000000 / 1426782273603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12301 : Bounds (104856893 / 100000000) (262142233 / 250000000) (Real.log (1426782273603 / 500000000000)) := by
  have h := reflection_log_12301_neg
  have he : Real.log (1426782273603 / 500000000000) = -Real.log (500000000000 / 1426782273603) := by
    rw [show ((1426782273603 / 500000000000) : ℝ) = ((500000000000 / 1426782273603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12302_neg : (1051172563 / 1000000000) ≤ -Real.log (250000000000 / 715250965251) ∧
    -Real.log (250000000000 / 715250965251) ≤ (210234513 / 200000000) := by
  have h := checkLog_sound (w := (215250965251 / 1215250965251)) (n := 12)
    (lo := (358025383 / 1000000000)) (hi := (44753173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715250965251 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(715250965251 / 500000000000) = 1/(250000000000 / 715250965251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12302 : Bounds (1051172563 / 1000000000) (210234513 / 200000000) (Real.log (715250965251 / 250000000000)) := by
  have h := reflection_log_12302_neg
  have he : Real.log (715250965251 / 250000000000) = -Real.log (250000000000 / 715250965251) := by
    rw [show ((715250965251 / 250000000000) : ℝ) = ((250000000000 / 715250965251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12303_neg : (394067063 / 1000000000) ≤ -Real.log (1000 / 1483) ∧
    -Real.log (1000 / 1483) ≤ (49258383 / 125000000) := by
  have h := checkLog_sound (w := (483 / 2483)) (n := 12)
    (lo := (394067063 / 1000000000)) (hi := (49258383 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1483 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1483 / 1000) = 1/(1000 / 1483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12303 : Bounds (394067063 / 1000000000) (49258383 / 125000000) (Real.log (1483 / 1000)) := by
  have h := reflection_log_12303_neg
  have he : Real.log (1483 / 1000) = -Real.log (1000 / 1483) := by
    rw [show ((1483 / 1000) : ℝ) = ((1000 / 1483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12304_neg : (164928101 / 250000000) ≤ -Real.log (517 / 1000) ∧
    -Real.log (517 / 1000) ≤ (131942481 / 200000000) := by
  have h := checkLog_sound (w := (483 / 1517)) (n := 12)
    (lo := (164928101 / 250000000)) (hi := (131942481 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 517) = 1/(517 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12304 : Bounds (-131942481 / 200000000) (-164928101 / 250000000) (Real.log (517 / 1000)) := by
  have h := reflection_log_12304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12305_neg : (482883 / 1000000000) ≤ -Real.log (1000000 / 1000483) ∧
    -Real.log (1000000 / 1000483) ≤ (120721 / 250000000) := by
  have h := checkLog_sound (w := (483 / 2000483)) (n := 12)
    (lo := (482883 / 1000000000)) (hi := (120721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000483 / 1000000) = 1/(1000000 / 1000483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12305 : Bounds (482883 / 1000000000) (120721 / 250000000) (Real.log (1000483 / 1000000)) := by
  have h := reflection_log_12305_neg
  have he : Real.log (1000483 / 1000000) = -Real.log (1000000 / 1000483) := by
    rw [show ((1000483 / 1000000) : ℝ) = ((1000000 / 1000483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12306_neg : (120779 / 250000000) ≤ -Real.log (999517 / 1000000) ∧
    -Real.log (999517 / 1000000) ≤ (483117 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 1999517)) (n := 12)
    (lo := (120779 / 250000000)) (hi := (483117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999517) = 1/(999517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12306 : Bounds (-483117 / 1000000000) (-120779 / 250000000) (Real.log (999517 / 1000000)) := by
  have h := reflection_log_12306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12307_neg : (89779 / 400000) ≤ -Real.log (1000000 / 1251631) ∧
    -Real.log (1000000 / 1251631) ≤ (224447501 / 1000000000) := by
  have h := checkLog_sound (w := (251631 / 2251631)) (n := 12)
    (lo := (89779 / 400000)) (hi := (224447501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251631 / 1000000) = 1/(1000000 / 1251631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12307 : Bounds (89779 / 400000) (224447501 / 1000000000) (Real.log (1251631 / 1000000)) := by
  have h := reflection_log_12307_neg
  have he : Real.log (1251631 / 1000000) = -Real.log (1000000 / 1251631) := by
    rw [show ((1251631 / 1000000) : ℝ) = ((1000000 / 1251631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12308_neg : (289859107 / 1000000000) ≤ -Real.log (748369 / 1000000) ∧
    -Real.log (748369 / 1000000) ≤ (72464777 / 250000000) := by
  have h := checkLog_sound (w := (251631 / 1748369)) (n := 12)
    (lo := (289859107 / 1000000000)) (hi := (72464777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748369) = 1/(748369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12308 : Bounds (-72464777 / 250000000) (-289859107 / 1000000000) (Real.log (748369 / 1000000)) := by
  have h := reflection_log_12308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12309_neg : (45054337 / 200000000) ≤ -Real.log (1000000 / 1252663) ∧
    -Real.log (1000000 / 1252663) ≤ (112635843 / 500000000) := by
  have h := checkLog_sound (w := (252663 / 2252663)) (n := 12)
    (lo := (45054337 / 200000000)) (hi := (112635843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252663 / 1000000) = 1/(1000000 / 1252663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12309 : Bounds (45054337 / 200000000) (112635843 / 500000000) (Real.log (1252663 / 1000000)) := by
  have h := reflection_log_12309_neg
  have he : Real.log (1252663 / 1000000) = -Real.log (1000000 / 1252663) := by
    rw [show ((1252663 / 1000000) : ℝ) = ((1000000 / 1252663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12310_neg : (291239057 / 1000000000) ≤ -Real.log (747337 / 1000000) ∧
    -Real.log (747337 / 1000000) ≤ (145619529 / 500000000) := by
  have h := checkLog_sound (w := (252663 / 1747337)) (n := 12)
    (lo := (291239057 / 1000000000)) (hi := (145619529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747337) = 1/(747337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12310 : Bounds (-145619529 / 500000000) (-291239057 / 1000000000) (Real.log (747337 / 1000000)) := by
  have h := reflection_log_12310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12311_neg : (16491843 / 250000000) ≤ -Real.log (936161408431 / 1000000000000) ∧
    -Real.log (936161408431 / 1000000000000) ≤ (65967373 / 1000000000) := by
  have h := checkLog_sound (w := (63838591569 / 1936161408431)) (n := 12)
    (lo := (16491843 / 250000000)) (hi := (65967373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 936161408431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 936161408431) = 1/(936161408431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12311 : Bounds (-65967373 / 1000000000) (-16491843 / 250000000) (Real.log (936161408431 / 1000000000000)) := by
  have h := reflection_log_12311_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12312_neg : (32705803 / 500000000) ≤ -Real.log (936681839839 / 1000000000000) ∧
    -Real.log (936681839839 / 1000000000000) ≤ (65411607 / 1000000000) := by
  have h := checkLog_sound (w := (63318160161 / 1936681839839)) (n := 12)
    (lo := (32705803 / 500000000)) (hi := (65411607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 936681839839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 936681839839) = 1/(936681839839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12312 : Bounds (-65411607 / 1000000000) (-32705803 / 500000000) (Real.log (936681839839 / 1000000000000)) := by
  have h := reflection_log_12312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12313_neg : (514306607 / 1000000000) ≤ -Real.log (250000000000 / 418119604099) ∧
    -Real.log (250000000000 / 418119604099) ≤ (32144163 / 62500000) := by
  have h := checkLog_sound (w := (168119604099 / 668119604099)) (n := 12)
    (lo := (514306607 / 1000000000)) (hi := (32144163 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((418119604099 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(418119604099 / 250000000000) = 1/(250000000000 / 418119604099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12313 : Bounds (514306607 / 1000000000) (32144163 / 62500000) (Real.log (418119604099 / 250000000000)) := by
  have h := reflection_log_12313_neg
  have he : Real.log (418119604099 / 250000000000) = -Real.log (250000000000 / 418119604099) := by
    rw [show ((418119604099 / 250000000000) : ℝ) = ((250000000000 / 418119604099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12314_neg : (258255371 / 500000000) ≤ -Real.log (500000000000 / 838084425099) ∧
    -Real.log (500000000000 / 838084425099) ≤ (516510743 / 1000000000) := by
  have h := checkLog_sound (w := (338084425099 / 1338084425099)) (n := 12)
    (lo := (258255371 / 500000000)) (hi := (516510743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838084425099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838084425099 / 500000000000) = 1/(500000000000 / 838084425099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12314 : Bounds (258255371 / 500000000) (516510743 / 1000000000) (Real.log (838084425099 / 500000000000)) := by
  have h := reflection_log_12314_neg
  have he : Real.log (838084425099 / 500000000000) = -Real.log (500000000000 / 838084425099) := by
    rw [show ((838084425099 / 500000000000) : ℝ) = ((500000000000 / 838084425099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12315_neg : (1051172563 / 1000000000) ≤ -Real.log (500000000000 / 1430501930501) ∧
    -Real.log (500000000000 / 1430501930501) ≤ (210234513 / 200000000) := by
  have h := checkLog_sound (w := (430501930501 / 2430501930501)) (n := 12)
    (lo := (358025383 / 1000000000)) (hi := (44753173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1430501930501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1430501930501 / 1000000000000) = 1/(500000000000 / 1430501930501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12315 : Bounds (1051172563 / 1000000000) (210234513 / 200000000) (Real.log (1430501930501 / 500000000000)) := by
  have h := reflection_log_12315_neg
  have he : Real.log (1430501930501 / 500000000000) = -Real.log (500000000000 / 1430501930501) := by
    rw [show ((1430501930501 / 500000000000) : ℝ) = ((500000000000 / 1430501930501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12316_neg : (1053779467 / 1000000000) ≤ -Real.log (50000000000 / 143423597679) ∧
    -Real.log (50000000000 / 143423597679) ≤ (1053779469 / 1000000000) := by
  have h := checkLog_sound (w := (43423597679 / 243423597679)) (n := 12)
    (lo := (360632287 / 1000000000)) (hi := (11269759 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143423597679 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(143423597679 / 100000000000) = 1/(50000000000 / 143423597679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12316 : Bounds (1053779467 / 1000000000) (1053779469 / 1000000000) (Real.log (143423597679 / 50000000000)) := by
  have h := reflection_log_12316_neg
  have he : Real.log (143423597679 / 50000000000) = -Real.log (50000000000 / 143423597679) := by
    rw [show ((143423597679 / 50000000000) : ℝ) = ((50000000000 / 143423597679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12317_neg : (49342643 / 125000000) ≤ -Real.log (250 / 371) ∧
    -Real.log (250 / 371) ≤ (78948229 / 200000000) := by
  have h := checkLog_sound (w := (121 / 621)) (n := 12)
    (lo := (49342643 / 125000000)) (hi := (78948229 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371 / 250) = 1/(250 / 371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12317 : Bounds (49342643 / 125000000) (78948229 / 200000000) (Real.log (371 / 250)) := by
  have h := reflection_log_12317_neg
  have he : Real.log (371 / 250) = -Real.log (250 / 371) := by
    rw [show ((371 / 250) : ℝ) = ((250 / 371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12318_neg : (661648513 / 1000000000) ≤ -Real.log (129 / 250) ∧
    -Real.log (129 / 250) ≤ (330824257 / 500000000) := by
  have h := checkLog_sound (w := (121 / 379)) (n := 12)
    (lo := (661648513 / 1000000000)) (hi := (330824257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 129) = 1/(129 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12318 : Bounds (-330824257 / 500000000) (-661648513 / 1000000000) (Real.log (129 / 250)) := by
  have h := reflection_log_12318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12319_neg : (241941 / 500000000) ≤ -Real.log (250000 / 250121) ∧
    -Real.log (250000 / 250121) ≤ (483883 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 500121)) (n := 12)
    (lo := (241941 / 500000000)) (hi := (483883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250121 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250121 / 250000) = 1/(250000 / 250121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12319 : Bounds (241941 / 500000000) (483883 / 1000000000) (Real.log (250121 / 250000)) := by
  have h := reflection_log_12319_neg
  have he : Real.log (250121 / 250000) = -Real.log (250000 / 250121) := by
    rw [show ((250121 / 250000) : ℝ) = ((250000 / 250121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12320_neg : (484117 / 1000000000) ≤ -Real.log (249879 / 250000) ∧
    -Real.log (249879 / 250000) ≤ (242059 / 500000000) := by
  have h := checkLog_sound (w := (121 / 499879)) (n := 12)
    (lo := (484117 / 1000000000)) (hi := (242059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249879) = 1/(249879 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12320 : Bounds (-242059 / 500000000) (-484117 / 1000000000) (Real.log (249879 / 250000)) := by
  have h := reflection_log_12320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12321_neg : (224903601 / 1000000000) ≤ -Real.log (500000 / 626101) ∧
    -Real.log (500000 / 626101) ≤ (112451801 / 500000000) := by
  have h := checkLog_sound (w := (126101 / 1126101)) (n := 12)
    (lo := (224903601 / 1000000000)) (hi := (112451801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626101 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626101 / 500000) = 1/(500000 / 626101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12321 : Bounds (224903601 / 1000000000) (112451801 / 500000000) (Real.log (626101 / 500000)) := by
  have h := reflection_log_12321_neg
  have he : Real.log (626101 / 500000) = -Real.log (500000 / 626101) := by
    rw [show ((626101 / 500000) : ℝ) = ((500000 / 626101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12322_neg : (29062239 / 100000000) ≤ -Real.log (373899 / 500000) ∧
    -Real.log (373899 / 500000) ≤ (290622391 / 1000000000) := by
  have h := checkLog_sound (w := (126101 / 873899)) (n := 12)
    (lo := (29062239 / 100000000)) (hi := (290622391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373899) = 1/(373899 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12322 : Bounds (-290622391 / 1000000000) (-29062239 / 100000000) (Real.log (373899 / 500000)) := by
  have h := reflection_log_12322_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12323_neg : (14108013 / 62500000) ≤ -Real.log (200000 / 250647) ∧
    -Real.log (200000 / 250647) ≤ (225728209 / 1000000000) := by
  have h := checkLog_sound (w := (50647 / 450647)) (n := 12)
    (lo := (14108013 / 62500000)) (hi := (225728209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250647 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250647 / 200000) = 1/(200000 / 250647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12323 : Bounds (14108013 / 62500000) (225728209 / 1000000000) (Real.log (250647 / 200000)) := by
  have h := reflection_log_12323_neg
  have he : Real.log (250647 / 200000) = -Real.log (200000 / 250647) := by
    rw [show ((250647 / 200000) : ℝ) = ((200000 / 250647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12324_neg : (58400947 / 200000000) ≤ -Real.log (149353 / 200000) ∧
    -Real.log (149353 / 200000) ≤ (2281287 / 7812500) := by
  have h := checkLog_sound (w := (50647 / 349353)) (n := 12)
    (lo := (58400947 / 200000000)) (hi := (2281287 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 149353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 149353) = 1/(149353 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12324 : Bounds (-2281287 / 7812500) (-58400947 / 200000000) (Real.log (149353 / 200000)) := by
  have h := reflection_log_12324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12325_neg : (33138263 / 500000000) ≤ -Real.log (37434881391 / 40000000000) ∧
    -Real.log (37434881391 / 40000000000) ≤ (66276527 / 1000000000) := by
  have h := checkLog_sound (w := (2565118609 / 77434881391)) (n := 12)
    (lo := (33138263 / 500000000)) (hi := (66276527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37434881391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37434881391) = 1/(37434881391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12325 : Bounds (-66276527 / 1000000000) (-33138263 / 500000000) (Real.log (37434881391 / 40000000000)) := by
  have h := reflection_log_12325_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12326_neg : (65718789 / 1000000000) ≤ -Real.log (234098537799 / 250000000000) ∧
    -Real.log (234098537799 / 250000000000) ≤ (6571879 / 100000000) := by
  have h := checkLog_sound (w := (15901462201 / 484098537799)) (n := 12)
    (lo := (65718789 / 1000000000)) (hi := (6571879 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 234098537799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 234098537799) = 1/(234098537799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12326 : Bounds (-6571879 / 100000000) (-65718789 / 1000000000) (Real.log (234098537799 / 250000000000)) := by
  have h := reflection_log_12326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12327_neg : (64440749 / 125000000) ≤ -Real.log (100000000000 / 167451905461) ∧
    -Real.log (100000000000 / 167451905461) ≤ (515525993 / 1000000000) := by
  have h := checkLog_sound (w := (67451905461 / 267451905461)) (n := 12)
    (lo := (64440749 / 125000000)) (hi := (515525993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167451905461 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167451905461 / 100000000000) = 1/(100000000000 / 167451905461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12327 : Bounds (64440749 / 125000000) (515525993 / 1000000000) (Real.log (167451905461 / 100000000000)) := by
  have h := reflection_log_12327_neg
  have he : Real.log (167451905461 / 100000000000) = -Real.log (100000000000 / 167451905461) := by
    rw [show ((167451905461 / 100000000000) : ℝ) = ((100000000000 / 167451905461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12328_neg : (517732943 / 1000000000) ≤ -Real.log (250000000000 / 419554679183) ∧
    -Real.log (250000000000 / 419554679183) ≤ (32358309 / 62500000) := by
  have h := checkLog_sound (w := (169554679183 / 669554679183)) (n := 12)
    (lo := (517732943 / 1000000000)) (hi := (32358309 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419554679183 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419554679183 / 250000000000) = 1/(250000000000 / 419554679183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12328 : Bounds (517732943 / 1000000000) (32358309 / 62500000) (Real.log (419554679183 / 250000000000)) := by
  have h := reflection_log_12328_neg
  have he : Real.log (419554679183 / 250000000000) = -Real.log (250000000000 / 419554679183) := by
    rw [show ((419554679183 / 250000000000) : ℝ) = ((250000000000 / 419554679183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12329_neg : (1053779467 / 1000000000) ≤ -Real.log (500000000000 / 1434235976789) ∧
    -Real.log (500000000000 / 1434235976789) ≤ (1053779469 / 1000000000) := by
  have h := checkLog_sound (w := (434235976789 / 2434235976789)) (n := 12)
    (lo := (360632287 / 1000000000)) (hi := (11269759 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1434235976789 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1434235976789 / 1000000000000) = 1/(500000000000 / 1434235976789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12329 : Bounds (1053779467 / 1000000000) (1053779469 / 1000000000) (Real.log (1434235976789 / 500000000000)) := by
  have h := reflection_log_12329_neg
  have he : Real.log (1434235976789 / 500000000000) = -Real.log (500000000000 / 1434235976789) := by
    rw [show ((1434235976789 / 500000000000) : ℝ) = ((500000000000 / 1434235976789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12330_neg : (1056389657 / 1000000000) ≤ -Real.log (4000000000 / 11503875969) ∧
    -Real.log (4000000000 / 11503875969) ≤ (1056389659 / 1000000000) := by
  have h := checkLog_sound (w := (3503875969 / 19503875969)) (n := 12)
    (lo := (363242477 / 1000000000)) (hi := (181621239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11503875969 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11503875969 / 8000000000) = 1/(4000000000 / 11503875969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12330 : Bounds (1056389657 / 1000000000) (1056389659 / 1000000000) (Real.log (11503875969 / 4000000000)) := by
  have h := reflection_log_12330_neg
  have he : Real.log (11503875969 / 4000000000) = -Real.log (4000000000 / 11503875969) := by
    rw [show ((11503875969 / 4000000000) : ℝ) = ((4000000000 / 11503875969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12331_neg : (98853693 / 250000000) ≤ -Real.log (200 / 297) ∧
    -Real.log (200 / 297) ≤ (395414773 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 497)) (n := 12)
    (lo := (98853693 / 250000000)) (hi := (395414773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297 / 200) = 1/(200 / 297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12331 : Bounds (98853693 / 250000000) (395414773 / 1000000000) (Real.log (297 / 200)) := by
  have h := reflection_log_12331_neg
  have he : Real.log (297 / 200) = -Real.log (200 / 297) := by
    rw [show ((297 / 200) : ℝ) = ((200 / 297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12332_neg : (331794189 / 500000000) ≤ -Real.log (103 / 200) ∧
    -Real.log (103 / 200) ≤ (663588379 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 303)) (n := 12)
    (lo := (331794189 / 500000000)) (hi := (663588379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 103) = 1/(103 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12332 : Bounds (-663588379 / 1000000000) (-331794189 / 500000000) (Real.log (103 / 200)) := by
  have h := reflection_log_12332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12333_neg : (242441 / 500000000) ≤ -Real.log (200000 / 200097) ∧
    -Real.log (200000 / 200097) ≤ (484883 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 400097)) (n := 12)
    (lo := (242441 / 500000000)) (hi := (484883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200097 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200097 / 200000) = 1/(200000 / 200097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12333 : Bounds (242441 / 500000000) (484883 / 1000000000) (Real.log (200097 / 200000)) := by
  have h := reflection_log_12333_neg
  have he : Real.log (200097 / 200000) = -Real.log (200000 / 200097) := by
    rw [show ((200097 / 200000) : ℝ) = ((200000 / 200097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12334_neg : (485117 / 1000000000) ≤ -Real.log (199903 / 200000) ∧
    -Real.log (199903 / 200000) ≤ (242559 / 500000000) := by
  have h := checkLog_sound (w := (97 / 399903)) (n := 12)
    (lo := (485117 / 1000000000)) (hi := (242559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199903) = 1/(199903 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12334 : Bounds (-242559 / 500000000) (-485117 / 1000000000) (Real.log (199903 / 200000)) := by
  have h := reflection_log_12334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12335_neg : (112679747 / 500000000) ≤ -Real.log (1000000 / 1252773) ∧
    -Real.log (1000000 / 1252773) ≤ (45071899 / 200000000) := by
  have h := checkLog_sound (w := (252773 / 2252773)) (n := 12)
    (lo := (112679747 / 500000000)) (hi := (45071899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252773 / 1000000) = 1/(1000000 / 1252773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12335 : Bounds (112679747 / 500000000) (45071899 / 200000000) (Real.log (1252773 / 1000000)) := by
  have h := reflection_log_12335_neg
  have he : Real.log (1252773 / 1000000) = -Real.log (1000000 / 1252773) := by
    rw [show ((1252773 / 1000000) : ℝ) = ((1000000 / 1252773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12336_neg : (291386257 / 1000000000) ≤ -Real.log (747227 / 1000000) ∧
    -Real.log (747227 / 1000000) ≤ (145693129 / 500000000) := by
  have h := checkLog_sound (w := (252773 / 1747227)) (n := 12)
    (lo := (291386257 / 1000000000)) (hi := (145693129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747227) = 1/(747227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12336 : Bounds (-145693129 / 500000000) (-291386257 / 1000000000) (Real.log (747227 / 1000000)) := by
  have h := reflection_log_12336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12337_neg : (113092261 / 500000000) ≤ -Real.log (1000000 / 1253807) ∧
    -Real.log (1000000 / 1253807) ≤ (226184523 / 1000000000) := by
  have h := checkLog_sound (w := (253807 / 2253807)) (n := 12)
    (lo := (113092261 / 500000000)) (hi := (226184523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253807 / 1000000) = 1/(1000000 / 1253807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12337 : Bounds (113092261 / 500000000) (226184523 / 1000000000) (Real.log (1253807 / 1000000)) := by
  have h := reflection_log_12337_neg
  have he : Real.log (1253807 / 1000000) = -Real.log (1000000 / 1253807) := by
    rw [show ((1253807 / 1000000) : ℝ) = ((1000000 / 1253807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12338_neg : (292770999 / 1000000000) ≤ -Real.log (746193 / 1000000) ∧
    -Real.log (746193 / 1000000) ≤ (292771 / 1000000) := by
  have h := checkLog_sound (w := (253807 / 1746193)) (n := 12)
    (lo := (292770999 / 1000000000)) (hi := (292771 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746193) = 1/(746193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12338 : Bounds (-292771 / 1000000) (-292770999 / 1000000000) (Real.log (746193 / 1000000)) := by
  have h := reflection_log_12338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12339_neg : (16646619 / 250000000) ≤ -Real.log (935582006751 / 1000000000000) ∧
    -Real.log (935582006751 / 1000000000000) ≤ (66586477 / 1000000000) := by
  have h := checkLog_sound (w := (64417993249 / 1935582006751)) (n := 12)
    (lo := (16646619 / 250000000)) (hi := (66586477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 935582006751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 935582006751) = 1/(935582006751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12339 : Bounds (-66586477 / 1000000000) (-16646619 / 250000000) (Real.log (935582006751 / 1000000000000)) := by
  have h := reflection_log_12339_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12340_neg : (66026763 / 1000000000) ≤ -Real.log (936105810471 / 1000000000000) ∧
    -Real.log (936105810471 / 1000000000000) ≤ (16506691 / 250000000) := by
  have h := checkLog_sound (w := (63894189529 / 1936105810471)) (n := 12)
    (lo := (66026763 / 1000000000)) (hi := (16506691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 936105810471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 936105810471) = 1/(936105810471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12340 : Bounds (-16506691 / 250000000) (-66026763 / 1000000000) (Real.log (936105810471 / 1000000000000)) := by
  have h := reflection_log_12340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12341_neg : (64593219 / 125000000) ≤ -Real.log (62500000000 / 104785175723) ∧
    -Real.log (62500000000 / 104785175723) ≤ (516745753 / 1000000000) := by
  have h := checkLog_sound (w := (42285175723 / 167285175723)) (n := 12)
    (lo := (64593219 / 125000000)) (hi := (516745753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104785175723 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104785175723 / 62500000000) = 1/(62500000000 / 104785175723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12341 : Bounds (64593219 / 125000000) (516745753 / 1000000000) (Real.log (104785175723 / 62500000000)) := by
  have h := reflection_log_12341_neg
  have he : Real.log (104785175723 / 62500000000) = -Real.log (62500000000 / 104785175723) := by
    rw [show ((104785175723 / 62500000000) : ℝ) = ((62500000000 / 104785175723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12342_neg : (518955521 / 1000000000) ≤ -Real.log (250000000000 / 420067931487) ∧
    -Real.log (250000000000 / 420067931487) ≤ (259477761 / 500000000) := by
  have h := checkLog_sound (w := (170067931487 / 670067931487)) (n := 12)
    (lo := (518955521 / 1000000000)) (hi := (259477761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420067931487 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(420067931487 / 250000000000) = 1/(250000000000 / 420067931487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12342 : Bounds (518955521 / 1000000000) (259477761 / 500000000) (Real.log (420067931487 / 250000000000)) := by
  have h := reflection_log_12342_neg
  have he : Real.log (420067931487 / 250000000000) = -Real.log (250000000000 / 420067931487) := by
    rw [show ((420067931487 / 250000000000) : ℝ) = ((250000000000 / 420067931487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12343_neg : (1056389657 / 1000000000) ≤ -Real.log (125000000000 / 359496124031) ∧
    -Real.log (125000000000 / 359496124031) ≤ (1056389659 / 1000000000) := by
  have h := checkLog_sound (w := (109496124031 / 609496124031)) (n := 12)
    (lo := (363242477 / 1000000000)) (hi := (181621239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359496124031 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(359496124031 / 250000000000) = 1/(125000000000 / 359496124031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12343 : Bounds (1056389657 / 1000000000) (1056389659 / 1000000000) (Real.log (359496124031 / 125000000000)) := by
  have h := reflection_log_12343_neg
  have he : Real.log (359496124031 / 125000000000) = -Real.log (125000000000 / 359496124031) := by
    rw [show ((359496124031 / 125000000000) : ℝ) = ((125000000000 / 359496124031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12344_neg : (21180063 / 20000000) ≤ -Real.log (31250000000 / 90109223301) ∧
    -Real.log (31250000000 / 90109223301) ≤ (66187697 / 62500000) := by
  have h := checkLog_sound (w := (27609223301 / 152609223301)) (n := 12)
    (lo := (36585597 / 100000000)) (hi := (365855971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90109223301 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(90109223301 / 62500000000) = 1/(31250000000 / 90109223301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12344 : Bounds (21180063 / 20000000) (66187697 / 62500000) (Real.log (90109223301 / 31250000000)) := by
  have h := reflection_log_12344_neg
  have he : Real.log (90109223301 / 31250000000) = -Real.log (31250000000 / 90109223301) := by
    rw [show ((90109223301 / 31250000000) : ℝ) = ((31250000000 / 90109223301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12345_neg : (198043973 / 500000000) ≤ -Real.log (500 / 743) ∧
    -Real.log (500 / 743) ≤ (396087947 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 1243)) (n := 12)
    (lo := (198043973 / 500000000)) (hi := (396087947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743 / 500) = 1/(500 / 743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12345 : Bounds (198043973 / 500000000) (396087947 / 1000000000) (Real.log (743 / 500)) := by
  have h := reflection_log_12345_neg
  have he : Real.log (743 / 500) = -Real.log (500 / 743) := by
    rw [show ((743 / 500) : ℝ) = ((500 / 743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12346_neg : (665532013 / 1000000000) ≤ -Real.log (257 / 500) ∧
    -Real.log (257 / 500) ≤ (332766007 / 500000000) := by
  have h := checkLog_sound (w := (243 / 757)) (n := 12)
    (lo := (665532013 / 1000000000)) (hi := (332766007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 257) = 1/(257 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12346 : Bounds (-332766007 / 500000000) (-665532013 / 1000000000) (Real.log (257 / 500)) := by
  have h := reflection_log_12346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12347_neg : (485881 / 1000000000) ≤ -Real.log (500000 / 500243) ∧
    -Real.log (500000 / 500243) ≤ (242941 / 500000000) := by
  have h := checkLog_sound (w := (243 / 1000243)) (n := 12)
    (lo := (485881 / 1000000000)) (hi := (242941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500243 / 500000) = 1/(500000 / 500243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12347 : Bounds (485881 / 1000000000) (242941 / 500000000) (Real.log (500243 / 500000)) := by
  have h := reflection_log_12347_neg
  have he : Real.log (500243 / 500000) = -Real.log (500000 / 500243) := by
    rw [show ((500243 / 500000) : ℝ) = ((500000 / 500243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12348_neg : (243059 / 500000000) ≤ -Real.log (499757 / 500000) ∧
    -Real.log (499757 / 500000) ≤ (486119 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 999757)) (n := 12)
    (lo := (243059 / 500000000)) (hi := (486119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499757) = 1/(499757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12348 : Bounds (-486119 / 1000000000) (-243059 / 500000000) (Real.log (499757 / 500000)) := by
  have h := reflection_log_12348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12349_neg : (225815977 / 1000000000) ≤ -Real.log (200000 / 250669) ∧
    -Real.log (200000 / 250669) ≤ (112907989 / 500000000) := by
  have h := checkLog_sound (w := (50669 / 450669)) (n := 12)
    (lo := (225815977 / 1000000000)) (hi := (112907989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250669 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250669 / 200000) = 1/(200000 / 250669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12349 : Bounds (225815977 / 1000000000) (112907989 / 500000000) (Real.log (250669 / 200000)) := by
  have h := reflection_log_12349_neg
  have he : Real.log (250669 / 200000) = -Real.log (200000 / 250669) := by
    rw [show ((250669 / 200000) : ℝ) = ((200000 / 250669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12350_neg : (292152047 / 1000000000) ≤ -Real.log (149331 / 200000) ∧
    -Real.log (149331 / 200000) ≤ (18259503 / 62500000) := by
  have h := checkLog_sound (w := (50669 / 349331)) (n := 12)
    (lo := (292152047 / 1000000000)) (hi := (18259503 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 149331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 149331) = 1/(149331 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12350 : Bounds (-18259503 / 62500000) (-292152047 / 1000000000) (Real.log (149331 / 200000)) := by
  have h := reflection_log_12350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12351_neg : (113320713 / 500000000) ≤ -Real.log (50000 / 62719) ∧
    -Real.log (50000 / 62719) ≤ (226641427 / 1000000000) := by
  have h := checkLog_sound (w := (12719 / 112719)) (n := 12)
    (lo := (113320713 / 500000000)) (hi := (226641427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62719 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62719 / 50000) = 1/(50000 / 62719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12351 : Bounds (113320713 / 500000000) (226641427 / 1000000000) (Real.log (62719 / 50000)) := by
  have h := reflection_log_12351_neg
  have he : Real.log (62719 / 50000) = -Real.log (50000 / 62719) := by
    rw [show ((62719 / 50000) : ℝ) = ((50000 / 62719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


