-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0160__3_q00
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0160__3_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T04:35:26.051589+00:00
-- url     : https://prove2.me/theorems/b57fbc79-8c65-4698-b9a7-a35586d13113
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0162) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0162) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0161, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0162) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0160 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0161, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0162) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0160 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10240_neg : (203984119 / 500000000) ≤ -Real.log (133 / 200) ∧
    -Real.log (133 / 200) ≤ (407968239 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 333)) (n := 12)
    (lo := (203984119 / 500000000)) (hi := (407968239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 133) = 1/(133 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10240 : Bounds (-407968239 / 1000000000) (-203984119 / 500000000) (Real.log (133 / 200)) := by
  have h := reflection_log_10240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10241_neg : (334943 / 1000000000) ≤ -Real.log (200000 / 200067) ∧
    -Real.log (200000 / 200067) ≤ (10467 / 31250000) := by
  have h := checkLog_sound (w := (67 / 400067)) (n := 12)
    (lo := (334943 / 1000000000)) (hi := (10467 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200067 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200067 / 200000) = 1/(200000 / 200067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10241 : Bounds (334943 / 1000000000) (10467 / 31250000) (Real.log (200067 / 200000)) := by
  have h := reflection_log_10241_neg
  have he : Real.log (200067 / 200000) = -Real.log (200000 / 200067) := by
    rw [show ((200067 / 200000) : ℝ) = ((200000 / 200067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10242_neg : (20941 / 62500000) ≤ -Real.log (199933 / 200000) ∧
    -Real.log (199933 / 200000) ≤ (335057 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 399933)) (n := 12)
    (lo := (20941 / 62500000)) (hi := (335057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199933) = 1/(199933 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10242 : Bounds (-335057 / 1000000000) (-20941 / 62500000) (Real.log (199933 / 200000)) := by
  have h := reflection_log_10242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10243_neg : (6290781 / 40000000) ≤ -Real.log (1000000 / 1170311) ∧
    -Real.log (1000000 / 1170311) ≤ (78634763 / 500000000) := by
  have h := checkLog_sound (w := (170311 / 2170311)) (n := 12)
    (lo := (6290781 / 40000000)) (hi := (78634763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1170311 / 1000000) = 1/(1000000 / 1170311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10243 : Bounds (6290781 / 40000000) (78634763 / 500000000) (Real.log (1170311 / 1000000)) := by
  have h := reflection_log_10243_neg
  have he : Real.log (1170311 / 1000000) = -Real.log (1000000 / 1170311) := by
    rw [show ((1170311 / 1000000) : ℝ) = ((1000000 / 1170311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10244_neg : (186704347 / 1000000000) ≤ -Real.log (829689 / 1000000) ∧
    -Real.log (829689 / 1000000) ≤ (46676087 / 250000000) := by
  have h := checkLog_sound (w := (170311 / 1829689)) (n := 12)
    (lo := (186704347 / 1000000000)) (hi := (46676087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 829689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 829689) = 1/(829689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10244 : Bounds (-46676087 / 250000000) (-186704347 / 1000000000) (Real.log (829689 / 1000000)) := by
  have h := reflection_log_10244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10245_neg : (79002051 / 500000000) ≤ -Real.log (1000000 / 1171171) ∧
    -Real.log (1000000 / 1171171) ≤ (158004103 / 1000000000) := by
  have h := checkLog_sound (w := (171171 / 2171171)) (n := 12)
    (lo := (79002051 / 500000000)) (hi := (158004103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1171171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1171171 / 1000000) = 1/(1000000 / 1171171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10245 : Bounds (79002051 / 500000000) (158004103 / 1000000000) (Real.log (1171171 / 1000000)) := by
  have h := reflection_log_10245_neg
  have he : Real.log (1171171 / 1000000) = -Real.log (1000000 / 1171171) := by
    rw [show ((1171171 / 1000000) : ℝ) = ((1000000 / 1171171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10246_neg : (187741417 / 1000000000) ≤ -Real.log (828829 / 1000000) ∧
    -Real.log (828829 / 1000000) ≤ (93870709 / 500000000) := by
  have h := checkLog_sound (w := (171171 / 1828829)) (n := 12)
    (lo := (187741417 / 1000000000)) (hi := (93870709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 828829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 828829) = 1/(828829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10246 : Bounds (-93870709 / 500000000) (-187741417 / 1000000000) (Real.log (828829 / 1000000)) := by
  have h := reflection_log_10246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10247_neg : (14868657 / 500000000) ≤ -Real.log (970700488759 / 1000000000000) ∧
    -Real.log (970700488759 / 1000000000000) ≤ (5947463 / 200000000) := by
  have h := checkLog_sound (w := (29299511241 / 1970700488759)) (n := 12)
    (lo := (14868657 / 500000000)) (hi := (5947463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970700488759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970700488759) = 1/(970700488759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10247 : Bounds (-5947463 / 200000000) (-14868657 / 500000000) (Real.log (970700488759 / 1000000000000)) := by
  have h := reflection_log_10247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10248_neg : (29434821 / 1000000000) ≤ -Real.log (970994163279 / 1000000000000) ∧
    -Real.log (970994163279 / 1000000000000) ≤ (14717411 / 500000000) := by
  have h := checkLog_sound (w := (29005836721 / 1970994163279)) (n := 12)
    (lo := (29434821 / 1000000000)) (hi := (14717411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970994163279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970994163279) = 1/(970994163279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10248 : Bounds (-14717411 / 500000000) (-29434821 / 1000000000) (Real.log (970994163279 / 1000000000000)) := by
  have h := reflection_log_10248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10249_neg : (21498367 / 62500000) ≤ -Real.log (500000000000 / 705270890659) ∧
    -Real.log (500000000000 / 705270890659) ≤ (343973873 / 1000000000) := by
  have h := checkLog_sound (w := (205270890659 / 1205270890659)) (n := 12)
    (lo := (21498367 / 62500000)) (hi := (343973873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705270890659 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705270890659 / 500000000000) = 1/(500000000000 / 705270890659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10249 : Bounds (21498367 / 62500000) (343973873 / 1000000000) (Real.log (705270890659 / 500000000000)) := by
  have h := reflection_log_10249_neg
  have he : Real.log (705270890659 / 500000000000) = -Real.log (500000000000 / 705270890659) := by
    rw [show ((705270890659 / 500000000000) : ℝ) = ((500000000000 / 705270890659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10250_neg : (4321819 / 12500000) ≤ -Real.log (250000000000 / 353260744979) ∧
    -Real.log (250000000000 / 353260744979) ≤ (345745521 / 1000000000) := by
  have h := checkLog_sound (w := (103260744979 / 603260744979)) (n := 12)
    (lo := (4321819 / 12500000)) (hi := (345745521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353260744979 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353260744979 / 250000000000) = 1/(250000000000 / 353260744979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10250 : Bounds (4321819 / 12500000) (345745521 / 1000000000) (Real.log (353260744979 / 250000000000)) := by
  have h := reflection_log_10250_neg
  have he : Real.log (353260744979 / 250000000000) = -Real.log (250000000000 / 353260744979) := by
    rw [show ((353260744979 / 250000000000) : ℝ) = ((250000000000 / 353260744979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10251_neg : (138929511 / 200000000) ≤ -Real.log (500000000000 / 1001501501501) ∧
    -Real.log (500000000000 / 1001501501501) ≤ (694647557 / 1000000000) := by
  have h := checkLog_sound (w := (1501501501 / 2001501501501)) (n := 12)
    (lo := (12003 / 8000000)) (hi := (187547 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1001501501501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1001501501501 / 1000000000000) = 1/(500000000000 / 1001501501501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10251 : Bounds (138929511 / 200000000) (694647557 / 1000000000) (Real.log (1001501501501 / 500000000000)) := by
  have h := reflection_log_10251_neg
  have he : Real.log (1001501501501 / 500000000000) = -Real.log (500000000000 / 1001501501501) := by
    rw [show ((1001501501501 / 500000000000) : ℝ) = ((500000000000 / 1001501501501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10252_neg : (696899529 / 1000000000) ≤ -Real.log (500000000000 / 1003759398497) ∧
    -Real.log (500000000000 / 1003759398497) ≤ (696899531 / 1000000000) := by
  have h := checkLog_sound (w := (3759398497 / 2003759398497)) (n := 12)
    (lo := (3752349 / 1000000000)) (hi := (75047 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1003759398497 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1003759398497 / 1000000000000) = 1/(500000000000 / 1003759398497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10252 : Bounds (696899529 / 1000000000) (696899531 / 1000000000) (Real.log (1003759398497 / 500000000000)) := by
  have h := reflection_log_10252_neg
  have he : Real.log (1003759398497 / 500000000000) = -Real.log (500000000000 / 1003759398497) := by
    rw [show ((1003759398497 / 500000000000) : ℝ) = ((500000000000 / 1003759398497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10253_neg : (11587203 / 40000000) ≤ -Real.log (125 / 167) ∧
    -Real.log (125 / 167) ≤ (72420019 / 250000000) := by
  have h := checkLog_sound (w := (21 / 146)) (n := 12)
    (lo := (11587203 / 40000000)) (hi := (72420019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167 / 125) = 1/(125 / 167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10253 : Bounds (11587203 / 40000000) (72420019 / 250000000) (Real.log (167 / 125)) := by
  have h := reflection_log_10253_neg
  have he : Real.log (167 / 125) = -Real.log (125 / 167) := by
    rw [show ((167 / 125) : ℝ) = ((125 / 167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10254_neg : (409473129 / 1000000000) ≤ -Real.log (83 / 125) ∧
    -Real.log (83 / 125) ≤ (40947313 / 100000000) := by
  have h := checkLog_sound (w := (21 / 104)) (n := 12)
    (lo := (409473129 / 1000000000)) (hi := (40947313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 83) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 83) = 1/(83 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10254 : Bounds (-40947313 / 100000000) (-409473129 / 1000000000) (Real.log (83 / 125)) := by
  have h := reflection_log_10254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10255_neg : (335943 / 1000000000) ≤ -Real.log (62500 / 62521) ∧
    -Real.log (62500 / 62521) ≤ (41993 / 125000000) := by
  have h := checkLog_sound (w := (21 / 125021)) (n := 12)
    (lo := (335943 / 1000000000)) (hi := (41993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62521 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62521 / 62500) = 1/(62500 / 62521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10255 : Bounds (335943 / 1000000000) (41993 / 125000000) (Real.log (62521 / 62500)) := by
  have h := reflection_log_10255_neg
  have he : Real.log (62521 / 62500) = -Real.log (62500 / 62521) := by
    rw [show ((62521 / 62500) : ℝ) = ((62500 / 62521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10256_neg : (42007 / 125000000) ≤ -Real.log (62479 / 62500) ∧
    -Real.log (62479 / 62500) ≤ (336057 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 124979)) (n := 12)
    (lo := (42007 / 125000000)) (hi := (336057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62479) = 1/(62479 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10256 : Bounds (-336057 / 1000000000) (-42007 / 125000000) (Real.log (62479 / 62500)) := by
  have h := reflection_log_10256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10257_neg : (39430787 / 250000000) ≤ -Real.log (500000 / 585421) ∧
    -Real.log (500000 / 585421) ≤ (157723149 / 1000000000) := by
  have h := checkLog_sound (w := (85421 / 1085421)) (n := 12)
    (lo := (39430787 / 250000000)) (hi := (157723149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585421 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585421 / 500000) = 1/(500000 / 585421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10257 : Bounds (39430787 / 250000000) (157723149 / 1000000000) (Real.log (585421 / 500000)) := by
  have h := reflection_log_10257_neg
  have he : Real.log (585421 / 500000) = -Real.log (500000 / 585421) := by
    rw [show ((585421 / 500000) : ℝ) = ((500000 / 585421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10258_neg : (3746891 / 20000000) ≤ -Real.log (414579 / 500000) ∧
    -Real.log (414579 / 500000) ≤ (187344551 / 1000000000) := by
  have h := checkLog_sound (w := (85421 / 914579)) (n := 12)
    (lo := (3746891 / 20000000)) (hi := (187344551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414579) = 1/(414579 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10258 : Bounds (-187344551 / 1000000000) (-3746891 / 20000000) (Real.log (414579 / 500000)) := by
  have h := reflection_log_10258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10259_neg : (158459099 / 1000000000) ≤ -Real.log (125000 / 146463) ∧
    -Real.log (125000 / 146463) ≤ (1584591 / 10000000) := by
  have h := checkLog_sound (w := (21463 / 271463)) (n := 12)
    (lo := (158459099 / 1000000000)) (hi := (1584591 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146463 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146463 / 125000) = 1/(125000 / 146463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10259 : Bounds (158459099 / 1000000000) (1584591 / 10000000) (Real.log (146463 / 125000)) := by
  have h := reflection_log_10259_neg
  have he : Real.log (146463 / 125000) = -Real.log (125000 / 146463) := by
    rw [show ((146463 / 125000) : ℝ) = ((125000 / 146463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10260_neg : (1883847 / 10000000) ≤ -Real.log (103537 / 125000) ∧
    -Real.log (103537 / 125000) ≤ (188384701 / 1000000000) := by
  have h := checkLog_sound (w := (21463 / 228537)) (n := 12)
    (lo := (1883847 / 10000000)) (hi := (188384701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 103537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 103537) = 1/(103537 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10260 : Bounds (-188384701 / 1000000000) (-1883847 / 10000000) (Real.log (103537 / 125000)) := by
  have h := reflection_log_10260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10261_neg : (29925601 / 1000000000) ≤ -Real.log (15164339631 / 15625000000) ∧
    -Real.log (15164339631 / 15625000000) ≤ (14962801 / 500000000) := by
  have h := checkLog_sound (w := (460660369 / 30789339631)) (n := 12)
    (lo := (29925601 / 1000000000)) (hi := (14962801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15164339631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15164339631) = 1/(15164339631 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10261 : Bounds (-14962801 / 500000000) (-29925601 / 1000000000) (Real.log (15164339631 / 15625000000)) := by
  have h := reflection_log_10261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10262_neg : (14810701 / 500000000) ≤ -Real.log (242703252759 / 250000000000) ∧
    -Real.log (242703252759 / 250000000000) ≤ (29621403 / 1000000000) := by
  have h := checkLog_sound (w := (7296747241 / 492703252759)) (n := 12)
    (lo := (14810701 / 500000000)) (hi := (29621403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242703252759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242703252759) = 1/(242703252759 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10262 : Bounds (-29621403 / 1000000000) (-14810701 / 500000000) (Real.log (242703252759 / 250000000000)) := by
  have h := reflection_log_10262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10263_neg : (345067699 / 1000000000) ≤ -Real.log (500000000000 / 706042756627) ∧
    -Real.log (500000000000 / 706042756627) ≤ (3450677 / 10000000) := by
  have h := checkLog_sound (w := (206042756627 / 1206042756627)) (n := 12)
    (lo := (345067699 / 1000000000)) (hi := (3450677 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706042756627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706042756627 / 500000000000) = 1/(500000000000 / 706042756627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10263 : Bounds (345067699 / 1000000000) (3450677 / 10000000) (Real.log (706042756627 / 500000000000)) := by
  have h := reflection_log_10263_neg
  have he : Real.log (706042756627 / 500000000000) = -Real.log (500000000000 / 706042756627) := by
    rw [show ((706042756627 / 500000000000) : ℝ) = ((500000000000 / 706042756627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10264_neg : (1734219 / 5000000) ≤ -Real.log (50000000000 / 70729787419) ∧
    -Real.log (50000000000 / 70729787419) ≤ (346843801 / 1000000000) := by
  have h := checkLog_sound (w := (20729787419 / 120729787419)) (n := 12)
    (lo := (1734219 / 5000000)) (hi := (346843801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70729787419 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70729787419 / 50000000000) = 1/(50000000000 / 70729787419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10264 : Bounds (1734219 / 5000000) (346843801 / 1000000000) (Real.log (70729787419 / 50000000000)) := by
  have h := reflection_log_10264_neg
  have he : Real.log (70729787419 / 50000000000) = -Real.log (50000000000 / 70729787419) := by
    rw [show ((70729787419 / 50000000000) : ℝ) = ((50000000000 / 70729787419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10265_neg : (696899529 / 1000000000) ≤ -Real.log (15625000000 / 31367481203) ∧
    -Real.log (15625000000 / 31367481203) ≤ (696899531 / 1000000000) := by
  have h := checkLog_sound (w := (117481203 / 62617481203)) (n := 12)
    (lo := (3752349 / 1000000000)) (hi := (75047 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31367481203 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31367481203 / 31250000000) = 1/(15625000000 / 31367481203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10265 : Bounds (696899529 / 1000000000) (696899531 / 1000000000) (Real.log (31367481203 / 15625000000)) := by
  have h := reflection_log_10265_neg
  have he : Real.log (31367481203 / 15625000000) = -Real.log (15625000000 / 31367481203) := by
    rw [show ((31367481203 / 15625000000) : ℝ) = ((15625000000 / 31367481203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10266_neg : (174788301 / 250000000) ≤ -Real.log (250000000000 / 503012048193) ∧
    -Real.log (250000000000 / 503012048193) ≤ (349576603 / 500000000) := by
  have h := checkLog_sound (w := (3012048193 / 1003012048193)) (n := 12)
    (lo := (750753 / 125000000)) (hi := (240241 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503012048193 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(503012048193 / 500000000000) = 1/(250000000000 / 503012048193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10266 : Bounds (174788301 / 250000000) (349576603 / 500000000) (Real.log (503012048193 / 250000000000)) := by
  have h := reflection_log_10266_neg
  have he : Real.log (503012048193 / 250000000000) = -Real.log (250000000000 / 503012048193) := by
    rw [show ((503012048193 / 250000000000) : ℝ) = ((250000000000 / 503012048193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10267_neg : (145214149 / 500000000) ≤ -Real.log (1000 / 1337) ∧
    -Real.log (1000 / 1337) ≤ (290428299 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 2337)) (n := 12)
    (lo := (145214149 / 500000000)) (hi := (290428299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337 / 1000) = 1/(1000 / 1337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10267 : Bounds (145214149 / 500000000) (290428299 / 1000000000) (Real.log (1337 / 1000)) := by
  have h := reflection_log_10267_neg
  have he : Real.log (1337 / 1000) = -Real.log (1000 / 1337) := by
    rw [show ((1337 / 1000) : ℝ) = ((1000 / 1337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10268_neg : (6421567 / 15625000) ≤ -Real.log (663 / 1000) ∧
    -Real.log (663 / 1000) ≤ (410980289 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 1663)) (n := 12)
    (lo := (6421567 / 15625000)) (hi := (410980289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 663) = 1/(663 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10268 : Bounds (-410980289 / 1000000000) (-6421567 / 15625000) (Real.log (663 / 1000)) := by
  have h := reflection_log_10268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10269_neg : (336943 / 1000000000) ≤ -Real.log (1000000 / 1000337) ∧
    -Real.log (1000000 / 1000337) ≤ (21059 / 62500000) := by
  have h := checkLog_sound (w := (337 / 2000337)) (n := 12)
    (lo := (336943 / 1000000000)) (hi := (21059 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000337 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000337 / 1000000) = 1/(1000000 / 1000337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10269 : Bounds (336943 / 1000000000) (21059 / 62500000) (Real.log (1000337 / 1000000)) := by
  have h := reflection_log_10269_neg
  have he : Real.log (1000337 / 1000000) = -Real.log (1000000 / 1000337) := by
    rw [show ((1000337 / 1000000) : ℝ) = ((1000000 / 1000337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10270_neg : (10533 / 31250000) ≤ -Real.log (999663 / 1000000) ∧
    -Real.log (999663 / 1000000) ≤ (337057 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 1999663)) (n := 12)
    (lo := (10533 / 31250000)) (hi := (337057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999663) = 1/(999663 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10270 : Bounds (-337057 / 1000000000) (-10533 / 31250000) (Real.log (999663 / 1000000)) := by
  have h := reflection_log_10270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10271_neg : (79088709 / 500000000) ≤ -Real.log (500000 / 585687) ∧
    -Real.log (500000 / 585687) ≤ (158177419 / 1000000000) := by
  have h := checkLog_sound (w := (85687 / 1085687)) (n := 12)
    (lo := (79088709 / 500000000)) (hi := (158177419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585687 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585687 / 500000) = 1/(500000 / 585687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10271 : Bounds (79088709 / 500000000) (158177419 / 1000000000) (Real.log (585687 / 500000)) := by
  have h := reflection_log_10271_neg
  have he : Real.log (585687 / 500000) = -Real.log (500000 / 585687) := by
    rw [show ((585687 / 500000) : ℝ) = ((500000 / 585687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10272_neg : (187986371 / 1000000000) ≤ -Real.log (414313 / 500000) ∧
    -Real.log (414313 / 500000) ≤ (46996593 / 250000000) := by
  have h := checkLog_sound (w := (85687 / 914313)) (n := 12)
    (lo := (187986371 / 1000000000)) (hi := (46996593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414313) = 1/(414313 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10272 : Bounds (-46996593 / 250000000) (-187986371 / 1000000000) (Real.log (414313 / 500000)) := by
  have h := reflection_log_10272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10273_neg : (158913889 / 1000000000) ≤ -Real.log (1000000 / 1172237) ∧
    -Real.log (1000000 / 1172237) ≤ (15891389 / 100000000) := by
  have h := checkLog_sound (w := (172237 / 2172237)) (n := 12)
    (lo := (158913889 / 1000000000)) (hi := (15891389 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1172237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1172237 / 1000000) = 1/(1000000 / 1172237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10273 : Bounds (158913889 / 1000000000) (15891389 / 100000000) (Real.log (1172237 / 1000000)) := by
  have h := reflection_log_10273_neg
  have he : Real.log (1172237 / 1000000) = -Real.log (1000000 / 1172237) := by
    rw [show ((1172237 / 1000000) : ℝ) = ((1000000 / 1172237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10274_neg : (189028397 / 1000000000) ≤ -Real.log (827763 / 1000000) ∧
    -Real.log (827763 / 1000000) ≤ (94514199 / 500000000) := by
  have h := checkLog_sound (w := (172237 / 1827763)) (n := 12)
    (lo := (189028397 / 1000000000)) (hi := (94514199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 827763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 827763) = 1/(827763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10274 : Bounds (-94514199 / 500000000) (-189028397 / 1000000000) (Real.log (827763 / 1000000)) := by
  have h := reflection_log_10274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10275_neg : (7528627 / 250000000) ≤ -Real.log (970334415831 / 1000000000000) ∧
    -Real.log (970334415831 / 1000000000000) ≤ (30114509 / 1000000000) := by
  have h := checkLog_sound (w := (29665584169 / 1970334415831)) (n := 12)
    (lo := (7528627 / 250000000)) (hi := (30114509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970334415831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970334415831) = 1/(970334415831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10275 : Bounds (-30114509 / 1000000000) (-7528627 / 250000000) (Real.log (970334415831 / 1000000000000)) := by
  have h := reflection_log_10275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10276_neg : (3726119 / 125000000) ≤ -Real.log (242657738031 / 250000000000) ∧
    -Real.log (242657738031 / 250000000000) ≤ (29808953 / 1000000000) := by
  have h := checkLog_sound (w := (7342261969 / 492657738031)) (n := 12)
    (lo := (3726119 / 125000000)) (hi := (29808953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242657738031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242657738031) = 1/(242657738031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10276 : Bounds (-29808953 / 1000000000) (-3726119 / 125000000) (Real.log (242657738031 / 250000000000)) := by
  have h := reflection_log_10276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10277_neg : (34616379 / 100000000) ≤ -Real.log (100000000000 / 141363413651) ∧
    -Real.log (100000000000 / 141363413651) ≤ (346163791 / 1000000000) := by
  have h := checkLog_sound (w := (41363413651 / 241363413651)) (n := 12)
    (lo := (34616379 / 100000000)) (hi := (346163791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141363413651 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141363413651 / 100000000000) = 1/(100000000000 / 141363413651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10277 : Bounds (34616379 / 100000000) (346163791 / 1000000000) (Real.log (141363413651 / 100000000000)) := by
  have h := reflection_log_10277_neg
  have he : Real.log (141363413651 / 100000000000) = -Real.log (100000000000 / 141363413651) := by
    rw [show ((141363413651 / 100000000000) : ℝ) = ((100000000000 / 141363413651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10278_neg : (173971143 / 500000000) ≤ -Real.log (500000000000 / 708075258257) ∧
    -Real.log (500000000000 / 708075258257) ≤ (347942287 / 1000000000) := by
  have h := checkLog_sound (w := (208075258257 / 1208075258257)) (n := 12)
    (lo := (173971143 / 500000000)) (hi := (347942287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708075258257 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708075258257 / 500000000000) = 1/(500000000000 / 708075258257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10278 : Bounds (173971143 / 500000000) (347942287 / 1000000000) (Real.log (708075258257 / 500000000000)) := by
  have h := reflection_log_10278_neg
  have he : Real.log (708075258257 / 500000000000) = -Real.log (500000000000 / 708075258257) := by
    rw [show ((708075258257 / 500000000000) : ℝ) = ((500000000000 / 708075258257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10279_neg : (174788301 / 250000000) ≤ -Real.log (100000000000 / 201204819277) ∧
    -Real.log (100000000000 / 201204819277) ≤ (349576603 / 500000000) := by
  have h := checkLog_sound (w := (1204819277 / 401204819277)) (n := 12)
    (lo := (750753 / 125000000)) (hi := (240241 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201204819277 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(201204819277 / 200000000000) = 1/(100000000000 / 201204819277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10279 : Bounds (174788301 / 250000000) (349576603 / 500000000) (Real.log (201204819277 / 100000000000)) := by
  have h := reflection_log_10279_neg
  have he : Real.log (201204819277 / 100000000000) = -Real.log (100000000000 / 201204819277) := by
    rw [show ((201204819277 / 100000000000) : ℝ) = ((100000000000 / 201204819277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10280_neg : (350704293 / 500000000) ≤ -Real.log (500000000000 / 1008295625943) ∧
    -Real.log (500000000000 / 1008295625943) ≤ (175352147 / 250000000) := by
  have h := checkLog_sound (w := (8295625943 / 2008295625943)) (n := 12)
    (lo := (4130703 / 500000000)) (hi := (8261407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1008295625943 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1008295625943 / 1000000000000) = 1/(500000000000 / 1008295625943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10280 : Bounds (350704293 / 500000000) (175352147 / 250000000) (Real.log (1008295625943 / 500000000000)) := by
  have h := reflection_log_10280_neg
  have he : Real.log (1008295625943 / 500000000000) = -Real.log (500000000000 / 1008295625943) := by
    rw [show ((1008295625943 / 500000000000) : ℝ) = ((500000000000 / 1008295625943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10281_neg : (291175961 / 1000000000) ≤ -Real.log (500 / 669) ∧
    -Real.log (500 / 669) ≤ (145587981 / 500000000) := by
  have h := checkLog_sound (w := (169 / 1169)) (n := 12)
    (lo := (291175961 / 1000000000)) (hi := (145587981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669 / 500) = 1/(500 / 669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10281 : Bounds (291175961 / 1000000000) (145587981 / 500000000) (Real.log (669 / 500)) := by
  have h := reflection_log_10281_neg
  have he : Real.log (669 / 500) = -Real.log (500 / 669) := by
    rw [show ((669 / 500) : ℝ) = ((500 / 669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10282_neg : (412489723 / 1000000000) ≤ -Real.log (331 / 500) ∧
    -Real.log (331 / 500) ≤ (103122431 / 250000000) := by
  have h := checkLog_sound (w := (169 / 831)) (n := 12)
    (lo := (412489723 / 1000000000)) (hi := (103122431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 331) = 1/(331 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10282 : Bounds (-103122431 / 250000000) (-412489723 / 1000000000) (Real.log (331 / 500)) := by
  have h := reflection_log_10282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10283_neg : (168971 / 500000000) ≤ -Real.log (500000 / 500169) ∧
    -Real.log (500000 / 500169) ≤ (337943 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 1000169)) (n := 12)
    (lo := (168971 / 500000000)) (hi := (337943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500169 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500169 / 500000) = 1/(500000 / 500169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10283 : Bounds (168971 / 500000000) (337943 / 1000000000) (Real.log (500169 / 500000)) := by
  have h := reflection_log_10283_neg
  have he : Real.log (500169 / 500000) = -Real.log (500000 / 500169) := by
    rw [show ((500169 / 500000) : ℝ) = ((500000 / 500169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10284_neg : (338057 / 1000000000) ≤ -Real.log (499831 / 500000) ∧
    -Real.log (499831 / 500000) ≤ (169029 / 500000000) := by
  have h := checkLog_sound (w := (169 / 999831)) (n := 12)
    (lo := (338057 / 1000000000)) (hi := (169029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499831) = 1/(499831 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10284 : Bounds (-169029 / 500000000) (-338057 / 1000000000) (Real.log (499831 / 500000)) := by
  have h := reflection_log_10284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10285_neg : (158631483 / 1000000000) ≤ -Real.log (500000 / 585953) ∧
    -Real.log (500000 / 585953) ≤ (39657871 / 250000000) := by
  have h := checkLog_sound (w := (85953 / 1085953)) (n := 12)
    (lo := (158631483 / 1000000000)) (hi := (39657871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585953 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585953 / 500000) = 1/(500000 / 585953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10285 : Bounds (158631483 / 1000000000) (39657871 / 250000000) (Real.log (585953 / 500000)) := by
  have h := reflection_log_10285_neg
  have he : Real.log (585953 / 500000) = -Real.log (500000 / 585953) := by
    rw [show ((585953 / 500000) : ℝ) = ((500000 / 585953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10286_neg : (47157151 / 250000000) ≤ -Real.log (414047 / 500000) ∧
    -Real.log (414047 / 500000) ≤ (37725721 / 200000000) := by
  have h := checkLog_sound (w := (85953 / 914047)) (n := 12)
    (lo := (47157151 / 250000000)) (hi := (37725721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414047) = 1/(414047 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10286 : Bounds (-37725721 / 200000000) (-47157151 / 250000000) (Real.log (414047 / 500000)) := by
  have h := reflection_log_10286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10287_neg : (19921059 / 125000000) ≤ -Real.log (100000 / 117277) ∧
    -Real.log (100000 / 117277) ≤ (159368473 / 1000000000) := by
  have h := checkLog_sound (w := (17277 / 217277)) (n := 12)
    (lo := (19921059 / 125000000)) (hi := (159368473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117277 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117277 / 100000) = 1/(100000 / 117277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10287 : Bounds (19921059 / 125000000) (159368473 / 1000000000) (Real.log (117277 / 100000)) := by
  have h := reflection_log_10287_neg
  have he : Real.log (117277 / 100000) = -Real.log (100000 / 117277) := by
    rw [show ((117277 / 100000) : ℝ) = ((100000 / 117277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10288_neg : (47418127 / 250000000) ≤ -Real.log (82723 / 100000) ∧
    -Real.log (82723 / 100000) ≤ (189672509 / 1000000000) := by
  have h := checkLog_sound (w := (17277 / 182723)) (n := 12)
    (lo := (47418127 / 250000000)) (hi := (189672509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82723) = 1/(82723 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10288 : Bounds (-189672509 / 1000000000) (-47418127 / 250000000) (Real.log (82723 / 100000)) := by
  have h := reflection_log_10288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10289_neg : (7576009 / 250000000) ≤ -Real.log (9701505271 / 10000000000) ∧
    -Real.log (9701505271 / 10000000000) ≤ (30304037 / 1000000000) := by
  have h := checkLog_sound (w := (298494729 / 19701505271)) (n := 12)
    (lo := (7576009 / 250000000)) (hi := (30304037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9701505271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9701505271) = 1/(9701505271 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10289 : Bounds (-30304037 / 1000000000) (-7576009 / 250000000) (Real.log (9701505271 / 10000000000)) := by
  have h := reflection_log_10289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10290_neg : (29997121 / 1000000000) ≤ -Real.log (242612081791 / 250000000000) ∧
    -Real.log (242612081791 / 250000000000) ≤ (14998561 / 500000000) := by
  have h := checkLog_sound (w := (7387918209 / 492612081791)) (n := 12)
    (lo := (29997121 / 1000000000)) (hi := (14998561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242612081791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242612081791) = 1/(242612081791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10290 : Bounds (-14998561 / 500000000) (-29997121 / 1000000000) (Real.log (242612081791 / 250000000000)) := by
  have h := reflection_log_10290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10291_neg : (347260087 / 1000000000) ≤ -Real.log (250000000000 / 353796187389) ∧
    -Real.log (250000000000 / 353796187389) ≤ (43407511 / 125000000) := by
  have h := checkLog_sound (w := (103796187389 / 603796187389)) (n := 12)
    (lo := (347260087 / 1000000000)) (hi := (43407511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353796187389 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353796187389 / 250000000000) = 1/(250000000000 / 353796187389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10291 : Bounds (347260087 / 1000000000) (43407511 / 125000000) (Real.log (353796187389 / 250000000000)) := by
  have h := reflection_log_10291_neg
  have he : Real.log (353796187389 / 250000000000) = -Real.log (250000000000 / 353796187389) := by
    rw [show ((353796187389 / 250000000000) : ℝ) = ((250000000000 / 353796187389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10292_neg : (17452049 / 50000000) ≤ -Real.log (50000000000 / 70885364409) ∧
    -Real.log (50000000000 / 70885364409) ≤ (349040981 / 1000000000) := by
  have h := checkLog_sound (w := (20885364409 / 120885364409)) (n := 12)
    (lo := (17452049 / 50000000)) (hi := (349040981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70885364409 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70885364409 / 50000000000) = 1/(50000000000 / 70885364409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10292 : Bounds (17452049 / 50000000) (349040981 / 1000000000) (Real.log (70885364409 / 50000000000)) := by
  have h := reflection_log_10292_neg
  have he : Real.log (70885364409 / 50000000000) = -Real.log (50000000000 / 70885364409) := by
    rw [show ((70885364409 / 50000000000) : ℝ) = ((50000000000 / 70885364409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10293_neg : (350704293 / 500000000) ≤ -Real.log (250000000000 / 504147812971) ∧
    -Real.log (250000000000 / 504147812971) ≤ (175352147 / 250000000) := by
  have h := checkLog_sound (w := (4147812971 / 1004147812971)) (n := 12)
    (lo := (4130703 / 500000000)) (hi := (8261407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((504147812971 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(504147812971 / 500000000000) = 1/(250000000000 / 504147812971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10293 : Bounds (350704293 / 500000000) (175352147 / 250000000) (Real.log (504147812971 / 250000000000)) := by
  have h := reflection_log_10293_neg
  have he : Real.log (504147812971 / 250000000000) = -Real.log (250000000000 / 504147812971) := by
    rw [show ((504147812971 / 250000000000) : ℝ) = ((250000000000 / 504147812971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10294_neg : (175916421 / 250000000) ≤ -Real.log (500000000000 / 1010574018127) ∧
    -Real.log (500000000000 / 1010574018127) ≤ (351832843 / 500000000) := by
  have h := checkLog_sound (w := (10574018127 / 2010574018127)) (n := 12)
    (lo := (1314813 / 125000000)) (hi := (2103701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1010574018127 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1010574018127 / 1000000000000) = 1/(500000000000 / 1010574018127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10294 : Bounds (175916421 / 250000000) (351832843 / 500000000) (Real.log (1010574018127 / 500000000000)) := by
  have h := reflection_log_10294_neg
  have he : Real.log (1010574018127 / 500000000000) = -Real.log (500000000000 / 1010574018127) := by
    rw [show ((1010574018127 / 500000000000) : ℝ) = ((500000000000 / 1010574018127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10295_neg : (145961533 / 500000000) ≤ -Real.log (1000 / 1339) ∧
    -Real.log (1000 / 1339) ≤ (291923067 / 1000000000) := by
  have h := checkLog_sound (w := (339 / 2339)) (n := 12)
    (lo := (145961533 / 500000000)) (hi := (291923067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1339 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1339 / 1000) = 1/(1000 / 1339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10295 : Bounds (145961533 / 500000000) (291923067 / 1000000000) (Real.log (1339 / 1000)) := by
  have h := reflection_log_10295_neg
  have he : Real.log (1339 / 1000) = -Real.log (1000 / 1339) := by
    rw [show ((1339 / 1000) : ℝ) = ((1000 / 1339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10296_neg : (414001439 / 1000000000) ≤ -Real.log (661 / 1000) ∧
    -Real.log (661 / 1000) ≤ (2587509 / 6250000) := by
  have h := checkLog_sound (w := (339 / 1661)) (n := 12)
    (lo := (414001439 / 1000000000)) (hi := (2587509 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 661) = 1/(661 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10296 : Bounds (-2587509 / 6250000) (-414001439 / 1000000000) (Real.log (661 / 1000)) := by
  have h := reflection_log_10296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10297_neg : (169471 / 500000000) ≤ -Real.log (1000000 / 1000339) ∧
    -Real.log (1000000 / 1000339) ≤ (338943 / 1000000000) := by
  have h := checkLog_sound (w := (339 / 2000339)) (n := 12)
    (lo := (169471 / 500000000)) (hi := (338943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000339 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000339 / 1000000) = 1/(1000000 / 1000339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10297 : Bounds (169471 / 500000000) (338943 / 1000000000) (Real.log (1000339 / 1000000)) := by
  have h := reflection_log_10297_neg
  have he : Real.log (1000339 / 1000000) = -Real.log (1000000 / 1000339) := by
    rw [show ((1000339 / 1000000) : ℝ) = ((1000000 / 1000339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10298_neg : (339057 / 1000000000) ≤ -Real.log (999661 / 1000000) ∧
    -Real.log (999661 / 1000000) ≤ (169529 / 500000000) := by
  have h := checkLog_sound (w := (339 / 1999661)) (n := 12)
    (lo := (339057 / 1000000000)) (hi := (169529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999661) = 1/(999661 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10298 : Bounds (-169529 / 500000000) (-339057 / 1000000000) (Real.log (999661 / 1000000)) := by
  have h := reflection_log_10298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10299_neg : (159085341 / 1000000000) ≤ -Real.log (500000 / 586219) ∧
    -Real.log (500000 / 586219) ≤ (79542671 / 500000000) := by
  have h := checkLog_sound (w := (86219 / 1086219)) (n := 12)
    (lo := (159085341 / 1000000000)) (hi := (79542671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586219 / 500000) = 1/(500000 / 586219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10299 : Bounds (159085341 / 1000000000) (79542671 / 500000000) (Real.log (586219 / 500000)) := by
  have h := reflection_log_10299_neg
  have he : Real.log (586219 / 500000) = -Real.log (500000 / 586219) := by
    rw [show ((586219 / 500000) : ℝ) = ((500000 / 586219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10300_neg : (151417 / 800000) ≤ -Real.log (413781 / 500000) ∧
    -Real.log (413781 / 500000) ≤ (189271251 / 1000000000) := by
  have h := checkLog_sound (w := (86219 / 913781)) (n := 12)
    (lo := (151417 / 800000)) (hi := (189271251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413781) = 1/(413781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10300 : Bounds (-189271251 / 1000000000) (-151417 / 800000) (Real.log (413781 / 500000)) := by
  have h := reflection_log_10300_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10301_neg : (312154 / 1953125) ≤ -Real.log (1000000 / 1173303) ∧
    -Real.log (1000000 / 1173303) ≤ (159822849 / 1000000000) := by
  have h := checkLog_sound (w := (173303 / 2173303)) (n := 12)
    (lo := (312154 / 1953125)) (hi := (159822849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1173303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1173303 / 1000000) = 1/(1000000 / 1173303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10301 : Bounds (312154 / 1953125) (159822849 / 1000000000) (Real.log (1173303 / 1000000)) := by
  have h := reflection_log_10301_neg
  have he : Real.log (1173303 / 1000000) = -Real.log (1000000 / 1173303) := by
    rw [show ((1173303 / 1000000) : ℝ) = ((1000000 / 1173303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10302_neg : (38063407 / 200000000) ≤ -Real.log (826697 / 1000000) ∧
    -Real.log (826697 / 1000000) ≤ (47579259 / 250000000) := by
  have h := checkLog_sound (w := (173303 / 1826697)) (n := 12)
    (lo := (38063407 / 200000000)) (hi := (47579259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 826697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 826697) = 1/(826697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10302 : Bounds (-47579259 / 250000000) (-38063407 / 200000000) (Real.log (826697 / 1000000)) := by
  have h := reflection_log_10302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10303_neg : (30494187 / 1000000000) ≤ -Real.log (969966070191 / 1000000000000) ∧
    -Real.log (969966070191 / 1000000000000) ≤ (7623547 / 250000000) := by
  have h := checkLog_sound (w := (30033929809 / 1969966070191)) (n := 12)
    (lo := (30494187 / 1000000000)) (hi := (7623547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969966070191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969966070191) = 1/(969966070191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10303 : Bounds (-7623547 / 250000000) (-30494187 / 1000000000) (Real.log (969966070191 / 1000000000000)) := by
  have h := reflection_log_10303_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


