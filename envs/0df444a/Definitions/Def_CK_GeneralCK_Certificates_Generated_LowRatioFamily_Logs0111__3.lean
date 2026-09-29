-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0111__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0111__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T01:22:40.353268+00:00
-- url     : https://prove2.me/theorems/46e36feb-8dfd-4c2f-a113-65e9c0224269
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0111 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0112, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0111 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0112, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0113)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0111 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0112, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0113)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0111 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0112, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0113) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0111 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0112, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0113).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0111 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7104_neg : (10650899 / 1000000000) ≤ -Real.log (989405620959 / 1000000000000) ∧
    -Real.log (989405620959 / 1000000000000) ≤ (106509 / 10000000) := by
  have h := checkLog_sound (w := (10594379041 / 1989405620959)) (n := 12)
    (lo := (10650899 / 1000000000)) (hi := (106509 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989405620959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989405620959) = 1/(989405620959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7104 : Bounds (-106509 / 10000000) (-10650899 / 1000000000) (Real.log (989405620959 / 1000000000000)) := by
  have h := reflection_log_7104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7105_neg : (41317927 / 200000000) ≤ -Real.log (500000000000 / 614738967149) ∧
    -Real.log (500000000000 / 614738967149) ≤ (51647409 / 250000000) := by
  have h := checkLog_sound (w := (114738967149 / 1114738967149)) (n := 12)
    (lo := (41317927 / 200000000)) (hi := (51647409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614738967149 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614738967149 / 500000000000) = 1/(500000000000 / 614738967149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7105 : Bounds (41317927 / 200000000) (51647409 / 250000000) (Real.log (614738967149 / 500000000000)) := by
  have h := reflection_log_7105_neg
  have he : Real.log (614738967149 / 500000000000) = -Real.log (500000000000 / 614738967149) := by
    rw [show ((614738967149 / 500000000000) : ℝ) = ((500000000000 / 614738967149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7106_neg : (207519531 / 1000000000) ≤ -Real.log (250000000000 / 307655438089) ∧
    -Real.log (250000000000 / 307655438089) ≤ (51879883 / 250000000) := by
  have h := checkLog_sound (w := (57655438089 / 557655438089)) (n := 12)
    (lo := (207519531 / 1000000000)) (hi := (51879883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307655438089 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307655438089 / 250000000000) = 1/(250000000000 / 307655438089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7106 : Bounds (207519531 / 1000000000) (51879883 / 250000000) (Real.log (307655438089 / 250000000000)) := by
  have h := reflection_log_7106_neg
  have he : Real.log (307655438089 / 250000000000) = -Real.log (250000000000 / 307655438089) := by
    rw [show ((307655438089 / 250000000000) : ℝ) = ((250000000000 / 307655438089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7107_neg : (207424487 / 500000000) ≤ -Real.log (3906250000 / 5914617379) ∧
    -Real.log (3906250000 / 5914617379) ≤ (16593959 / 40000000) := by
  have h := checkLog_sound (w := (2008367379 / 9820867379)) (n := 12)
    (lo := (207424487 / 500000000)) (hi := (16593959 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5914617379 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5914617379 / 3906250000) = 1/(3906250000 / 5914617379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7107 : Bounds (207424487 / 500000000) (16593959 / 40000000) (Real.log (5914617379 / 3906250000)) := by
  have h := reflection_log_7107_neg
  have he : Real.log (5914617379 / 3906250000) = -Real.log (3906250000 / 5914617379) := by
    rw [show ((5914617379 / 3906250000) : ℝ) = ((3906250000 / 5914617379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7108_neg : (415892731 / 1000000000) ≤ -Real.log (500000000000 / 757861635221) ∧
    -Real.log (500000000000 / 757861635221) ≤ (103973183 / 250000000) := by
  have h := checkLog_sound (w := (257861635221 / 1257861635221)) (n := 12)
    (lo := (415892731 / 1000000000)) (hi := (103973183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757861635221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757861635221 / 500000000000) = 1/(500000000000 / 757861635221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7108 : Bounds (415892731 / 1000000000) (103973183 / 250000000) (Real.log (757861635221 / 500000000000)) := by
  have h := reflection_log_7108_neg
  have he : Real.log (757861635221 / 500000000000) = -Real.log (500000000000 / 757861635221) := by
    rw [show ((757861635221 / 500000000000) : ℝ) = ((500000000000 / 757861635221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7109_neg : (93447209 / 500000000) ≤ -Real.log (2000 / 2411) ∧
    -Real.log (2000 / 2411) ≤ (186894419 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 4411)) (n := 12)
    (lo := (93447209 / 500000000)) (hi := (186894419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2411 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2411 / 2000) = 1/(2000 / 2411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7109 : Bounds (93447209 / 500000000) (186894419 / 1000000000) (Real.log (2411 / 2000)) := by
  have h := reflection_log_7109_neg
  have he : Real.log (2411 / 2000) = -Real.log (2000 / 2411) := by
    rw [show ((2411 / 2000) : ℝ) = ((2000 / 2411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7110_neg : (230042293 / 1000000000) ≤ -Real.log (1589 / 2000) ∧
    -Real.log (1589 / 2000) ≤ (115021147 / 500000000) := by
  have h := checkLog_sound (w := (411 / 3589)) (n := 12)
    (lo := (230042293 / 1000000000)) (hi := (115021147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1589) = 1/(1589 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7110 : Bounds (-115021147 / 500000000) (-230042293 / 1000000000) (Real.log (1589 / 2000)) := by
  have h := reflection_log_7110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7111_neg : (102739 / 500000000) ≤ -Real.log (2000000 / 2000411) ∧
    -Real.log (2000000 / 2000411) ≤ (205479 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 4000411)) (n := 12)
    (lo := (102739 / 500000000)) (hi := (205479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000411 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000411 / 2000000) = 1/(2000000 / 2000411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7111 : Bounds (102739 / 500000000) (205479 / 1000000000) (Real.log (2000411 / 2000000)) := by
  have h := reflection_log_7111_neg
  have he : Real.log (2000411 / 2000000) = -Real.log (2000000 / 2000411) := by
    rw [show ((2000411 / 2000000) : ℝ) = ((2000000 / 2000411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7112_neg : (205521 / 1000000000) ≤ -Real.log (1999589 / 2000000) ∧
    -Real.log (1999589 / 2000000) ≤ (102761 / 500000000) := by
  have h := checkLog_sound (w := (411 / 3999589)) (n := 12)
    (lo := (205521 / 1000000000)) (hi := (102761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999589) = 1/(1999589 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7112 : Bounds (-102761 / 500000000) (-205521 / 1000000000) (Real.log (1999589 / 2000000)) := by
  have h := reflection_log_7112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7113_neg : (3068767 / 31250000) ≤ -Real.log (62500 / 68949) ∧
    -Real.log (62500 / 68949) ≤ (19640109 / 200000000) := by
  have h := checkLog_sound (w := (6449 / 131449)) (n := 12)
    (lo := (3068767 / 31250000)) (hi := (19640109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68949 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68949 / 62500) = 1/(62500 / 68949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7113 : Bounds (3068767 / 31250000) (19640109 / 200000000) (Real.log (68949 / 62500)) := by
  have h := reflection_log_7113_neg
  have he : Real.log (68949 / 62500) = -Real.log (62500 / 68949) := by
    rw [show ((68949 / 62500) : ℝ) = ((62500 / 68949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7114_neg : (54452283 / 500000000) ≤ -Real.log (56051 / 62500) ∧
    -Real.log (56051 / 62500) ≤ (108904567 / 1000000000) := by
  have h := checkLog_sound (w := (6449 / 118551)) (n := 12)
    (lo := (54452283 / 500000000)) (hi := (108904567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56051) = 1/(56051 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7114 : Bounds (-108904567 / 1000000000) (-54452283 / 500000000) (Real.log (56051 / 62500)) := by
  have h := reflection_log_7114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7115_neg : (49309169 / 500000000) ≤ -Real.log (200000 / 220729) ∧
    -Real.log (200000 / 220729) ≤ (98618339 / 1000000000) := by
  have h := checkLog_sound (w := (20729 / 420729)) (n := 12)
    (lo := (49309169 / 500000000)) (hi := (98618339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220729 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220729 / 200000) = 1/(200000 / 220729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7115 : Bounds (49309169 / 500000000) (98618339 / 1000000000) (Real.log (220729 / 200000)) := by
  have h := reflection_log_7115_neg
  have he : Real.log (220729 / 200000) = -Real.log (200000 / 220729) := by
    rw [show ((220729 / 200000) : ℝ) = ((200000 / 220729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7116_neg : (109418739 / 1000000000) ≤ -Real.log (179271 / 200000) ∧
    -Real.log (179271 / 200000) ≤ (5470937 / 50000000) := by
  have h := checkLog_sound (w := (20729 / 379271)) (n := 12)
    (lo := (109418739 / 1000000000)) (hi := (5470937 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 179271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 179271) = 1/(179271 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7116 : Bounds (-5470937 / 50000000) (-109418739 / 1000000000) (Real.log (179271 / 200000)) := by
  have h := reflection_log_7116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7117_neg : (27001 / 2500000) ≤ -Real.log (39570308559 / 40000000000) ∧
    -Real.log (39570308559 / 40000000000) ≤ (10800401 / 1000000000) := by
  have h := checkLog_sound (w := (429691441 / 79570308559)) (n := 12)
    (lo := (27001 / 2500000)) (hi := (10800401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39570308559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39570308559) = 1/(39570308559 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7117 : Bounds (-10800401 / 1000000000) (-27001 / 2500000) (Real.log (39570308559 / 40000000000)) := by
  have h := reflection_log_7117_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7118_neg : (5352011 / 500000000) ≤ -Real.log (3864660399 / 3906250000) ∧
    -Real.log (3864660399 / 3906250000) ≤ (10704023 / 1000000000) := by
  have h := checkLog_sound (w := (41589601 / 7770910399)) (n := 12)
    (lo := (5352011 / 500000000)) (hi := (10704023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3864660399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3864660399) = 1/(3864660399 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7118 : Bounds (-10704023 / 1000000000) (-5352011 / 500000000) (Real.log (3864660399 / 3906250000)) := by
  have h := reflection_log_7118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7119_neg : (20710511 / 100000000) ≤ -Real.log (100000000000 / 123011186241) ∧
    -Real.log (100000000000 / 123011186241) ≤ (207105111 / 1000000000) := by
  have h := checkLog_sound (w := (23011186241 / 223011186241)) (n := 12)
    (lo := (20710511 / 100000000)) (hi := (207105111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123011186241 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123011186241 / 100000000000) = 1/(100000000000 / 123011186241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7119 : Bounds (20710511 / 100000000) (207105111 / 1000000000) (Real.log (123011186241 / 100000000000)) := by
  have h := reflection_log_7119_neg
  have he : Real.log (123011186241 / 100000000000) = -Real.log (100000000000 / 123011186241) := by
    rw [show ((123011186241 / 100000000000) : ℝ) = ((100000000000 / 123011186241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7120_neg : (208037077 / 1000000000) ≤ -Real.log (500000000000 / 615629410223) ∧
    -Real.log (500000000000 / 615629410223) ≤ (104018539 / 500000000) := by
  have h := checkLog_sound (w := (115629410223 / 1115629410223)) (n := 12)
    (lo := (208037077 / 1000000000)) (hi := (104018539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615629410223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615629410223 / 500000000000) = 1/(500000000000 / 615629410223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7120 : Bounds (208037077 / 1000000000) (104018539 / 500000000) (Real.log (615629410223 / 500000000000)) := by
  have h := reflection_log_7120_neg
  have he : Real.log (615629410223 / 500000000000) = -Real.log (500000000000 / 615629410223) := by
    rw [show ((615629410223 / 500000000000) : ℝ) = ((500000000000 / 615629410223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7121_neg : (415892731 / 1000000000) ≤ -Real.log (25000000000 / 37893081761) ∧
    -Real.log (25000000000 / 37893081761) ≤ (103973183 / 250000000) := by
  have h := checkLog_sound (w := (12893081761 / 62893081761)) (n := 12)
    (lo := (415892731 / 1000000000)) (hi := (103973183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37893081761 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37893081761 / 25000000000) = 1/(25000000000 / 37893081761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7121 : Bounds (415892731 / 1000000000) (103973183 / 250000000) (Real.log (37893081761 / 25000000000)) := by
  have h := reflection_log_7121_neg
  have he : Real.log (37893081761 / 25000000000) = -Real.log (25000000000 / 37893081761) := by
    rw [show ((37893081761 / 25000000000) : ℝ) = ((25000000000 / 37893081761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7122_neg : (416936711 / 1000000000) ≤ -Real.log (500000000000 / 758653241033) ∧
    -Real.log (500000000000 / 758653241033) ≤ (52117089 / 125000000) := by
  have h := checkLog_sound (w := (258653241033 / 1258653241033)) (n := 12)
    (lo := (416936711 / 1000000000)) (hi := (52117089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758653241033 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(758653241033 / 500000000000) = 1/(500000000000 / 758653241033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7122 : Bounds (416936711 / 1000000000) (52117089 / 125000000) (Real.log (758653241033 / 500000000000)) := by
  have h := reflection_log_7122_neg
  have he : Real.log (758653241033 / 500000000000) = -Real.log (500000000000 / 758653241033) := by
    rw [show ((758653241033 / 500000000000) : ℝ) = ((500000000000 / 758653241033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7123_neg : (93654549 / 500000000) ≤ -Real.log (500 / 603) ∧
    -Real.log (500 / 603) ≤ (187309099 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1103)) (n := 12)
    (lo := (93654549 / 500000000)) (hi := (187309099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603 / 500) = 1/(500 / 603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7123 : Bounds (93654549 / 500000000) (187309099 / 1000000000) (Real.log (603 / 500)) := by
  have h := reflection_log_7123_neg
  have he : Real.log (603 / 500) = -Real.log (500 / 603) := by
    rw [show ((603 / 500) : ℝ) = ((500 / 603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7124_neg : (230671817 / 1000000000) ≤ -Real.log (397 / 500) ∧
    -Real.log (397 / 500) ≤ (115335909 / 500000000) := by
  have h := checkLog_sound (w := (103 / 897)) (n := 12)
    (lo := (230671817 / 1000000000)) (hi := (115335909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 397) = 1/(397 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7124 : Bounds (-115335909 / 500000000) (-230671817 / 1000000000) (Real.log (397 / 500)) := by
  have h := reflection_log_7124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7125_neg : (102989 / 500000000) ≤ -Real.log (500000 / 500103) ∧
    -Real.log (500000 / 500103) ≤ (205979 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1000103)) (n := 12)
    (lo := (102989 / 500000000)) (hi := (205979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500103 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500103 / 500000) = 1/(500000 / 500103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7125 : Bounds (102989 / 500000000) (205979 / 1000000000) (Real.log (500103 / 500000)) := by
  have h := reflection_log_7125_neg
  have he : Real.log (500103 / 500000) = -Real.log (500000 / 500103) := by
    rw [show ((500103 / 500000) : ℝ) = ((500000 / 500103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7126_neg : (206021 / 1000000000) ≤ -Real.log (499897 / 500000) ∧
    -Real.log (499897 / 500000) ≤ (103011 / 500000000) := by
  have h := checkLog_sound (w := (103 / 999897)) (n := 12)
    (lo := (206021 / 1000000000)) (hi := (103011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499897) = 1/(499897 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7126 : Bounds (-103011 / 500000000) (-206021 / 1000000000) (Real.log (499897 / 500000)) := by
  have h := reflection_log_7126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7127_neg : (24608143 / 250000000) ≤ -Real.log (12500 / 13793) ∧
    -Real.log (12500 / 13793) ≤ (98432573 / 1000000000) := by
  have h := checkLog_sound (w := (1293 / 26293)) (n := 12)
    (lo := (24608143 / 250000000)) (hi := (98432573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13793 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13793 / 12500) = 1/(12500 / 13793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7127 : Bounds (24608143 / 250000000) (98432573 / 1000000000) (Real.log (13793 / 12500)) := by
  have h := reflection_log_7127_neg
  have he : Real.log (13793 / 12500) = -Real.log (12500 / 13793) := by
    rw [show ((13793 / 12500) : ℝ) = ((12500 / 13793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7128_neg : (109190061 / 1000000000) ≤ -Real.log (11207 / 12500) ∧
    -Real.log (11207 / 12500) ≤ (54595031 / 500000000) := by
  have h := checkLog_sound (w := (1293 / 23707)) (n := 12)
    (lo := (109190061 / 1000000000)) (hi := (54595031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 11207) = 1/(11207 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7128 : Bounds (-54595031 / 500000000) (-109190061 / 1000000000) (Real.log (11207 / 12500)) := by
  have h := reflection_log_7128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7129_neg : (98850269 / 1000000000) ≤ -Real.log (1000000 / 1103901) ∧
    -Real.log (1000000 / 1103901) ≤ (9885027 / 100000000) := by
  have h := checkLog_sound (w := (103901 / 2103901)) (n := 12)
    (lo := (98850269 / 1000000000)) (hi := (9885027 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1103901 / 1000000) = 1/(1000000 / 1103901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7129 : Bounds (98850269 / 1000000000) (9885027 / 100000000) (Real.log (1103901 / 1000000)) := by
  have h := reflection_log_7129_neg
  have he : Real.log (1103901 / 1000000) = -Real.log (1000000 / 1103901) := by
    rw [show ((1103901 / 1000000) : ℝ) = ((1000000 / 1103901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7130_neg : (109704381 / 1000000000) ≤ -Real.log (896099 / 1000000) ∧
    -Real.log (896099 / 1000000) ≤ (54852191 / 500000000) := by
  have h := checkLog_sound (w := (103901 / 1896099)) (n := 12)
    (lo := (109704381 / 1000000000)) (hi := (54852191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 896099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 896099) = 1/(896099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7130 : Bounds (-54852191 / 500000000) (-109704381 / 1000000000) (Real.log (896099 / 1000000)) := by
  have h := reflection_log_7130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7131_neg : (10854111 / 1000000000) ≤ -Real.log (989204582199 / 1000000000000) ∧
    -Real.log (989204582199 / 1000000000000) ≤ (339191 / 31250000) := by
  have h := checkLog_sound (w := (10795417801 / 1989204582199)) (n := 12)
    (lo := (10854111 / 1000000000)) (hi := (339191 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989204582199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989204582199) = 1/(989204582199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7131 : Bounds (-339191 / 31250000) (-10854111 / 1000000000) (Real.log (989204582199 / 1000000000000)) := by
  have h := reflection_log_7131_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7132_neg : (672343 / 62500000) ≤ -Real.log (154578151 / 156250000) ∧
    -Real.log (154578151 / 156250000) ≤ (10757489 / 1000000000) := by
  have h := checkLog_sound (w := (1671849 / 310828151)) (n := 12)
    (lo := (672343 / 62500000)) (hi := (10757489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 154578151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 154578151) = 1/(154578151 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7132 : Bounds (-10757489 / 1000000000) (-672343 / 62500000) (Real.log (154578151 / 156250000)) := by
  have h := reflection_log_7132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7133_neg : (103811317 / 500000000) ≤ -Real.log (500000000000 / 615374319621) ∧
    -Real.log (500000000000 / 615374319621) ≤ (41524527 / 200000000) := by
  have h := checkLog_sound (w := (115374319621 / 1115374319621)) (n := 12)
    (lo := (103811317 / 500000000)) (hi := (41524527 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615374319621 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615374319621 / 500000000000) = 1/(500000000000 / 615374319621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7133 : Bounds (103811317 / 500000000) (41524527 / 200000000) (Real.log (615374319621 / 500000000000)) := by
  have h := reflection_log_7133_neg
  have he : Real.log (615374319621 / 500000000000) = -Real.log (500000000000 / 615374319621) := by
    rw [show ((615374319621 / 500000000000) : ℝ) = ((500000000000 / 615374319621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7134_neg : (4171093 / 20000000) ≤ -Real.log (125000000000 / 153987031567) ∧
    -Real.log (125000000000 / 153987031567) ≤ (208554651 / 1000000000) := by
  have h := checkLog_sound (w := (28987031567 / 278987031567)) (n := 12)
    (lo := (4171093 / 20000000)) (hi := (208554651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153987031567 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153987031567 / 125000000000) = 1/(125000000000 / 153987031567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7134 : Bounds (4171093 / 20000000) (208554651 / 1000000000) (Real.log (153987031567 / 125000000000)) := by
  have h := reflection_log_7134_neg
  have he : Real.log (153987031567 / 125000000000) = -Real.log (125000000000 / 153987031567) := by
    rw [show ((153987031567 / 125000000000) : ℝ) = ((125000000000 / 153987031567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7135_neg : (416936711 / 1000000000) ≤ -Real.log (62500000000 / 94831655129) ∧
    -Real.log (62500000000 / 94831655129) ≤ (52117089 / 125000000) := by
  have h := checkLog_sound (w := (32331655129 / 157331655129)) (n := 12)
    (lo := (416936711 / 1000000000)) (hi := (52117089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94831655129 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94831655129 / 62500000000) = 1/(62500000000 / 94831655129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7135 : Bounds (416936711 / 1000000000) (52117089 / 125000000) (Real.log (94831655129 / 62500000000)) := by
  have h := reflection_log_7135_neg
  have he : Real.log (94831655129 / 62500000000) = -Real.log (62500000000 / 94831655129) := by
    rw [show ((94831655129 / 62500000000) : ℝ) = ((62500000000 / 94831655129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7136_neg : (104495229 / 250000000) ≤ -Real.log (500000000000 / 759445843829) ∧
    -Real.log (500000000000 / 759445843829) ≤ (417980917 / 1000000000) := by
  have h := checkLog_sound (w := (259445843829 / 1259445843829)) (n := 12)
    (lo := (104495229 / 250000000)) (hi := (417980917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759445843829 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759445843829 / 500000000000) = 1/(500000000000 / 759445843829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7136 : Bounds (104495229 / 250000000) (417980917 / 1000000000) (Real.log (759445843829 / 500000000000)) := by
  have h := reflection_log_7136_neg
  have he : Real.log (759445843829 / 500000000000) = -Real.log (500000000000 / 759445843829) := by
    rw [show ((759445843829 / 500000000000) : ℝ) = ((500000000000 / 759445843829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7137_neg : (93861803 / 500000000) ≤ -Real.log (2000 / 2413) ∧
    -Real.log (2000 / 2413) ≤ (187723607 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 4413)) (n := 12)
    (lo := (93861803 / 500000000)) (hi := (187723607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2413 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2413 / 2000) = 1/(2000 / 2413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7137 : Bounds (93861803 / 500000000) (187723607 / 1000000000) (Real.log (2413 / 2000)) := by
  have h := reflection_log_7137_neg
  have he : Real.log (2413 / 2000) = -Real.log (2000 / 2413) := by
    rw [show ((2413 / 2000) : ℝ) = ((2000 / 2413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7138_neg : (231301739 / 1000000000) ≤ -Real.log (1587 / 2000) ∧
    -Real.log (1587 / 2000) ≤ (11565087 / 50000000) := by
  have h := checkLog_sound (w := (413 / 3587)) (n := 12)
    (lo := (231301739 / 1000000000)) (hi := (11565087 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1587) = 1/(1587 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7138 : Bounds (-11565087 / 50000000) (-231301739 / 1000000000) (Real.log (1587 / 2000)) := by
  have h := reflection_log_7138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7139_neg : (103239 / 500000000) ≤ -Real.log (2000000 / 2000413) ∧
    -Real.log (2000000 / 2000413) ≤ (206479 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 4000413)) (n := 12)
    (lo := (103239 / 500000000)) (hi := (206479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000413 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000413 / 2000000) = 1/(2000000 / 2000413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7139 : Bounds (103239 / 500000000) (206479 / 1000000000) (Real.log (2000413 / 2000000)) := by
  have h := reflection_log_7139_neg
  have he : Real.log (2000413 / 2000000) = -Real.log (2000000 / 2000413) := by
    rw [show ((2000413 / 2000000) : ℝ) = ((2000000 / 2000413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7140_neg : (206521 / 1000000000) ≤ -Real.log (1999587 / 2000000) ∧
    -Real.log (1999587 / 2000000) ≤ (103261 / 500000000) := by
  have h := checkLog_sound (w := (413 / 3999587)) (n := 12)
    (lo := (206521 / 1000000000)) (hi := (103261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999587) = 1/(1999587 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7140 : Bounds (-103261 / 500000000) (-206521 / 1000000000) (Real.log (1999587 / 2000000)) := by
  have h := reflection_log_7140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7141_neg : (98663641 / 1000000000) ≤ -Real.log (200000 / 220739) ∧
    -Real.log (200000 / 220739) ≤ (49331821 / 500000000) := by
  have h := checkLog_sound (w := (20739 / 420739)) (n := 12)
    (lo := (98663641 / 1000000000)) (hi := (49331821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220739 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220739 / 200000) = 1/(200000 / 220739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7141 : Bounds (98663641 / 1000000000) (49331821 / 500000000) (Real.log (220739 / 200000)) := by
  have h := reflection_log_7141_neg
  have he : Real.log (220739 / 200000) = -Real.log (200000 / 220739) := by
    rw [show ((220739 / 200000) : ℝ) = ((200000 / 220739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7142_neg : (54737261 / 500000000) ≤ -Real.log (179261 / 200000) ∧
    -Real.log (179261 / 200000) ≤ (109474523 / 1000000000) := by
  have h := checkLog_sound (w := (20739 / 379261)) (n := 12)
    (lo := (54737261 / 500000000)) (hi := (109474523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 179261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 179261) = 1/(179261 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7142 : Bounds (-109474523 / 1000000000) (-54737261 / 500000000) (Real.log (179261 / 200000)) := by
  have h := reflection_log_7142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7143_neg : (99082147 / 1000000000) ≤ -Real.log (1000000 / 1104157) ∧
    -Real.log (1000000 / 1104157) ≤ (24770537 / 250000000) := by
  have h := checkLog_sound (w := (104157 / 2104157)) (n := 12)
    (lo := (99082147 / 1000000000)) (hi := (24770537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1104157 / 1000000) = 1/(1000000 / 1104157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7143 : Bounds (99082147 / 1000000000) (24770537 / 250000000) (Real.log (1104157 / 1000000)) := by
  have h := reflection_log_7143_neg
  have he : Real.log (1104157 / 1000000) = -Real.log (1000000 / 1104157) := by
    rw [show ((1104157 / 1000000) : ℝ) = ((1000000 / 1104157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7144_neg : (13748763 / 125000000) ≤ -Real.log (895843 / 1000000) ∧
    -Real.log (895843 / 1000000) ≤ (21998021 / 200000000) := by
  have h := checkLog_sound (w := (104157 / 1895843)) (n := 12)
    (lo := (13748763 / 125000000)) (hi := (21998021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 895843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 895843) = 1/(895843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7144 : Bounds (-21998021 / 200000000) (-13748763 / 125000000) (Real.log (895843 / 1000000)) := by
  have h := reflection_log_7144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7145_neg : (2726989 / 250000000) ≤ -Real.log (989151319351 / 1000000000000) ∧
    -Real.log (989151319351 / 1000000000000) ≤ (10907957 / 1000000000) := by
  have h := checkLog_sound (w := (10848680649 / 1989151319351)) (n := 12)
    (lo := (2726989 / 250000000)) (hi := (10907957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989151319351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989151319351) = 1/(989151319351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7145 : Bounds (-10907957 / 1000000000) (-2726989 / 250000000) (Real.log (989151319351 / 1000000000000)) := by
  have h := reflection_log_7145_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7146_neg : (4223 / 390625) ≤ -Real.log (39569893879 / 40000000000) ∧
    -Real.log (39569893879 / 40000000000) ≤ (10810881 / 1000000000) := by
  have h := checkLog_sound (w := (430106121 / 79569893879)) (n := 12)
    (lo := (4223 / 390625)) (hi := (10810881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39569893879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39569893879) = 1/(39569893879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7146 : Bounds (-10810881 / 1000000000) (-4223 / 390625) (Real.log (39569893879 / 40000000000)) := by
  have h := reflection_log_7146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7147_neg : (208138163 / 1000000000) ≤ -Real.log (500000000000 / 615691645143) ∧
    -Real.log (500000000000 / 615691645143) ≤ (52034541 / 250000000) := by
  have h := checkLog_sound (w := (115691645143 / 1115691645143)) (n := 12)
    (lo := (208138163 / 1000000000)) (hi := (52034541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615691645143 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615691645143 / 500000000000) = 1/(500000000000 / 615691645143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7147 : Bounds (208138163 / 1000000000) (52034541 / 250000000) (Real.log (615691645143 / 500000000000)) := by
  have h := reflection_log_7147_neg
  have he : Real.log (615691645143 / 500000000000) = -Real.log (500000000000 / 615691645143) := by
    rw [show ((615691645143 / 500000000000) : ℝ) = ((500000000000 / 615691645143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7148_neg : (52268063 / 250000000) ≤ -Real.log (125000000000 / 154066756117) ∧
    -Real.log (125000000000 / 154066756117) ≤ (209072253 / 1000000000) := by
  have h := checkLog_sound (w := (29066756117 / 279066756117)) (n := 12)
    (lo := (52268063 / 250000000)) (hi := (209072253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154066756117 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154066756117 / 125000000000) = 1/(125000000000 / 154066756117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7148 : Bounds (52268063 / 250000000) (209072253 / 1000000000) (Real.log (154066756117 / 125000000000)) := by
  have h := reflection_log_7148_neg
  have he : Real.log (154066756117 / 125000000000) = -Real.log (125000000000 / 154066756117) := by
    rw [show ((154066756117 / 125000000000) : ℝ) = ((125000000000 / 154066756117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7149_neg : (104495229 / 250000000) ≤ -Real.log (125000000000 / 189861460957) ∧
    -Real.log (125000000000 / 189861460957) ≤ (417980917 / 1000000000) := by
  have h := checkLog_sound (w := (64861460957 / 314861460957)) (n := 12)
    (lo := (104495229 / 250000000)) (hi := (417980917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189861460957 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189861460957 / 125000000000) = 1/(125000000000 / 189861460957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7149 : Bounds (104495229 / 250000000) (417980917 / 1000000000) (Real.log (189861460957 / 125000000000)) := by
  have h := reflection_log_7149_neg
  have he : Real.log (189861460957 / 125000000000) = -Real.log (125000000000 / 189861460957) := by
    rw [show ((189861460957 / 125000000000) : ℝ) = ((125000000000 / 189861460957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7150_neg : (83805069 / 200000000) ≤ -Real.log (100000000000 / 152047889099) ∧
    -Real.log (100000000000 / 152047889099) ≤ (209512673 / 500000000) := by
  have h := checkLog_sound (w := (52047889099 / 252047889099)) (n := 12)
    (lo := (83805069 / 200000000)) (hi := (209512673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152047889099 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152047889099 / 100000000000) = 1/(100000000000 / 152047889099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7150 : Bounds (83805069 / 200000000) (209512673 / 500000000) (Real.log (152047889099 / 100000000000)) := by
  have h := reflection_log_7150_neg
  have he : Real.log (152047889099 / 100000000000) = -Real.log (100000000000 / 152047889099) := by
    rw [show ((152047889099 / 100000000000) : ℝ) = ((100000000000 / 152047889099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7151_neg : (94068971 / 500000000) ≤ -Real.log (1000 / 1207) ∧
    -Real.log (1000 / 1207) ≤ (188137943 / 1000000000) := by
  have h := checkLog_sound (w := (207 / 2207)) (n := 12)
    (lo := (94068971 / 500000000)) (hi := (188137943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207 / 1000) = 1/(1000 / 1207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7151 : Bounds (94068971 / 500000000) (188137943 / 1000000000) (Real.log (1207 / 1000)) := by
  have h := reflection_log_7151_neg
  have he : Real.log (1207 / 1000) = -Real.log (1000 / 1207) := by
    rw [show ((1207 / 1000) : ℝ) = ((1000 / 1207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7152_neg : (231932057 / 1000000000) ≤ -Real.log (793 / 1000) ∧
    -Real.log (793 / 1000) ≤ (115966029 / 500000000) := by
  have h := checkLog_sound (w := (207 / 1793)) (n := 12)
    (lo := (231932057 / 1000000000)) (hi := (115966029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 793) = 1/(793 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7152 : Bounds (-115966029 / 500000000) (-231932057 / 1000000000) (Real.log (793 / 1000)) := by
  have h := reflection_log_7152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7153_neg : (103489 / 500000000) ≤ -Real.log (1000000 / 1000207) ∧
    -Real.log (1000000 / 1000207) ≤ (206979 / 1000000000) := by
  have h := checkLog_sound (w := (207 / 2000207)) (n := 12)
    (lo := (103489 / 500000000)) (hi := (206979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000207 / 1000000) = 1/(1000000 / 1000207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7153 : Bounds (103489 / 500000000) (206979 / 1000000000) (Real.log (1000207 / 1000000)) := by
  have h := reflection_log_7153_neg
  have he : Real.log (1000207 / 1000000) = -Real.log (1000000 / 1000207) := by
    rw [show ((1000207 / 1000000) : ℝ) = ((1000000 / 1000207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7154_neg : (207021 / 1000000000) ≤ -Real.log (999793 / 1000000) ∧
    -Real.log (999793 / 1000000) ≤ (103511 / 500000000) := by
  have h := checkLog_sound (w := (207 / 1999793)) (n := 12)
    (lo := (207021 / 1000000000)) (hi := (103511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999793) = 1/(999793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7154 : Bounds (-103511 / 500000000) (-207021 / 1000000000) (Real.log (999793 / 1000000)) := by
  have h := reflection_log_7154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7155_neg : (49447781 / 500000000) ≤ -Real.log (1000000 / 1103951) ∧
    -Real.log (1000000 / 1103951) ≤ (98895563 / 1000000000) := by
  have h := checkLog_sound (w := (103951 / 2103951)) (n := 12)
    (lo := (49447781 / 500000000)) (hi := (98895563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1103951 / 1000000) = 1/(1000000 / 1103951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7155 : Bounds (49447781 / 500000000) (98895563 / 1000000000) (Real.log (1103951 / 1000000)) := by
  have h := reflection_log_7155_neg
  have he : Real.log (1103951 / 1000000) = -Real.log (1000000 / 1103951) := by
    rw [show ((1103951 / 1000000) : ℝ) = ((1000000 / 1103951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7156_neg : (5488009 / 50000000) ≤ -Real.log (896049 / 1000000) ∧
    -Real.log (896049 / 1000000) ≤ (109760181 / 1000000000) := by
  have h := checkLog_sound (w := (103951 / 1896049)) (n := 12)
    (lo := (5488009 / 50000000)) (hi := (109760181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 896049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 896049) = 1/(896049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7156 : Bounds (-109760181 / 1000000000) (-5488009 / 50000000) (Real.log (896049 / 1000000)) := by
  have h := reflection_log_7156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7157_neg : (24828493 / 250000000) ≤ -Real.log (1000000 / 1104413) ∧
    -Real.log (1000000 / 1104413) ≤ (99313973 / 1000000000) := by
  have h := checkLog_sound (w := (104413 / 2104413)) (n := 12)
    (lo := (24828493 / 250000000)) (hi := (99313973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1104413 / 1000000) = 1/(1000000 / 1104413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7157 : Bounds (24828493 / 250000000) (99313973 / 1000000000) (Real.log (1104413 / 1000000)) := by
  have h := reflection_log_7157_neg
  have he : Real.log (1104413 / 1000000) = -Real.log (1000000 / 1104413) := by
    rw [show ((1104413 / 1000000) : ℝ) = ((1000000 / 1104413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7158_neg : (110275909 / 1000000000) ≤ -Real.log (895587 / 1000000) ∧
    -Real.log (895587 / 1000000) ≤ (11027591 / 100000000) := by
  have h := checkLog_sound (w := (104413 / 1895587)) (n := 12)
    (lo := (110275909 / 1000000000)) (hi := (11027591 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 895587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 895587) = 1/(895587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7158 : Bounds (-11027591 / 100000000) (-110275909 / 1000000000) (Real.log (895587 / 1000000)) := by
  have h := reflection_log_7158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7159_neg : (10961937 / 1000000000) ≤ -Real.log (989097925431 / 1000000000000) ∧
    -Real.log (989097925431 / 1000000000000) ≤ (5480969 / 500000000) := by
  have h := checkLog_sound (w := (10902074569 / 1989097925431)) (n := 12)
    (lo := (10961937 / 1000000000)) (hi := (5480969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989097925431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989097925431) = 1/(989097925431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7159 : Bounds (-5480969 / 500000000) (-10961937 / 1000000000) (Real.log (989097925431 / 1000000000000)) := by
  have h := reflection_log_7159_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7160_neg : (10864617 / 1000000000) ≤ -Real.log (989194189599 / 1000000000000) ∧
    -Real.log (989194189599 / 1000000000000) ≤ (5432309 / 500000000) := by
  have h := checkLog_sound (w := (10805810401 / 1989194189599)) (n := 12)
    (lo := (10864617 / 1000000000)) (hi := (5432309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989194189599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989194189599) = 1/(989194189599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7160 : Bounds (-5432309 / 500000000) (-10864617 / 1000000000) (Real.log (989194189599 / 1000000000000)) := by
  have h := reflection_log_7160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7161_neg : (104327871 / 500000000) ≤ -Real.log (31250000000 / 38500649797) ∧
    -Real.log (31250000000 / 38500649797) ≤ (208655743 / 1000000000) := by
  have h := checkLog_sound (w := (7250649797 / 69750649797)) (n := 12)
    (lo := (104327871 / 500000000)) (hi := (208655743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38500649797 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38500649797 / 31250000000) = 1/(31250000000 / 38500649797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7161 : Bounds (104327871 / 500000000) (208655743 / 1000000000) (Real.log (38500649797 / 31250000000)) := by
  have h := reflection_log_7161_neg
  have he : Real.log (38500649797 / 31250000000) = -Real.log (31250000000 / 38500649797) := by
    rw [show ((38500649797 / 31250000000) : ℝ) = ((31250000000 / 38500649797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7162_neg : (209589881 / 1000000000) ≤ -Real.log (25000000000 / 30829305249) ∧
    -Real.log (25000000000 / 30829305249) ≤ (104794941 / 500000000) := by
  have h := checkLog_sound (w := (5829305249 / 55829305249)) (n := 12)
    (lo := (209589881 / 1000000000)) (hi := (104794941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30829305249 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30829305249 / 25000000000) = 1/(25000000000 / 30829305249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7162 : Bounds (209589881 / 1000000000) (104794941 / 500000000) (Real.log (30829305249 / 25000000000)) := by
  have h := reflection_log_7162_neg
  have he : Real.log (30829305249 / 25000000000) = -Real.log (25000000000 / 30829305249) := by
    rw [show ((30829305249 / 25000000000) : ℝ) = ((25000000000 / 30829305249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7163_neg : (83805069 / 200000000) ≤ -Real.log (250000000000 / 380119722747) ∧
    -Real.log (250000000000 / 380119722747) ≤ (209512673 / 500000000) := by
  have h := checkLog_sound (w := (130119722747 / 630119722747)) (n := 12)
    (lo := (83805069 / 200000000)) (hi := (209512673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380119722747 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380119722747 / 250000000000) = 1/(250000000000 / 380119722747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7163 : Bounds (83805069 / 200000000) (209512673 / 500000000) (Real.log (380119722747 / 250000000000)) := by
  have h := reflection_log_7163_neg
  have he : Real.log (380119722747 / 250000000000) = -Real.log (250000000000 / 380119722747) := by
    rw [show ((380119722747 / 250000000000) : ℝ) = ((250000000000 / 380119722747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7164_neg : (420069999 / 1000000000) ≤ -Real.log (6250000000 / 9512925599) ∧
    -Real.log (6250000000 / 9512925599) ≤ (42007 / 100000) := by
  have h := checkLog_sound (w := (3262925599 / 15762925599)) (n := 12)
    (lo := (420069999 / 1000000000)) (hi := (42007 / 100000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9512925599 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9512925599 / 6250000000) = 1/(6250000000 / 9512925599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7164 : Bounds (420069999 / 1000000000) (42007 / 100000) (Real.log (9512925599 / 6250000000)) := by
  have h := reflection_log_7164_neg
  have he : Real.log (9512925599 / 6250000000) = -Real.log (6250000000 / 9512925599) := by
    rw [show ((9512925599 / 6250000000) : ℝ) = ((6250000000 / 9512925599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7165_neg : (94276053 / 500000000) ≤ -Real.log (400 / 483) ∧
    -Real.log (400 / 483) ≤ (188552107 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 883)) (n := 12)
    (lo := (94276053 / 500000000)) (hi := (188552107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483 / 400) = 1/(400 / 483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7165 : Bounds (94276053 / 500000000) (188552107 / 1000000000) (Real.log (483 / 400)) := by
  have h := reflection_log_7165_neg
  have he : Real.log (483 / 400) = -Real.log (400 / 483) := by
    rw [show ((483 / 400) : ℝ) = ((400 / 483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7166_neg : (232562773 / 1000000000) ≤ -Real.log (317 / 400) ∧
    -Real.log (317 / 400) ≤ (116281387 / 500000000) := by
  have h := checkLog_sound (w := (83 / 717)) (n := 12)
    (lo := (232562773 / 1000000000)) (hi := (116281387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 317) = 1/(317 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7166 : Bounds (-116281387 / 500000000) (-232562773 / 1000000000) (Real.log (317 / 400)) := by
  have h := reflection_log_7166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7167_neg : (103739 / 500000000) ≤ -Real.log (400000 / 400083) ∧
    -Real.log (400000 / 400083) ≤ (207479 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 800083)) (n := 12)
    (lo := (103739 / 500000000)) (hi := (207479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400083 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400083 / 400000) = 1/(400000 / 400083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7167 : Bounds (103739 / 500000000) (207479 / 1000000000) (Real.log (400083 / 400000)) := by
  have h := reflection_log_7167_neg
  have he : Real.log (400083 / 400000) = -Real.log (400000 / 400083) := by
    rw [show ((400083 / 400000) : ℝ) = ((400000 / 400083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0112 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7168_neg : (207521 / 1000000000) ≤ -Real.log (399917 / 400000) ∧
    -Real.log (399917 / 400000) ≤ (103761 / 500000000) := by
  have h := checkLog_sound (w := (83 / 799917)) (n := 12)
    (lo := (207521 / 1000000000)) (hi := (103761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399917) = 1/(399917 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7168 : Bounds (-103761 / 500000000) (-207521 / 1000000000) (Real.log (399917 / 400000)) := by
  have h := reflection_log_7168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7169_neg : (9912743 / 100000000) ≤ -Real.log (1000000 / 1104207) ∧
    -Real.log (1000000 / 1104207) ≤ (99127431 / 1000000000) := by
  have h := checkLog_sound (w := (104207 / 2104207)) (n := 12)
    (lo := (9912743 / 100000000)) (hi := (99127431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1104207 / 1000000) = 1/(1000000 / 1104207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7169 : Bounds (9912743 / 100000000) (99127431 / 1000000000) (Real.log (1104207 / 1000000)) := by
  have h := reflection_log_7169_neg
  have he : Real.log (1104207 / 1000000) = -Real.log (1000000 / 1104207) := by
    rw [show ((1104207 / 1000000) : ℝ) = ((1000000 / 1104207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7170_neg : (110045919 / 1000000000) ≤ -Real.log (895793 / 1000000) ∧
    -Real.log (895793 / 1000000) ≤ (687787 / 6250000) := by
  have h := checkLog_sound (w := (104207 / 1895793)) (n := 12)
    (lo := (110045919 / 1000000000)) (hi := (687787 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 895793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 895793) = 1/(895793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7170 : Bounds (-687787 / 6250000) (-110045919 / 1000000000) (Real.log (895793 / 1000000)) := by
  have h := reflection_log_7170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7171_neg : (49772871 / 500000000) ≤ -Real.log (1000000 / 1104669) ∧
    -Real.log (1000000 / 1104669) ≤ (99545743 / 1000000000) := by
  have h := checkLog_sound (w := (104669 / 2104669)) (n := 12)
    (lo := (49772871 / 500000000)) (hi := (99545743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1104669 / 1000000) = 1/(1000000 / 1104669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7171 : Bounds (49772871 / 500000000) (99545743 / 1000000000) (Real.log (1104669 / 1000000)) := by
  have h := reflection_log_7171_neg
  have he : Real.log (1104669 / 1000000) = -Real.log (1000000 / 1104669) := by
    rw [show ((1104669 / 1000000) : ℝ) = ((1000000 / 1104669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7172_neg : (27640449 / 250000000) ≤ -Real.log (895331 / 1000000) ∧
    -Real.log (895331 / 1000000) ≤ (110561797 / 1000000000) := by
  have h := checkLog_sound (w := (104669 / 1895331)) (n := 12)
    (lo := (27640449 / 250000000)) (hi := (110561797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 895331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 895331) = 1/(895331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7172 : Bounds (-110561797 / 1000000000) (-27640449 / 250000000) (Real.log (895331 / 1000000)) := by
  have h := reflection_log_7172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7173_neg : (5508027 / 500000000) ≤ -Real.log (989044400439 / 1000000000000) ∧
    -Real.log (989044400439 / 1000000000000) ≤ (2203211 / 200000000) := by
  have h := checkLog_sound (w := (10955599561 / 1989044400439)) (n := 12)
    (lo := (5508027 / 500000000)) (hi := (2203211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989044400439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989044400439) = 1/(989044400439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7173 : Bounds (-2203211 / 200000000) (-5508027 / 500000000) (Real.log (989044400439 / 1000000000000)) := by
  have h := reflection_log_7173_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7174_neg : (10918489 / 1000000000) ≤ -Real.log (989140901151 / 1000000000000) ∧
    -Real.log (989140901151 / 1000000000000) ≤ (1091849 / 100000000) := by
  have h := checkLog_sound (w := (10859098849 / 1989140901151)) (n := 12)
    (lo := (10918489 / 1000000000)) (hi := (1091849 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989140901151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989140901151) = 1/(989140901151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7174 : Bounds (-1091849 / 100000000) (-10918489 / 1000000000) (Real.log (989140901151 / 1000000000000)) := by
  have h := reflection_log_7174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7175_neg : (209173349 / 1000000000) ≤ -Real.log (125000000000 / 154082332637) ∧
    -Real.log (125000000000 / 154082332637) ≤ (4183467 / 20000000) := by
  have h := checkLog_sound (w := (29082332637 / 279082332637)) (n := 12)
    (lo := (209173349 / 1000000000)) (hi := (4183467 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154082332637 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154082332637 / 125000000000) = 1/(125000000000 / 154082332637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7175 : Bounds (209173349 / 1000000000) (4183467 / 20000000) (Real.log (154082332637 / 125000000000)) := by
  have h := reflection_log_7175_neg
  have he : Real.log (154082332637 / 125000000000) = -Real.log (125000000000 / 154082332637) := by
    rw [show ((154082332637 / 125000000000) : ℝ) = ((125000000000 / 154082332637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7176_neg : (210107539 / 1000000000) ≤ -Real.log (500000000000 / 616905367959) ∧
    -Real.log (500000000000 / 616905367959) ≤ (10505377 / 50000000) := by
  have h := checkLog_sound (w := (116905367959 / 1116905367959)) (n := 12)
    (lo := (210107539 / 1000000000)) (hi := (10505377 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616905367959 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616905367959 / 500000000000) = 1/(500000000000 / 616905367959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7176 : Bounds (210107539 / 1000000000) (10505377 / 50000000) (Real.log (616905367959 / 500000000000)) := by
  have h := reflection_log_7176_neg
  have he : Real.log (616905367959 / 500000000000) = -Real.log (500000000000 / 616905367959) := by
    rw [show ((616905367959 / 500000000000) : ℝ) = ((500000000000 / 616905367959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7177_neg : (420069999 / 1000000000) ≤ -Real.log (500000000000 / 761034047919) ∧
    -Real.log (500000000000 / 761034047919) ≤ (42007 / 100000) := by
  have h := checkLog_sound (w := (261034047919 / 1261034047919)) (n := 12)
    (lo := (420069999 / 1000000000)) (hi := (42007 / 100000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761034047919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761034047919 / 500000000000) = 1/(500000000000 / 761034047919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7177 : Bounds (420069999 / 1000000000) (42007 / 100000) (Real.log (761034047919 / 500000000000)) := by
  have h := reflection_log_7177_neg
  have he : Real.log (761034047919 / 500000000000) = -Real.log (500000000000 / 761034047919) := by
    rw [show ((761034047919 / 500000000000) : ℝ) = ((500000000000 / 761034047919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7178_neg : (421114879 / 1000000000) ≤ -Real.log (500000000000 / 761829652997) ∧
    -Real.log (500000000000 / 761829652997) ≤ (164498 / 390625) := by
  have h := checkLog_sound (w := (261829652997 / 1261829652997)) (n := 12)
    (lo := (421114879 / 1000000000)) (hi := (164498 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761829652997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761829652997 / 500000000000) = 1/(500000000000 / 761829652997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7178 : Bounds (421114879 / 1000000000) (164498 / 390625) (Real.log (761829652997 / 500000000000)) := by
  have h := reflection_log_7178_neg
  have he : Real.log (761829652997 / 500000000000) = -Real.log (500000000000 / 761829652997) := by
    rw [show ((761829652997 / 500000000000) : ℝ) = ((500000000000 / 761829652997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7179_neg : (188966099 / 1000000000) ≤ -Real.log (125 / 151) ∧
    -Real.log (125 / 151) ≤ (1889661 / 10000000) := by
  have h := checkLog_sound (w := (13 / 138)) (n := 12)
    (lo := (188966099 / 1000000000)) (hi := (1889661 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151 / 125) = 1/(125 / 151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7179 : Bounds (188966099 / 1000000000) (1889661 / 10000000) (Real.log (151 / 125)) := by
  have h := reflection_log_7179_neg
  have he : Real.log (151 / 125) = -Real.log (125 / 151) := by
    rw [show ((151 / 125) : ℝ) = ((125 / 151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7180_neg : (233193887 / 1000000000) ≤ -Real.log (99 / 125) ∧
    -Real.log (99 / 125) ≤ (7287309 / 31250000) := by
  have h := checkLog_sound (w := (13 / 112)) (n := 12)
    (lo := (233193887 / 1000000000)) (hi := (7287309 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 99) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 99) = 1/(99 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7180 : Bounds (-7287309 / 31250000) (-233193887 / 1000000000) (Real.log (99 / 125)) := by
  have h := reflection_log_7180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7181_neg : (103989 / 500000000) ≤ -Real.log (62500 / 62513) ∧
    -Real.log (62500 / 62513) ≤ (207979 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 125013)) (n := 12)
    (lo := (103989 / 500000000)) (hi := (207979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62513 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62513 / 62500) = 1/(62500 / 62513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7181 : Bounds (103989 / 500000000) (207979 / 1000000000) (Real.log (62513 / 62500)) := by
  have h := reflection_log_7181_neg
  have he : Real.log (62513 / 62500) = -Real.log (62500 / 62513) := by
    rw [show ((62513 / 62500) : ℝ) = ((62500 / 62513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7182_neg : (208021 / 1000000000) ≤ -Real.log (62487 / 62500) ∧
    -Real.log (62487 / 62500) ≤ (104011 / 500000000) := by
  have h := checkLog_sound (w := (13 / 124987)) (n := 12)
    (lo := (208021 / 1000000000)) (hi := (104011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62487) = 1/(62487 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7182 : Bounds (-104011 / 500000000) (-208021 / 1000000000) (Real.log (62487 / 62500)) := by
  have h := reflection_log_7182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7183_neg : (49679169 / 500000000) ≤ -Real.log (500000 / 552231) ∧
    -Real.log (500000 / 552231) ≤ (99358339 / 1000000000) := by
  have h := checkLog_sound (w := (52231 / 1052231)) (n := 12)
    (lo := (49679169 / 500000000)) (hi := (99358339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552231 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552231 / 500000) = 1/(500000 / 552231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7183 : Bounds (49679169 / 500000000) (99358339 / 1000000000) (Real.log (552231 / 500000)) := by
  have h := reflection_log_7183_neg
  have he : Real.log (552231 / 500000) = -Real.log (500000 / 552231) := by
    rw [show ((552231 / 500000) : ℝ) = ((500000 / 552231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7184_neg : (110330623 / 1000000000) ≤ -Real.log (447769 / 500000) ∧
    -Real.log (447769 / 500000) ≤ (430979 / 3906250) := by
  have h := checkLog_sound (w := (52231 / 947769)) (n := 12)
    (lo := (110330623 / 1000000000)) (hi := (430979 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447769) = 1/(447769 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7184 : Bounds (-430979 / 3906250) (-110330623 / 1000000000) (Real.log (447769 / 500000)) := by
  have h := reflection_log_7184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7185_neg : (24944591 / 250000000) ≤ -Real.log (500000 / 552463) ∧
    -Real.log (500000 / 552463) ≤ (19955673 / 200000000) := by
  have h := checkLog_sound (w := (52463 / 1052463)) (n := 12)
    (lo := (24944591 / 250000000)) (hi := (19955673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552463 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552463 / 500000) = 1/(500000 / 552463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7185 : Bounds (24944591 / 250000000) (19955673 / 200000000) (Real.log (552463 / 500000)) := by
  have h := reflection_log_7185_neg
  have he : Real.log (552463 / 500000) = -Real.log (500000 / 552463) := by
    rw [show ((552463 / 500000) : ℝ) = ((500000 / 552463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7186_neg : (55424441 / 500000000) ≤ -Real.log (447537 / 500000) ∧
    -Real.log (447537 / 500000) ≤ (110848883 / 1000000000) := by
  have h := checkLog_sound (w := (52463 / 947537)) (n := 12)
    (lo := (55424441 / 500000000)) (hi := (110848883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447537) = 1/(447537 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7186 : Bounds (-110848883 / 1000000000) (-55424441 / 500000000) (Real.log (447537 / 500000)) := by
  have h := reflection_log_7186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7187_neg : (5535259 / 500000000) ≤ -Real.log (247247633631 / 250000000000) ∧
    -Real.log (247247633631 / 250000000000) ≤ (11070519 / 1000000000) := by
  have h := checkLog_sound (w := (2752366369 / 497247633631)) (n := 12)
    (lo := (5535259 / 500000000)) (hi := (11070519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247247633631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247247633631) = 1/(247247633631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7187 : Bounds (-11070519 / 1000000000) (-5535259 / 500000000) (Real.log (247247633631 / 250000000000)) := by
  have h := reflection_log_7187_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7188_neg : (2194457 / 200000000) ≤ -Real.log (247271922639 / 250000000000) ∧
    -Real.log (247271922639 / 250000000000) ≤ (5486143 / 500000000) := by
  have h := checkLog_sound (w := (2728077361 / 497271922639)) (n := 12)
    (lo := (2194457 / 200000000)) (hi := (5486143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247271922639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247271922639) = 1/(247271922639 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7188 : Bounds (-5486143 / 500000000) (-2194457 / 200000000) (Real.log (247271922639 / 250000000000)) := by
  have h := reflection_log_7188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7189_neg : (104844481 / 500000000) ≤ -Real.log (500000000000 / 616647199783) ∧
    -Real.log (500000000000 / 616647199783) ≤ (209688963 / 1000000000) := by
  have h := checkLog_sound (w := (116647199783 / 1116647199783)) (n := 12)
    (lo := (104844481 / 500000000)) (hi := (209688963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616647199783 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616647199783 / 500000000000) = 1/(500000000000 / 616647199783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7189 : Bounds (104844481 / 500000000) (209688963 / 1000000000) (Real.log (616647199783 / 500000000000)) := by
  have h := reflection_log_7189_neg
  have he : Real.log (616647199783 / 500000000000) = -Real.log (500000000000 / 616647199783) := by
    rw [show ((616647199783 / 500000000000) : ℝ) = ((500000000000 / 616647199783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7190_neg : (105313623 / 500000000) ≤ -Real.log (125000000000 / 154306515439) ∧
    -Real.log (125000000000 / 154306515439) ≤ (210627247 / 1000000000) := by
  have h := checkLog_sound (w := (29306515439 / 279306515439)) (n := 12)
    (lo := (105313623 / 500000000)) (hi := (210627247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154306515439 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154306515439 / 125000000000) = 1/(125000000000 / 154306515439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7190 : Bounds (105313623 / 500000000) (210627247 / 1000000000) (Real.log (154306515439 / 125000000000)) := by
  have h := reflection_log_7190_neg
  have he : Real.log (154306515439 / 125000000000) = -Real.log (125000000000 / 154306515439) := by
    rw [show ((154306515439 / 125000000000) : ℝ) = ((125000000000 / 154306515439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7191_neg : (421114879 / 1000000000) ≤ -Real.log (125000000000 / 190457413249) ∧
    -Real.log (125000000000 / 190457413249) ≤ (164498 / 390625) := by
  have h := checkLog_sound (w := (65457413249 / 315457413249)) (n := 12)
    (lo := (421114879 / 1000000000)) (hi := (164498 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190457413249 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190457413249 / 125000000000) = 1/(125000000000 / 190457413249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7191 : Bounds (421114879 / 1000000000) (164498 / 390625) (Real.log (190457413249 / 125000000000)) := by
  have h := reflection_log_7191_neg
  have he : Real.log (190457413249 / 125000000000) = -Real.log (125000000000 / 190457413249) := by
    rw [show ((190457413249 / 125000000000) : ℝ) = ((125000000000 / 190457413249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7192_neg : (211079993 / 500000000) ≤ -Real.log (500000000000 / 762626262627) ∧
    -Real.log (500000000000 / 762626262627) ≤ (422159987 / 1000000000) := by
  have h := checkLog_sound (w := (262626262627 / 1262626262627)) (n := 12)
    (lo := (211079993 / 500000000)) (hi := (422159987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762626262627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762626262627 / 500000000000) = 1/(500000000000 / 762626262627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7192 : Bounds (211079993 / 500000000) (422159987 / 1000000000) (Real.log (762626262627 / 500000000000)) := by
  have h := reflection_log_7192_neg
  have he : Real.log (762626262627 / 500000000000) = -Real.log (500000000000 / 762626262627) := by
    rw [show ((762626262627 / 500000000000) : ℝ) = ((500000000000 / 762626262627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7193_neg : (189379921 / 1000000000) ≤ -Real.log (2000 / 2417) ∧
    -Real.log (2000 / 2417) ≤ (94689961 / 500000000) := by
  have h := checkLog_sound (w := (417 / 4417)) (n := 12)
    (lo := (189379921 / 1000000000)) (hi := (94689961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2417 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2417 / 2000) = 1/(2000 / 2417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7193 : Bounds (189379921 / 1000000000) (94689961 / 500000000) (Real.log (2417 / 2000)) := by
  have h := reflection_log_7193_neg
  have he : Real.log (2417 / 2000) = -Real.log (2000 / 2417) := by
    rw [show ((2417 / 2000) : ℝ) = ((2000 / 2417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7194_neg : (233825399 / 1000000000) ≤ -Real.log (1583 / 2000) ∧
    -Real.log (1583 / 2000) ≤ (1169127 / 5000000) := by
  have h := checkLog_sound (w := (417 / 3583)) (n := 12)
    (lo := (233825399 / 1000000000)) (hi := (1169127 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1583) = 1/(1583 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7194 : Bounds (-1169127 / 5000000) (-233825399 / 1000000000) (Real.log (1583 / 2000)) := by
  have h := reflection_log_7194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7195_neg : (104239 / 500000000) ≤ -Real.log (2000000 / 2000417) ∧
    -Real.log (2000000 / 2000417) ≤ (208479 / 1000000000) := by
  have h := checkLog_sound (w := (417 / 4000417)) (n := 12)
    (lo := (104239 / 500000000)) (hi := (208479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000417 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000417 / 2000000) = 1/(2000000 / 2000417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7195 : Bounds (104239 / 500000000) (208479 / 1000000000) (Real.log (2000417 / 2000000)) := by
  have h := reflection_log_7195_neg
  have he : Real.log (2000417 / 2000000) = -Real.log (2000000 / 2000417) := by
    rw [show ((2000417 / 2000000) : ℝ) = ((2000000 / 2000417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7196_neg : (208521 / 1000000000) ≤ -Real.log (1999583 / 2000000) ∧
    -Real.log (1999583 / 2000000) ≤ (104261 / 500000000) := by
  have h := checkLog_sound (w := (417 / 3999583)) (n := 12)
    (lo := (208521 / 1000000000)) (hi := (104261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999583) = 1/(1999583 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7196 : Bounds (-104261 / 500000000) (-208521 / 1000000000) (Real.log (1999583 / 2000000)) := by
  have h := reflection_log_7196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7197_neg : (49795049 / 500000000) ≤ -Real.log (500000 / 552359) ∧
    -Real.log (500000 / 552359) ≤ (99590099 / 1000000000) := by
  have h := checkLog_sound (w := (52359 / 1052359)) (n := 12)
    (lo := (49795049 / 500000000)) (hi := (99590099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552359 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552359 / 500000) = 1/(500000 / 552359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7197 : Bounds (49795049 / 500000000) (99590099 / 1000000000) (Real.log (552359 / 500000)) := by
  have h := reflection_log_7197_neg
  have he : Real.log (552359 / 500000) = -Real.log (500000 / 552359) := by
    rw [show ((552359 / 500000) : ℝ) = ((500000 / 552359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7198_neg : (55308263 / 500000000) ≤ -Real.log (447641 / 500000) ∧
    -Real.log (447641 / 500000) ≤ (110616527 / 1000000000) := by
  have h := checkLog_sound (w := (52359 / 947641)) (n := 12)
    (lo := (55308263 / 500000000)) (hi := (110616527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447641) = 1/(447641 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7198 : Bounds (-110616527 / 1000000000) (-55308263 / 500000000) (Real.log (447641 / 500000)) := by
  have h := reflection_log_7198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7199_neg : (100010027 / 1000000000) ≤ -Real.log (500000 / 552591) ∧
    -Real.log (500000 / 552591) ≤ (25002507 / 250000000) := by
  have h := checkLog_sound (w := (52591 / 1052591)) (n := 12)
    (lo := (100010027 / 1000000000)) (hi := (25002507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552591 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552591 / 500000) = 1/(500000 / 552591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7199 : Bounds (100010027 / 1000000000) (25002507 / 250000000) (Real.log (552591 / 500000)) := by
  have h := reflection_log_7199_neg
  have he : Real.log (552591 / 500000) = -Real.log (500000 / 552591) := by
    rw [show ((552591 / 500000) : ℝ) = ((500000 / 552591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7200_neg : (111134933 / 1000000000) ≤ -Real.log (447409 / 500000) ∧
    -Real.log (447409 / 500000) ≤ (55567467 / 500000000) := by
  have h := checkLog_sound (w := (52591 / 947409)) (n := 12)
    (lo := (111134933 / 1000000000)) (hi := (55567467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447409) = 1/(447409 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7200 : Bounds (-55567467 / 500000000) (-111134933 / 1000000000) (Real.log (447409 / 500000)) := by
  have h := reflection_log_7200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7201_neg : (5562453 / 500000000) ≤ -Real.log (247234186719 / 250000000000) ∧
    -Real.log (247234186719 / 250000000000) ≤ (11124907 / 1000000000) := by
  have h := checkLog_sound (w := (2765813281 / 497234186719)) (n := 12)
    (lo := (5562453 / 500000000)) (hi := (11124907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247234186719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247234186719) = 1/(247234186719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7201 : Bounds (-11124907 / 1000000000) (-5562453 / 500000000) (Real.log (247234186719 / 250000000000)) := by
  have h := reflection_log_7201_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7202_neg : (11026427 / 1000000000) ≤ -Real.log (247258535119 / 250000000000) ∧
    -Real.log (247258535119 / 250000000000) ≤ (2756607 / 250000000) := by
  have h := checkLog_sound (w := (2741464881 / 497258535119)) (n := 12)
    (lo := (11026427 / 1000000000)) (hi := (2756607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247258535119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247258535119) = 1/(247258535119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7202 : Bounds (-2756607 / 250000000) (-11026427 / 1000000000) (Real.log (247258535119 / 250000000000)) := by
  have h := reflection_log_7202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7203_neg : (1681653 / 8000000) ≤ -Real.log (250000000000 / 308483248853) ∧
    -Real.log (250000000000 / 308483248853) ≤ (105103313 / 500000000) := by
  have h := checkLog_sound (w := (58483248853 / 558483248853)) (n := 12)
    (lo := (1681653 / 8000000)) (hi := (105103313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308483248853 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308483248853 / 250000000000) = 1/(250000000000 / 308483248853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7203 : Bounds (1681653 / 8000000) (105103313 / 500000000) (Real.log (308483248853 / 250000000000)) := by
  have h := reflection_log_7203_neg
  have he : Real.log (308483248853 / 250000000000) = -Real.log (250000000000 / 308483248853) := by
    rw [show ((308483248853 / 250000000000) : ℝ) = ((250000000000 / 308483248853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7204_neg : (164957 / 781250) ≤ -Real.log (62500000000 / 77193211357) ∧
    -Real.log (62500000000 / 77193211357) ≤ (211144961 / 1000000000) := by
  have h := checkLog_sound (w := (14693211357 / 139693211357)) (n := 12)
    (lo := (164957 / 781250)) (hi := (211144961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77193211357 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77193211357 / 62500000000) = 1/(62500000000 / 77193211357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7204 : Bounds (164957 / 781250) (211144961 / 1000000000) (Real.log (77193211357 / 62500000000)) := by
  have h := reflection_log_7204_neg
  have he : Real.log (77193211357 / 62500000000) = -Real.log (62500000000 / 77193211357) := by
    rw [show ((77193211357 / 62500000000) : ℝ) = ((62500000000 / 77193211357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7205_neg : (211079993 / 500000000) ≤ -Real.log (250000000000 / 381313131313) ∧
    -Real.log (250000000000 / 381313131313) ≤ (422159987 / 1000000000) := by
  have h := checkLog_sound (w := (131313131313 / 631313131313)) (n := 12)
    (lo := (211079993 / 500000000)) (hi := (422159987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381313131313 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381313131313 / 250000000000) = 1/(250000000000 / 381313131313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7205 : Bounds (211079993 / 500000000) (422159987 / 1000000000) (Real.log (381313131313 / 250000000000)) := by
  have h := reflection_log_7205_neg
  have he : Real.log (381313131313 / 250000000000) = -Real.log (250000000000 / 381313131313) := by
    rw [show ((381313131313 / 250000000000) : ℝ) = ((250000000000 / 381313131313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7206_neg : (10580133 / 25000000) ≤ -Real.log (62500000000 / 95427984839) ∧
    -Real.log (62500000000 / 95427984839) ≤ (423205321 / 1000000000) := by
  have h := checkLog_sound (w := (32927984839 / 157927984839)) (n := 12)
    (lo := (10580133 / 25000000)) (hi := (423205321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95427984839 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95427984839 / 62500000000) = 1/(62500000000 / 95427984839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7206 : Bounds (10580133 / 25000000) (423205321 / 1000000000) (Real.log (95427984839 / 62500000000)) := by
  have h := reflection_log_7206_neg
  have he : Real.log (95427984839 / 62500000000) = -Real.log (62500000000 / 95427984839) := by
    rw [show ((95427984839 / 62500000000) : ℝ) = ((62500000000 / 95427984839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7207_neg : (189793571 / 1000000000) ≤ -Real.log (1000 / 1209) ∧
    -Real.log (1000 / 1209) ≤ (47448393 / 250000000) := by
  have h := checkLog_sound (w := (209 / 2209)) (n := 12)
    (lo := (189793571 / 1000000000)) (hi := (47448393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209 / 1000) = 1/(1000 / 1209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7207 : Bounds (189793571 / 1000000000) (47448393 / 250000000) (Real.log (1209 / 1000)) := by
  have h := reflection_log_7207_neg
  have he : Real.log (1209 / 1000) = -Real.log (1000 / 1209) := by
    rw [show ((1209 / 1000) : ℝ) = ((1000 / 1209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7208_neg : (234457311 / 1000000000) ≤ -Real.log (791 / 1000) ∧
    -Real.log (791 / 1000) ≤ (7326791 / 31250000) := by
  have h := checkLog_sound (w := (209 / 1791)) (n := 12)
    (lo := (234457311 / 1000000000)) (hi := (7326791 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 791) = 1/(791 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7208 : Bounds (-7326791 / 31250000) (-234457311 / 1000000000) (Real.log (791 / 1000)) := by
  have h := reflection_log_7208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7209_neg : (104489 / 500000000) ≤ -Real.log (1000000 / 1000209) ∧
    -Real.log (1000000 / 1000209) ≤ (208979 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 2000209)) (n := 12)
    (lo := (104489 / 500000000)) (hi := (208979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000209 / 1000000) = 1/(1000000 / 1000209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7209 : Bounds (104489 / 500000000) (208979 / 1000000000) (Real.log (1000209 / 1000000)) := by
  have h := reflection_log_7209_neg
  have he : Real.log (1000209 / 1000000) = -Real.log (1000000 / 1000209) := by
    rw [show ((1000209 / 1000000) : ℝ) = ((1000000 / 1000209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7210_neg : (209021 / 1000000000) ≤ -Real.log (999791 / 1000000) ∧
    -Real.log (999791 / 1000000) ≤ (104511 / 500000000) := by
  have h := checkLog_sound (w := (209 / 1999791)) (n := 12)
    (lo := (209021 / 1000000000)) (hi := (104511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999791) = 1/(999791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7210 : Bounds (-104511 / 500000000) (-209021 / 1000000000) (Real.log (999791 / 1000000)) := by
  have h := reflection_log_7210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7211_neg : (19964361 / 200000000) ≤ -Real.log (500000 / 552487) ∧
    -Real.log (500000 / 552487) ≤ (49910903 / 500000000) := by
  have h := checkLog_sound (w := (52487 / 1052487)) (n := 12)
    (lo := (19964361 / 200000000)) (hi := (49910903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552487 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552487 / 500000) = 1/(500000 / 552487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7211 : Bounds (19964361 / 200000000) (49910903 / 500000000) (Real.log (552487 / 500000)) := by
  have h := reflection_log_7211_neg
  have he : Real.log (552487 / 500000) = -Real.log (500000 / 552487) := by
    rw [show ((552487 / 500000) : ℝ) = ((500000 / 552487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7212_neg : (11090251 / 100000000) ≤ -Real.log (447513 / 500000) ∧
    -Real.log (447513 / 500000) ≤ (110902511 / 1000000000) := by
  have h := checkLog_sound (w := (52487 / 947513)) (n := 12)
    (lo := (11090251 / 100000000)) (hi := (110902511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447513) = 1/(447513 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7212 : Bounds (-110902511 / 1000000000) (-11090251 / 100000000) (Real.log (447513 / 500000)) := by
  have h := reflection_log_7212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7213_neg : (25060409 / 250000000) ≤ -Real.log (500000 / 552719) ∧
    -Real.log (500000 / 552719) ≤ (100241637 / 1000000000) := by
  have h := checkLog_sound (w := (52719 / 1052719)) (n := 12)
    (lo := (25060409 / 250000000)) (hi := (100241637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552719 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552719 / 500000) = 1/(500000 / 552719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7213 : Bounds (25060409 / 250000000) (100241637 / 1000000000) (Real.log (552719 / 500000)) := by
  have h := reflection_log_7213_neg
  have he : Real.log (552719 / 500000) = -Real.log (500000 / 552719) := by
    rw [show ((552719 / 500000) : ℝ) = ((500000 / 552719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7214_neg : (22284213 / 200000000) ≤ -Real.log (447281 / 500000) ∧
    -Real.log (447281 / 500000) ≤ (55710533 / 500000000) := by
  have h := checkLog_sound (w := (52719 / 947281)) (n := 12)
    (lo := (22284213 / 200000000)) (hi := (55710533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447281) = 1/(447281 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7214 : Bounds (-55710533 / 500000000) (-22284213 / 200000000) (Real.log (447281 / 500000)) := by
  have h := reflection_log_7214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7215_neg : (11179429 / 1000000000) ≤ -Real.log (247220707039 / 250000000000) ∧
    -Real.log (247220707039 / 250000000000) ≤ (1117943 / 100000000) := by
  have h := checkLog_sound (w := (2779292961 / 497220707039)) (n := 12)
    (lo := (11179429 / 1000000000)) (hi := (1117943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247220707039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247220707039) = 1/(247220707039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7215 : Bounds (-1117943 / 100000000) (-11179429 / 1000000000) (Real.log (247220707039 / 250000000000)) := by
  have h := reflection_log_7215_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7216_neg : (2216141 / 200000000) ≤ -Real.log (247245114831 / 250000000000) ∧
    -Real.log (247245114831 / 250000000000) ≤ (5540353 / 500000000) := by
  have h := checkLog_sound (w := (2754885169 / 497245114831)) (n := 12)
    (lo := (2216141 / 200000000)) (hi := (5540353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247245114831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247245114831) = 1/(247245114831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7216 : Bounds (-5540353 / 500000000) (-2216141 / 200000000) (Real.log (247245114831 / 250000000000)) := by
  have h := reflection_log_7216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7217_neg : (52681079 / 250000000) ≤ -Real.log (125000000000 / 154321494571) ∧
    -Real.log (125000000000 / 154321494571) ≤ (210724317 / 1000000000) := by
  have h := checkLog_sound (w := (29321494571 / 279321494571)) (n := 12)
    (lo := (52681079 / 250000000)) (hi := (210724317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154321494571 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154321494571 / 125000000000) = 1/(125000000000 / 154321494571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7217 : Bounds (52681079 / 250000000) (210724317 / 1000000000) (Real.log (154321494571 / 125000000000)) := by
  have h := reflection_log_7217_neg
  have he : Real.log (154321494571 / 125000000000) = -Real.log (125000000000 / 154321494571) := by
    rw [show ((154321494571 / 125000000000) : ℝ) = ((125000000000 / 154321494571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7218_neg : (105831351 / 500000000) ≤ -Real.log (100000000000 / 123573100579) ∧
    -Real.log (100000000000 / 123573100579) ≤ (211662703 / 1000000000) := by
  have h := checkLog_sound (w := (23573100579 / 223573100579)) (n := 12)
    (lo := (105831351 / 500000000)) (hi := (211662703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123573100579 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123573100579 / 100000000000) = 1/(100000000000 / 123573100579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7218 : Bounds (105831351 / 500000000) (211662703 / 1000000000) (Real.log (123573100579 / 100000000000)) := by
  have h := reflection_log_7218_neg
  have he : Real.log (123573100579 / 100000000000) = -Real.log (100000000000 / 123573100579) := by
    rw [show ((123573100579 / 100000000000) : ℝ) = ((100000000000 / 123573100579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7219_neg : (10580133 / 25000000) ≤ -Real.log (500000000000 / 763423878711) ∧
    -Real.log (500000000000 / 763423878711) ≤ (423205321 / 1000000000) := by
  have h := checkLog_sound (w := (263423878711 / 1263423878711)) (n := 12)
    (lo := (10580133 / 25000000)) (hi := (423205321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((763423878711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(763423878711 / 500000000000) = 1/(500000000000 / 763423878711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7219 : Bounds (10580133 / 25000000) (423205321 / 1000000000) (Real.log (763423878711 / 500000000000)) := by
  have h := reflection_log_7219_neg
  have he : Real.log (763423878711 / 500000000000) = -Real.log (500000000000 / 763423878711) := by
    rw [show ((763423878711 / 500000000000) : ℝ) = ((500000000000 / 763423878711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7220_neg : (212125441 / 500000000) ≤ -Real.log (500000000000 / 764222503161) ∧
    -Real.log (500000000000 / 764222503161) ≤ (424250883 / 1000000000) := by
  have h := checkLog_sound (w := (264222503161 / 1264222503161)) (n := 12)
    (lo := (212125441 / 500000000)) (hi := (424250883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764222503161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764222503161 / 500000000000) = 1/(500000000000 / 764222503161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7220 : Bounds (212125441 / 500000000) (424250883 / 1000000000) (Real.log (764222503161 / 500000000000)) := by
  have h := reflection_log_7220_neg
  have he : Real.log (764222503161 / 500000000000) = -Real.log (500000000000 / 764222503161) := by
    rw [show ((764222503161 / 500000000000) : ℝ) = ((500000000000 / 764222503161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7221_neg : (190207051 / 1000000000) ≤ -Real.log (2000 / 2419) ∧
    -Real.log (2000 / 2419) ≤ (47551763 / 250000000) := by
  have h := checkLog_sound (w := (419 / 4419)) (n := 12)
    (lo := (190207051 / 1000000000)) (hi := (47551763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2419 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2419 / 2000) = 1/(2000 / 2419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7221 : Bounds (190207051 / 1000000000) (47551763 / 250000000) (Real.log (2419 / 2000)) := by
  have h := reflection_log_7221_neg
  have he : Real.log (2419 / 2000) = -Real.log (2000 / 2419) := by
    rw [show ((2419 / 2000) : ℝ) = ((2000 / 2419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7222_neg : (117544811 / 500000000) ≤ -Real.log (1581 / 2000) ∧
    -Real.log (1581 / 2000) ≤ (235089623 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 3581)) (n := 12)
    (lo := (117544811 / 500000000)) (hi := (235089623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1581) = 1/(1581 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7222 : Bounds (-235089623 / 1000000000) (-117544811 / 500000000) (Real.log (1581 / 2000)) := by
  have h := reflection_log_7222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7223_neg : (104739 / 500000000) ≤ -Real.log (2000000 / 2000419) ∧
    -Real.log (2000000 / 2000419) ≤ (209479 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 4000419)) (n := 12)
    (lo := (104739 / 500000000)) (hi := (209479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000419 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000419 / 2000000) = 1/(2000000 / 2000419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7223 : Bounds (104739 / 500000000) (209479 / 1000000000) (Real.log (2000419 / 2000000)) := by
  have h := reflection_log_7223_neg
  have he : Real.log (2000419 / 2000000) = -Real.log (2000000 / 2000419) := by
    rw [show ((2000419 / 2000000) : ℝ) = ((2000000 / 2000419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7224_neg : (209521 / 1000000000) ≤ -Real.log (1999581 / 2000000) ∧
    -Real.log (1999581 / 2000000) ≤ (104761 / 500000000) := by
  have h := checkLog_sound (w := (419 / 3999581)) (n := 12)
    (lo := (209521 / 1000000000)) (hi := (104761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999581) = 1/(1999581 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7224 : Bounds (-104761 / 500000000) (-209521 / 1000000000) (Real.log (1999581 / 2000000)) := by
  have h := reflection_log_7224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7225_neg : (50026729 / 500000000) ≤ -Real.log (100000 / 110523) ∧
    -Real.log (100000 / 110523) ≤ (100053459 / 1000000000) := by
  have h := checkLog_sound (w := (10523 / 210523)) (n := 12)
    (lo := (50026729 / 500000000)) (hi := (100053459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110523 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(110523 / 100000) = 1/(100000 / 110523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7225 : Bounds (50026729 / 500000000) (100053459 / 1000000000) (Real.log (110523 / 100000)) := by
  have h := reflection_log_7225_neg
  have he : Real.log (110523 / 100000) = -Real.log (100000 / 110523) := by
    rw [show ((110523 / 100000) : ℝ) = ((100000 / 110523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7226_neg : (3474643 / 31250000) ≤ -Real.log (89477 / 100000) ∧
    -Real.log (89477 / 100000) ≤ (111188577 / 1000000000) := by
  have h := checkLog_sound (w := (10523 / 189477)) (n := 12)
    (lo := (3474643 / 31250000)) (hi := (111188577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 89477) = 1/(89477 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7226 : Bounds (-111188577 / 1000000000) (-3474643 / 31250000) (Real.log (89477 / 100000)) := by
  have h := reflection_log_7226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7227_neg : (12559149 / 125000000) ≤ -Real.log (500000 / 552847) ∧
    -Real.log (500000 / 552847) ≤ (100473193 / 1000000000) := by
  have h := checkLog_sound (w := (52847 / 1052847)) (n := 12)
    (lo := (12559149 / 125000000)) (hi := (100473193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552847 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552847 / 500000) = 1/(500000 / 552847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7227 : Bounds (12559149 / 125000000) (100473193 / 1000000000) (Real.log (552847 / 500000)) := by
  have h := reflection_log_7227_neg
  have he : Real.log (552847 / 500000) = -Real.log (500000 / 552847) := by
    rw [show ((552847 / 500000) : ℝ) = ((500000 / 552847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7228_neg : (1396341 / 12500000) ≤ -Real.log (447153 / 500000) ∧
    -Real.log (447153 / 500000) ≤ (111707281 / 1000000000) := by
  have h := checkLog_sound (w := (52847 / 947153)) (n := 12)
    (lo := (1396341 / 12500000)) (hi := (111707281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447153) = 1/(447153 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7228 : Bounds (-111707281 / 1000000000) (-1396341 / 12500000) (Real.log (447153 / 500000)) := by
  have h := reflection_log_7228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7229_neg : (1404261 / 125000000) ≤ -Real.log (247207194591 / 250000000000) ∧
    -Real.log (247207194591 / 250000000000) ≤ (11234089 / 1000000000) := by
  have h := checkLog_sound (w := (2792805409 / 497207194591)) (n := 12)
    (lo := (1404261 / 125000000)) (hi := (11234089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247207194591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247207194591) = 1/(247207194591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7229 : Bounds (-11234089 / 1000000000) (-1404261 / 125000000) (Real.log (247207194591 / 250000000000)) := by
  have h := reflection_log_7229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7230_neg : (5567559 / 500000000) ≤ -Real.log (9889266471 / 10000000000) ∧
    -Real.log (9889266471 / 10000000000) ≤ (11135119 / 1000000000) := by
  have h := checkLog_sound (w := (110733529 / 19889266471)) (n := 12)
    (lo := (5567559 / 500000000)) (hi := (11135119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9889266471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9889266471) = 1/(9889266471 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7230 : Bounds (-11135119 / 1000000000) (-5567559 / 500000000) (Real.log (9889266471 / 10000000000)) := by
  have h := reflection_log_7230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7231_neg : (42248407 / 200000000) ≤ -Real.log (500000000000 / 617605641673) ∧
    -Real.log (500000000000 / 617605641673) ≤ (52810509 / 250000000) := by
  have h := checkLog_sound (w := (117605641673 / 1117605641673)) (n := 12)
    (lo := (42248407 / 200000000)) (hi := (52810509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617605641673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(617605641673 / 500000000000) = 1/(500000000000 / 617605641673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7231 : Bounds (42248407 / 200000000) (52810509 / 250000000) (Real.log (617605641673 / 500000000000)) := by
  have h := reflection_log_7231_neg
  have he : Real.log (617605641673 / 500000000000) = -Real.log (500000000000 / 617605641673) := by
    rw [show ((617605641673 / 500000000000) : ℝ) = ((500000000000 / 617605641673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0113 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7232_neg : (26522559 / 125000000) ≤ -Real.log (500000000000 / 618185498029) ∧
    -Real.log (500000000000 / 618185498029) ≤ (212180473 / 1000000000) := by
  have h := checkLog_sound (w := (118185498029 / 1118185498029)) (n := 12)
    (lo := (26522559 / 125000000)) (hi := (212180473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618185498029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618185498029 / 500000000000) = 1/(500000000000 / 618185498029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7232 : Bounds (26522559 / 125000000) (212180473 / 1000000000) (Real.log (618185498029 / 500000000000)) := by
  have h := reflection_log_7232_neg
  have he : Real.log (618185498029 / 500000000000) = -Real.log (500000000000 / 618185498029) := by
    rw [show ((618185498029 / 500000000000) : ℝ) = ((500000000000 / 618185498029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7233_neg : (212125441 / 500000000) ≤ -Real.log (12500000000 / 19105562579) ∧
    -Real.log (12500000000 / 19105562579) ≤ (424250883 / 1000000000) := by
  have h := checkLog_sound (w := (6605562579 / 31605562579)) (n := 12)
    (lo := (212125441 / 500000000)) (hi := (424250883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19105562579 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19105562579 / 12500000000) = 1/(12500000000 / 19105562579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7233 : Bounds (212125441 / 500000000) (424250883 / 1000000000) (Real.log (19105562579 / 12500000000)) := by
  have h := reflection_log_7233_neg
  have he : Real.log (19105562579 / 12500000000) = -Real.log (12500000000 / 19105562579) := by
    rw [show ((19105562579 / 12500000000) : ℝ) = ((12500000000 / 19105562579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7234_neg : (425296673 / 1000000000) ≤ -Real.log (15625000000 / 23906941809) ∧
    -Real.log (15625000000 / 23906941809) ≤ (212648337 / 500000000) := by
  have h := checkLog_sound (w := (8281941809 / 39531941809)) (n := 12)
    (lo := (425296673 / 1000000000)) (hi := (212648337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23906941809 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23906941809 / 15625000000) = 1/(15625000000 / 23906941809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7234 : Bounds (425296673 / 1000000000) (212648337 / 500000000) (Real.log (23906941809 / 15625000000)) := by
  have h := reflection_log_7234_neg
  have he : Real.log (23906941809 / 15625000000) = -Real.log (15625000000 / 23906941809) := by
    rw [show ((23906941809 / 15625000000) : ℝ) = ((15625000000 / 23906941809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7235_neg : (190620359 / 1000000000) ≤ -Real.log (100 / 121) ∧
    -Real.log (100 / 121) ≤ (4765509 / 25000000) := by
  have h := checkLog_sound (w := (21 / 221)) (n := 12)
    (lo := (190620359 / 1000000000)) (hi := (4765509 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121 / 100) = 1/(100 / 121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7235 : Bounds (190620359 / 1000000000) (4765509 / 25000000) (Real.log (121 / 100)) := by
  have h := reflection_log_7235_neg
  have he : Real.log (121 / 100) = -Real.log (100 / 121) := by
    rw [show ((121 / 100) : ℝ) = ((100 / 121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7236_neg : (235722333 / 1000000000) ≤ -Real.log (79 / 100) ∧
    -Real.log (79 / 100) ≤ (117861167 / 500000000) := by
  have h := checkLog_sound (w := (21 / 179)) (n := 12)
    (lo := (235722333 / 1000000000)) (hi := (117861167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 79) = 1/(79 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7236 : Bounds (-117861167 / 500000000) (-235722333 / 1000000000) (Real.log (79 / 100)) := by
  have h := reflection_log_7236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7237_neg : (209977 / 1000000000) ≤ -Real.log (100000 / 100021) ∧
    -Real.log (100000 / 100021) ≤ (104989 / 500000000) := by
  have h := checkLog_sound (w := (21 / 200021)) (n := 12)
    (lo := (209977 / 1000000000)) (hi := (104989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100021 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100021 / 100000) = 1/(100000 / 100021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7237 : Bounds (209977 / 1000000000) (104989 / 500000000) (Real.log (100021 / 100000)) := by
  have h := reflection_log_7237_neg
  have he : Real.log (100021 / 100000) = -Real.log (100000 / 100021) := by
    rw [show ((100021 / 100000) : ℝ) = ((100000 / 100021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7238_neg : (105011 / 500000000) ≤ -Real.log (99979 / 100000) ∧
    -Real.log (99979 / 100000) ≤ (210023 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 199979)) (n := 12)
    (lo := (105011 / 500000000)) (hi := (210023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99979) = 1/(99979 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7238 : Bounds (-210023 / 1000000000) (-105011 / 500000000) (Real.log (99979 / 100000)) := by
  have h := reflection_log_7238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7239_neg : (100285057 / 1000000000) ≤ -Real.log (500000 / 552743) ∧
    -Real.log (500000 / 552743) ≤ (50142529 / 500000000) := by
  have h := checkLog_sound (w := (52743 / 1052743)) (n := 12)
    (lo := (100285057 / 1000000000)) (hi := (50142529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552743 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552743 / 500000) = 1/(500000 / 552743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7239 : Bounds (100285057 / 1000000000) (50142529 / 500000000) (Real.log (552743 / 500000)) := by
  have h := reflection_log_7239_neg
  have he : Real.log (552743 / 500000) = -Real.log (500000 / 552743) := by
    rw [show ((552743 / 500000) : ℝ) = ((500000 / 552743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7240_neg : (27868681 / 250000000) ≤ -Real.log (447257 / 500000) ∧
    -Real.log (447257 / 500000) ≤ (4458989 / 40000000) := by
  have h := checkLog_sound (w := (52743 / 947257)) (n := 12)
    (lo := (27868681 / 250000000)) (hi := (4458989 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447257) = 1/(447257 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7240 : Bounds (-4458989 / 40000000) (-27868681 / 250000000) (Real.log (447257 / 500000)) := by
  have h := reflection_log_7240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7241_neg : (50352799 / 500000000) ≤ -Real.log (1000000 / 1105951) ∧
    -Real.log (1000000 / 1105951) ≤ (100705599 / 1000000000) := by
  have h := checkLog_sound (w := (105951 / 2105951)) (n := 12)
    (lo := (50352799 / 500000000)) (hi := (100705599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1105951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1105951 / 1000000) = 1/(1000000 / 1105951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7241 : Bounds (50352799 / 500000000) (100705599 / 1000000000) (Real.log (1105951 / 1000000)) := by
  have h := reflection_log_7241_neg
  have he : Real.log (1105951 / 1000000) = -Real.log (1000000 / 1105951) := by
    rw [show ((1105951 / 1000000) : ℝ) = ((1000000 / 1105951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7242_neg : (22398939 / 200000000) ≤ -Real.log (894049 / 1000000) ∧
    -Real.log (894049 / 1000000) ≤ (13999337 / 125000000) := by
  have h := checkLog_sound (w := (105951 / 1894049)) (n := 12)
    (lo := (22398939 / 200000000)) (hi := (13999337 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 894049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 894049) = 1/(894049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7242 : Bounds (-13999337 / 125000000) (-22398939 / 200000000) (Real.log (894049 / 1000000)) := by
  have h := reflection_log_7242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7243_neg : (11289097 / 1000000000) ≤ -Real.log (988774385599 / 1000000000000) ∧
    -Real.log (988774385599 / 1000000000000) ≤ (5644549 / 500000000) := by
  have h := checkLog_sound (w := (11225614401 / 1988774385599)) (n := 12)
    (lo := (11289097 / 1000000000)) (hi := (5644549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988774385599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988774385599) = 1/(988774385599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7243 : Bounds (-5644549 / 500000000) (-11289097 / 1000000000) (Real.log (988774385599 / 1000000000000)) := by
  have h := reflection_log_7243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7244_neg : (11189667 / 1000000000) ≤ -Real.log (247218175951 / 250000000000) ∧
    -Real.log (247218175951 / 250000000000) ≤ (2797417 / 250000000) := by
  have h := checkLog_sound (w := (2781824049 / 497218175951)) (n := 12)
    (lo := (11189667 / 1000000000)) (hi := (2797417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247218175951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247218175951) = 1/(247218175951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7244 : Bounds (-2797417 / 250000000) (-11189667 / 1000000000) (Real.log (247218175951 / 250000000000)) := by
  have h := reflection_log_7244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7245_neg : (105879891 / 500000000) ≤ -Real.log (50000000000 / 61792548803) ∧
    -Real.log (50000000000 / 61792548803) ≤ (211759783 / 1000000000) := by
  have h := checkLog_sound (w := (11792548803 / 111792548803)) (n := 12)
    (lo := (105879891 / 500000000)) (hi := (211759783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61792548803 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61792548803 / 50000000000) = 1/(50000000000 / 61792548803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7245 : Bounds (105879891 / 500000000) (211759783 / 1000000000) (Real.log (61792548803 / 50000000000)) := by
  have h := reflection_log_7245_neg
  have he : Real.log (61792548803 / 50000000000) = -Real.log (50000000000 / 61792548803) := by
    rw [show ((61792548803 / 50000000000) : ℝ) = ((50000000000 / 61792548803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7246_neg : (212700293 / 1000000000) ≤ -Real.log (500000000000 / 618506927473) ∧
    -Real.log (500000000000 / 618506927473) ≤ (106350147 / 500000000) := by
  have h := checkLog_sound (w := (118506927473 / 1118506927473)) (n := 12)
    (lo := (212700293 / 1000000000)) (hi := (106350147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618506927473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618506927473 / 500000000000) = 1/(500000000000 / 618506927473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7246 : Bounds (212700293 / 1000000000) (106350147 / 500000000) (Real.log (618506927473 / 500000000000)) := by
  have h := reflection_log_7246_neg
  have he : Real.log (618506927473 / 500000000000) = -Real.log (500000000000 / 618506927473) := by
    rw [show ((618506927473 / 500000000000) : ℝ) = ((500000000000 / 618506927473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7247_neg : (425296673 / 1000000000) ≤ -Real.log (500000000000 / 765022137887) ∧
    -Real.log (500000000000 / 765022137887) ≤ (212648337 / 500000000) := by
  have h := checkLog_sound (w := (265022137887 / 1265022137887)) (n := 12)
    (lo := (425296673 / 1000000000)) (hi := (212648337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765022137887 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765022137887 / 500000000000) = 1/(500000000000 / 765022137887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7247 : Bounds (425296673 / 1000000000) (212648337 / 500000000) (Real.log (765022137887 / 500000000000)) := by
  have h := reflection_log_7247_neg
  have he : Real.log (765022137887 / 500000000000) = -Real.log (500000000000 / 765022137887) := by
    rw [show ((765022137887 / 500000000000) : ℝ) = ((500000000000 / 765022137887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7248_neg : (426342693 / 1000000000) ≤ -Real.log (500000000000 / 765822784811) ∧
    -Real.log (500000000000 / 765822784811) ≤ (213171347 / 500000000) := by
  have h := checkLog_sound (w := (265822784811 / 1265822784811)) (n := 12)
    (lo := (426342693 / 1000000000)) (hi := (213171347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765822784811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765822784811 / 500000000000) = 1/(500000000000 / 765822784811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7248 : Bounds (426342693 / 1000000000) (213171347 / 500000000) (Real.log (765822784811 / 500000000000)) := by
  have h := reflection_log_7248_neg
  have he : Real.log (765822784811 / 500000000000) = -Real.log (500000000000 / 765822784811) := by
    rw [show ((765822784811 / 500000000000) : ℝ) = ((500000000000 / 765822784811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7249_neg : (191033497 / 1000000000) ≤ -Real.log (2000 / 2421) ∧
    -Real.log (2000 / 2421) ≤ (95516749 / 500000000) := by
  have h := checkLog_sound (w := (421 / 4421)) (n := 12)
    (lo := (191033497 / 1000000000)) (hi := (95516749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2421 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2421 / 2000) = 1/(2000 / 2421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7249 : Bounds (191033497 / 1000000000) (95516749 / 500000000) (Real.log (2421 / 2000)) := by
  have h := reflection_log_7249_neg
  have he : Real.log (2421 / 2000) = -Real.log (2000 / 2421) := by
    rw [show ((2421 / 2000) : ℝ) = ((2000 / 2421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7250_neg : (47271089 / 200000000) ≤ -Real.log (1579 / 2000) ∧
    -Real.log (1579 / 2000) ≤ (118177723 / 500000000) := by
  have h := checkLog_sound (w := (421 / 3579)) (n := 12)
    (lo := (47271089 / 200000000)) (hi := (118177723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1579) = 1/(1579 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7250 : Bounds (-118177723 / 500000000) (-47271089 / 200000000) (Real.log (1579 / 2000)) := by
  have h := reflection_log_7250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7251_neg : (210477 / 1000000000) ≤ -Real.log (2000000 / 2000421) ∧
    -Real.log (2000000 / 2000421) ≤ (105239 / 500000000) := by
  have h := checkLog_sound (w := (421 / 4000421)) (n := 12)
    (lo := (210477 / 1000000000)) (hi := (105239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000421 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000421 / 2000000) = 1/(2000000 / 2000421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7251 : Bounds (210477 / 1000000000) (105239 / 500000000) (Real.log (2000421 / 2000000)) := by
  have h := reflection_log_7251_neg
  have he : Real.log (2000421 / 2000000) = -Real.log (2000000 / 2000421) := by
    rw [show ((2000421 / 2000000) : ℝ) = ((2000000 / 2000421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7252_neg : (105261 / 500000000) ≤ -Real.log (1999579 / 2000000) ∧
    -Real.log (1999579 / 2000000) ≤ (210523 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 3999579)) (n := 12)
    (lo := (105261 / 500000000)) (hi := (210523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999579) = 1/(1999579 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7252 : Bounds (-210523 / 1000000000) (-105261 / 500000000) (Real.log (1999579 / 2000000)) := by
  have h := reflection_log_7252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7253_neg : (50257849 / 500000000) ≤ -Real.log (1000000 / 1105741) ∧
    -Real.log (1000000 / 1105741) ≤ (100515699 / 1000000000) := by
  have h := checkLog_sound (w := (105741 / 2105741)) (n := 12)
    (lo := (50257849 / 500000000)) (hi := (100515699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1105741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1105741 / 1000000) = 1/(1000000 / 1105741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7253 : Bounds (50257849 / 500000000) (100515699 / 1000000000) (Real.log (1105741 / 1000000)) := by
  have h := reflection_log_7253_neg
  have he : Real.log (1105741 / 1000000) = -Real.log (1000000 / 1105741) := by
    rw [show ((1105741 / 1000000) : ℝ) = ((1000000 / 1105741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7254_neg : (27939959 / 250000000) ≤ -Real.log (894259 / 1000000) ∧
    -Real.log (894259 / 1000000) ≤ (111759837 / 1000000000) := by
  have h := checkLog_sound (w := (105741 / 1894259)) (n := 12)
    (lo := (27939959 / 250000000)) (hi := (111759837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 894259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 894259) = 1/(894259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7254 : Bounds (-111759837 / 1000000000) (-27939959 / 250000000) (Real.log (894259 / 1000000)) := by
  have h := reflection_log_7254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7255_neg : (50468523 / 500000000) ≤ -Real.log (1000000 / 1106207) ∧
    -Real.log (1000000 / 1106207) ≤ (100937047 / 1000000000) := by
  have h := checkLog_sound (w := (106207 / 2106207)) (n := 12)
    (lo := (50468523 / 500000000)) (hi := (100937047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1106207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1106207 / 1000000) = 1/(1000000 / 1106207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7255 : Bounds (50468523 / 500000000) (100937047 / 1000000000) (Real.log (1106207 / 1000000)) := by
  have h := reflection_log_7255_neg
  have he : Real.log (1106207 / 1000000) = -Real.log (1000000 / 1106207) := by
    rw [show ((1106207 / 1000000) : ℝ) = ((1000000 / 1106207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7256_neg : (56140537 / 500000000) ≤ -Real.log (893793 / 1000000) ∧
    -Real.log (893793 / 1000000) ≤ (4491243 / 40000000) := by
  have h := checkLog_sound (w := (106207 / 1893793)) (n := 12)
    (lo := (56140537 / 500000000)) (hi := (4491243 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 893793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 893793) = 1/(893793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7256 : Bounds (-4491243 / 40000000) (-56140537 / 500000000) (Real.log (893793 / 1000000)) := by
  have h := reflection_log_7256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7257_neg : (11344027 / 1000000000) ≤ -Real.log (988720073151 / 1000000000000) ∧
    -Real.log (988720073151 / 1000000000000) ≤ (2836007 / 250000000) := by
  have h := checkLog_sound (w := (11279926849 / 1988720073151)) (n := 12)
    (lo := (11344027 / 1000000000)) (hi := (2836007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988720073151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988720073151) = 1/(988720073151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7257 : Bounds (-2836007 / 250000000) (-11344027 / 1000000000) (Real.log (988720073151 / 1000000000000)) := by
  have h := reflection_log_7257_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7258_neg : (5622069 / 500000000) ≤ -Real.log (988818840919 / 1000000000000) ∧
    -Real.log (988818840919 / 1000000000000) ≤ (11244139 / 1000000000) := by
  have h := checkLog_sound (w := (11181159081 / 1988818840919)) (n := 12)
    (lo := (5622069 / 500000000)) (hi := (11244139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988818840919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988818840919) = 1/(988818840919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7258 : Bounds (-11244139 / 1000000000) (-5622069 / 500000000) (Real.log (988818840919 / 1000000000000)) := by
  have h := reflection_log_7258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7259_neg : (42455107 / 200000000) ≤ -Real.log (500000000000 / 618244267041) ∧
    -Real.log (500000000000 / 618244267041) ≤ (13267221 / 62500000) := by
  have h := checkLog_sound (w := (118244267041 / 1118244267041)) (n := 12)
    (lo := (42455107 / 200000000)) (hi := (13267221 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618244267041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618244267041 / 500000000000) = 1/(500000000000 / 618244267041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7259 : Bounds (42455107 / 200000000) (13267221 / 62500000) (Real.log (618244267041 / 500000000000)) := by
  have h := reflection_log_7259_neg
  have he : Real.log (618244267041 / 500000000000) = -Real.log (500000000000 / 618244267041) := by
    rw [show ((618244267041 / 500000000000) : ℝ) = ((500000000000 / 618244267041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7260_neg : (5330453 / 25000000) ≤ -Real.log (125000000000 / 154706822497) ∧
    -Real.log (125000000000 / 154706822497) ≤ (213218121 / 1000000000) := by
  have h := checkLog_sound (w := (29706822497 / 279706822497)) (n := 12)
    (lo := (5330453 / 25000000)) (hi := (213218121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154706822497 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154706822497 / 125000000000) = 1/(125000000000 / 154706822497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7260 : Bounds (5330453 / 25000000) (213218121 / 1000000000) (Real.log (154706822497 / 125000000000)) := by
  have h := reflection_log_7260_neg
  have he : Real.log (154706822497 / 125000000000) = -Real.log (125000000000 / 154706822497) := by
    rw [show ((154706822497 / 125000000000) : ℝ) = ((125000000000 / 154706822497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7261_neg : (426342693 / 1000000000) ≤ -Real.log (50000000000 / 76582278481) ∧
    -Real.log (50000000000 / 76582278481) ≤ (213171347 / 500000000) := by
  have h := checkLog_sound (w := (26582278481 / 126582278481)) (n := 12)
    (lo := (426342693 / 1000000000)) (hi := (213171347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76582278481 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76582278481 / 50000000000) = 1/(50000000000 / 76582278481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7261 : Bounds (426342693 / 1000000000) (213171347 / 500000000) (Real.log (76582278481 / 50000000000)) := by
  have h := reflection_log_7261_neg
  have he : Real.log (76582278481 / 50000000000) = -Real.log (50000000000 / 76582278481) := by
    rw [show ((76582278481 / 50000000000) : ℝ) = ((50000000000 / 76582278481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7262_neg : (213694471 / 500000000) ≤ -Real.log (125000000000 / 191656111463) ∧
    -Real.log (125000000000 / 191656111463) ≤ (427388943 / 1000000000) := by
  have h := checkLog_sound (w := (66656111463 / 316656111463)) (n := 12)
    (lo := (213694471 / 500000000)) (hi := (427388943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191656111463 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191656111463 / 125000000000) = 1/(125000000000 / 191656111463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7262 : Bounds (213694471 / 500000000) (427388943 / 1000000000) (Real.log (191656111463 / 125000000000)) := by
  have h := reflection_log_7262_neg
  have he : Real.log (191656111463 / 125000000000) = -Real.log (125000000000 / 191656111463) := by
    rw [show ((191656111463 / 125000000000) : ℝ) = ((125000000000 / 191656111463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7263_neg : (2991351 / 15625000) ≤ -Real.log (1000 / 1211) ∧
    -Real.log (1000 / 1211) ≤ (38289293 / 200000000) := by
  have h := checkLog_sound (w := (211 / 2211)) (n := 12)
    (lo := (2991351 / 15625000)) (hi := (38289293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211 / 1000) = 1/(1000 / 1211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7263 : Bounds (2991351 / 15625000) (38289293 / 200000000) (Real.log (1211 / 1000)) := by
  have h := reflection_log_7263_neg
  have he : Real.log (1211 / 1000) = -Real.log (1000 / 1211) := by
    rw [show ((1211 / 1000) : ℝ) = ((1000 / 1211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7264_neg : (118494479 / 500000000) ≤ -Real.log (789 / 1000) ∧
    -Real.log (789 / 1000) ≤ (236988959 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1789)) (n := 12)
    (lo := (118494479 / 500000000)) (hi := (236988959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 789) = 1/(789 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7264 : Bounds (-236988959 / 1000000000) (-118494479 / 500000000) (Real.log (789 / 1000)) := by
  have h := reflection_log_7264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7265_neg : (210977 / 1000000000) ≤ -Real.log (1000000 / 1000211) ∧
    -Real.log (1000000 / 1000211) ≤ (105489 / 500000000) := by
  have h := checkLog_sound (w := (211 / 2000211)) (n := 12)
    (lo := (210977 / 1000000000)) (hi := (105489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000211 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000211 / 1000000) = 1/(1000000 / 1000211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7265 : Bounds (210977 / 1000000000) (105489 / 500000000) (Real.log (1000211 / 1000000)) := by
  have h := reflection_log_7265_neg
  have he : Real.log (1000211 / 1000000) = -Real.log (1000000 / 1000211) := by
    rw [show ((1000211 / 1000000) : ℝ) = ((1000000 / 1000211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7266_neg : (105511 / 500000000) ≤ -Real.log (999789 / 1000000) ∧
    -Real.log (999789 / 1000000) ≤ (211023 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1999789)) (n := 12)
    (lo := (105511 / 500000000)) (hi := (211023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999789) = 1/(999789 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7266 : Bounds (-211023 / 1000000000) (-105511 / 500000000) (Real.log (999789 / 1000000)) := by
  have h := reflection_log_7266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7267_neg : (10074719 / 100000000) ≤ -Real.log (1000000 / 1105997) ∧
    -Real.log (1000000 / 1105997) ≤ (100747191 / 1000000000) := by
  have h := checkLog_sound (w := (105997 / 2105997)) (n := 12)
    (lo := (10074719 / 100000000)) (hi := (100747191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1105997 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1105997 / 1000000) = 1/(1000000 / 1105997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7267 : Bounds (10074719 / 100000000) (100747191 / 1000000000) (Real.log (1105997 / 1000000)) := by
  have h := reflection_log_7267_neg
  have he : Real.log (1105997 / 1000000) = -Real.log (1000000 / 1105997) := by
    rw [show ((1105997 / 1000000) : ℝ) = ((1000000 / 1105997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7268_neg : (28011537 / 250000000) ≤ -Real.log (894003 / 1000000) ∧
    -Real.log (894003 / 1000000) ≤ (112046149 / 1000000000) := by
  have h := checkLog_sound (w := (105997 / 1894003)) (n := 12)
    (lo := (28011537 / 250000000)) (hi := (112046149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 894003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 894003) = 1/(894003 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7268 : Bounds (-112046149 / 1000000000) (-28011537 / 250000000) (Real.log (894003 / 1000000)) := by
  have h := reflection_log_7268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7269_neg : (101168441 / 1000000000) ≤ -Real.log (1000000 / 1106463) ∧
    -Real.log (1000000 / 1106463) ≤ (50584221 / 500000000) := by
  have h := checkLog_sound (w := (106463 / 2106463)) (n := 12)
    (lo := (101168441 / 1000000000)) (hi := (50584221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1106463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1106463 / 1000000) = 1/(1000000 / 1106463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7269 : Bounds (101168441 / 1000000000) (50584221 / 500000000) (Real.log (1106463 / 1000000)) := by
  have h := reflection_log_7269_neg
  have he : Real.log (1106463 / 1000000) = -Real.log (1000000 / 1106463) := by
    rw [show ((1106463 / 1000000) : ℝ) = ((1000000 / 1106463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7270_neg : (22513507 / 200000000) ≤ -Real.log (893537 / 1000000) ∧
    -Real.log (893537 / 1000000) ≤ (7035471 / 62500000) := by
  have h := checkLog_sound (w := (106463 / 1893537)) (n := 12)
    (lo := (22513507 / 200000000)) (hi := (7035471 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 893537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 893537) = 1/(893537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7270 : Bounds (-7035471 / 62500000) (-22513507 / 200000000) (Real.log (893537 / 1000000)) := by
  have h := reflection_log_7270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7271_neg : (11399093 / 1000000000) ≤ -Real.log (988665629631 / 1000000000000) ∧
    -Real.log (988665629631 / 1000000000000) ≤ (5699547 / 500000000) := by
  have h := checkLog_sound (w := (11334370369 / 1988665629631)) (n := 12)
    (lo := (11399093 / 1000000000)) (hi := (5699547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988665629631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988665629631) = 1/(988665629631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7271 : Bounds (-5699547 / 500000000) (-11399093 / 1000000000) (Real.log (988665629631 / 1000000000000)) := by
  have h := reflection_log_7271_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7272_neg : (11298957 / 1000000000) ≤ -Real.log (988764635991 / 1000000000000) ∧
    -Real.log (988764635991 / 1000000000000) ≤ (5649479 / 500000000) := by
  have h := checkLog_sound (w := (11235364009 / 1988764635991)) (n := 12)
    (lo := (11298957 / 1000000000)) (hi := (5649479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988764635991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988764635991) = 1/(988764635991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7272 : Bounds (-5649479 / 500000000) (-11298957 / 1000000000) (Real.log (988764635991 / 1000000000000)) := by
  have h := reflection_log_7272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7273_neg : (106396669 / 500000000) ≤ -Real.log (50000000000 / 61856447909) ∧
    -Real.log (50000000000 / 61856447909) ≤ (212793339 / 1000000000) := by
  have h := checkLog_sound (w := (11856447909 / 111856447909)) (n := 12)
    (lo := (106396669 / 500000000)) (hi := (212793339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61856447909 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61856447909 / 50000000000) = 1/(50000000000 / 61856447909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7273 : Bounds (106396669 / 500000000) (212793339 / 1000000000) (Real.log (61856447909 / 50000000000)) := by
  have h := reflection_log_7273_neg
  have he : Real.log (61856447909 / 50000000000) = -Real.log (50000000000 / 61856447909) := by
    rw [show ((61856447909 / 50000000000) : ℝ) = ((50000000000 / 61856447909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7274_neg : (26716997 / 125000000) ≤ -Real.log (62500000000 / 77393479509) ∧
    -Real.log (62500000000 / 77393479509) ≤ (213735977 / 1000000000) := by
  have h := checkLog_sound (w := (14893479509 / 139893479509)) (n := 12)
    (lo := (26716997 / 125000000)) (hi := (213735977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77393479509 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77393479509 / 62500000000) = 1/(62500000000 / 77393479509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7274 : Bounds (26716997 / 125000000) (213735977 / 1000000000) (Real.log (77393479509 / 62500000000)) := by
  have h := reflection_log_7274_neg
  have he : Real.log (77393479509 / 62500000000) = -Real.log (62500000000 / 77393479509) := by
    rw [show ((77393479509 / 62500000000) : ℝ) = ((62500000000 / 77393479509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7275_neg : (213694471 / 500000000) ≤ -Real.log (500000000000 / 766624445851) ∧
    -Real.log (500000000000 / 766624445851) ≤ (427388943 / 1000000000) := by
  have h := checkLog_sound (w := (266624445851 / 1266624445851)) (n := 12)
    (lo := (213694471 / 500000000)) (hi := (427388943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((766624445851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(766624445851 / 500000000000) = 1/(500000000000 / 766624445851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7275 : Bounds (213694471 / 500000000) (427388943 / 1000000000) (Real.log (766624445851 / 500000000000)) := by
  have h := reflection_log_7275_neg
  have he : Real.log (766624445851 / 500000000000) = -Real.log (500000000000 / 766624445851) := by
    rw [show ((766624445851 / 500000000000) : ℝ) = ((500000000000 / 766624445851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7276_neg : (214217711 / 500000000) ≤ -Real.log (500000000000 / 767427122941) ∧
    -Real.log (500000000000 / 767427122941) ≤ (428435423 / 1000000000) := by
  have h := checkLog_sound (w := (267427122941 / 1267427122941)) (n := 12)
    (lo := (214217711 / 500000000)) (hi := (428435423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767427122941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767427122941 / 500000000000) = 1/(500000000000 / 767427122941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7276 : Bounds (214217711 / 500000000) (428435423 / 1000000000) (Real.log (767427122941 / 500000000000)) := by
  have h := reflection_log_7276_neg
  have he : Real.log (767427122941 / 500000000000) = -Real.log (500000000000 / 767427122941) := by
    rw [show ((767427122941 / 500000000000) : ℝ) = ((500000000000 / 767427122941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7277_neg : (191859261 / 1000000000) ≤ -Real.log (2000 / 2423) ∧
    -Real.log (2000 / 2423) ≤ (95929631 / 500000000) := by
  have h := checkLog_sound (w := (423 / 4423)) (n := 12)
    (lo := (191859261 / 1000000000)) (hi := (95929631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2423 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2423 / 2000) = 1/(2000 / 2423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7277 : Bounds (191859261 / 1000000000) (95929631 / 500000000) (Real.log (2423 / 2000)) := by
  have h := reflection_log_7277_neg
  have he : Real.log (2423 / 2000) = -Real.log (2000 / 2423) := by
    rw [show ((2423 / 2000) : ℝ) = ((2000 / 2423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7278_neg : (29702859 / 125000000) ≤ -Real.log (1577 / 2000) ∧
    -Real.log (1577 / 2000) ≤ (237622873 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 3577)) (n := 12)
    (lo := (29702859 / 125000000)) (hi := (237622873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1577) = 1/(1577 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7278 : Bounds (-237622873 / 1000000000) (-29702859 / 125000000) (Real.log (1577 / 2000)) := by
  have h := reflection_log_7278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7279_neg : (211477 / 1000000000) ≤ -Real.log (2000000 / 2000423) ∧
    -Real.log (2000000 / 2000423) ≤ (105739 / 500000000) := by
  have h := checkLog_sound (w := (423 / 4000423)) (n := 12)
    (lo := (211477 / 1000000000)) (hi := (105739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000423 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000423 / 2000000) = 1/(2000000 / 2000423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7279 : Bounds (211477 / 1000000000) (105739 / 500000000) (Real.log (2000423 / 2000000)) := by
  have h := reflection_log_7279_neg
  have he : Real.log (2000423 / 2000000) = -Real.log (2000000 / 2000423) := by
    rw [show ((2000423 / 2000000) : ℝ) = ((2000000 / 2000423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7280_neg : (105761 / 500000000) ≤ -Real.log (1999577 / 2000000) ∧
    -Real.log (1999577 / 2000000) ≤ (211523 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 3999577)) (n := 12)
    (lo := (105761 / 500000000)) (hi := (211523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999577) = 1/(1999577 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7280 : Bounds (-211523 / 1000000000) (-105761 / 500000000) (Real.log (1999577 / 2000000)) := by
  have h := reflection_log_7280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7281_neg : (100978629 / 1000000000) ≤ -Real.log (1000000 / 1106253) ∧
    -Real.log (1000000 / 1106253) ≤ (10097863 / 100000000) := by
  have h := checkLog_sound (w := (106253 / 2106253)) (n := 12)
    (lo := (100978629 / 1000000000)) (hi := (10097863 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1106253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1106253 / 1000000) = 1/(1000000 / 1106253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7281 : Bounds (100978629 / 1000000000) (10097863 / 100000000) (Real.log (1106253 / 1000000)) := by
  have h := reflection_log_7281_neg
  have he : Real.log (1106253 / 1000000) = -Real.log (1000000 / 1106253) := by
    rw [show ((1106253 / 1000000) : ℝ) = ((1000000 / 1106253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7282_neg : (112332541 / 1000000000) ≤ -Real.log (893747 / 1000000) ∧
    -Real.log (893747 / 1000000) ≤ (56166271 / 500000000) := by
  have h := checkLog_sound (w := (106253 / 1893747)) (n := 12)
    (lo := (112332541 / 1000000000)) (hi := (56166271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 893747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 893747) = 1/(893747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7282 : Bounds (-56166271 / 500000000) (-112332541 / 1000000000) (Real.log (893747 / 1000000)) := by
  have h := reflection_log_7282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7283_neg : (20280137 / 200000000) ≤ -Real.log (6250 / 6917) ∧
    -Real.log (6250 / 6917) ≤ (50700343 / 500000000) := by
  have h := checkLog_sound (w := (667 / 13167)) (n := 12)
    (lo := (20280137 / 200000000)) (hi := (50700343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6917 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6917 / 6250) = 1/(6250 / 6917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7283 : Bounds (20280137 / 200000000) (50700343 / 500000000) (Real.log (6917 / 6250)) := by
  have h := reflection_log_7283_neg
  have he : Real.log (6917 / 6250) = -Real.log (6250 / 6917) := by
    rw [show ((6917 / 6250) : ℝ) = ((6250 / 6917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7284_neg : (112855197 / 1000000000) ≤ -Real.log (5583 / 6250) ∧
    -Real.log (5583 / 6250) ≤ (56427599 / 500000000) := by
  have h := checkLog_sound (w := (667 / 11833)) (n := 12)
    (lo := (112855197 / 1000000000)) (hi := (56427599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 5583) = 1/(5583 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7284 : Bounds (-56427599 / 500000000) (-112855197 / 1000000000) (Real.log (5583 / 6250)) := by
  have h := reflection_log_7284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7285_neg : (11454511 / 1000000000) ≤ -Real.log (38617611 / 39062500) ∧
    -Real.log (38617611 / 39062500) ≤ (715907 / 62500000) := by
  have h := checkLog_sound (w := (444889 / 77680111)) (n := 12)
    (lo := (11454511 / 1000000000)) (hi := (715907 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 38617611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 38617611) = 1/(38617611 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7285 : Bounds (-715907 / 62500000) (-11454511 / 1000000000) (Real.log (38617611 / 39062500)) := by
  have h := reflection_log_7285_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7286_neg : (1419239 / 125000000) ≤ -Real.log (988710299991 / 1000000000000) ∧
    -Real.log (988710299991 / 1000000000000) ≤ (11353913 / 1000000000) := by
  have h := checkLog_sound (w := (11289700009 / 1988710299991)) (n := 12)
    (lo := (1419239 / 125000000)) (hi := (11353913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988710299991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988710299991) = 1/(988710299991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7286 : Bounds (-11353913 / 1000000000) (-1419239 / 125000000) (Real.log (988710299991 / 1000000000000)) := by
  have h := reflection_log_7286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7287_neg : (21331117 / 100000000) ≤ -Real.log (250000000000 / 309442437289) ∧
    -Real.log (250000000000 / 309442437289) ≤ (213311171 / 1000000000) := by
  have h := checkLog_sound (w := (59442437289 / 559442437289)) (n := 12)
    (lo := (21331117 / 100000000)) (hi := (213311171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309442437289 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309442437289 / 250000000000) = 1/(250000000000 / 309442437289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7287 : Bounds (21331117 / 100000000) (213311171 / 1000000000) (Real.log (309442437289 / 250000000000)) := by
  have h := reflection_log_7287_neg
  have he : Real.log (309442437289 / 250000000000) = -Real.log (250000000000 / 309442437289) := by
    rw [show ((309442437289 / 250000000000) : ℝ) = ((250000000000 / 309442437289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7288_neg : (214255883 / 1000000000) ≤ -Real.log (250000000000 / 309734909547) ∧
    -Real.log (250000000000 / 309734909547) ≤ (53563971 / 250000000) := by
  have h := checkLog_sound (w := (59734909547 / 559734909547)) (n := 12)
    (lo := (214255883 / 1000000000)) (hi := (53563971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309734909547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309734909547 / 250000000000) = 1/(250000000000 / 309734909547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7288 : Bounds (214255883 / 1000000000) (53563971 / 250000000) (Real.log (309734909547 / 250000000000)) := by
  have h := reflection_log_7288_neg
  have he : Real.log (309734909547 / 250000000000) = -Real.log (250000000000 / 309734909547) := by
    rw [show ((309734909547 / 250000000000) : ℝ) = ((250000000000 / 309734909547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7289_neg : (214217711 / 500000000) ≤ -Real.log (25000000000 / 38371356147) ∧
    -Real.log (25000000000 / 38371356147) ≤ (428435423 / 1000000000) := by
  have h := checkLog_sound (w := (13371356147 / 63371356147)) (n := 12)
    (lo := (214217711 / 500000000)) (hi := (428435423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38371356147 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38371356147 / 25000000000) = 1/(25000000000 / 38371356147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7289 : Bounds (214217711 / 500000000) (428435423 / 1000000000) (Real.log (38371356147 / 25000000000)) := by
  have h := reflection_log_7289_neg
  have he : Real.log (38371356147 / 25000000000) = -Real.log (25000000000 / 38371356147) := by
    rw [show ((38371356147 / 25000000000) : ℝ) = ((25000000000 / 38371356147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7290_neg : (429482133 / 1000000000) ≤ -Real.log (500000000000 / 768230818009) ∧
    -Real.log (500000000000 / 768230818009) ≤ (214741067 / 500000000) := by
  have h := checkLog_sound (w := (268230818009 / 1268230818009)) (n := 12)
    (lo := (429482133 / 1000000000)) (hi := (214741067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768230818009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768230818009 / 500000000000) = 1/(500000000000 / 768230818009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7290 : Bounds (429482133 / 1000000000) (214741067 / 500000000) (Real.log (768230818009 / 500000000000)) := by
  have h := reflection_log_7290_neg
  have he : Real.log (768230818009 / 500000000000) = -Real.log (500000000000 / 768230818009) := by
    rw [show ((768230818009 / 500000000000) : ℝ) = ((500000000000 / 768230818009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7291_neg : (192271887 / 1000000000) ≤ -Real.log (250 / 303) ∧
    -Real.log (250 / 303) ≤ (12016993 / 62500000) := by
  have h := checkLog_sound (w := (53 / 553)) (n := 12)
    (lo := (192271887 / 1000000000)) (hi := (12016993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303 / 250) = 1/(250 / 303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7291 : Bounds (192271887 / 1000000000) (12016993 / 62500000) (Real.log (303 / 250)) := by
  have h := reflection_log_7291_neg
  have he : Real.log (303 / 250) = -Real.log (250 / 303) := by
    rw [show ((303 / 250) : ℝ) = ((250 / 303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7292_neg : (238257189 / 1000000000) ≤ -Real.log (197 / 250) ∧
    -Real.log (197 / 250) ≤ (23825719 / 100000000) := by
  have h := checkLog_sound (w := (53 / 447)) (n := 12)
    (lo := (238257189 / 1000000000)) (hi := (23825719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 197) = 1/(197 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7292 : Bounds (-23825719 / 100000000) (-238257189 / 1000000000) (Real.log (197 / 250)) := by
  have h := reflection_log_7292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7293_neg : (211977 / 1000000000) ≤ -Real.log (250000 / 250053) ∧
    -Real.log (250000 / 250053) ≤ (105989 / 500000000) := by
  have h := checkLog_sound (w := (53 / 500053)) (n := 12)
    (lo := (211977 / 1000000000)) (hi := (105989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250053 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250053 / 250000) = 1/(250000 / 250053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7293 : Bounds (211977 / 1000000000) (105989 / 500000000) (Real.log (250053 / 250000)) := by
  have h := reflection_log_7293_neg
  have he : Real.log (250053 / 250000) = -Real.log (250000 / 250053) := by
    rw [show ((250053 / 250000) : ℝ) = ((250000 / 250053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7294_neg : (106011 / 500000000) ≤ -Real.log (249947 / 250000) ∧
    -Real.log (249947 / 250000) ≤ (212023 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 499947)) (n := 12)
    (lo := (106011 / 500000000)) (hi := (212023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249947) = 1/(249947 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7294 : Bounds (-212023 / 1000000000) (-106011 / 500000000) (Real.log (249947 / 250000)) := by
  have h := reflection_log_7294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7295_neg : (50605007 / 500000000) ≤ -Real.log (1000000 / 1106509) ∧
    -Real.log (1000000 / 1106509) ≤ (20242003 / 200000000) := by
  have h := checkLog_sound (w := (106509 / 2106509)) (n := 12)
    (lo := (50605007 / 500000000)) (hi := (20242003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1106509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1106509 / 1000000) = 1/(1000000 / 1106509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7295 : Bounds (50605007 / 500000000) (20242003 / 200000000) (Real.log (1106509 / 1000000)) := by
  have h := reflection_log_7295_neg
  have he : Real.log (1106509 / 1000000) = -Real.log (1000000 / 1106509) := by
    rw [show ((1106509 / 1000000) : ℝ) = ((1000000 / 1106509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


